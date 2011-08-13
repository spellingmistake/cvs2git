#!/usr/bin/perl

use strict;
use warnings;
use Cwd qw(cwd);
use File::Basename qw(dirname);
use File::Path qw(mkpath);
use File::Copy qw(copy);
use File::stat qw(stat);
use File::Spec::Functions qw(rel2abs);
use Data::Dumper qw(Dumper);
use POSIX qw(dup2);
use IO::File;
use IO::File qw();
use Encode qw(encode decode);
use File::Temp qw(tempfile);
use Date::Parse;
use Date::Format;
use Getopt::Long;

my %authors = (
	'wasi'      => [ 'Thomas Egerer',      'thomas.washeim@gmx.net' ],
);

sub INITIAL() { return 0; }
sub WAITING_FOR_RCS_FILE() { return 1; }
sub PROCESSING_RCS_FILE() { return 2; }
sub WAITING_FOR_REVISION() { return 3; }
sub WAITING_FOR_INFOS() { return 4; }
sub WAITING_FOR_BRANCH_INFOS() { return 5; }
sub BUILDING_COMMIT_LOG() { return 6; }

sub create_commit_object(%$$)
{
	my ($commits, $filename, $infos) = @_;
	my (@commit_tags, $commit_tag, $epoch);

	if ($infos->{'state'} eq 'dead') {
		$infos->{'rev'} = 'dead';
	}
	$epoch = str2time("$infos->{'date'} $infos->{'time'}");

	$infos->{'commitid'} = "<unknown>" if (!exists $infos->{'commitid'});

	for my $i (-15 .. 15) {
		push @commit_tags, (sprintf('%010d', ($epoch +$i)) . '|' . $infos->{'commitid'} . '|'  . $infos->{'author'});
	}

	foreach my $tag (@commit_tags) {
		if (exists $commits->{$tag}) {
			if ($commits->{$tag}->{'comment'} eq (join("\n", @{$infos->{'comment_lines'}}))) {
				$commit_tag = $tag;
				last;
			}
		}
	}
	if (!defined $commit_tag) {
		$commit_tag = $commit_tags[5];	# yes, quite ugly :)
	}


	if (!exists $commits->{$commit_tag}) {
		$commits->{$commit_tag} = {
			"date" => $infos->{'date'},
			"time" => $infos->{'time'},
			"author" => $infos->{'author'},
			"commitid" => $infos->{'commitid'},
			"comment" => join("\n", @{$infos->{'comment_lines'}})
		};
	}
	unshift @{${$commits->{$commit_tag}}{'files'}}, {
		"revision" => $infos->{'rev'},
		"filename" => $filename
	};
}

sub extract_commits($$$%)
{
	my ($prefix, $cmd, $ignoreunknown, $commits) = @_;
	my ($state, $current_file, $current_infos, $saved_line, $count, $buf, $rest);

	$state =  INITIAL;
	$count = 0;
	select(STDOUT);
	$| = 1;

	$cmd .= " | ";
	open C, $cmd;

	while (read(C, $buf, 4096) or $rest) {
		$buf = "\n" if !defined $buf;
		$buf = ($rest . $buf) if defined $rest;

		while ($buf =~ s/(.*)\n//) {
			my $line = $1;
			#print "Looking at: $line\n";
			if ($state == INITIAL) {
				if ($line =~ /^$/) {
					$state = WAITING_FOR_RCS_FILE;
					next;
				} else {
					die "Invalid input in state INITIAL: $line\n";
				}
			} elsif ($state == WAITING_FOR_RCS_FILE) {
				if ($line =~ /RCS file: (.*?),v.*/) {
					$current_file = $1;
					$current_file =~ s|/Attic/|/|;
					$current_file =~ s/\Q$prefix\E//o;
					undef $current_infos;
					$state = PROCESSING_RCS_FILE;
					next;
				} else {
					die "Invalid input in state WAITING_FOR_RCS_FILE: $line\n";
				}
			} elsif ($state == PROCESSING_RCS_FILE) {
				if ($line eq '----------------------------') {
					$state = WAITING_FOR_REVISION;
					$saved_line = $line;
				}
				next;
			} elsif ($state == WAITING_FOR_REVISION) {
				if ($line =~ /^revision (\S+)/) {

					# is there a previous commit to store?
					if (defined $current_infos) {
						create_commit_object($commits, $current_file, $current_infos);
						undef $current_infos;
					}

					$current_infos->{rev} = $1;
					$state = WAITING_FOR_INFOS;
					next;
				} else {
					# continue building the commit message
					push @{$current_infos->{comment_lines}}, $saved_line;
					push @{$current_infos->{comment_lines}}, $line;
					$state = BUILDING_COMMIT_LOG;
					next;
				}
			} elsif ($state == WAITING_FOR_INFOS) {
				if (exists $current_infos->{commitid}) {
					die "Commit ID is already set";
				}
				if ($line =~ /date: (\S+) (.*?);/) {
					$current_infos->{date} = $1;
					$current_infos->{time} = $2;
				}
				if ($line =~ /author: (.*?);/) {
					die "unknown author '$1', please fix! ($current_file: $current_infos->{rev})" if (!defined $authors{$1} and !$ignoreunknown);
					$current_infos->{author} = $1;
				}
				if ($line =~ /state: (.*?);/) {
					$current_infos->{state} = $1;
				}
				if ($line =~ /commitid: (.*?);/) {
					$current_infos->{commitid} = $1;
				}
				$state = WAITING_FOR_BRANCH_INFOS;
				next;
			} elsif ($state == WAITING_FOR_BRANCH_INFOS) {
				if ($line =~ /^branches: /) {
					$state = BUILDING_COMMIT_LOG;
				} else {
					# message already belongs to commit message
					$state = BUILDING_COMMIT_LOG;
					push @{$current_infos->{comment_lines}}, $line;
				}
				next;
			} elsif ($state == BUILDING_COMMIT_LOG) {
				if ($line eq '----------------------------') {
					# commit will be stored if the first revision if found after the separator
					$state = WAITING_FOR_REVISION;
				} elsif($line eq '=============================================================================') {
	#				print "Found first revision for file\n";
					if (exists $current_infos->{commitid} and $current_infos->{commitid} eq '<unknown>') {
						die "Commit ID is already set to unknown";
					}
					create_commit_object($commits, $current_file, $current_infos);
					undef $current_infos;
					$state = INITIAL;
					print "\rProcessed RCS file " .  ++$count;
				} else {
					push @{$current_infos->{comment_lines}}, $line;
				}
				next;
			}
		}
		$rest = $buf;
	}
	close C;
	print "\n";
	select(STDOUT);
	$| = 0;
	$count;
}

sub do_command($$) {
	my ($cmd, $debug) = @_;

	print "$cmd\n" if $debug;
	`$cmd`;
}

sub do_command_no_output
{
	print "@_\n";
	system(@_) == 0
	  or warn "Failed to run command: $?";
}

# Parameters: filename => , command =>
sub do_command_with_redirect
{
    my %params = @_;
    my $filename = $params{filename}
      or die "Missing filename parameter";
    my $command = $params{command}
      or die "Missing commmand parameter";
    print "@$command -> $filename\n" if $params{debug};
    my $file = IO::File->new($filename, 'w')
      or die "Failed to write to file: $!";
    my $pid = fork();
    if ($pid == 0) {
	dup2(fileno($file), 1);
	exec (@$command);
	die "cmd failed";
    } elsif ($pid > 0) {
	waitpid($pid, 0);
	if ($? != 0) {
	    #die "Command returned error code $pid\n";
		return 1;
	}
	$file->close;
    } else {
	die "Fork failed with: $!";
    }

	return 0;
}

sub write_file($$) {
	my ($file, $content) = @_;
	open FILE, ">$file";
	print FILE $content;
	close FILE;
}

sub convert_charset
{
	my $comment = shift;

	# Check if contents is uft8
	my $result = $comment;
	eval {
		decode('utf-8', $comment, Encode::FB_CROAK);
	};
	if ($@) {
		my $string = decode('latin1', $comment);
		$result = encode('utf-8', $string);
	}
	return $result;
}

sub trim_comment($) {
	my $comment = shift;
	my ($ret, $count, $line);
	$ret = "";
	$count = $line = 0;

	foreach my $s (split /\n/, $comment) {
		my (@words, $words, $len);

		$s =~ s/^\s+//;
		$s =~ s/^[-+_o*]{1,2}\s?(\w|\"|\')/$1/g;
		$s =~ s/^.{1,10}:\s*// if !$line;
		$s =~ s/^\[.*?\]// if !$line;
		# some crazy folks use o for bullets :$
		#$s =~ s/^[o_] //;

		@words = split /\s/, $s;
		$words = scalar @words;
		$len = $words ? length($words[0]) : 0;

		if ((2 <= $words or ($len > 9 and $s !~ /:$/)) and !length $ret) {
			($ret = $s) =~ s/^\s//g;
		} elsif (length $ret) {
			++$count if 1 <= $words;
			last;
		}
		++$line;
	}
	if (length($ret) > 50) {
	    $ret = substr($ret, 0, 47);
	    # remove any start of a german utf-8 character
	    $ret =~ s/\xC3$//;
	    $ret .= "...";
	} elsif ($count) {
		$ret =~ s/\s*$/.../;
	}
	$ret = $comment if !length $ret;
	$ret =~ s/ \.\.\.$/.../;

	"$ret\n";
}

sub cvs2git($$$$) {
	my ($filename, $revision, $mode, $git_dir) = @_;

	my $destination_file = "$git_dir/$filename";
	mkpath(dirname($destination_file));

	my $ret;
	do {
		$ret = do_command_with_redirect(filename => $destination_file,
			debug => 1,
			command => ['cvs', 'update', '-p',
				'-r', $revision,
				$filename]);
	} while ($ret == 1);

	if (defined $mode) {
		chmod $mode, $destination_file
			or die "Failed to chmod file '$destination_file': $!";
	}
}

sub create_commits($$$$$) {
	my ($r_commits, $cvs_dir, $git_dir, $end, $squash_date) = @_;
	my (%revisions, %commits, $total, $i, $commits, $start_date, $end_date, $squashed);
	my (undef, $temp_file) = tempfile();
	$squashed = 0;

	$commits = $i = 0;
	%commits = %{$r_commits};
	$total = scalar keys %commits;

	if ($end) {
		warn "Processing $end of the $total total commits\n";
		$total = $end
	} else {
		warn "Processing $total commits\n";
	}
	foreach my $commit (sort keys %commits) {
		my ($author, $mail, $commit_str, $headline, $comment, $epoch, $date, $env, $login, $do_commit);

		$login = $commits{$commit}->{'author'};
		($author, $mail) = (defined $authors{$login}) ? @{$authors{$login}} : ($login, "unknown");

		$epoch = str2time("$commits{$commit}->{'date'} $commits{$commit}->{'time'}");
		$date = ctime($epoch);
		chomp $date;

		$do_commit = $epoch > $squash_date;

		if (!$do_commit) {
			warn "Skipping commit ${\(++$i)}/$total\n";
			$start_date = $date if (!defined $start_date);
			$end_date = $date;
			++$squashed;
		} else {
			warn "Processing commit ${\(++$i)}/$total\n";
			if ($squashed) {
				$commit_str = "CVS import: Initial squash-commit\n\nThis commit squashes $squashed commits starting from\n$start_date and ending $end_date\ninto a single commit to simplify git history.\n\nfiles\n";
				$squashed = 0;
				$env = "GIT_COMMITTER_DATE=\"$end_date\" GIT_AUTHOR_DATE=\"$end_date\" GIT_AUTHOR_NAME=\"Cvs T. Git (cvs2git.pl)\" GIT_AUTHOR_EMAIL=\"hakke_007@gmx.de\"";

				foreach my $filename (sort (keys %revisions)) {
					$commit_str .= "\t$filename: revision $revisions{$filename}\n";
					cvs2git($filename, $revisions{$filename}, undef, $git_dir);
				}
				chdir $git_dir or die "Failed to chdir to '$git_dir': $!";
				do_command_no_output('git', 'add', '.');
				print $commit_str;
				write_file($temp_file, $commit_str);
				do_command("$env git commit -F $temp_file", 1);
				++$commits;
				chdir $cvs_dir or die "Failed to chdir to '$cvs_dir': $!";
			}
		}

		$comment = $commits{$commit}->{'comment'};
		$comment = convert_charset($comment);
		$headline = trim_comment($comment);
		$comment = (" " x 4). $comment;
		$comment =~ s/\n/$& . (" " x 4)/eg;

		$commit_str = "$headline\nCVS import: $author" .
					  (($login ne $author) ? " ($login)" : "") .
					  ", $date\n\noriginal comment:\n$comment\n\nfiles:\n";
		my @git_remove;
		my %commit_str;
		foreach my $file (sort @{${$commits{$commit}}{"files"}}) {
			my ($revision, $filename, $prev_revision, $tmp);
			my $file_mode;

			$revision = ${$file}{"revision"};
			$filename = ${$file}{"filename"};
			$prev_revision = $revisions{$filename};

			next if ($revision =~ /\d+\.\d+\.\d+\./);

			if (!defined $prev_revision) {
				if ($revision eq 'dead') {
					# skip file that was initially committed to other branch
					next;
				}

				# new file, push it to git_add and set (prev_)revision(s)
				$commit_str{$filename} = "\t$filename: initial version ($revision)\n";
				my $stat = stat($filename);
				if (defined $stat) {
					$file_mode = $stat->mode & 0777;
				} else {
					# File do not exist (anymore), use some default moode
					$file_mode = 0644;
				}

				$prev_revision = $revisions{$filename} = "1.0";
			} elsif ($revision eq 'dead') {
				if (!defined $commit_str{$filename}) {
					push @git_remove, $filename;
					$commit_str{$filename} = "\t$filename: $prev_revision deleted\n";
				} else {
					do_command_no_output('rm', $filename);
				}

				# Skip the following cvs add and cvs update operations
				delete $revisions{$filename};
				next;
			} else {
				# update commit string for file update only
				$commit_str{$filename} = "\t$filename: $prev_revision -> $revision\n";
			}

			# update revision for current file
			$revisions{$filename} = $revision;

			if ($do_commit) {
				cvs2git($filename, $revision, $file_mode, $git_dir);
			}
		}

		foreach my $filename (sort (keys %commit_str)) {
			$commit_str .= $commit_str{$filename};
		}

		if ($do_commit) {
			$env = "GIT_COMMITTER_DATE=\"$date\" GIT_AUTHOR_DATE=\"$date\" GIT_AUTHOR_NAME=\"$author" .
				   (($login ne $author) ? " ($login)" : "") .
				   "\" GIT_AUTHOR_EMAIL=\"$mail\"";
			chdir $git_dir or die "Failed to chdir to '$git_dir': $!";
			foreach my $a (@git_remove) {
				if ($do_commit) {
					do_command_no_output('git', 'rm', '-f', $a);
				}
			}

			do_command_no_output('git', 'add', '.');
			# commit changes
			print $commit_str;
			write_file($temp_file, $commit_str);
			do_command("$env git commit -F $temp_file", 1);
			# unlink temporary files
			#unlink "msg", "patch.diff";
			++$commits;
		}
		return $commits if $end && $i == $end;
		chdir $cvs_dir or die "Failed to chdir to '$cvs_dir': $!";
	}
	unlink($temp_file);
	return $commits;
}

my ($cvs_dir, $git_dir, $max_commits, $squash_date, $ignoreunknown, $removeprefix, $finisher, $help, $args);

eval {
	local $SIG{__WARN__} = sub { die "@_"; };

	GetOptions(
	'cvsdir=s'        => \$cvs_dir,
	'gitdir=s'        => \$git_dir,
	'maxcommits=i'    => \$max_commits,
	'squashdate=s'    => \$squash_date,
	'finisher=s'      => \$finisher,
	'ignore-unknown'  => \$ignoreunknown,
	'remove-prefix=s' => \$removeprefix,
	'help'            => \$help);
};
chomp ($args = $@) if $@;

if ($help) {
	++$help;	# do nothing
} elsif ($args) {
	warn "There were warnings/errors parings the command line: \n\t$args\n\n";
	$help = 1;
} elsif (!defined $cvs_dir or !defined $git_dir) {
	warn "undefined ${\($cvs_dir ? 'git' : 'cvs' )}-dir, please fix!\n\n";
	$help = 1;
} elsif (defined $finisher and not -x $finisher) {
	warn "finisher script '$finisher' is not an executable file!\n\n";
	$help = 1;
}
if ($help) {
	die <<EOF;
Usage: $0 --cvsdir <cvs_dir> --gitdir <git_dir>
          [--maxcommits <max number of commits>]
          [--squashdate <date up to which commits will be squashed>]
          [--finisher <scriptlet>] [--remove-prefix <prefix>]
          [--ignore-unknown] [--help]

Convert CVS component in directory cvs-directory and store all commits
in git_directory.

cvs_directory is a working directory holding the component to convert
and must be updated prior to running this script.

git_directory must exist and a 'git init' must have been run. New
commits will be appended to the current branch, so best create a new
empty branch in the general case.

optional parameter maxcommits can be set a positive value to indicate
maximum number of commits to process.

optional parameter squashdate can be set to a date to indicate that all
files committed before that date will be squashed into in big commit.
below is a list known to be understood by squashdate:
	1995:01:24T09:08:17.1823213           ISO-8601
	1995-01-24T09:08:17.1823213
	Wed, 16 Jun 94 07:29:35 CST           Comma and day name are optional
	Thu, 13 Oct 94 10:13:13 -0700
	Wed, 9 Nov 1994 09:50:32 -0500 (EST)  Text in () will be ignored.
	21 dec 17:05                          Will be parsed in the current time zone
	21-dec 17:05
	21/dec 17:05
	21/dec/93 17:05
	1999 10:02:18 "GMT"
	16 Nov 94 22:28:20 PST

the optional parameter finisher specifies a script run in gitdir, after
the conversion process is (almost) finished; it can be used to issue
filters etc; script is given cvsdir, gitdir and number of commits
as command line arguments;

the optional parameter ignore-unknown allows for unknown authors (i.e.
those not included in authors hash to not cause this program to fail
but to keep running modifying the commit message a little.

the optional parameter remove-prefix is the prefix to be removed from
path and defaults to '/export/sina/cvs/components/tgz/'

EOF
}

$squash_date = str2time($squash_date);

my $component;
$cvs_dir = rel2abs($cvs_dir);
if ($cvs_dir =~ m|/components/tgz/*$|) {
    print "Converting toplevel\n";
} elsif ($cvs_dir =~ m|/?([^/]+)/*$|) {
	$component = $1;
	print "Converting component $component in directory $cvs_dir\n";
} else {
	die "Unable to determine component from directory name $cvs_dir\n";
}

# Qualify $git_dir if needed
$git_dir = rel2abs($git_dir);

unless (-d $git_dir) {
	die "Destination Git directory '$git_dir' not existing\n";
}

system('git', '--git-dir', "$git_dir/.git", 'rev-parse', '--is-inside-work-tree') == 0
  or die "Directory '$git_dir' is no Git working directory\n";

chdir $cvs_dir
  or die "Failed to change to directory '$cvs_dir': $!";

my (%commits, $commits);
my $prefix = $removeprefix ? $removeprefix : '/export/sina/cvs/components/tgz/';
if (defined $component) {
	$prefix =~ s/\/$//g;
    $prefix .= "/$component/";
}

#extract_commits($prefix, 'cvs log -r1 2>/dev/null', $ignoreunknown, \%commits);
extract_commits($prefix, 'cat ../cvslog', $ignoreunknown, \%commits);
#print Data::Dumper->Dump([\%commits], [qw(foo)]);
#exit;
$commits = create_commits(\%commits, $cvs_dir, $git_dir, $max_commits, $squash_date ? $squash_date : 0);

if ($finisher) {
	chdir $git_dir
		or die "Failed to change to directory '$cvs_dir': $!";
	system("$finisher", "$cvs_dir", "$git_dir", "$commits");
}
