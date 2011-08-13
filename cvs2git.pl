#!/usr/bin/perl

use strict;
use warnings;
use Cwd qw(cwd);
use Data::Dumper qw(Dumper);
use Date::Format;
use Date::Parse;
use Encode qw(encode decode);
use File::Basename qw(dirname);
use File::Copy qw(copy);
use File::Path qw(mkpath);
use File::Spec::Functions qw(rel2abs);
use File::stat qw(stat);
use File::Temp qw(tempfile);
use Getopt::Long;
use IO::File;
use IO::File qw();
use POSIX qw(dup2);

my %authors = (
	'wasi'      => [ 'Thomas Egerer',      'thomas.washeim@gmx.net' ],
);

sub START() { return 0; }
sub INITIAL() { return 1; }
sub RCS_FILE() { return 2; }
sub SKIP_TO_TAGS() { return 3; }
sub PROCESS_TAGS() { return 4; }
sub SKIP_TO_REVISION() { return 5; }
sub SKIP_TO_INFOS() { return 6; }
sub SKIP_TO_BRANCH_INFO() { return 7; }
sub BUILD_COMMIT_LOG() { return 8; }

sub help()
{
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

################################################################################
# generate_commit_hash - generate a commit hash from the infos of the file     #
#                        currently processed to identify all files within this #
#                        commit: <epoch>_|||_<commitid>_||_<author>,           #
#                        sounds easier than it is since CVS does not generate  #
#                        commit IDs all the time and if it does collisions are #
#                        quite probable (I've seen them often)                 #
# in:  quite obvious                                                           #
# out: even more                                                               #
################################################################################
sub generate_commit_hash($$$)
{
	my ($epoch, $commitid, $author) = @_;

	# for projects with commits prior to Sep 9 2001, 03:46:40 we must
	# make sure that sorting succeeds when using the epoch value by
	# prepending zeros so it is 10 digits long
	sprintf('%010d', $epoch) . '_|||_' .  $commitid . '_|||_' . $author;
}

################################################################################
# populate_commit_hash - looks for a suitable entry in <commits> and inserts   #
#                        the pushes file info contained in <rinfos> into this  #
#                        commits files array; if no entry is found, a new one  #
#                        is generated and <count> is increased.                #
# in:  commits - ref to commits hash                                           #
#      rinfos  - ref to file info hash (will be wiped except for the filename) #
#      count   - ref to number of commits, gets increased for a new one        #
# out: filename                                                                #
################################################################################
sub populate_commit_hash(%$$)
{
	my ($commits, $rinfos, $count) = @_;
	my (@commit_tags, $commit_tag, $epoch, $filename);

	my $infos = $$rinfos;
	$infos->{'rev'} = 'dead' if ($infos->{'state'} eq 'dead');
	$infos->{'commitid'} = "<unknown>" if (!exists $infos->{'commitid'});

	$epoch = $infos->{'epoch'};
	$filename = $infos->{'filename'};

	# CVS commits aren't atomic in means of time (or any other)
	# so we use this heuristic and accept all commits with the
	# same name and commit ID (if any, thank you CVS!) and author
	# within 15 seconds before and after the commit we're 
	# currently processing; if we have a hit we check the commit
	# message to be 100% sure it's really the same commit;
	for my $i (-15 .. 15)
	{
		my $tag = generate_commit_hash($epoch + $i, $infos->{'commitid'},
									   $infos->{'author'});

		if (exists $commits->{$tag})
		{
			# compare commit messages
			if ($commits->{$tag}->{'comment'} eq (join("\n", @{$infos->{'comment'}})))
			{
				$commit_tag = $tag;
				last;
			}
		}
	}

	if (!defined $commit_tag)
	{
		# we need a new kenn^w commit tag
		$commit_tag = generate_commit_hash($epoch, $infos->{'commitid'},
										   $infos->{'author'});
	}

	if (!exists $commits->{$commit_tag})
	{
		$commits->{$commit_tag} =
		{
			'comment'  => join("\n", @{$infos->{'comment'}}),
			'date'     => ctime($epoch),
		};
		#print "\rProcessed commit " . ++$$count;
	}

	my $hash = 
	{
		'revision' => $infos->{'rev'},
		'filename' => $filename,
	};
	$hash->{'tags'} = $infos->{'tags'} if $infos->{'tags'};
	unshift @{${$commits->{$commit_tag}}{'files'}}, $hash;

	# clear up info hash except for the filename
	undef $$rinfos;
	$$rinfos->{'filename'} = $filename;
}

################################################################################
# parse_commit_log - parse the commit log obtained by executing <cmd> (read in #
#                    chunks of 4096 bytes into an internal structure that will #
#                    later on be used to generate git commits from; <prefix>   #
#                    is removed from path strings and unless <ignore> is set,  #
#                    unknown authors are complained about; results are stored  #
#                    in $commits ref;                                          #
# in:  cmd           command to execute for cvs log (e.g. a cat command)       #
#      prefix        prefix to remove from cvs path                            #
#      ignore        ignore unknown authors                                    #
#      commits       hash ref to store results in                              #
# out: number of commits                                                       #
################################################################################
sub parse_commit_log($$$%)
{
	my ($cmd, $prefix, $ignore, $commits) = @_;
	my ($state, $infos, $tags, $count, $buf, $rest, %unknown_authors);

	$state = START;
	$count = 0;
	select(STDOUT);
	$| = 1;

	$cmd .= " | ";
	open C, $cmd;

	# this let's commit log contents stay within a page of memory;
	# some commit logs I've seen were very large and blew up this
	# little parser
	while (read(C, $buf, 4096) or $rest)
	{
		$buf = "\n" if !defined $buf;
		$buf = ($rest . $buf) if defined $rest;

		while ($buf =~ s/(.*)\n//)
		{
			my $line = $1;

			if ($state == INITIAL or $state == START)
			{
				if ($line =~ /^$/)
				{
					$state = RCS_FILE;
					next;
				}
				elsif ($state == START and $line =~ /^\? /)
				{
					# untracked file, skip it
					next;
				}
				else
				{
					die "Invalid input in state INITIAL: $line\n";
				}
			}
			elsif ($state == RCS_FILE)
			{
				if ($line =~ /RCS file: (.*?),v.*/)
				{
					undef $infos;
					undef $tags;
					$infos->{'filename'} = $1;
					$infos->{'filename'} =~ s|/Attic/|/|;
					if (defined $prefix and 0 == $infos->{'filename'} =~ s/\Q$prefix\E//o)
					{
						die "prefix '$prefix' not found in '$infos->{'filename'}"
					}
					$state = SKIP_TO_TAGS;
					next;
				}
				else
				{
					die "Invalid input in state RCS_FILE: $line\n";
				}
			}
			elsif ($state == SKIP_TO_TAGS)
			{
				$state = PROCESS_TAGS if ($line =~ /^symbolic names:/);
				next;
			}
			elsif ($state == PROCESS_TAGS)
			{
				if ($line =~ /^\t(.+): ([0-9.]+)/)
				{
					my ($tag, $rev) = ($1, $2);
					# ignore branches!
					unshift @{$tags->{$rev}}, $tag if $rev =~ /[0-9]+\.[0-9]+/;
				}
				elsif ($line eq ('-' x 28))
				{
					$state = SKIP_TO_REVISION;
				}
				next;
			}
			elsif ($state == SKIP_TO_REVISION)
			{
				if ($line =~ /^revision (\S+)/)
				{
					$infos->{'rev'} = $1;
					$infos->{'tags'} = $tags->{$1} if defined $tags->{$1};
					$state = SKIP_TO_INFOS;
				}
				next;
			}
			elsif ($state == SKIP_TO_INFOS)
			{
				if ($line =~ /date: (\S+) (.*?);/)
				{
					$infos->{'epoch'} = str2time("$1 $2");
				}

				if ($line =~ /author: (.*?);/)
				{
					$unknown_authors{$1} = 1 if (!defined $authors{$1} and !$ignore);
					$infos->{'author'} = $1;
				}

				$infos->{'state'} = $1 if ($line =~ /state: (.*?);/);
				$infos->{'commitid'} = $1 if ($line =~ /commitid: (.*?);/);

				$state = SKIP_TO_BRANCH_INFO;
				next;
			}
			elsif ($state == SKIP_TO_BRANCH_INFO)
			{
				if ($line =~ /^branches: [0-9.]+;/)
				{
					$state = BUILD_COMMIT_LOG;
				}
				else
				{
					# message already belongs to commit message
					push @{$infos->{'comment'}}, $line;
					$state = BUILD_COMMIT_LOG;
				}

				next;
			}
			elsif ($state == BUILD_COMMIT_LOG)
			{
				if ($line eq ('-' x 28))
				{
					populate_commit_hash($commits, \$infos, \$count);
					$state = SKIP_TO_REVISION;
				}
				elsif($line eq ('=' x 77))
				{
					# last revision for file
					populate_commit_hash($commits, \$infos, \$count);
					$state = INITIAL;

				}
				else
				{
					# part of the commit message
					push @{$infos->{'comment'}}, $line;
				}
				next;
			}
		}
		$rest = $buf;
	}

	if (!$ignore && scalar keys %unknown_authors)
	{
		my @unknown_authors = keys %unknown_authors;
		local $" = ",\n\t";

		die "Unknown authors found:\n\t@unknown_authors,\nPlease fix!";
	}

	close C;
	print "\n";

	select(STDOUT);
	$| = 0;
	$count;
}

sub cd($)
{
	chdir $_[0] or die "Failed to change to directory '$_[0]': $!";
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

	if ($end)
	{
		warn "Processing $end of the $total total commits\n";
		$total = $end
	}
	else
	{
		warn "Processing $total commits\n";
	}

	foreach my $commit (sort keys %commits)
	{
		my ($author, $mail, $commit_str, $headline, $comment, $epoch, $date, $env, $login, $do_commit);

		$login = (split /_|||_/, $commit)[2];
		($author, $mail) = (defined $authors{$login}) ?
				@{$authors{$login}} : ($login, "unknown");

		$epoch = (split /_|||_/, $commit, 1)[0];
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
				cd($git_dir);
				do_command_no_output('git', 'add', '.');
				print $commit_str;
				write_file($temp_file, $commit_str);
				do_command("$env git commit -F $temp_file", 1);
				++$commits;
				cd($cvs_dir);
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
			cd($git_dir);
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
		cd($cvs_dir);
	}
	unlink($temp_file);
	return $commits;
}

my ($cvs_dir, $git_dir, $max_commits, $squash_date, $ignoreunknown, $removeprefix, $finisher, $help, $args, $component);

eval
{
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

if ($help)
{
	++$help;	# do nothing
}
elsif ($args)
{
	warn "There were warnings/errors parings the command line: \n\t$args\n\n";
	$help = 1;
}
elsif (!defined $cvs_dir or !defined $git_dir)
{
	warn "undefined ${\($cvs_dir ? 'git' : 'cvs' )}-dir, please fix!\n\n";
	$help = 1;
}
elsif (defined $finisher and not -x $finisher)
{
	warn "finisher script '$finisher' is not an executable file!\n\n";
	$help = 1;
}

if ($help)
{
	help;
}


$squash_date = str2time($squash_date);

$cvs_dir = rel2abs($cvs_dir);
if ($cvs_dir =~ m|/components/tgz/*$|)
{
    print "Converting toplevel\n";
}
elsif ($cvs_dir =~ m|/?([^/]+)/*$|)
{
	$component = $1;
	print "Converting component $component in directory $cvs_dir\n";
}
else
{
	die "Unable to determine component from directory name $cvs_dir\n";
}

# Qualify $git_dir if needed
$git_dir = rel2abs($git_dir);

unless (-d $git_dir)
{
	die "Destination Git directory '$git_dir' not existing\n";
}

system('git', '--git-dir', "$git_dir/.git", 'rev-parse') == 0
  or die "Directory '$git_dir' is no Git working directory\n";

cd($cvs_dir);

my (%commits, $commits);
my $prefix = $removeprefix ? $removeprefix : '/export/sina/cvs/components/tgz/';

if (defined $component)
{
	$prefix =~ s|/$||g;
    $prefix .= "/$component/";
}

#parse_commit_log('cvs log -r1 2>/dev/null', $prefix, $ignoreunknown, \%commits);
#parse_commit_log('cat lcdproc.cvslog', $prefix, $ignoreunknown, \%commits);
parse_commit_log('cat lcdproc.cvslog', '/cvsroot/lcdproc/lcdproc/', 1, \%commits);
#print Data::Dumper->Dump([\%commits], [qw(foo)]);
$commits = create_commits(\%commits, $cvs_dir, $git_dir, $max_commits, $squash_date ? $squash_date : 0);

if ($finisher)
{
	system("$finisher", "$cvs_dir", "$git_dir", "$commits");
}
