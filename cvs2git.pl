#!/usr/bin/perl

################################################################################
#                                                                              #
# Copyright (C) 2011 Thomas Egerer and Torsten Hilbrich, secunet Security      #
# Networks AG                                                                  #
#                                                                              #
# This program is free software; you can redistribute it and/or modify it      #
# under the terms of the GNU General Public License as published by the        #
# Free Software Foundation; either version 2 of the License, or (at your       #
# option) any later version.  See <http://www.fsf.org/copyleft/gpl.txt>.       #
#                                                                              #
# This program is distributed in the hope that it will be useful, but          #
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY   #
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License     #
# for more details.                                                            #
#                                                                              #
################################################################################

use strict;
use warnings;
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
use IPC::Open3;
use Symbol;

my %authors = (
	'wasi'      => [ 'Thomas Egerer',      'thomas.washeim@gmx.net' ],
);

sub help($;$)
{
	my ($err, $long) = @_;
	my $ret = defined $err ? -1 : 0;

	print $err if defined $err;
	print <<EOF;
usage: $0 --cvsdir <cvs_dir> --gitdir <git_dir> [<options>]

Convert CVS component in directory cvs_dir and store all commits in git_dir.

    --cvsdir <cvs_dir>        CVS source directory to use in conversion
    --gitdir <git_dir>        git destination directory (must exist)
    --prefix <prefix>         prefix to cut off from CVS path
    --maxcommits <number>     stop conversion after <number> of commits
    --squashdate <date>       squash all commits up to <date> into a single one
    --finisher <scriptlet>    scriptlet to be executed after conversion process
    --debug                   be verbose about what script is doing
    --dry-run                 simulate the conversion process
    --no-unknown              do not allow unknown authors
    --force-binary            force binary conversion mode on all files
    --update                  update a repository already converted
    --help                    display this help text
    --longhelp                display more verbose help information
EOF

exit $ret unless (defined $long);

print <<EOF;
NOTES:
cvs_dir is a working directory holding the component to convert. It
must exist and should be up to date when starting the conversion
process. The option --update causes a 'cvs up' to be executed prior
to the conversion.

git_dir must exist a 'git init' must not necessarily have been run
in this directory. Commits will be appended to the current branch,
so if you're using the --update option be sure you are in the branch
which is meant to be the one updated.

The string given with --prefix concatenated with the name of the
cvs_dir is removed from the beginning of each RCS file. So with
'--cvsdir fnord --prefix /cvsroot/fnord' /cvsroot/fnord/fnord is to
be removed from a RCS file. If the string given here is not found
in the RCS file path the script terminates.

Use --maxcommits to only perform conversion of the first <number> of CVS
commits. If you use it with --squashdate you might end up with no conversion
at all if all of the first <number> of commits are before <date>.

Use --squashdate to squash all CVS commits up to and including <date> into
one commit. Below is a list of date formats known to be understood by
--squashdate:
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

The options --finisher <scriptlet> causes <scriptlet> to be executed after
the conversion has been performed in <git_dir>. It can be used to perform
git repacking or running git filter-branch. It is called with cvs_dir,
git_dir and number of commits as arguments.

Use --debug to see (almost) everything the script is doing during the
conversion.

The --dry-run option simulates the conversion process without actually
doing anything. You can use it with --debug to see what will be done during
the conversion.

The --no-unknown forces all authors to be known in the %authors hash. It
can be used to get a commit log with complete author information for each
author.

Use --force-binary to force all files to be treated as binary files. In
for CVS keyword substitution had to be explicitely disabled for binary
files. Most repositories contain binary files that were not added with
the -kb switch. This options treats all files as if they were binary.
EOF

exit $ret;
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
# build_env_hash - build environemnt for git to accept author date and mail    #
#                  for a commit                                                #
# in:  date - date to use for author date value                                #
#      author - author to use with commit                                      #
#      mail - mail address of the author                                       #
#      cdate - commit date to use with commit (defaults to date if omited)     #
# out: environemnt string to use with git commit                               #
################################################################################
sub build_env_hash($$$;$)
{
	my ($date, $author, $mail, $cdate) = @_;

	{
		'GIT_AUTHOR_DATE'       => $date,
		'GIT_AUTHOR_NAME'       => $author,
		'GIT_AUTHOR_EMAIL'      => $mail,
		'GIT_COMMITTER_DATE'    => "${\(defined $cdate ? $cdate : $date)}"
	}
}

################################################################################
# populate_commit_hash - looks for a suitable entry in <commits> and inserts   #
#                        the pushes file info contained in <rinfos> into this  #
#                        commits files array; if no entry is found, a new one  #
#                        is generated and <count> is increased.                #
# in:  commits - ref to commits hash                                           #
#      rinfos  - ref to file info hash (will be wiped except for the filename) #
#      count   - ref to number of commits, gets increased for a new one        #
#      update  - date to use with update option, means all commits prior and   #
#                up to this epoch value are not included in commit hash        #
# out: filename                                                                #
################################################################################
sub populate_commit_hash(%$$$)
{
	my ($commits, $rinfos, $count, $update) = @_;
	my (@commit_tags, $commit_tag, $epoch, $filename);

	if ($$rinfos->{'curr'}->{'rev'} !~ /^[0-9]+\.[0-9]+$/)
	{
		# skip all branch commits
		delete $$rinfos->{'curr'};
		return;
	}
	return if ($update and $update >= $$rinfos->{'curr'}->{'epoch'});

	my $infos = $$rinfos;
	$infos->{'curr'}->{'rev'} = 'dead' if ($infos->{'curr'}->{'state'} eq 'dead');
	$infos->{'curr'}->{'commitid'} = "<unknown>" if (!exists $infos->{'curr'}->{'commitid'});

	$epoch = $infos->{'curr'}->{'epoch'};
	$filename = $infos->{'filename'};

	# CVS commits aren't atomic in means of time (or any other)
	# so we use this heuristic and accept all commits with the
	# same name and commit ID (if any, thank you CVS!) and author
	# within 15 seconds before and after the commit we're 
	# currently processing; if we have a hit we check the commit
	# message to be 100% sure it's really the same commit;
	for my $i (-15 .. 15)
	{
		my $tag = generate_commit_hash($epoch + $i, $infos->{'curr'}->{'commitid'},
									   $infos->{'curr'}->{'author'});

		if (exists $commits->{$tag})
		{
			# compare commit messages
			if ($commits->{$tag}->{'comment'} eq (join("\n", @{$infos->{'curr'}->{'comment'}})))
			{
				$commit_tag = $tag;
				last;
			}
		}
	}

	if (!defined $commit_tag)
	{
		# we need a new kenn^w commit tag
		$commit_tag = generate_commit_hash($epoch, $infos->{'curr'}->{'commitid'},
										   $infos->{'curr'}->{'author'});
	}

	if (!exists $commits->{$commit_tag})
	{
		chomp (my $date = ctime($epoch));
		$commits->{$commit_tag} =
		{
			'comment'  => join("\n", @{$infos->{'curr'}->{'comment'}}),
			#'date'     => $date,
		};

		print "\rProcessed commit " . ++$$count;
	}

	my $hash =
	{
		'revision' => $infos->{'curr'}->{'rev'},
		'filename' => $filename,
	};
	$hash->{'binary'} = 1 if $infos->{'binary'};
	unshift @{${$commits->{$commit_tag}}{'files'}}, $hash;

	if ($infos->{'curr'}->{'tags'})
	{
		foreach my $tag (@{$infos->{'curr'}->{'tags'}})
		{
			if (!defined $commits->{'tags'}->{$tag} or
				defined $commits->{'tags'}->{$tag} < $epoch)
			{
				$commits->{'tags'}->{$tag} = $epoch
			}
		}
	}

	# clear up info hash except for the filename
	delete $$rinfos->{'curr'};
	$$rinfos->{'filename'} = $filename;
}

################################################################################
# <helper functions for commit log parser>                                     #
################################################################################
sub START() { return 0; }
sub INITIAL() { return 1; }
sub RCS_FILE() { return 2; }
sub SKIP_TO_TAGS() { return 3; }
sub PROCESS_TAGS() { return 4; }
sub SKIP_TO_REVISION() { return 5; }
sub SKIP_TO_INFOS() { return 6; }
sub SKIP_TO_BRANCH_INFO() { return 7; }
sub BUILD_COMMIT_LOG() { return 8; }
################################################################################
# </helper functions for commit log parser>                                    #
################################################################################

################################################################################
# parse_commit_log - parse the commit log obtained by executing <cmd> (read in #
#                    chunks of 4096 bytes into an internal structure that will #
#                    later on be used to generate git commits from; <prefix>   #
#                    is removed from path strings and unless <allow> is set,   #
#                    unknown authors are complained about; results are stored  #
#                    in $commits ref;                                          #
# in:  cmd           command to execute for cvs log (e.g. a cat command)       #
#      prefix        prefix to remove from cvs path                            #
#      noallow       allow unknown authors                                     #
#      forcebinary   set binary flag on all files                              #
#      update        date to use with update options                           #
#      commits       hash ref to store results in                              #
# out: number of commits                                                       #
################################################################################
sub parse_commit_log($$$$%)
{
	my ($cmd, $prefix, $noallow, $forcebinary, $update, $commits) = @_;
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
					$infos->{'binary'} = 1 if $forcebinary;
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
				elsif ($line =~ /^keyword substitution: b/)
				{
					# for now this only handles binary keyword substitution
					$infos->{'binary'} = 1;
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
					$infos->{'curr'}->{'rev'} = $1;
					$infos->{'curr'}->{'tags'} = $tags->{$1} if defined $tags->{$1};
					$state = SKIP_TO_INFOS;
				}
				next;
			}
			elsif ($state == SKIP_TO_INFOS)
			{
				if ($line =~ /date: (\S+) (.*?);/)
				{
					$infos->{'curr'}->{'epoch'} = str2time("$1 $2");
				}

				if ($line =~ /author: (.*?);/)
				{
					$unknown_authors{$1} = 1 if (!defined $authors{$1} and $noallow);
					$infos->{'curr'}->{'author'} = $1;
				}

				$infos->{'curr'}->{'state'} = $1 if ($line =~ /state: (.*?);/);
				$infos->{'curr'}->{'commitid'} = $1 if ($line =~ /commitid: (.*?);/);

				$state = SKIP_TO_BRANCH_INFO;
				next;
			}
			elsif ($state == SKIP_TO_BRANCH_INFO)
			{
				if ($line =~ /^branches:  [0-9.]+;/)
				{
					$state = BUILD_COMMIT_LOG;
				}
				else
				{
					# message already belongs to commit message
					unless ($line =~ /^\s*$/)
					{
						push @{$infos->{'curr'}->{'comment'}}, "$line"
					}
					$state = BUILD_COMMIT_LOG;
				}

				next;
			}
			elsif ($state == BUILD_COMMIT_LOG)
			{
				if ($line eq ('-' x 28))
				{
					populate_commit_hash($commits, \$infos, \$count, $update);
					$state = SKIP_TO_REVISION;
				}
				elsif($line eq ('=' x 77))
				{
					# last revision for file
					populate_commit_hash($commits, \$infos, \$count, $update);
					$state = INITIAL;

				}
				else
				{
					# part of the commit message
					unless ($line =~ /^\s*$/)
					{
						push @{$infos->{'curr'}->{'comment'}}, "$line"
					}
				}
				next;
			}
		}
		$rest = $buf;
	}

	if ($noallow && scalar keys %unknown_authors)
	{
		my @unknown_authors = keys %unknown_authors;

		die "Unknown authors found:\n\t@unknown_authors,\nPlease fix!";
	}

	close C;
	print "\n";

	select(STDOUT);
	$| = 0;
	$count;
}

################################################################################
# cd - change into directory - dies on failure                                 #
# in:  directory to cd in                                                      #
################################################################################
sub cd($)
{
	chdir $_[0] or die "Failed to change to directory '$_[0]': $!";
}

################################################################################
# do_command - execute command with optional redirection of stdout and stderr  #
#              into a file or variable                                         #
# in:  command  - command to execute (must be an array ref)                    #
#      out      - where to direct stdout and stderr, must be a hash ref;       #
#                 'stderr'/'stdout' define where the appropriate output goes:  #
#                 use a SCALAR ref to get the output to a variable, if value   #
#                 is no ref, output goes to the given string interpreted as a  #
#                 file; if any of the values is ommited output goes nowhere    #
#      debug    - 1 == debug, 2 == dry-run                                     #
#      environ  - environment to use with command                              #
# out: return code of the process run                                          #
################################################################################
sub do_command($%;$$)
{
	my ($cmd, $out, $debug, $environ) = @_;
	my ($stderr, $stdout, $pid);

	if ($debug & 1)
	{
		local $" = " ";
		print "@{$cmd}";
		if ($out->{'stderr'} and "" eq ref($out->{'stderr'}))
		{
			print(" 2>" . $out->{'stderr'});
		}
		if ($out->{'stdout'} and "" eq ref($out->{'stdout'}))
		{
			print(" >"  . $out->{'stdout'});
		}
		print "\n";
	}
	return 0 if 2 & $debug;

	if (defined $environ)
	{
		foreach my $name (keys %{$environ})
		{
			$ENV{$name} = $environ->{$name};
		}
	}

	if ($out->{'stdout'} and "" eq (ref $out->{'stdout'}))
	{
		open C, ">$out->{'stdout'}";
		$stdout = ">&C";
		delete $out->{'stdout'};
	}
	if ($out->{'stderr'} and "" eq (ref $out->{'stderr'}))
	{
		open C, ">$out->{'stderr'}";
		$stderr = ">&C";
		delete $out->{'stderr'};
	}
	$stderr = gensym if !defined $stderr;
	$cmd = (join ' ', @{$cmd});
	$pid = open3(undef, $stdout, $stderr, $cmd);

	waitpid($pid, 0);

	if (defined $out->{'stdout'})
	{
		${$out->{'stdout'}} .= $_ while (<$stdout>);
	}
	if (defined $out->{'stderr'})
	{
		${$out->{'stderr'}} .= $_ while (<$stderr>);
	}

	close $stdout;
	close $stderr;

	$? >> 8;
}

################################################################################
# write_file - write given <content> into file                                 #
# in:  file to write to                                                        #
#      contents to write to file                                               #
################################################################################
sub write_file($$)
{
	my ($file, $content) = @_;
	open FILE, ">$file";
	print FILE $content;
	close FILE;
}

################################################################################
# convert_charset - convert charset from latin1 to utf-8                       #
#                   NOTE: had to shorten this sub like this, feels good though #
# in:  string to convert                                                       #
# out: converted string                                                        #
################################################################################
sub convert_charset($)
{
	my $comment = $_[0];
	eval
	{
		# Check if contents is uft8
		decode('utf-8', $_[0], Encode::FB_CROAK);
	};

	$@ ? encode('utf-8', decode('latin1', $comment)) : $comment;
}

################################################################################
# trim_comment - make first commit line for git look good; since git is        #
#                superiour to CVS in many ways a commit line displayed with    #
#                --oneline option should not exceed the 80 chars limit;        #
#                this is essentially what this function does; somehow the      #
#                commits that I've had the honor to convert with it kinda did  #
#                every crap one can possible think of (me included, though I   #
#                have been at least consistent in the crap I did);             #
#                took me quite some time to finally figure out what I had      #
#                planned with every single line in the first place, seemed to  #
#                make sense by the time writing it; note to self: use comments #
#                next time!                                                    #
# in:  possible crappy comment                                                 #
# out: somehow not so crappy headline of the new git commit                    #
################################################################################
sub trim_comment($)
{
	my $comment = $_[0];
	my ($ret, $line);
	$line = 0;

	$comment = convert_charset($comment);
	foreach my $s (split /\n/, $comment)
	{
		my ($words, $len);

		# leading white spaces
		$s =~ s/^\s+//;
		# leading dot-like stuff once, or even twice
		$s =~ s/^[-+_o*]{1,2}\s?(\w|\"|\')/$1/g;

		$words = scalar(my @words = split /\s/, $s);
		$len = $words ? length($words[0]) : 0;

		# we accept it as valid comment iff
		# - it has at least two words, or
		# - the first word is > 9 characters and comment line does not end
		#   with a colon(oscopie)
		if ((2 <= $words or ($len > 9 and $s !~ /:$/)) and !defined $ret)
		{
			($ret = $s) =~ s/^\s//g;
		}
		elsif (defined $ret)
		{
			# indicate that comment continues
			$ret =~ s/\s*$/.../;
			last;
		}
		++$line;
	}

	# fall back to single comment line
	$ret = $comment if !defined $ret;

	# limit lenght of line to 50 chars tops
	if (length($ret) > 50)
	{
	    $ret = substr($ret, 0, 47);
	    # remove any start of a german utf-8 character
	    $ret =~ s/\xC3$//;
		$ret =~ s/\s*$/.../;
	}

	$ret;
}

################################################################################
# cvs2git - perform actual cvs update of the file and redirect it into git     #
#           repository                                                         #
# in:  filename - filename of the CVS file to copy to git                      #
#      revision - revision of the CVS file to use with update                  #
#      gitdir   - git directory to use for file                                #
#      chmod    - perform a chmod operation on the file                        #
#      binary   - is this a binary file?                                       #
#      debug    - 1 == debug, 2 == dry-run                                     #
# out: number of commits done                                                  #
################################################################################
sub cvs2git($$$$$$) {
	my ($filename, $revision, $gitdir, $chmod, $binary, $debug) = @_;
	my ($file, $cmd, $out, $ret, $stderr);

	$file = "$gitdir/$filename";
	print "mkdir ${\(dirname($file))}\n" if $debug & 1;
	mkpath(dirname($file)) if !($debug & 2);

	$cmd = ['cvs', 'update', ($binary ? '' : '-p'), '-r', $revision, $filename];
	$out = { 'stderr' =>  \$stderr };
	$out->{'stdout'} = $file if !$binary;

	# this loop is required to catch errors that sometimes occur with CVS
	# whie updating files
	do {
		$ret = do_command($cmd, $out, $debug);
	} while ($ret and $out->{'stderr'} =~ /anoncvs_.*?: no such system user/);
	die "error: $stderr" if ($ret);

	# binary files are sticky, we have to copy them
	if ($binary)
	{
		print "cp $filename $file\n" if $debug & 1;
		copy($filename, $file) if !($debug & 2);
	}

	if ($chmod)
	{
		my $stat = stat($filename);
		my $mode = defined $stat ? $stat->mode & 0777 : 0644;

		printf("chmod %o $file\n", $mode) if $debug & 1;

		if (!($debug & 2))
		{
			chmod $mode, $file or die "Failed to chmod file '$file': $!";
		}
	}
}

################################################################################
# create_squash_commit - create a single commit from all files contained in    #
#                        <squashed> hash ref;                                  #
# in:  squashed - hash ref with files to commit, revision, binary status,      #
#                 start and end date, as well as number of commits squashed    #
#      cvsdir   - CVS directory to use                                         #
#      gitdir   - git directory to use for file                                #
#      tmpfile  - temporary file to use for git comment                        #
#      debug    - 1 == debug, 2 == dry-run                                     #
################################################################################
sub create_squash_commit(%$$$$) {
	my ($squashed, $cvsdir, $gitdir, $tmpfile, $debug) = @_;
	my ($commitstr, $env, $filename, $binary, $only, $authors, $count);

	$commitstr = <<EOF;
CVS import: Initial squash-commit

This commit squashes $squashed->{'count'} commit(s) starting from
$squashed->{'start'} ending $squashed->{'end'}
into a single commit to simplify git history.

Commits of the following authors (in order of number):
EOF

	$count = 0;
	# helper sub for sorting by commit number

	$authors = "";
	foreach $a (sort
				   {
					   $squashed->{'authors'}->{$b} <=> $squashed->{'authors'}->{$a}
				   } keys %{$squashed->{'authors'}})
	{
		$authors .= "\t$a: $squashed->{'authors'}->{$a}\n";
		$only = $a;
		++$count;
	}
	$commitstr .= "$authors\nFiles:\n";

	$env = build_env_hash($squashed->{'end'},
						  $count == 1 ? $only : "various artists",
						  'hakke_007@gmx.de');

	foreach my $filename (sort(keys %{$squashed->{'files'}}))
	{
		my ($revision, $binary) = @{$squashed->{'files'}->{$filename}};

		$commitstr .= "\tadded:    $filename -> $revision\n";
		cvs2git($filename, $revision, $gitdir, 1, $binary, $debug);
	}
	cd($gitdir);
	do_command(['git', 'add', '.'], {}, $debug);
	write_file($tmpfile, $commitstr);
	do_command(['git', 'commit', '-F', "$tmpfile"], {}, $debug, $env);
	cd($cvsdir);
}

################################################################################
# create_regular_commit -  create a regular commit from all files contained in #
#                          <commitobj> hash ref;                               #
# in:  commitobj - hash ref with files to commit, revision, binary status,     #
#                  start and end date                                          #
#      cvsdir    - CVS directory to use                                        #
#      gitdir    - git directory to use for file                               #
#      tmpfile   - temporary file to use for git comment                       #
#      debug     - 1 == debug, 2 == dry-run                                    #
################################################################################
sub create_regular_commit(%$$$$)
{
	my ($commitobj, $cvsdir, $gitdir, $tmpfile, $debug) = @_;
	my ($headline, $comment, $commitstr, $env);

	$headline = trim_comment($commitobj->{'comment'});
	($comment = (" " x 4) . $commitobj->{'comment'}) =~ s/\n/$& . (" " x 4)/eg;

	$commitstr = <<EOF;
$headline

CVS import: $commitobj->{'author'}, $commitobj->{'date'}

original comment:\n$comment

Files:
EOF
	$env = build_env_hash($commitobj->{'date'},
						  $commitobj->{'author'},
						  $commitobj->{'mail'});


	foreach my $filename (sort(keys %{$commitobj->{'added'}}))
	{
		my ($revision, $binary) = @{$commitobj->{'added'}->{$filename}};
		cvs2git($filename, $revision, $gitdir, 1, $binary, $debug);
		$commitstr .= "\tadded:    $filename -> $revision\n"
	}

	foreach my $filename (sort(keys %{$commitobj->{'updated'}}))
	{
		my ($revision, $binary) = @{$commitobj->{'updated'}->{$filename}};
		cvs2git($filename, $revision, $gitdir, 0, $binary, $debug);
		$commitstr .= "\tupdated:  $filename -> $revision\n"
	}
	cd($gitdir);
	foreach my $filename (sort(keys %{$commitobj->{'removed'}}))
	{
		do_command(['git', 'rm', '-f', $filename], {}, $debug);
		$commitstr .= "\tremoved:  $filename\n"
	}
	do_command(['git', 'add', '.'], {}, $debug);
	write_file($tmpfile, $commitstr);
	do_command(['git', 'commit', '-F', "$tmpfile"], {}, $debug, $env);
	cd($cvsdir);
}

################################################################################
# create_commits -                                                             #
#                                                                              #
# in:  commits     -                                                           #
#      cvsdir      -                                                           #
#      gitdir      -                                                           #
#      end         -                                                           #
#      squash_date -                                                           #
#      count       -                                                           #
#      debug       -                                                           #
# out: number of commits done                                                  #
################################################################################
sub create_commits(%$$$$$)
{
	my ($commits, $cvsdir, $gitdir, $end, $squash_date, $count, $debug) = @_;
	my (%revisions, $squashed, $i, $commitno);
	my (undef, $tmpfile) = tempfile();

	$commitno = $i = 0;

	if ($end)
	{
		warn "Processing $end of the $count total commits\n";
		$count = $end
	}
	else
	{
		warn "Processing $count commits\n";
	}

	foreach my $commit (sort keys %{$commits})
	{
		my ($commitobj, $author, $mail, $epoch, $date, $login);

		next if $commit eq 'tags';
		die "no files: $commit" if 0 == (scalar @{${$commits->{$commit}}{"files"}});

		($epoch, undef, $login) = (split /\Q_|||_\E/, $commit);
		($author, $mail) = (defined $authors{$login}) ?
				@{$authors{$login}} : ($login, "unknown");
		$author .= " ($login)" unless $author eq $login;
		chomp ($date = ctime($epoch));

		if ($epoch <= $squash_date)
		{
			warn "Skipping commit ${\(++$i)}/$count\n";
			if (!$squashed)
			{
				# intialize squashed hash
				$squashed = { "start" => $date, "end" => $date, "count" => 0, };
			}
			++$squashed->{'count'};
			$squashed->{'authors'}->{$author} = 0 if !defined $squashed->{'authors'}->{$author};
			++$squashed->{'authors'}->{$author};
		}
		else
		{
			warn "Processing commit ${\(++$i)}/$count\n";
			if ($squashed)
			{
				create_squash_commit($squashed, $cvsdir, $gitdir, $tmpfile,
									 $debug);
				 $squashed = undef;
				++$commitno;
			}
		}

		$commitobj->{'comment'} = $commits->{$commit}->{'comment'};
		$commitobj->{'date'} = $date;
		$commitobj->{'author'} = $author;
		$commitobj->{'mail'} = $mail;

		foreach my $file (sort @{${$commits->{$commit}}{"files"}})
		{
			# TODO add tags!
			my ($revision, $filename, $binary) = 
				(
					${$file}{'revision'},
					${$file}{'filename'},
					${$file}{'binary'} ? 1 : 0,
					undef
				);

			if (!defined $revisions{$filename})
			{
				# ignore file originally commited on another branch
				next if $revision eq 'dead';

				# new file, set revision

				$revisions{$filename} = $revision;
				$commitobj->{'added'}->{$filename} = [ $revision, $binary ];
				$squashed->{'files'}->{$filename} = [ $revision, $binary ] if ($squashed);
			}
			elsif ($revision eq 'dead')
			{
				# file has been deleted
				$commitobj->{'removed'}->{$filename} = $revisions{$filename};
				delete $revisions{$filename};
				delete $squashed->{'files'}->{$filename} if ($squashed);
			}
			else
			{
				# update commit string for file update only
				$revisions{$filename} = $revision;
				$commitobj->{'updated'}->{$filename} = [ $revision, $binary ];
				$squashed->{'files'}->{$filename} = [ $revision, $binary ] if ($squashed);
			}

		}

		if ($epoch > $squash_date)
		{
			create_regular_commit($commitobj, $cvsdir, $gitdir, $tmpfile, $debug);
			++$commitno;
		}

		return $commitno if $end && $i == $end;
	}

	# all commits need to get squashed!
	create_squash_commit($squashed, $cvsdir, $gitdir, $tmpfile, $debug) if ($squashed);

	unlink($tmpfile);
	return $commitno;
}

################################################################################
# parse_opts - parse opts and perform various sanity checks, dies on failure   #
# out: option array containing programs options:                               #
#      - cvsdir - CVS directory, must exist and contain a CVS subdir           #
#      - gitdir - git destination directory, will be created if non-existent   #
#      - maxcommits - maximum number of commits (optional)                     #
#      - squashdate - date to which all commits will be squashed (optional)    #
#      - finisher - finisher script to run after completion of conversion is   #
#                   complete e.g. git-filter-branch (optional)                 #
#      - nounknown - do not abort if unknown authors were found (optional)     #
#      - prefix - prefix to cut from files parsed in CVS log (optional)        #
################################################################################
sub parse_opts()
{
	my ($opts, $args);

	eval
	{
		local $SIG{__WARN__} = sub { die "@_"; };

		GetOptions(
				'cvsdir=s'        => \$opts->{'cvsdir'},
				'gitdir=s'        => \$opts->{'gitdir'},
				'maxcommits=i'    => \$opts->{'maxcommits'},
				'squashdate=s'    => \$opts->{'squashdate'},
				'finisher=s'      => \$opts->{'finisher'},
				'no-unknown'      => \$opts->{'nounknown'},
				'prefix=s'        => \$opts->{'prefix'},
				'force-binary'    => \$opts->{'forcebinary'},
				'dry-run'         => \$opts->{'dryrun'},
				'update'          => \$opts->{'update'},
				'debug'           => \$opts->{'debug'},
				'help'            => \$opts->{'help'},
				'longhelp'        => \$opts->{'longhelp'})
				# TODO patterns for binary file detection and ignore list
				# read authors from file
				# perform an actual update for CVS repo in case of update
	};

	chomp ($args = $@) if $@;

	if ($args)
	{
		help("There were warnings/errors parsing the command line:\n\t$args\n\n");
	}

	help(undef, $opts->{'longhelp'}) if $opts->{'help'} or $opts->{'longhelp'};

	if (!defined $opts->{'cvsdir'} or !defined $opts->{'gitdir'})
	{
		help("cvs- and git-dir are mandatory, please fix!\n\n");
	}
	elsif (defined $opts->{'finisher'} and not -x $opts->{'finisher'})
	{
		help("finisher script '$opts->{'finisher'}' is not executable!\n\n");
	}

	$opts->{'cvsdir'} = rel2abs($opts->{'cvsdir'});
	if (! -d $opts->{'cvsdir'} or ! -d "$opts->{'cvsdir'}/CVS")
	{
		die "Source CVS dir $opts->{'cvsdir'} does not exist " .
			"or is not a CVS directory!";
	}

	$opts->{'gitdir'} = rel2abs($opts->{'gitdir'});
	if (! -d $opts->{'gitdir'})
	{
		die "Source CVS dir $opts->{'gitdir'} does not exist!";
	}

	if (0 != system('git', '--git-dir', "$opts->{'gitdir'}/.git", 'rev-parse'))
	{
		cd($opts->{'gitdir'});
		system('git', 'init') and die "unable to create empty git-repo: $!";
	}

	$opts->{'squashdate'} = defined $opts->{'squashdate'} ?
		str2time($opts->{'squashdate'}) : 0;

	if (defined $opts->{'prefix'})
	{
		$opts->{'prefix'} .= '/' if ($opts->{'prefix'} !~ m|/$|);
	}

	if (defined $opts->{'dryrun'})
	{
		$opts->{'debug'} += 2;
		delete $opts->{'dryrun'};
	}
	$opts->{'debug'} = 0 if !defined $opts->{'debug'};

	if ($opts->{'update'})
	{
		delete $opts->{'update'};
		do_command(['git', '--git-dir', "$opts->{'gitdir'}/.git", 'log',
				   '-n1', '--pretty="format:%at"', 'HEAD'],
				   { 'stdout' => \$opts->{'update'} },
				   ($opts->{'debug'} & (~2))) and die "You suck!";
	}

	return %$opts;
}

sub main()
{
	my ($component, %commits, $commits, $count);
	my %opts = parse_opts();

	if ($opts{'cvsdir'} =~ m|/?([^/]+)/*$|)
	{
		$component = $1;
		print "Converting component $component in directory $opts{'cvsdir'}\n";
	}
	$opts{'prefix'} .= "$component/" if (defined $component);

	cd($opts{'cvsdir'});
	if ($opts{'update'})
	{
		my ($stderr, $ret);
		$ret = do_command([ 'cvs', 'up' ], { 'stderr' => \$stderr },
						  $opts{'debug'});
		die "Error performing cvs update command: $stderr" if $ret;
	}

	$count = parse_commit_log('cvs log -r1 2>/dev/null',
							  $opts{'prefix'},
							  $opts{'nounknown'},
							  $opts{'forcebinary'},
							  $opts{'update'},
							  \%commits);
	#print Data::Dumper->Dump([\%commits], [qw/foo/]);
	#exit;
	$commits = create_commits(\%commits,
							  $opts{'cvsdir'},
							  $opts{'gitdir'},
							  $opts{'maxcommits'},
							  $opts{'squashdate'},
							  $count,
							  $opts{'debug'});

	if ($opts{'finisher'})
	{
		system($opts{'finisher'}, $opts{'cvsdir'},
			   $opts{'gitdir'}, $commits);
	}
}

main();
