<!-- vim: set textwidth=120: -->
Symbooglix
==========

The Symbolic execution engine for [Boogie](http://research.microsoft.com/en-us/projects/boogie/)

Dependencies
============

To build you will need

Common dependencies
-------------------

- Git
- Mercurial

If using Linux
--------------

- Mono and related tools (I advise you use Monodevelop as your IDE)

If using Windows
----------------

**I've not tested running under windows. Use at your own risk!**

Getting started
===============

We use [git-remote-hg](https://github.com/felipec/git/wiki/git-remote-hg) so we can treat the Mercurial Boogie
repository just like a Git repository.

This remote helper script is available in new versions of git. To use it you can do something like...

```
$ cp /usr/share/git/remote-helpers/git-remote-hg ~/bin
$ cd ~/bin
$ chmod a+x git-remote-hg
$ export PATH=$(pwd):$PATH
```
We use Git's submodule feature for the Boogie folder. To set things up run...

```
$ cd symboogilix/ # Root of Git repository
$ git submodule init
$ git submodule update
```

Now if everthing went okay you can build Symbooglix by running

```
$ cd symbooglix/ # A symboolgix.sln file should be in this directory
$ xbuild
```

Alternatively you can load the ``symbooglix/symbooglix.sln`` file into Visual
Studio or Monodevelop and build from there.

Have fun!
