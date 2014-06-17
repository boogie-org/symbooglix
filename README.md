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

If using Linux
--------------

- Mono and related tools (I advise you use Monodevelop as your IDE)

If using Windows
----------------

**I've not tested running under windows. Use at your own risk!**

Getting started
===============

We use several git submodules for symbooglix. Before you start you should initialise them by running

```
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
