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
- Python

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

Testing
=======

There are two forms of testing used for Symbooglix

NUnit tests
===========

[NUnit](https://github.com/nunit) is used for unit testing. This comes preinstalled
in mono 3.2 (and probably other versions). I'm not sure about Windows users.

These tests are easy to run from within monodevelop.

However you can run these tests from the console on Linux. To do so run
the following.

```
$ ./nunitconsole.sh symbooglix/SymbooglixLibTests/SymbooglixLibTests.csproj
$ ./nunitconsole.sh symbooglix/BoogieTests/BoogieTests.csproj
```

Driver tests
============

Install the lit and OutputCheck tools

```
$ pip install lit
$ pip install OutputCheck
```

Now to run the tests run

```
$ lit -s test_programs/
```
