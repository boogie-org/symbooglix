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
- Z3 (SMT Solver)

If using Linux
--------------

- Mono and related tools (I advise you use Monodevelop as your IDE)

If using Windows
----------------

- NUnit 2.6.3. You should install the "NUnit Test Adapter" in Visual Studio so you can run the unit tests.

Getting started
===============

We use several git submodules for symbooglix. Before you start you should initialise them by running

```
$ git submodule init
$ git submodule update
```
Now if everthing went okay you can build Symbooglix by running

```
$ cd src/ # A symboolgix.sln file should be in this directory
$ xbuild
```

Alternatively you can load the ``symbooglix/symbooglix.sln`` file into Visual
Studio or Monodevelop and build from there.

Now make a symbolic link (or copy) to the the z3 executable and place it in the directory
containing the built ``symbooglix.exe``.

Testing
=======

There are two forms of testing used for Symbooglix

NUnit tests
===========

[NUnit](https://github.com/nunit) is used for unit testing. This comes preinstalled
in mono 3.2 (and probably other versions).

These tests are easy to run from within monodevelop.

However you can run these tests from the console on Linux. To do so run
the following (replace ``Debug`` with another build configuration if you
want to use that configuration's build instead).

```
$ nunit-console4 src/BoogieTests/bin/Debug/BoogieTests.dll
$ nunit-console4 src/SymbooglixLibTests/bin/Debug/SymbooglixLibTests.dll
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
