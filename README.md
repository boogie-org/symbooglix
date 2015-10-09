<!-- vim: set textwidth=120: -->
Symbooglix
==========

The Symbolic execution engine for [Boogie](http://research.microsoft.com/en-us/projects/boogie/). This project
is currently at the research stage and so is not yet making stable releases.

[![Build
Status](https://magnum.travis-ci.com/delcypher/symbooglix.svg?token=QQ3F3xFawVVs4ymGi3xa)](https://magnum.travis-ci.com/delcypher/symbooglix)

Dependencies
============

To build you will need

Common dependencies
-------------------

- Git
- Python
- Z3 4.3.1 (avoid Z3 4.3.2, newer versions should be fine)
- Boogie (obtained via a Git submodule)
- NUnit 2.6.4 (obtained via NuGet on restore)
- CommandLine (obtained via NuGet on restore)
- System.Collections.Immutable (obtained via NuGet on restore)

If using Linux
--------------

- Mono and related tools (I advise you use Monodevelop as your IDE)

If using Windows
----------------

- You should install the "NUnit Test Adapter" in Visual Studio so you can run the unit tests.

Getting started
===============

We use several git submodules for symbooglix. Before you start you should initialise them by running

```
$ git submodule init
$ git submodule update
```

We also depend on several NuGet packages. To get these run

```
$ cd src
$ wget https://dist.nuget.org/win-x86-commandline/v2.8.6/nuget.exe
$ mono nuget.exe restore
```

Now if everthing went okay you can build Symbooglix by running

```
$ cd src/ # A symboolgix.sln file should be in this directory
$ mono nuget.exe restore symbooglix.sln
$ xbuild /p:Configuration=<BUILD_TYPE>
```

where ``<BUILD_TYPE>`` is ``Debug`` or ``Release``. If you use ``Release`` you also need
to pass ``/p:Platform=x86`` (this needs fixing!).

Now make a symbolic link (or copy) to the the z3 executable and place it in the following directories:

* ``src/SymbooglixDriver/bin/<BUILD_TYPE>/``
* ``src/Symbooglix/bin/<BUILD_TYPE>/``

where ``<BUILD_TYPE>`` is the build type used to build Symbooglix.

Alternatively you can load the ``symbooglix/symbooglix.sln`` file into Visual
Studio or Monodevelop and build from there.

Testing
=======

There are two forms of testing used for Symbooglix

NUnit tests
===========

[NUnit](https://github.com/nunit) is used for unit testing. This comes preinstalled
in mono but the version is too old so you need to obtain NUnit 2.6.4. When you built
Symbooglix you will have already obtained the newer version of NUnit using NuGet.

These tests are easy to run from within monodevelop or Visual Studio (you need the NUnit Test Adapter add-on installed).

However you can run these tests from the console on Linux. To do so you need
to obtain the NUnit.Runners NuGet package and then use a shell script to run
the tests. Replace ``<BUILD_TYPE>`` with the build type you wish to test.

```
$ mono ./nuget.exe install -Version 2.6.4 NUnit.Runners
$ utils/run-unit-tests.sh NUnit.Runners.2.6.4/tools/nunit-console.exe <BUILD_TYPE>
```

Driver tests
============

The Symbooglix driver is ``sbx.exe``. To test it install the lit and OutputCheck tools

```
$ pip install lit
$ pip install OutputCheck
```

Now to run the tests run

```
$ lit -s test_programs/
```
