# Symbooglix

[![Build Status](https://travis-ci.org/boogie-org/symbooglix.svg?branch=master)](https://travis-ci.org/boogie-org/symbooglix)

A symbolic execution engine for
[Boogie](http://research.microsoft.com/en-us/projects/boogie/).  A
paper describing Symbooglix can be accessed [here](https://srg.doc.ic.ac.uk/publications/16-symbooglix-icst.html).

This project is currently at the research stage and so is not yet making stable releases.

# Docker Image

A Docker image is available at https://hub.docker.com/r/symbooglix/symbooglix/

# Dependencies

To build you will need:

## Common dependencies

- Git
- Python
- Z3 4.3.1 (avoid Z3 4.3.2, newer versions should be fine)
- Boogie (obtained via a Git submodule)
- NUnit 2.6.4 (obtained via NuGet on restore)
- CommandLine (obtained via NuGet on restore)
- System.Collections.Immutable (obtained via NuGet on restore)

## If using Linux

- Mono and related tools (I advise you use Monodevelop as your IDE)

## If using Windows

- You should install the "NUnit Test Adapter" in Visual Studio so you can run the unit tests.

# Getting started

We use several git submodules for Symbooglix. Before you start you should initialise them by running

```
$ git submodule init
$ git submodule update
```

## Building in Monodevelop or Visual Studio

You can load the ``src/Symbooglix.sln`` file into Visual Studio or Monodevelop and build from there.

We depend on several NuGet packages. Hopefully NuGet will automatically "restore" the packages we depend
on but if not you may need to "restore them manually" before building.

## Building on the command line (Linux/OSX)

We depend on several NuGet packages. To get these run

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

where ``<BUILD_TYPE>`` is ``Debug`` or ``Release``.

Now make a symbolic link (or copy) to the the z3 executable and place it in the following directories:

* ``src/SymbooglixDriver/bin/<BUILD_TYPE>/``
* ``src/Symbooglix/bin/<BUILD_TYPE>/``

where ``<BUILD_TYPE>`` is the build type used to build Symbooglix.

## Running your first Boogie program

```
$ mono src/SymbooglixDriver/<BUILD_TYPE>/Debug/sbx.exe test_programs/basic/symbolic/142.bpl
```

To see the available Symbooglix driver options run

```
$ mono src/SymbooglixDriver/<BUILD_TYPE>/Debug/sbx.exe --help
```

# Testing

There are two forms of testing used for Symbooglix

# NUnit tests

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

# Driver tests

The Symbooglix driver is ``sbx.exe``. To test it install the lit and OutputCheck tools

```
$ pip install lit
$ pip install OutputCheck
```

Now to run the tests run

```
$ lit -s test_programs/
```

# Symbooglix Driver Output

When the SymbooglixDriver (``sbx.exe``) runs it creates a directory named
``symbooglix-<N>`` (where <N> is an increasing integer) which contains files
detailing various parts of the execution.  The can be disabled using
``--file-logging=0``.

Here are some of the files and directories that you will find inside ``symbooglix-<N>``.

* ``instr_stats.callgrind`` - A file that can be given to KCacheGrind to visualise line coverage and the number of times certain branches were taken.
* ``executor_info.yml`` - Statistics about the Execution engine.
* ``terminated_states/`` contains a file for each reporting how it terminated (emission of successful states can be suppressed using ``--skip-log-success-states``, you may wish to use ``--skip-log-unsat-assume-states`` too).
* ``nonterminated_states/`` contains a file for each state that had not finished executing (i.e. due to hitting a global timeout).
* ``termination_counters.yml`` - Reports the number of states by termination type where the termination type is non speculative
* ``termination_counters_ONLY_SPECULATIVE.yml`` - Same as above but only reports speculative execution state. A speculative execution state is marked as speculative when a solver query fails (i.e. returns unknown or times out) and currently Symbooglix will kill an execution state when this occurs.
* ``program.bpl`` - The transformed version of the Boogie program that Symbooglix actually executed on.
