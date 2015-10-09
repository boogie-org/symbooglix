//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using System.Linq;
using System.Collections.Generic;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class BlockCmdIterator : SymbooglixTest
    {
        [Test()]
        public void Enumerator()
        {
            p = LoadProgramFrom("programs/GotoMultiplePaths.bpl");

            var block = GetMain(p).Blocks[0];

            // Try using the Enumerable so we can use in foreach loop
            var blockEnumerable= new BlockCmdEnumerable(block);

            var cmdStrings = new List<string>();
            foreach (var cmd in blockEnumerable)
            {
                cmdStrings.Add(TrimNewLines(cmd.ToString()));
            }

            Assert.AreEqual(2, cmdStrings.Count);
            Assert.AreEqual("assert {:symbooglix_bp \"entry\"} true;", cmdStrings[0]);
            Assert.AreEqual("goto P0, P1, P2;", cmdStrings[1]);
        }

        [Test()]
        public void EnumeratorHitEnd()
        {
            p = LoadProgramFrom("programs/GotoMultiplePaths.bpl");
            var block = GetMain(p).Blocks[0];

            var blockEnumerator = new BlockCmdEnumerator(block);

            Assert.AreEqual(2, blockEnumerator.Count);

            bool ok = blockEnumerator.MoveNext();
            Assert.IsTrue(ok);
            Assert.AreSame(block.Cmds[0], blockEnumerator.Current);

            ok = blockEnumerator.MoveNext();
            Assert.IsTrue(ok);
            Assert.AreSame(block.TransferCmd, blockEnumerator.Current);

            ok = blockEnumerator.MoveNext();
            Assert.IsFalse(ok);
        }

        [Test(),ExpectedException(typeof(InvalidOperationException))]
        public void EnumeratorMovePastEnd()
        {
            p = LoadProgramFrom("programs/GotoMultiplePaths.bpl");
            var block = GetMain(p).Blocks[0];

            var blockEnumerator = new BlockCmdEnumerator(block);

            Assert.AreEqual(2, blockEnumerator.Count);

            bool ok = false;

            for (int i = 0; i < 2; ++i)
            {
                ok = blockEnumerator.MoveNext();
                Assert.IsTrue(ok);
            }

            ok = blockEnumerator.MoveNext();
            Assert.IsFalse(ok);

            // Should throw InvalidOperation
            var x = blockEnumerator.Current;
        }

        [Test()]
        public void EntryWithImmediateGoto()
        {
            p = LoadProgramFrom("programs/EntryWithImmediateGoto.bpl");
            var block = GetMain(p).Blocks[0];

            var blockEnumerator = new BlockCmdEnumerator(block);

            Assert.AreEqual(1, blockEnumerator.Count);

            blockEnumerator.MoveNext();
            Assert.AreEqual("goto end;", TrimNewLines(blockEnumerator.Current.ToString()));
        }

        [Test()]
        public void EnumeratorMultipleCmds()
        {
            p = LoadProgramFrom("programs/Concretise.bpl");
            var block = GetMain(p).Blocks[0];

            var blockEnumerator = new BlockCmdEnumerator(block);

            Assert.AreEqual(5, blockEnumerator.Count);

            blockEnumerator.MoveNext();
            Assert.AreEqual("assert {:symbooglix_bp \"entry\"} true;", TrimNewLines(blockEnumerator.Current.ToString()));

            blockEnumerator.MoveNext();
            Assert.AreEqual("a := 1bv8;", TrimNewLines(blockEnumerator.Current.ToString()));

            blockEnumerator.MoveNext();
            Assert.AreEqual("x := 2bv8;", TrimNewLines(blockEnumerator.Current.ToString()));

            blockEnumerator.MoveNext();
            Assert.AreEqual("assert {:symbooglix_bp \"now_concrete\"} true;", TrimNewLines(blockEnumerator.Current.ToString()));

            blockEnumerator.MoveNext();
            Assert.AreEqual("return;", TrimNewLines(blockEnumerator.Current.ToString()));
        }

        [Test()]
        public void EnumeratorClone()
        {
            p = LoadProgramFrom("programs/Concretise.bpl");
            var block = GetMain(p).Blocks[0];

            var blockEnumerator = new BlockCmdEnumerator(block);

            Assert.AreEqual(5, blockEnumerator.Count);

            blockEnumerator.MoveNext();
            blockEnumerator.MoveNext();

            var copiedblockEnumerator = blockEnumerator.Clone();

            var oldPosition = blockEnumerator.Current;

            blockEnumerator.MoveNext();

            // The copied blockEnumerator shouldn't have moved.
            Assert.AreSame(oldPosition, copiedblockEnumerator.Current);

            copiedblockEnumerator.MoveNext();
            Assert.AreSame(blockEnumerator.Current, copiedblockEnumerator.Current);

            oldPosition = copiedblockEnumerator.Current;
            copiedblockEnumerator.MoveNext();

            // The blockEnumerator shouldn't have moved.
            Assert.AreSame(oldPosition, blockEnumerator.Current);
        }
    }
}

