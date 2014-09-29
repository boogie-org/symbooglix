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
            p = loadProgram("programs/GotoMultiplePaths.bpl");

            var block = getMain(p).Blocks[0];

            // Try using the Enumerable so we can use in foreach loop
            var blockEnumerable= new BlockCmdEnumerable(block);

            var cmdStrings = new List<string>();
            foreach (var cmd in blockEnumerable)
            {
                cmdStrings.Add(cmd.ToString());
            }

            Assert.AreEqual(2, cmdStrings.Count);
            Assert.AreEqual("assert {:symbooglix_bp \"entry\"} true;\n", cmdStrings[0]);
            Assert.AreEqual("Microsoft.Boogie.GotoCmd", cmdStrings[1]);
        }

        [Test()]
        public void EnumeratorHitEnd()
        {
            p = loadProgram("programs/GotoMultiplePaths.bpl");
            var block = getMain(p).Blocks[0];

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
            p = loadProgram("programs/GotoMultiplePaths.bpl");
            var block = getMain(p).Blocks[0];

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
            p = loadProgram("programs/EntryWithImmediateGoto.bpl");
            var block = getMain(p).Blocks[0];

            var blockEnumerator = new BlockCmdEnumerator(block);

            Assert.AreEqual(1, blockEnumerator.Count);

            blockEnumerator.MoveNext();
            Assert.AreEqual("Microsoft.Boogie.GotoCmd", blockEnumerator.Current.ToString());
        }

        [Test()]
        public void EnumeratorMultipleCmds()
        {
            p = loadProgram("programs/Concretise.bpl");
            var block = getMain(p).Blocks[0];

            var blockEnumerator = new BlockCmdEnumerator(block);

            Assert.AreEqual(5, blockEnumerator.Count);

            blockEnumerator.MoveNext();
            Assert.AreEqual("assert {:symbooglix_bp \"entry\"} true;\n", blockEnumerator.Current.ToString());

            blockEnumerator.MoveNext();
            Assert.AreEqual("a := 1bv8;\n", blockEnumerator.Current.ToString());

            blockEnumerator.MoveNext();
            Assert.AreEqual("x := 2bv8;\n", blockEnumerator.Current.ToString());

            blockEnumerator.MoveNext();
            Assert.AreEqual("assert {:symbooglix_bp \"now_concrete\"} true;\n", blockEnumerator.Current.ToString());

            blockEnumerator.MoveNext();
            Assert.AreEqual("Microsoft.Boogie.ReturnCmd", blockEnumerator.Current.ToString());
        }

        [Test()]
        public void EnumeratorClone()
        {
            p = loadProgram("programs/Concretise.bpl");
            var block = getMain(p).Blocks[0];

            var blockEnumerator = new BlockCmdEnumerator(block);

            Assert.AreEqual(5, blockEnumerator.Count);

            blockEnumerator.MoveNext();
            blockEnumerator.MoveNext();

            var copiedblockEnumerator = blockEnumerator.DeepClone();

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

