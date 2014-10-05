using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using SymbooglixLibTests;
using System.Linq;

namespace BoogieTests
{
    [TestFixture ()]
    public class DuplicatorTests
    {
        Duplicator d;

        [SetUp]
        public void init()
        {
            d = new Duplicator();
        }

        [Test ()]
        public void BVConcatExpr()
        {
            var bv1_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 8);
            var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
            var A = new BvConcatExpr(Token.NoToken, bv1_8, bv2_8);
            var B = d.Visit(A);

            // The duplicator should ensure we get new BVConcatExprs
            Assert.IsFalse(Object.ReferenceEquals(A, B));
        }

        [Test()]
        public void BvExtractExpr()
        {
            var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
            var A = new BvExtractExpr(Token.NoToken, bv2_8, 6,0);
            var B = d.Visit(A);

            // The duplicator should ensure we get new BVExtractExprs
            Assert.IsFalse(Object.ReferenceEquals(A, B));
        }

        [Test()]
        public void NaryExpr()
        {
            var bv1_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 8);
            var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
            var A = NAryExpr.Eq (bv1_8, bv2_8);
            var B = d.Visit(A);

            Assert.IsFalse(Object.ReferenceEquals(A, B));
        }

        [Test()]
        public void WholeProgram()
        {
            var p = new Program();
            var t = new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.Bool);
            var gv = new GlobalVariable(Token.NoToken, t);
            p.AddTopLevelDeclaration(gv);
            string metaDataString = "This is a test";
            p.SetMetadata(0, metaDataString);

            // Now try to clone
            var p2 = (Program) d.Visit(p);

            // Check global is a copy
            int counter = 0;
            GlobalVariable gv2 = null;
            foreach (var g in p2.TopLevelDeclarations)
            {
                ++counter;
                Assert.IsInstanceOfType(typeof(GlobalVariable), g);
                gv2 = g as GlobalVariable;
            }
            Assert.AreEqual(1, counter);
            Assert.AreNotSame(gv, gv2);
            Assert.AreEqual(metaDataString, p2.GetMetatdata<string>(0));


            // Check Top level declarations list is duplicated properly
            var t2 = new TypedIdent(Token.NoToken, "bar", Microsoft.Boogie.Type.Bool);
            var gv3 = new GlobalVariable(Token.NoToken, t2);
            p2.AddTopLevelDeclaration(gv3);

            counter = 0;
            foreach (var g in p2.TopLevelDeclarations)
            {
                ++counter;
                Assert.IsInstanceOfType(typeof(GlobalVariable), g);
            }
            Assert.AreEqual(2, counter);

            // The original program should still only have one global variable
            counter = 0;
            foreach (var g in p.TopLevelDeclarations)
            {
                ++counter;
                Assert.IsInstanceOfType(typeof(GlobalVariable), g);
                Assert.AreSame(g, gv);
            }

            Assert.AreEqual(1, counter);

            // Change Metadata in p2, this shouldn't affect p
            string newMetaDataString = "Another test";
            p2.SetMetadata(0, newMetaDataString);

            Assert.AreNotEqual(p2.GetMetatdata<string>(0), p.GetMetatdata<string>(0));
        }

        [Test()]
        public void GotoTargets()
        {
            Program p = SymbooglixLibTests.SymbooglixTest.loadProgram("programs/GotoCmd.bpl");

            var main = p.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "main").First();

            // Access blocks via their labels of gotocmds
            var oldEntryBlock =  ( main.Blocks[1].TransferCmd as GotoCmd ).labelTargets[0];
            Assert.AreEqual("entry", oldEntryBlock.Label);

            var oldThing1Block = ( main.Blocks[1].TransferCmd as GotoCmd ).labelTargets[1];
            Assert.AreEqual("thing1", oldThing1Block.Label);

            var oldThing2Block = ( main.Blocks[0].TransferCmd as GotoCmd ).labelTargets[1];
            Assert.AreEqual("thing2", oldThing2Block.Label);

            // Now duplicate
            var duplicator = new Duplicator();
            var newProgram = (Program) duplicator.Visit(p);

            // FIXME:
            // There is a bug in Boogie where the label targets of GotoCmds don't get changed on duplication

            // First lets check BBs have been duplicated
            var newMain= newProgram.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "main").First();
            var newEntryBlock = newMain.Blocks[0];
            Assert.AreEqual("entry", newEntryBlock.Label);
            Assert.AreNotSame(newEntryBlock, oldEntryBlock);

            var newThing1Block = newMain.Blocks[1];
            Assert.AreEqual("thing1", newThing1Block.Label);
            Assert.AreNotSame(newThing1Block, oldThing1Block);

            var newThing2Block = newMain.Blocks[2];
            Assert.AreEqual("thing2", newThing2Block.Label);
            Assert.AreNotSame(newThing2Block, oldThing2Block);

            // Okay let's examine the gotos and make sure they point to the right instances
            var newEntryGotoCmd = newEntryBlock.TransferCmd as GotoCmd;
            var newthing1GotoCmd = newThing1Block.TransferCmd as GotoCmd;

            Assert.AreNotSame(newEntryGotoCmd.labelTargets[0], oldThing1Block);
            Assert.AreSame(newEntryGotoCmd.labelTargets[0], newThing1Block);
            Assert.AreNotSame(newEntryGotoCmd.labelTargets[1], oldThing2Block);
            Assert.AreSame(newEntryGotoCmd.labelTargets[1], newThing2Block);

            Assert.AreNotSame(newthing1GotoCmd.labelTargets[0], oldEntryBlock);
            Assert.AreSame(newthing1GotoCmd.labelTargets[0], newEntryBlock);
            Assert.AreNotSame(newthing1GotoCmd.labelTargets[1], oldThing1Block);
            Assert.AreSame(newthing1GotoCmd.labelTargets[1], newThing1Block);

        }
    }
}

