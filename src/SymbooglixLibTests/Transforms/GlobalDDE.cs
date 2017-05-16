//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using Microsoft.Boogie;
using NUnit.Framework;
using System;
using System.Linq;

namespace TransformTests
{
    [TestFixture()]
    public class GlobalDDE
    {
        [Test()]
        public void FuncUsedInImpl()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is live so it should not be removed
                function foo(x:int) returns(bool);

                procedure main()
                {
                    assert foo(5);
                }
                ", "test.bpl");

            Assert.AreEqual(1, FunctionCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, FunctionCount(prog));

        }

        [Test()]
        public void FuncUsedInRequires()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is live so it should not be removed
                function foo(x:int) returns(bool);

                procedure main()
                requires foo(5) == true;
                {
                    return;
                }
                ", "test.bpl");

            Assert.AreEqual(1, FunctionCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, FunctionCount(prog));

        }

        [Test()]
        public void FuncUsedInEnsures()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is live so it should not be removed
                function foo(x:int) returns(bool);

                procedure main()
                ensures foo(5) == true; // This doesn't make sense but we only care about uses
                {
                    return;
                }
                ", "test.bpl");

            Assert.AreEqual(1, FunctionCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, FunctionCount(prog));

        }

        [Test()]
        public void FuncNotUsed()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is dead so it should be removed
                function foo(x:int) returns(bool);

                procedure main()
                {
                    assert true;
                }
                ", "test.bpl");

            Assert.AreEqual(1, FunctionCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0, FunctionCount(prog));

        }

        [Test()]
        public void RecursiveFuncUsed()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is alive and is recursive
                function foo(x:int) returns(int) {
                    if x !=0 && x > 0 then foo(x-1) else 0
                }

                procedure main()
                {
                    assert foo(1) == 0;
                }
                " , "test.bpl");

            Assert.AreEqual(1 , FunctionCount(prog));
            Assert.AreEqual(1 , AxiomCount(prog)); // Implicit axiom on foo()
            RunGDDE(prog);
            Assert.AreEqual(1, FunctionCount(prog));
            Assert.AreEqual(1, AxiomCount(prog)); // Implicit axiom on foo()
        }

        [Test()]
        public void InDirectFuncUseWithImplicitAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is not dead because it's used by bar
                function foo(x:int) returns(bool);

                // This gets converted to an axiom during parsing so it is considered to be used
                function bar() returns (bool)
                {
                    foo(5)
                }

                // Baz is dead
                function baz() returns (bool)
                {
                    true
                }   

                procedure main()
                {
                    assert bar();
                }
                ", "test.bpl");

            Assert.AreEqual(3, FunctionCount(prog));
            Assert.AreEqual(2 , AxiomCount(prog)); // Implicit
            RunGDDE(prog);
            Assert.AreEqual(2, FunctionCount(prog));
            Assert.AreEqual(1 , AxiomCount(prog)); // Implicit
        }

        [Test()]
        public void InDirectFuncIsDeadUseWithImplicitAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is dead because it's used by bar which is dead
                function foo(x:int) returns(bool);

                // This gets converted to an axiom during parsing
                function bar() returns (bool)
                {
                    foo(5)
                }

                // Baz is dead. This gets converted to an axiom during parsing
                function baz() returns (bool)
                {
                    true
                }

                procedure main()
                {
                    assert true;
                }
                " , "test.bpl");
            Assert.AreEqual(2 , AxiomCount(prog)); // Implicit
            Assert.AreEqual(3 , FunctionCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0 , FunctionCount(prog));
            Assert.AreEqual(0 , AxiomCount(prog));
        }

        [Test()]
        public void InDirectFuncUseWithoutImplicitAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is not dead because it's used by bar
                function foo(x:int) returns(bool);

                // No axiom is used here
                function {:inline } bar() returns (bool)
                {
                    foo(5)
                }

                // Baz is dead
                function baz() returns (bool)
                {
                    true
                }   

                procedure main()
                {
                    assert bar();
                }
                ", "test.bpl");

            Assert.AreEqual(3, FunctionCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(2, FunctionCount(prog));

        }

        [Test()]
        public void FuncNotInCodeButUsedInDeadAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo is dead so it should be removed
                function foo(x:int) returns(bool);

                // Axiom is dead so it should be removed
                axiom foo(5) == true;


                procedure main()
                {
                    assert true;
                }
                ", "test.bpl");

            Assert.AreEqual(1, FunctionCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0, FunctionCount(prog));
            Assert.AreEqual(0, AxiomCount(prog));

        }

        [Test()]
        public void InDirectFuncIsDeadUseWithoutImplicitAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // foo is dead because it's used by bar
                function foo(x:int) returns(bool);

                // No axiom is used here, bar is dead
                function {:inline } bar() returns (bool)
                {
                    foo(5)
                }

                procedure main()
                {
                    assert true;
                }
                " , "test.bpl");

            Assert.AreEqual(2 , FunctionCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0 , FunctionCount(prog));

        }

        [Test()]
        public void DoubleInDirectFuncIsDeadUseWithoutImplicitAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // baz is dead because bar() is dead
                function baz(x:int) returns(bool);

                // foo is dead because it's used by bar
                function {:inline } foo(x:int) returns(bool)
                {
                    baz(2)
                }

                // No axiom is used here, bar is dead
                function {:inline } bar() returns (bool)
                {
                    foo(5)
                }

                procedure main()
                {
                    assert true;
                }
                " , "test.bpl");

            Assert.AreEqual(3 , FunctionCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0 , FunctionCount(prog));

        }

        [Test()]
        public void DeadAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Axiom's that don't reference any globals variables
                // or functions are considered to be dead.
                // FIXME: This means ""axiom false;"" is considered to be dead
                // and will be removed. This might not be desirable
                axiom true;


                procedure main()
                {
                    assert true;
                }
                ", "test.bpl");

            Assert.AreEqual(1, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0, AxiomCount(prog));

        }

        [Test()]
        public void FuncNotInCodeButUsedInLiveAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                // Foo looks dead but we can't remove it
                // due to axiom
                function foo(x:int) returns(bool);
                
                const g:bool;

                // Axiom is not dead due to global variable use
                axiom (foo(5) == true) && g;

                procedure main()
                {
                    assert g;
                }
                ", "test.bpl");

            Assert.AreEqual(1, FunctionCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
            Assert.AreEqual(1, GlobalVariableCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, FunctionCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
            Assert.AreEqual(1, GlobalVariableCount(prog));
        }

        [Test()]
        public void GlobalVariableNotUsed()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                var g:bool;

                procedure main()
                {
                    return;
                }
                ", "test.bpl");

            Assert.AreEqual(1, GlobalVariableCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0, GlobalVariableCount(prog));
        }

        [Test()]
        public void GlobalVariableUsedInImpl()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                var g:bool;

                procedure main()
                {
                    assert g;
                }
                ", "test.bpl");

            Assert.AreEqual(1, GlobalVariableCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, GlobalVariableCount(prog));
        }

        [Test()]
        public void GlobalVariableSomeAliveSomeDead()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                var g:bool;
                var d1:bool; // dead
                var d2:bool; // dead

                procedure main()
                {
                    assert g;
                }
                ", "test.bpl");

            Assert.AreEqual(3, GlobalVariableCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, GlobalVariableCount(prog));
        }

        [Test()]
        public void GlobalVariableUsedInProcModSet()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                var g:bool;

                procedure main();
                modifies g;

                ", "test.bpl");

            Assert.AreEqual(1, GlobalVariableCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, GlobalVariableCount(prog));
        }

        [Test()]
        public void GlobalVariableUsedInRequires()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                var g:bool;

                procedure main();
                requires g;

                ", "test.bpl");

            Assert.AreEqual(1, GlobalVariableCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, GlobalVariableCount(prog));
        }

        [Test()]
        public void GlobalVariableUsedInEnsures()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                var g:bool;

                procedure main();
                ensures g;

                ", "test.bpl");

            Assert.AreEqual(1, GlobalVariableCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, GlobalVariableCount(prog));
        }

        [Test()]
        public void DeadGlobalVariableUsedInAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                const g:bool;
                axiom g == true;

                procedure main();

                ", "test.bpl");

            Assert.AreEqual(1, GlobalVariableCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0, GlobalVariableCount(prog));
            Assert.AreEqual(0, AxiomCount(prog));
        }

        [Test()]
        public void LiveGlobalVariableUsedInAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                const g:bool;
                axiom g == true;

                procedure main()
                {
                    assert g;
                }

                ", "test.bpl");

            Assert.AreEqual(1, GlobalVariableCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(1, GlobalVariableCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
        }

        [Test()]
        public void LiveGlobalVariablesUsedInAxiom()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                const x:int;
                // FIXME: Should GlobalDDE be changed to remove this variable?
                const z:int; // This variable could be considered dead but the axiom will keep it alive
                axiom x == z;

                procedure main() {
                    var y:int;

                    y := x;
                }
                ", "test.bpl");

            Assert.AreEqual(2, GlobalVariableCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(2, GlobalVariableCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
        }

        [Test()]
        public void TransitiveAxiomFunctionDependency()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                function f(int) returns (int);
                function g(int) returns (int);
                function h(int) returns (int);

                axiom (forall x:int :: f(x) > g(x)); // Should not remove
                axiom (forall x:int :: g(x) > h(x)); // Should not remove

                procedure main(a:int)
                requires h(a) > 0;
                {
                    assert true;
                }
                ", "test.bpl");

            Assert.AreEqual(3, FunctionCount(prog));
            Assert.AreEqual(2, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(3, FunctionCount(prog));
            Assert.AreEqual(2, AxiomCount(prog));
        }

        [Test()]
        public void TransitiveAxiomGlobalDependency()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                const f:int;
                const g:int;
                const h:int;

                axiom f > g; // Should not remove
                axiom g > h; // Should not remove

                procedure main(a:int)
                requires h > 0;
                {
                    assert true;
                }
                ", "test.bpl");

            Assert.AreEqual(3, GlobalVariableCount(prog));
            Assert.AreEqual(2, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(3, GlobalVariableCount(prog));
            Assert.AreEqual(2, AxiomCount(prog));
        }

        [Test()]
        public void TransitiveAxiomGlobalAndFunctionDependency()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                const e:int;
                const f:int;
                function g(int) returns (int);
                const h:int;

                axiom (e == f); // Should not remove
                axiom (forall x:int :: f > g(x)); // Should not remove
                axiom (forall x:int :: g(x) > h); // Should not remove

                procedure main(a:int)
                requires h > 0;
                {
                    assert true;
                }
                ", "test.bpl");

            Assert.AreEqual(3, GlobalVariableCount(prog));
            Assert.AreEqual(1, FunctionCount(prog));
            Assert.AreEqual(3, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(3, GlobalVariableCount(prog));
            Assert.AreEqual(1, FunctionCount(prog));
            Assert.AreEqual(3, AxiomCount(prog));
        }

        [Test()]
        public void TransitiveAxiomTwoSets()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                const e:int;
                const f:int;
                function g(int) returns (int);
                const h:int;

                // One set the based on transitivity should not be removed
                axiom (e == f);
                axiom (forall x:int :: f > g(x));
                axiom (forall x:int :: g(x) > h);

                // Another set that based on transitivity should not be removed
                function w(int) returns (int);
                const x:int;
                const y:int;
                const z:int;
                axiom x > y;
                axiom y > z;
                axiom (forall n:int :: w(n) > z);

                // Should be removed
                axiom false;

                procedure main(a:int)
                requires h > 0;
                requires z > 0;
                {
                    assert true;
                }
                ", "test.bpl");

            Assert.AreEqual(6, GlobalVariableCount(prog));
            Assert.AreEqual(2, FunctionCount(prog));
            Assert.AreEqual(7, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(6, GlobalVariableCount(prog));
            Assert.AreEqual(2, FunctionCount(prog));
            Assert.AreEqual(6, AxiomCount(prog));
        }

        [Test()]
        public void NoAxiomDependencyOnInterpretedFunctions()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                function {:bvbuiltin ""bvadd""} BVADD32(bv32,bv32) returns (bv32);

                // This function and axiom are dead
                function ADD_ONE(bv32) returns (bv32);
                axiom (forall x:bv32 :: ADD_ONE(x) == BVADD32(x, 1bv32));

                procedure main() {
                    var x:bv32;
                    var y:bv32;

                    x := BVADD32(x, y);
                    assert x == BVADD32(x, y);
                }
            ", "test.bpl");

            Assert.AreEqual(0, GlobalVariableCount(prog));
            Assert.AreEqual(2, FunctionCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0, GlobalVariableCount(prog));
            Assert.AreEqual(1, FunctionCount(prog));
            Assert.AreEqual(0, AxiomCount(prog));

            var func = prog.TopLevelDeclarations.OfType<Function>().First();
            Assert.AreEqual("BVADD32", func.Name);
        }

        [Test()]
        public void NoAxiomDependencyOnInterpretedFunctions2()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
                function {:bvbuiltin ""bvadd""} BVADD32(bv32,bv32) returns (bv32);

                // This function and axiom are live due to being used in main()
                function ADD_ONE(bv32) returns (bv32);
                axiom (forall x:bv32 :: ADD_ONE(x) == BVADD32(x, 1bv32));

                procedure main() {
                    var x:bv32;
                    var y:bv32;

                    x := BVADD32(x, y);
                    assert x == BVADD32(x, y);
                    assert BVADD32(x, 1bv32) == ADD_ONE(x);
                }
            ", "test.bpl");

            Assert.AreEqual(0, GlobalVariableCount(prog));
            Assert.AreEqual(2, FunctionCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
            RunGDDE(prog);
            Assert.AreEqual(0, GlobalVariableCount(prog));
            Assert.AreEqual(2, FunctionCount(prog));
            Assert.AreEqual(1, AxiomCount(prog));
        }


        public void RunGDDE(Program prog)
        {
            var GDDE = new Symbooglix.Transform.GlobalDeadDeclEliminationPass();
            var PM = new Symbooglix.Transform.PassManager();
            PM.Add(GDDE);
            PM.Run(prog);
        }

        public int FunctionCount(Program prog)
        {
            return prog.TopLevelDeclarations.OfType<Function>().Count();
        }

        public int AxiomCount(Program prog)
        {
            return prog.TopLevelDeclarations.OfType<Axiom>().Count();
        }

        public int GlobalVariableCount(Program prog)
        {
            return prog.TopLevelDeclarations.OfType<Variable>().Count();
        }
    }
}

