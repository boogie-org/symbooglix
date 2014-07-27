using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Linq;

namespace Symbooglix
{
    namespace Transform
    {
        public class PassManager
        {
            protected List<Tuple<IPass,PassInfo>> Passes;
            public Program TheProgram
            {
                get;
                private set;
            }


            public class PassManagerEventArgs
            {
                public readonly IPass ThePass;
                public readonly Program TheProgram;
                public PassManagerEventArgs(IPass pass, Program program) { ThePass = pass; TheProgram = program; }
            }
            public delegate void PassRunEvent(Object sender, PassManagerEventArgs args);
            public event PassRunEvent BeforePassRun;
            public event PassRunEvent AfterPassRun;


            public PassManager(Program prog)
            {
                Passes = new List<Tuple<IPass,PassInfo>>();
                TheProgram = prog;
            }

            public void Add(IPass pass)
            {
                var passInfo = new PassInfo();

                // Get the dependencies
                pass.SetPassInfo(ref passInfo);
                var tuple = Tuple.Create(pass, passInfo);

                if (passInfo.Dependencies != null)
                {
                    // We could be more sophisticatd here and try to optimise
                    // the list of passes so we don't run redundant analyses
                    // Leave this for now

                    // The pass has Dependencies so Add them

                    // It is not safe to iterate over a dictionary and modify it
                    // at the same time so do it in two stages.
                    // 1. Collect all the KeyValue Pairs in the dictionary
                    // 2. Iterate over the collected KeyValue pairs and modify the dictionary
                    var depList = new List<KeyValuePair<System.Type,IPass>>();
                    foreach (var keyValuePair in passInfo.Dependencies)
                    {
                        depList.Add(keyValuePair);
                    }

                    foreach (var keyValuePair in depList)
                    {
                        // Create dependency. This requires that the pass has a default constructor
                        IPass dependencyOfPass = Activator.CreateInstance(keyValuePair.Key) as IPass;

                        passInfo.Dependencies[keyValuePair.Key] = dependencyOfPass;

                        // Do this recursively so we handle any dependencies of the dependencies (of the...)*
                        Add(dependencyOfPass);
                    }

                }

                Passes.Add(tuple);
            }
                
            public void Run()
            {
                foreach (var pass in Passes.Select( p => p.Item1))
                {
                    // Passes may implement multiple IPass interfaces
                    // so we can't use Handle(pass as dynmaic) or double
                    // dispatch here because may need to call Handle multiple
                    // times. So we must do this manually
                    bool handled = false;

                    if (BeforePassRun != null)
                        BeforePassRun(this, new PassManagerEventArgs(pass, TheProgram));

                    // Eurgh: Macros would be handy here!

                    if (pass is IProgramPass)
                    {
                        Handle(pass as IProgramPass);
                        handled = true;
                    }

                    if (pass is IFunctionPass)
                    {
                        Handle(pass as IFunctionPass);
                        handled = true;
                    }

                    if (pass is IProcedurePass)
                    {
                        Handle(pass as IProcedurePass);
                        handled = true;
                    }

                    if (pass is IImplementationPass)
                    {
                        Handle(pass as IImplementationPass);
                        handled = true;
                    }

                    if (pass is IAxiomPass)
                    {
                        Handle(pass as IAxiomPass);
                        handled = true;
                    }

                    if (pass is IGlobalVariablePass)
                    {
                        Handle(pass as IGlobalVariablePass);
                        handled = true;
                    }

                    if (pass is IConstantVariablePass)
                    {
                        Handle(pass as IConstantVariablePass);
                        handled = true;
                    }

                    if (!handled)
                        throw new InvalidCastException("Pass type not handled!");

                    if (AfterPassRun != null)
                        AfterPassRun(this, new PassManagerEventArgs(pass, TheProgram));
                }
            }

            private void Handle(IProgramPass pass)
            {
                pass.RunOn(TheProgram);
            }

            private void Handle(IFunctionPass pass)
            {
                var functions = TheProgram.TopLevelDeclarations.OfType<Function>();
                foreach (var function in functions)
                {
                    pass.RunOn(function);
                }
            }

            private void Handle(IProcedurePass pass)
            {
                var procedures = TheProgram.TopLevelDeclarations.OfType<Procedure>();
                foreach (var procedure in procedures)
                {
                    pass.RunOn(procedure);
                }
            }

            private void Handle(IImplementationPass pass)
            {
                var implementations= TheProgram.TopLevelDeclarations.OfType<Implementation>();
                foreach (var implementation in implementations)
                {
                    pass.RunOn(implementation);
                }
            }

            private void Handle(IAxiomPass pass)
            {
                var axioms = TheProgram.TopLevelDeclarations.OfType<Axiom>();
                foreach (var axiom in axioms)
                {
                    pass.RunOn(axiom);
                }
            }

            private void Handle(IBasicBlockPass pass)
            {
                foreach (var basicBlock in TheProgram.Blocks())
                {
                    pass.RunOn(basicBlock);
                }
            }

            private void Handle(IGlobalVariablePass pass)
            {
                foreach (var global in TheProgram.TopLevelDeclarations.OfType<GlobalVariable>())
                {
                    pass.RunOn(global);
                }
            }

            private void Handle(IConstantVariablePass pass)
            {
                foreach (var constant in TheProgram.TopLevelDeclarations.OfType<Constant>())
                {
                    pass.RunOn(constant);
                }
            }

            public class PassInfo
            {
                // FIXME: This shouldn't be public, only the PassManager should be able to access this
                public Dictionary<System.Type,IPass> Dependencies = null;

                // Passes use this to declare what passes they need run before them in SetPassInfo()
                public void AddDependency<T>() where T : IPass
                {
                    // We don't create the passes here
                    if (Dependencies == null)
                    {
                        Dependencies = new Dictionary<System.Type, IPass>();
                    }

                    // Don't create the passes here. Let the PassManager
                    // do it instead so it can optimise the list of passes to
                    // run.
                    Dependencies.Add(typeof(T), null);
                }

                // Passes can use this to gain access to passes they depend on.
                public T GetDependency<T>() where T : class, IPass
                {
                    return Dependencies[typeof(T)] as T;
                }
            }

        }
    }
}

