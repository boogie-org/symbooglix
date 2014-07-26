using System;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace Symbooglix
{
    namespace Transform
    {
        public interface IPass
        {
            string GetName();
            void SetPassInfo(ref PassManager.PassInfo passInfo);
        }

        public interface IProgramPass : IPass
        {
            bool RunOn(Program prog);
        }

        public interface IFunctionPass : IPass
        {
            bool RunOn(Function func);
        }

        public interface IProcedurePass : IPass
        {
            bool RunOn(Procedure proc);
        }

        public interface IImplementationPass : IPass
        {
            bool RunOn(Implementation impl);
        }

        public interface IAxiomPass : IPass
        {
            bool RunOn(Axiom axiom);
        }

        // TODO : GlobalVariablePass / constant pass?
        public interface IGlobalVariablePass : IPass
        {
            bool RunOn(GlobalVariable globalVariable);
        }

        public interface IConstantVariablePass : IPass
        {
            bool RunOn(Constant constant);
        }

        public interface IBasicBlockPass : IPass
        {
            bool RunOn(Block block);
        }
    }
}

