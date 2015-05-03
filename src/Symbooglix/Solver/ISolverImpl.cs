using System;
using System.Collections.Generic;
using System.IO;

namespace Symbooglix
{
    namespace Solver
    {
        // This interface is designed around the needs of the underlying solver
        // as opposed to the Executor.
        public interface ISolverImpl : IDisposable
        {
            IQueryResult ComputeSatisfiability(Query query);
            void SetTimeout(int seconds);
            ISolverImplStatistics Statistics { get;}
            void Interrupt();
        }

        public interface ISolverImplStatistics : Util.IYAMLWriter
        {
            void Reset();
        }
    }
}

