//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    namespace Solver
    {
        // This needs rethinking. In it's current form I don't think we'll ever get a hit!
        // e.g.
        //
        // if ( x== 1) {}
        // if ( x==1) {}
        // We won't get a hit for the above because after executing the first if the constraint changes.
        public struct SimpleSolverCacheStatistics : ISolverImplStatistics
        {
            public ISolverImplStatistics UnderlyingSolverStats;
            public int cacheHits;
            public int cacheMisses;
            public int maxCacheSize;
            public int currentCacheSize;
            public void Reset()
            {
                cacheHits = 0;
                cacheMisses = 0;
                maxCacheSize = 0;
                currentCacheSize = 0;
            }

            public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
            {
                double denominator = (double) ( cacheHits + cacheMisses );
                if (denominator == 0)
                    denominator = 1;
                double hitsPercentage = 100* ((double) (cacheHits)) / denominator;
                double missesPercentage = 100* ((double)cacheHits) / denominator;
                TW.WriteLine("{0}:", this.GetType().ToString());
                TW.Indent += 1;
                TW.WriteLine("cache_hits: {0} #({1}%)", cacheHits, hitsPercentage);
                TW.WriteLine("cache_misses: {0} #({1}%)", cacheMisses, missesPercentage);
                TW.WriteLine("max_cache_size: {0}", maxCacheSize);
                TW.WriteLine("current_cache_size: {0}", currentCacheSize);
                TW.WriteLine("underlying_solver:");
                TW.Indent += 1;
                UnderlyingSolverStats.WriteAsYAML(TW);
                TW.Indent -= 2;
            }
        }

        public class SimpleSolverCache : ISolverImpl
        {
            private ISolverImpl UnderlyingSolver;
            private SimpleSolverCacheStatistics InternalStatistics;
            private Dictionary<Query,Solver.IQueryResult> Cache;
            public int MaxCacheSize   // Zero means no limit, number of queries to cache
            { 
                get
                {
                    return InternalStatistics.maxCacheSize;
                }

                private set
                {
                    InternalStatistics.maxCacheSize = value;
                }
            }

            public SimpleSolverCache(ISolverImpl underlyingSolver, int maxCacheSize=0)
            {
                this.UnderlyingSolver = underlyingSolver;
                Cache = new Dictionary<Query, IQueryResult>();
                InternalStatistics.Reset();

                if (maxCacheSize < 0)
                    throw new ArgumentException("maxCacheSize must be >= 0");

                this.MaxCacheSize = maxCacheSize;
            }

            public IQueryResult ComputeSatisfiability(Query query)
            {
                IQueryResult cachedResult = null;
                Cache.TryGetValue(query, out cachedResult);

                if (cachedResult != null)
                {
                    ++InternalStatistics.cacheHits;
                    return cachedResult;
                }
                else
                {
                    ++InternalStatistics.cacheMisses;
                    var result = UnderlyingSolver.ComputeSatisfiability(query);

                    if (MaxCacheSize != 0 && Cache.Count >= MaxCacheSize)
                    {
                        // We need to drop something from the cache
                        // Drop this first thing we find
                        var e = Cache.GetEnumerator();
                        var ok = e.MoveNext();
                        var toRemove = e.Current.Key;
                        Debug.Assert(ok);
                        if (!Cache.Remove(toRemove))
                            throw new InvalidOperationException("Failed to remove key from cache");
                    }

                    // Make sure we store a copy. We can't store what we were given because the executor
                    // will change it during execution
                    Cache[query.Clone()] = result;
                    return result;
                }
            }

            public void SetTimeout(int seconds)
            {
                UnderlyingSolver.SetTimeout(seconds);
            }

            public void Interrupt()
            {
                UnderlyingSolver.Interrupt();
            }

            public void Dispose()
            {
                Cache.Clear();
                UnderlyingSolver.Dispose();
            }

            public ISolverImplStatistics Statistics 
            {
                get 
                {
                    InternalStatistics.UnderlyingSolverStats = UnderlyingSolver.Statistics;
                    InternalStatistics.currentCacheSize = Cache.Count;
                    return InternalStatistics; // Return copy as statistics is a struct
                }
            }
        }
    }
}

