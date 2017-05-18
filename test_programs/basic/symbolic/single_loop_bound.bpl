// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --max-loop-depth=3 --output-dir %t.symbooglix-out %s | %OutputCheck %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 4
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedLoopBound 1
procedure main()
{
  var x:int;
  var y:int;
  havoc x; // Symbolic
  y := 0;
  // CHECK: Terminated with loop bound 3 exceeded at .+${CHECKFILE_NAME}:${LINE:+1}
  while (x < 100)
  {
    x := x + 1;
  }
}
