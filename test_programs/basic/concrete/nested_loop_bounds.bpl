// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --max-loop-depth=10 --output-dir %t.symbooglix-out %s | %OutputCheck %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedLoopBound 1
procedure main()
{
  var x:int;
  var y:int;
  x := 0;
  y := 0;
  while (x < 100)
  {
    // CHECK: Terminated with loop bound 10 exceeded at .+${CHECKFILE_NAME}:${LINE:+1}
    while (true) {
      y := y + 1;
    }
    x := x + 1;
  }
}
