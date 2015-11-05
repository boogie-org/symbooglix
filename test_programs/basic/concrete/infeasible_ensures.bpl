// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 2 %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingEnsures 1
var g:bv8;

procedure main()
requires g == 0bv8;
modifies g;
// CHECK: State 0: Terminated with failing ensures .+${CHECKFILE_NAME}:${LINE:+1}: g == 1bv8
ensures g == 1bv8;
{
    g := 2bv8;
}
