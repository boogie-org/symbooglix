// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 2 %symbooglix --output-dir %t.symbooglix-out %s | %OutputCheck %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 0
procedure main(p1:bv8)
requires p1 == 0bv8;
{
    // CHECK: State 0: Terminated with assertion failure .+${CHECKFILE_NAME}:${LINE:+1}: assert p1 == 1bv8;
    assert p1 == 1bv8; // Effectively assert false
}
