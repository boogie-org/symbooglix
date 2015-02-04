// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
function {:builtin "rem"} rem(int, int) returns (int);
procedure main()
{
    assert rem(5,-2) == -1;
}
