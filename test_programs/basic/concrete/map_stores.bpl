// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
procedure main()
{
    var x:[int]int;
    x[0] := 5;
    x[1] := 6;
    assert x[0] == 5;
}
