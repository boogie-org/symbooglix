// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 2 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedSpeculativePath 0
procedure main()
{
    var a:int;
    var b:int;
    assert (exists c:int :: a + c == b);
}
