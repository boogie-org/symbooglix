// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out  %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
type foo = int;
procedure main()
{
    var x:int;
    var y:foo;
    y := 5:foo;
    x := y:int;
    assert x == 5;
}
