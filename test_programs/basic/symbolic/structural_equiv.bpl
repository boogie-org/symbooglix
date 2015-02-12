// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out --fold-constants=1 %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
procedure main(x:int, y:int)
{
    var a:int;
    var b:int;

    a := x + y;
    b := x + y;
    assert a == b;
}

