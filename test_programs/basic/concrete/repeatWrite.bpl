// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --fold-constants=1 --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0

// This test is much faster with constant folding enabled
procedure main()
{
    var x:[int]int;
    var counter:int;
    counter := 0;
    while (counter < 1000)
    {
        x[0] := counter;
        counter := counter +1;
    }
    assert x[0] == 999;
    assert counter == 1000;
}
