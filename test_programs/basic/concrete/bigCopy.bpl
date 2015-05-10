// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
procedure main()
{
    var x:[int]int;
    var y:[int]int;
    var counter:int;

    // Writes
    counter := 0;
    while (counter < 2000)
    {
        x[counter] := counter;
        counter := counter + 1;
    }

    y := x;

    // Reads
    counter := 0;
    while (counter < 2000)
    {
        assert y[counter] == counter;
        assert y[counter] == x[counter];
        counter := counter + 1;
    }
}
