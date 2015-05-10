// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
procedure main()
{
    var symOffset:int;
    var counter:int;
    var x:[int]int;

    counter := 0;

    // Symbooglix's ability to handle
    // symbolic store locations that don't alias
    // should make this benchmark very quick to
    // execute

    // Writes
    while (counter < 2000)
    {
        x[symOffset + counter] := counter;
        counter := counter + 1;
    }

    // Reads
    while (counter < 2000)
    {
        assert x[symOffset + counter] == counter;
        counter := counter + 1;
    }
}

