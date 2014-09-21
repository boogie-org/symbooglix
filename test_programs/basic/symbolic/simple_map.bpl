// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck %s
procedure main()
{
    var m:[bv32]bv8;
    var index:bv32;

    m[index] := 0bv8;
    assert m[index] == 0bv8;
    // FIXME: Make this an NUnit test instead
    // CHECK-L: State 0: Terminated without error
}
