// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
procedure main()
{
    var x:[int]bool;
    var y:[int]bool;

    x[0] := false;
    x[1] := true;
    y := x;
    y[0] := true;
    assert x[0] == false;
    assert y[0] == true;
    assert x[1] == y[1];
}
