// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out --goto-assume-look-ahead=1 %s | %OutputCheck %s
procedure fact(N:int) returns(r:int);

implementation fact(N:int) returns(r:int)
{
    if (N == 0)
    {
        r := 1;
    }
    else
    {
        call r:= fact(N-1);
        r := r * N;
    }
}

procedure main(N:int)
requires (N == 4);
{
    var local:int;
    call local := fact(N);
    assert local == 24;
}

// CHECK-L: State 0: Terminated without error

