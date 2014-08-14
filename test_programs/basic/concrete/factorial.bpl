// RUN: %symbooglix %s | %OutputCheck %s
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

// CHECK-L: State 4: Terminated without error

