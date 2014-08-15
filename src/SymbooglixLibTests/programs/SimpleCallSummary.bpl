var a:int, b:int, c:int;

procedure main(x:int)
requires x > 0;
modifies a, b, c;
{
    a := 2;
    call b := bar(x);
    assert {:symbooglix_bp "cmodset"} b >= 0;
}

procedure bar(y:int) returns (r:int);
requires a > 0;
requires y > -1;
modifies c;
ensures r > 0;
