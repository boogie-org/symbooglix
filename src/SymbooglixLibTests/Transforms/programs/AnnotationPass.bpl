var g0:int;
var g1:int;
var g2:int;

const c0:int;
const c1:int;
const c2:int;

axiom true;
axiom true;

function foo(a:int, b:int) returns(r:bool);

function bar(a:int, b:int) returns(r:bool)
{
    a > b
}

function {:inline} barI(a:int, b:int) returns(r:bool)
{
    a > b
}

procedure main(x:int, y:int) returns(r:bool)
modifies g0, g1;
requires x != y;
ensures r;
{
    var dummy:bool;
    dummy := foo(x,y);
    call cool(x,y);
    call dummy := evencooler(x,y);

    r:= barI(x,y) && bar(x,y);

    if (r)
    {
        assert true;
    }
    else
    {
        assert true;
    }

}


procedure cool(x:int, y:int);
requires x > y;
requires x == x;
requires y == y;
ensures old(g0) < g0;
modifies g0;



procedure evencooler(x:int, y:int) returns(r:bool)
requires x > y;
ensures old(g1) < g1;
ensures r == false;
modifies g1;
{
    r:= false;
    g1 := g1 +2;
}
