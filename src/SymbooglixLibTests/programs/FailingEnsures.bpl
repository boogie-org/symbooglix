procedure main() returns(r:int)
ensures r > 0;
{
    var x:int;
    assume ( x <= 0);
    r := x;
}
