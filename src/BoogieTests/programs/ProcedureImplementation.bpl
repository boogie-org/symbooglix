procedure main(a:int) returns (r:int);
requires a > 0;
ensures  r > a;

implementation main(a:int) returns (r:int)
{
    r:= a + 1;
}
