var v:int;

procedure main(a:int)
requires a == 0;
modifies v;
ensures v > a;
{
    assert true;
}
