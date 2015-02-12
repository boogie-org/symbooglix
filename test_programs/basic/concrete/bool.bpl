// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
procedure main(p1:bool, p2:bool) returns (r:bool)
requires (p1 == true);
requires (p2 == false);
{
    r := (p1 || p2) && !(p1 && p2);
    assert r == true;
}
