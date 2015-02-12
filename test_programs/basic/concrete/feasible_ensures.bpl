// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
var g:bv8;

procedure main()
requires g == 0bv8;
modifies g;
ensures g == 2bv8;
{
    g := 2bv8;
}
