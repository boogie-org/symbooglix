// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck -d %s
// CHECK-L: Added uninterpreted function foo
function foo(a:bv32) returns (bv32);
// CHECK-L: Added uninterpreted function bar
function bar(a:bv32) returns (bv32);

procedure main(p1:bv32) returns (r:bool)
{
    assert foo(p1) == foo(p1);
    assert bar(p1) == bar(p1);
    assert foo(p1) != bar(p1);
}
