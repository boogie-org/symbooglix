// RUN: %rmdir %t.symbooglix-out
// RUN: %not %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck %s
// CHECK-L: Detected the following recursive functions
// CHECK-NEXT-L: foo
// CHECK-NEXT-L: bar

function foo(x:int) returns(bool)
{
    if x > 0 then true else bar(x-1)
}

function {:inline true} bar(x:int) returns(bool)
{
   if x ==0 then true else foo(x-1)
}

procedure main(x:int)
{
    assert bar(x);
}
