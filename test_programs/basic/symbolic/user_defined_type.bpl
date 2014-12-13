// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 1 %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck %s
type fox;
function f(x:fox) returns(r:bool);
procedure main()
{
    var y:fox;
    assert f(y);
}
// CHECK-L: TerminatedWithoutError=1
// CHECK-L: TerminatedAtFailingAssert=1
