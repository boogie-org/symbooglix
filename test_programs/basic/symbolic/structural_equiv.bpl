// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out --fold-constants=1 %s 2>&1 | %OutputCheck %s
procedure main(x:int, y:int)
{
    var a:int;
    var b:int;

    a := x + y;
    b := x + y;

    // CHECK-L: Mutating tree: '~sb_x_0 + ~sb_y_0 == ~sb_x_0 + ~sb_y_0' => 'true'
    // CHECK-L: Assert : true

    assert a == b;

}

