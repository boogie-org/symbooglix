// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out --goto-assume-look-ahead=1 %s 2>&1 | %OutputCheck %s
procedure {:inline 1} next(x : int) returns (y : int) {

  if((x mod 2) == 0) {
    y := x div 2;
  } else {
    y := 3*x + 1;
  }

}

procedure main(x : int)
requires (x > 0);
requires (x < 3);
{

  var i : int;
  var current : int;

  i := 0;
  current := x;

  while(i < 20) {
    call current := next(current);
    i := i + 1;
  }

  assert(current == 1 || current == 2 || current == 4);

}

// CHECK-L: State 0: Terminated without error
// CHECK-L: State 1: Terminated without error

