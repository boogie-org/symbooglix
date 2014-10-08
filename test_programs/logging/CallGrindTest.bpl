// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %OutputCheck --file-to-check %t.symbooglix-out/instr_stats.callgrind %s

// CHECK-L: events: Covered Terminations Forks
// CHECK-L: fl=program.bpl

// CHECK-L: # Start Axioms
// CHECK-NEXT-L: fn=main
// CHECK-L: 1 1 0 0
axiom true;

procedure main();


// CHECK-L: fn=main
implementation main()
{
  var x: int;
  var counter: int;

  anon0:
// CHECK-L: 12 1 0 0
    assume x > 0;

// CHECK-L: 13 1 0 0
    counter := 0;

// CHECK-L: jump=1 16
// CHECK-NEXT-L: 14
// CHECK-NEXT-L: 14 1 0 0
    goto anon2_LoopHead;

  anon2_LoopHead:
// CHECK-L: jcnd=1/4 26
// CHECK-NEXT-L: 17
// CHECK-NEXT-L: jcnd=3/4 19
// CHECK-NEXT-L: 17
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
// CHECK-L: 20 3 0 0
    assume {:partition} counter < 3;

// CHECK-NEXT-L: 21 3 0 0
    counter := counter + 1;

// CHECK-L: cfn=foo
// CHECK-NEXT-L: # Call into implementation
// CHECK-NEXT-L: calls=3 37
// CHECK-NEXT-L: 22 3 0 0
    call x := foo(x);

// CHECK-L: cfn=main
// CHECK-L: cfn=bar
// CHECK-NEXT-L: # Call into procedure
// CHECK-NEXT-L: calls=3 46
// CHECK-NEXT-L: 23 3 0 0
// CHECK-L: cfn=main
    call x := bar(x);

// CHECK-L: jump=3 16
// CHECK-L-NEXT: 24
// CHECK-L-NEXT: 24 3 0 0
    goto anon2_LoopHead;

  anon2_LoopDone:
// CHECK-L: 27 1 0 0
    assume {:partition} counter >=3;
// CHECK-L: 28 1 1 0
    return;
}


// CHECK-L: fn=foo
procedure foo(x: int) returns (r: int);
// CHECK-L: 33 3 0 0
  requires x > 0;
// CHECK-L: 34 3 0 0
  ensures r > x;


implementation foo(x: int) returns (r: int)
{

  anon0:
// CHECK-L: 41 3 0 0
    r := x + 1;
// CHECK-NEXT-L: 42 3 0 0
    return;
}

// CHECK-L: fn=bar
procedure bar(x: int) returns (r: int);
// CHECK-L: 47 3 0 0
  requires x > 0;
// CHECK-L: 48 3 0 0
  ensures r > x;

