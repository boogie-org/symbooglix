// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %OutputCheck --file-to-check %t.symbooglix-out/instr_stats.callgrind %s

// CHECK-L: events: Covered Terminations Forks
// CHECK-L: fl=program.bpl

// CHECK-L: # Start Axioms
// CHECK-NEXT-L: fn=main
// CHECK-L: 2 1 0 0
const g:bool;
axiom g == true;
// CHECK-L: # End axioms

// CHECK-L: # Statistics for main
// CHECK-L: fn=main
procedure main();
// CHECK-L: Requires statements Start
// CHECK-L: 4 1 0 0
requires g == true; // Prevent GlobalDDE from removing axiom
// CHECK-L: Requires statements End


implementation main()
{
  var x: int;
  var counter: int;

  anon0:
// CHECK-L: 14 1 0 0
    assume x > 0;

// CHECK-L: 15 1 0 0
    counter := 0;

// CHECK-L: jump=1 18
// CHECK-NEXT-L: 16
// CHECK-NEXT-L: 16 1 0 0
    goto anon2_LoopHead;

  anon2_LoopHead:
// CHECK-L: jcnd=1/4 28
// CHECK-NEXT-L: 19
// CHECK-NEXT-L: jcnd=3/4 21
// CHECK-NEXT-L: 19
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
// CHECK-L: 22 3 0 0
    assume {:partition} counter < 3;

// CHECK-NEXT-L: 23 3 0 0
    counter := counter + 1;

// CHECK-L: cfn=foo
// CHECK-NEXT-L: # Call into implementation
// CHECK-NEXT-L: calls=3 39
// CHECK-NEXT-L: 24 3 0 0
    call x := foo(x);

// CHECK-L: cfn=main
// CHECK-L: cfn=bar
// CHECK-NEXT-L: # Call into procedure
// CHECK-NEXT-L: calls=3 48
// CHECK-NEXT-L: 25 3 0 0
// CHECK-L: cfn=main
    call x := bar(x);

// CHECK-L: jump=3 18
// CHECK-L-NEXT: 26
// CHECK-L-NEXT: 26 3 0 0
    goto anon2_LoopHead;

  anon2_LoopDone:
// CHECK-L: 29 1 0 0
    assume {:partition} counter >=3;
// CHECK-L: 30 1 1 0
    return;
}


// CHECK-L: fn=foo
procedure foo(x: int) returns (r: int);
// CHECK-L: 35 3 0 0
  requires x > 0;
// CHECK-L: 36 3 0 0
  ensures r > x;


implementation foo(x: int) returns (r: int)
{

  anon0:
// CHECK-L: 43 3 0 0
    r := x + 1;
// CHECK-NEXT-L: 44 3 0 0
    return;
}

// CHECK-L: fn=bar
procedure bar(x: int) returns (r: int);
// CHECK-L: 49 3 0 0
  requires x > 0;
// CHECK-L: 50 3 0 0
  ensures r > x;

