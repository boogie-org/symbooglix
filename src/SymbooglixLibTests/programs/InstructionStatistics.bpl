const g:bool;
axiom g == true;

procedure main();
requires g == true; // Prevent GDDE from removing axiom

implementation main()
{
  var x: int;
  var counter: int;


  anon0:
    assume x > 0;
    counter := 0;
    goto anon2_LoopHead;

  anon2_LoopHead:
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
    assume {:partition} counter < 3;
    counter := counter + 1;
    call x := foo(x);
    goto anon2_LoopHead;

  anon2_LoopDone:
    assume {:partition} counter >=3;
    return;
}


procedure foo(x: int) returns (r: int);
  requires x > 0;
  ensures r > x;


implementation foo(x: int) returns (r: int)
{

  anon0:
    r := x + 1;
    return;
}


