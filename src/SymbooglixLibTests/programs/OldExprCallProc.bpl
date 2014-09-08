var g:int;

procedure main()
modifies g;
ensures g > old(g + 1);
{
    call foo();
}

// FIXME: Boogie verifies this as correct. Why!?
procedure foo() returns ();
// deliberatly have modifies g missing, so ensures can't be satisfied (old(g) == g)
ensures g > old(g + old(2));
