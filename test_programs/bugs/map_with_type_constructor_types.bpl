// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// ######################################
// #        HEAP & LOCAL VARIABLES      #
// ######################################
type Ref;

type Bool;

type BoolHeap = [Ref][Bool]bool;

var boolHeap : BoolHeap;

// ######################################
// #              METHODS               #
// ######################################

var array : [int] Bool;

const array$size : int;
axiom array$size == 5;

procedure main(this : Ref) returns ()
{
 var pos   : int;
 var field : Bool;
 var value : bool;

 pos   := 0;
 field := array[pos];
 value := boolHeap[this][field];
 if (value) {

 }
}
