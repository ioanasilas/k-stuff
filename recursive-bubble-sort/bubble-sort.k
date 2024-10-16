module BUBBLE-SORT
  imports INT
  imports BOOL

  syntax InputTypes ::= Ints | Bool
  
  configuration <k> $PGM:InputTypes </k>

  syntax Ints ::= List{Int, ","}

  syntax Ints ::= bSort(Ints) [function]

  syntax Bool ::= compare(Int, Int) [function]

  syntax Ints ::= bSortWrapper(Ints, Int) [function]

  syntax Int ::= len(Ints) [function]

  syntax Ints ::= bubble(Ints) [function]

  // compute length
  rule len(.Ints) => 0
  rule len(_:Int, Ints) => 1 +Int len(Ints)

  // base cases
  rule bSort(I1:Int, .Ints) => I1
  rule bSortWrapper(Is:Ints, 0) => Is
  
  // call with this
  rule bubble(Is:Ints) => bSortWrapper(Is, len(Is))

  rule bSortWrapper(Is:Ints, N:Int) => bSortWrapper(bSort(Is), N -Int 1) requires N >=Int 1

  // recursive cases
  rule bSort(I1:Int, I2:Int, Is:Ints) => I1, bSort(I2, Is) [owise]
  rule bSort(I1:Int, I2:Int, Is:Ints) => I2, bSort(I1, Is) requires compare(I1, I2)

  rule compare(I1:Int, I2:Int) => I1 >=Int I2

    // function to check if a list is sorted
  syntax Bool ::= isSorted(Ints) [function]

  rule isSorted(I1:Int, I2:Int, Is:Ints) => I1 <=Int I2 andBool isSorted(I2, Is) [owise]
  rule isSorted(_:Int) => true
  rule isSorted(.Ints) => true


endmodule