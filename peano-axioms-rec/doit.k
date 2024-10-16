module DOIT
  imports INT
  imports BOOL

  syntax Nat ::= "O" | S(Nat)

  syntax Nat ::= Nat "+" Nat [function]

  rule X:Nat + O => X
  rule X:Nat + S(Y:Nat) => S(X + Y) 

  syntax Nat ::= Int "+" Int
  syntax Nat ::= transform(Int)

  rule transform(I:Int) => S(transform(I -Int 1)) requires I >Int 0 [anywhere]
  rule transform(0) => O [anywhere]

  rule I:Int + I2:Int => transform(I) + transform(I2)
  

endmodule
