module EX-2-SYNTAX
imports BOOL-SYNTAX
imports INT-SYNTAX
imports ID-SYNTAX

    syntax ValBool ::= Bool | ExpBool | Id
    syntax ValInt ::= Int | ExpInt | Id

    syntax ExpInt ::= "(" ExpInt ")" [bracket]
                > left: ValInt "*" ValInt
                | ValInt "/" ValInt
                > left: ValInt "+" ValInt
                | ValInt "-" ValInt

    syntax ExpBool ::= "(" ExpBool ")" [bracket]
                > left: "!" ValBool
                | ValBool "^" ValBool
                | ValBool "||" ValBool
                | ValBool "&&" ValBool
                > left: ValInt "<" ValInt
                | ValInt "<=" ValInt
                | ValInt ">" ValInt
                | ValInt ">=" ValInt
                | ValInt "==" ValInt
                | ValInt "!=" ValInt

endmodule

module MODIFIED-EX-1-LESSON-16-SYNTAX
  imports EX-2-SYNTAX

  syntax Exp ::= Id "(" ")" | ValInt | ValBool | Id | ExpInt | ExpBool

  syntax Stmt ::= "int" Id "=" ValInt ";" [strict(2)]
                | "bool" Id "=" ValBool ";" [strict(2)]
                | "fun" Id "(" ")" "{" Stmt "}"
                | "return" Exp ";"[strict(1)] 
                | Id "=" Exp ";" [strict(2)]
                | Stmt Stmt [right]
                | "if" "(" ValBool ")" Block "else" Block [strict(1)]

  syntax Block ::= "{" Stmt "}" | "{" "}"

  syntax Pgm ::= Stmt

  syntax Id ::= "main" [token]

endmodule


module MODIFIED-EX-1-LESSON-16
  imports MODIFIED-EX-1-LESSON-16-SYNTAX
  imports INT
  imports BOOL
  imports LIST
  imports ID
  imports K-EQUAL

  configuration <T>
                  <k> $PGM:Stmt ~> main()</k>
                  <variables> .Map </variables>
                  <functions> .Map </functions>
                  <stack> .List </stack>
                </T>
  // decl seq
  rule <k> S:Stmt SS:Stmt => S ~> SS ...</k>
//   rule <k> .Stmt => . ...</k>

  // variable def
  rule <k> int X:Id = V:ValInt ; => .K ...</k>
       <variables> VARIABLES => VARIABLES [ X <- V ] </variables>

  // variable def
  rule <k> bool B:Id = V:ValBool ; => .K ...</k>
       <variables> VARIABLES => VARIABLES [ B <- V ] </variables>

  // function def
  rule <k> fun F:Id ( ) { S:Stmt } => .K ... </k>
       <functions> FUNCTIONS => FUNCTIONS [ F <- S ] </functions>

  // if stmt
  rule <k> if (B:ValBool) B1:Block else B2:Block => #if B #then B1 #else B2 #fi ... </k>
 
  // variable lookup
  rule <k> X:Id => V:ValInt ...</k>
       <variables>... X |-> V ...</variables>

  // variable lookup
  rule <k> B:Id => V:ValBool ...</k>
       <variables>... B |-> V ...</variables>

  // variable update
  rule <k> X:Id = V:ValInt ; => .K ...</k>
       <variables> VARIABLES => VARIABLES [X <- V] </variables>

  // variable update
  rule <k> B:Id = V:ValBool ; => .K ...</k>
       <variables> VARIABLES => VARIABLES [B <- V] </variables>

  // function call
  syntax KItem ::= stackFrame(K)
  rule <k> F:Id () ~> K => S </k>
  <functions>... F |-> S ...</functions>
  <stack> .List => ListItem(stackFrame(K)) ...</stack>
  
  // vs
  rule <k> return E:Exp ; ~> _ => E ~> K </k>
       <stack> ListItem(stackFrame(K)) => .List ...</stack>

  // blocks of stmt
  rule <k> { S:Stmt } => S ... </k>

  rule <k> { } => .K ... </k>

  // Rules for Exp operations
  rule <k> I1:Int + I2:Int => I1 +Int I2 ...</k> [anywhere]
  rule <k> I1:Int - I2:Int => I1 -Int I2 ...</k> [anywhere]
  rule <k> I1:Int * I2:Int => I1 *Int I2 ...</k> [anywhere]
  rule <k> I1:Int / I2:Int => I1 /Int I2 ...</k> requires I2 =/=Int 0 [anywhere]
  rule <k> B1:Bool && B2:Bool => B1 andBool B2 ...</k> [anywhere]
  rule <k> B1:Bool || B2:Bool => B1 orBool B2 ...</k> [anywhere]
  rule <k> B1:Bool ^ B2:Bool => B1 xorBool B2 ...</k> [anywhere]
  rule <k> ! B:Bool => notBool(B) ...</k> [anywhere]

  // Rules for Integer Comparisons
  rule <k> I1:Int < I2:Int => I1 <Int I2 ...</k> [anywhere]
  rule <k> I1:Int <= I2:Int => I1 <=Int I2 ...</k> [anywhere]
  rule <k> I1:Int > I2:Int => I1 >Int I2 ...</k> [anywhere]
  rule <k> I1:Int >= I2:Int => I1 >=Int I2 ...</k> [anywhere]
  rule <k> I1:Int == I2:Int => I1 ==Int I2 ...</k> [anywhere]
  rule <k> I1:Int != I2:Int => I1 =/=Int I2 ...</k> [anywhere]

  // isKResult function
  syntax Bool ::= isKResult(K) [function, symbol(isKResult)]
  rule isKResult(_:Int) => true
  rule isKResult(_:Bool) => true
  rule isKResult(_) => false [owise]
endmodule