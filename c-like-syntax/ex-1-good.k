module EX-2-SYNTAX
imports BOOL-SYNTAX
imports INT-SYNTAX

    syntax ValBool ::= Bool | ExpBool
    syntax ValInt ::= Int | ExpInt

    syntax ExpInt ::= "(" ExpInt ")" [bracket]
                > left: ValInt "*" ValInt [seqstrict]
                | ValInt ":" ValInt [seqstrict]
                > left: ValInt "+" ValInt [seqstrict]
                | ValInt "-" ValInt [seqstrict]

    syntax ExpBool ::= "(" ExpBool ")" [bracket]
                > left: "!" ValBool [seqstrict]
                | ValBool "^" ValBool [seqstrict]
                | ValBool "||" ValBool [seqstrict]
                | ValBool "&&" ValBool [seqstrict]
                > left: ValInt "<" ValInt [seqstrict]
                | ValInt "<=" ValInt [seqstrict]
                | ValInt ">" ValInt [seqstrict]
                | ValInt ">=" ValInt [seqstrict]
                | ValInt "==" ValInt [seqstrict]
                | ValInt "!=" ValInt [seqstrict]

endmodule

module EX-1-SYNTAX
  imports EX-2-SYNTAX
  imports ID-SYNTAX

  syntax Exp ::= Id "(" ")" | ValInt | ValBool
  syntax Decl ::= "int" Id "=" ValInt ";" [strict(2)]
                | "bool" Id "=" ValBool ";" [strict(2)]
                | "fun" Id "(" ")" "{" Stmt "}"
               //  | Stmt

//   syntax Declss ::= List{Decl, ""}
//   syntax Stmts ::= List{Stmt, ""}

  syntax Stmt ::= "return" Exp ";" [strict]  | Id "=" ValInt ";" [strict(2)]
                | Id "=" ValBool ";" [strict(2)]
                | "if" "(" Bool ")" Exp "else" Exp ";" [strict(1)] // do we need this?
               //  | "return" Id ";"
               //  | Declss 

  syntax Pgm ::= List{Decl, ""}

  syntax Id ::= "main" [token]

endmodule


module EX-1-GOOD
  imports EX-1-SYNTAX
  imports INT
  imports BOOL
  imports LIST
  imports ID
  imports K-EQUAL

  configuration <T>
                  <k> $PGM:Pgm ~> main()</k>
                  <variables> .Map </variables>
                  <functions> .Map </functions>
                  <stack> .List </stack>
                </T>
  // decl seq
  rule <k> D:Decl P:Pgm => D ~> P ...</k>
  rule <k> .Pgm => . ...</k>

  // variable def
  rule <k> int X:Id = V:ValInt ; => . ...</k>
       <variables> VARIABLES => VARIABLES [ X <- V ] </variables>

  // variable def
  rule <k> bool B:Id = V:ValBool ; => . ...</k>
       <variables> VARIABLES => VARIABLES [ B <- V ] </variables>

  // function def
  rule <k> fun F:Id ( ) { S:Stmt } => . ... </k>
  <functions> FUNCTIONS => FUNCTIONS [ F <- S ] </functions>
 
  // variable lookup
  rule <k> X:Id => V:ValInt ...</k>
       <variables>... X |-> V ...</variables>

  // variable lookup
  rule <k> B:Id => V:ValBool ...</k>
       <variables>... B |-> V ...</variables>

  // variable update
  rule <k> X:Id = V:ValInt ; => . ...</k>
       <variables> VARIABLES => VARIABLES [X <- V] </variables>

  // variable update
  rule <k> B:Id = V:ValBool ; => . ...</k>
       <variables> VARIABLES => VARIABLES [B <- V] </variables>

  // function call
  syntax KItem ::= stackFrame(K)
  rule <k> F:Id () ~> K => S </k>
  <functions>... F |-> S ...</functions>
  <stack> .List => ListItem(stackFrame(K)) ...</stack>

  // return
  rule <k> return E:Exp ; ~> _ => E ~> K </k>
       <stack> ListItem(stackFrame(K)) => .List ...</stack>
       
  // if stmt
  rule <k> if (B:Bool) E1:Exp else E2:Exp ; => #if B #then E1 #else E2 #fi </k>
//   rule <stack> ListItem(stackFrame(K)) => .List ...</stack>


  // Rules for Exp operations
  rule <k> I1:Int + I2:Int => I1 +Int I2 ...</k>
  rule <k> I1:Int - I2:Int => I1 -Int I2 ...</k>
  rule <k> I1:Int * I2:Int => I1 *Int I2 ...</k>
  rule <k> I1:Int : I2:Int => I1 /Int I2 ...</k> requires I2 =/=Int 0
  rule <k> B1:Bool && B2:Bool => B1 andBool B2 ...</k>
  rule <k> B1:Bool || B2:Bool => B1 orBool B2 ...</k>
  rule <k> B1:Bool ^ B2:Bool => B1 xorBool B2 ...</k>
  rule <k> ! B:Bool => notBool(B) ...</k>

  // Rules for Integer Comparisons
  rule <k> I1:Int < I2:Int => I1 <Int I2 ...</k>
  rule <k> I1:Int <= I2:Int => I1 <=Int I2 ...</k>
  rule <k> I1:Int > I2:Int => I1 >Int I2 ...</k>
  rule <k> I1:Int >= I2:Int => I1 >=Int I2 ...</k>
  rule <k> I1:Int == I2:Int => I1 ==Int I2 ...</k>
  rule <k> I1:Int != I2:Int => I1 =/=Int I2 ...</k>

  // isKResult function
  syntax Bool ::= isKResult(K) [function, symbol(isKResult)]
  rule isKResult(_:Int) => true
  rule isKResult(_:Bool) => true
  rule isKResult(_) => false [owise]
endmodule