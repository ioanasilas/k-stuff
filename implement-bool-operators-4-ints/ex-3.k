module SYNTAXX
    imports INT-SYNTAX
    imports BOOL

    syntax Bool ::= Int "==" Int [function]
                | Int "<" Int [function]
                | Int "<=" Int [function]
                | Int ">" Int [function]
                | Int ">=" Int [function]
                | isZero(Int) [function]
                | isPositive(Int) [function]
                | isPositiveWrapper(Int, Int) [function]
endmodule

module EX-3
    imports SYNTAXX
    imports INT

    rule isZero(0) => true
    //everything non zero is false
    rule isZero(_) => false [owise]


    rule isPositive(0) => false
    rule isPositive(N) => isPositiveWrapper(N, N) [owise]
    
    rule isPositiveWrapper(0, _) => false
    rule isPositiveWrapper(_, 0) => true

    rule isPositiveWrapper(N, M) => isPositiveWrapper(N +Int 1, M -Int 1) [owise]

    rule A == B => true requires isZero(A -Int B)
    rule _ == _ => false [owise]

    rule A > B => true requires isPositive(A -Int B)
    rule _ > _ => false [owise]

    rule A < B => notBool (A >= B)
    
    rule A >= B => (A > B) orBool (A == B)

    rule A <= B => notBool (A > B)
    
endmodule