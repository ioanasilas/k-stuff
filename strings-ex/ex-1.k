module EX-1
    imports STRING
    imports INT
    imports BOOL

    syntax Int ::= findFirstSpace(String) [function]
                | findDot(String) [function]

    syntax String ::= reducebySentence(String) [function]
                    | copyAllFirstWords(String) [function]
                    | copyFirstWord(String) [function]
                    | copyWords(String) [function]

    syntax Bool ::= flagFunc(String) [function]



    // flag
    rule flagFunc(S) => lengthString(S) >Int 0

    rule copyAllFirstWords(S) => copyWords(S)

    rule copyWords(S) => copyFirstWord(S) +String " " +String copyWords(reducebySentence(S)) requires flagFunc(S)
    rule copyWords(_S) => "" [owise]

    //prim spatiu
    rule copyFirstWord(S) => substrString(S, 0, findFirstSpace(S)) requires findFirstSpace(S) =/=Int -1
    rule copyFirstWord(_S) => "Sucks to be you." [owise]
    rule findFirstSpace(S) => findChar(S, " ", 0)

    // first dot
    rule findDot(S) => findChar(S, ".", 0)

    //take one sentence out one at a time
    rule reducebySentence(S) => substrString(S, findDot(S) +Int 1, lengthString(S))
    
endmodule