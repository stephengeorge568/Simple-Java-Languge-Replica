(* =========================================================================================================== *)
exception model_error;
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

fun typeOf( itree(inode("expression",_), [ disjunction ] ), m) = typeOf(disjunction, m)

    | typeOf( itree(inode("disjunction",_),
                    [
                        disjunction,
                        itree(inode("or",_), [] ),
                        conjunction
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(disjunction,m)
                val t2 = typeOf(conjunction,m)
            in
                if t1 = t2 andalso t1 = BOOL then BOOL
                else ERROR
            end
    |   typeOf( itree(inode("disjunction",_), [ conjunction ] ), m) = typeOf(conjunction, m)
    |   typeOf( itree(inode("conjunction",_),
                    [
                        conjunction,
                        itree(inode("and",_), [] ),
                        equality
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(conjunction,m)
                val t2 = typeOf(equality,m)
            in
                if t1 = t2 andalso t1 = BOOL then BOOL
                else ERROR
            end
    |   typeOf( itree(inode("conjunction",_), [ equality ] ), m) = typeOf(equality, m)
    |   typeOf( itree(inode("equality",_),
                    [
                        equality,
                        itree(inode("==",_), [] ),
                        relational
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(equality,m)
                val t2 = typeOf(relational,m)
            in
                if t1 = t2  then BOOL
            
                else ERROR
            end
    |   typeOf( itree(inode("equality",_),
                    [
                        equality,
                        itree(inode("!=",_), [] ),
                        relational
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(equality,m)
                val t2 = typeOf(relational,m)
            in
                if t1 = t2 then BOOL
                else ERROR
            end
    |   typeOf( itree(inode("equality",_), [ relational ] ), m) = typeOf(relational, m)
    |   typeOf( itree(inode("relational",_),
                    [
                        relational,
                        itree(inode(">",_), [] ),
                        add_sub
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(relational,m)
                val t2 = typeOf(add_sub,m)
            in
                if t1 = t2 andalso t1 = INT then BOOL
                else ERROR
            end
    |   typeOf( itree(inode("relational",_),
                    [
                        relational,
                        itree(inode("<",_), [] ),
                        add_sub
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(relational,m)
                val t2 = typeOf( add_sub,m)
            in
                if t1 = t2 andalso t1 = INT then BOOL
                else ERROR
            end
     |   typeOf( itree(inode("relational",_),
                    [
                        relational,
                        itree(inode("<=",_), [] ),
                        add_sub
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(relational,m)
                val t2 = typeOf( add_sub,m)
            in
                if t1 = t2 andalso t1 = INT then BOOL
                else ERROR
            end
    |   typeOf( itree(inode("relational",_),
                    [
                        relational,
                        itree(inode(">=",_), [] ),
                        add_sub
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(relational,m)
                val t2 = typeOf( add_sub,m)
            in
                if t1 = t2 andalso t1 = INT then BOOL
                else ERROR
            end            
    |   typeOf( itree(inode("relational",_), [ add_sub ] ), m) = typeOf( add_sub, m)
    |   typeOf( itree(inode("add_sub",_),
                    [
                        add_sub,
                        itree(inode("+",_), [] ),
                        mult_div_mod
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(add_sub,m)
                val t2 = typeOf(mult_div_mod,m)
            in
                if t1 = t2 andalso t1 = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("add_sub",_),
                    [
                        add_sub,
                        itree(inode("-",_), [] ),
                        mult_div_mod
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(add_sub,m)
                val t2 = typeOf(mult_div_mod,m)
            in
                if t1 = t2 andalso t1 = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("add_sub",_), [ mult_div_mod ] ), m) = typeOf(mult_div_mod, m)
    |   typeOf( itree(inode("mult_div_mod",_),
                    [
                        mult_div_mod,
                        itree(inode("*",_), [] ),
                        unary_minus
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(mult_div_mod,m)
                val t2 = typeOf(unary_minus,m)
            in
                if t1 = t2 andalso t1 = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("mult_div_mod",_),
                    [
                        mult_div_mod,
                        itree(inode("/",_), [] ),
                        unary_minus
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(mult_div_mod,m)
                val t2 = typeOf(unary_minus,m)
            in
                if t1 = t2 andalso t1 = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("mult_div_mod",_),
                    [
                        mult_div_mod,
                        itree(inode("%",_), [] ),
                        unary_minus
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(mult_div_mod,m)
                val t2 = typeOf(unary_minus,m)
            in
                if t1 = t2 andalso t1 = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("mult_div_mod",_), [ unary_minus ] ), m) = typeOf(unary_minus, m)
    |   typeOf( itree(inode("unary_minus",_),
                    [
                        itree(inode("-",_), [] ),
                        unary_minus
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(unary_minus,m)
            in
                if t1 = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("unary_minus",_), [ exponent ] ), m) = typeOf(exponent, m)
    |   typeOf( itree(inode("exponent",_),
                    [
                        negation,
                        itree(inode("^",_), [] ),
                        exponent
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(negation,m)
                val t2 = typeOf(exponent,m)
            in
                if t1 = t2 andalso t1 = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("exponent",_), [ negation ] ), m) = typeOf(negation, m)
    |   typeOf( itree(inode("negation",_),
                    [
                        itree(inode("!",_), [] ),
                        negation
                    ]
                ),
            m
        ) = typeOf(negation,m)
    |   typeOf( itree(inode("negation",_),[primary_expr]),m) = typeOf(primary_expr, m)   
    |   typeOf( itree(inode("primary_expr",_),
                    [
                        itree(inode("(",_), [] ),
                        expression,
                        itree(inode(")",_), [] )
                    ]
                ),
            m
        ) = typeOf(expression,m)
    |   typeOf( itree(inode("primary_expr",_),
                    [
                        itree(inode("|",_), [] ),
                        expression,
                        itree(inode("|",_), [] )
                    ]
                ),
            m
        ) = let
                val t1 = typeOf(expression,m)
            in
                if t1 = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("primary_expr",_),
                    [
                        value
                    ]
                ),
            m
        ) = typeOf(value,m)     
    |   typeOf( itree(inode("value",_),
                    [
                        itree(inode("true",_),[])
                    ]
                ),
            m
        ) = BOOL
    |   typeOf( itree(inode("value",_),
                    [
                        itree(inode("false",_),[])
                    ]
                ),
            m
        ) = BOOL        
    |   typeOf( itree(inode("value",_),
                    [
                        integer
                    ]
                ),
            m
        ) = INT
    |   typeOf( itree(inode("variable_id",_),
                    [
                        variable_id
                    ]
                ),
            m
        ) = getType(accessEnv(getLeaf(variable_id),m))
    |   typeOf( itree(inode("pre_post_statement",_),
                    [
                        itree(inode("++",_), [] ),
                        variable_id
                    ]
                ),
            m
        ) = let
                val t = getType(accessEnv(getLeaf(variable_id),m))
            in
                if t = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("pre_post_statement",_),
                    [
                        itree(inode("--",_), [] ),
                        variable_id
                    ]
                ),
            m
        ) = let
                val t = getType(accessEnv(getLeaf(variable_id),m))
            in
                if t = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("pre_post_statement",_),
                    [
                        variableId,
                        itree(inode("++",_), [] )
                        
                    ]
                ),
            m
        ) = let
                val t = getType(accessEnv(getLeaf(variableId),m))
            in
                if t = INT then INT
                else ERROR
            end
    |   typeOf( itree(inode("pre_post_statement",_),
                    [
                        variable_id,
                        itree(inode("--",_), [] )
                    ]
                ),
            m
        ) = let
                val t = getType(accessEnv(getLeaf(variable_id),m))
            in
                if t = INT then INT
                else ERROR
            end
    | typeOf( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")

    | typeOf _ = raise Fail("Error in Model.typeOf - this should never occur")

fun typeCheck( itree(inode("program",_), [ statement_list] ), m) = typeCheck(statement_list,m)

    |   typeCheck(itree(inode("statement_list",_),
                        [
                            statement1,
                            statement_list
                        ]
                    ),
                m0
            )= let
                    val m1 = typeCheck(statement1,m0)
                    val m2 = typeCheck(statement_list,m1)
                in
                    m2
                end
    |   typeCheck(itree(inode("statement_list",_),
                        [
                            itree(inode("epsilon",_), _ )
                        ]
                    ),
                m
            ) = m
    |   typeCheck(itree(inode("statement",_),
                        [
                            statement
                        ]
                    ),
                m0
            ) = typeCheck(statement,m0)
    |   typeCheck(itree(inode("statement",_),
                        [
                            statement,
                            itree(inode(";",_), [] )
                        ]
                    ),
                m0
            ) = typeCheck(statement,m0)
    |   typeCheck(itree(inode("declaration_statement",_),
                        [
                            declaration
                        ]
                    ),
                m0
            ) = let
                    val m1 = typeCheck(declaration,m0)
                in
                    m1
                end
                
    |   typeCheck(itree(inode("int_declaration",_),
                        [
                            itree(inode("int",_), [] ),
                            variableId
                        ]
                    ),
                m
            ) = let
                    val id = getLeaf(variableId)
                    val (_,counter,_) = m
                in
                    updateEnv(id,INT,counter,m)
                end
    |   typeCheck(itree(inode("bool_declaration",_),
                        [
                            itree(inode("bool",_), [] ),
                            variableId
                        ]
                    ),
                m
            ) = let
                    val id = getLeaf(variableId)
                    val (_,counter,_) = m
                in
                    updateEnv(id,BOOL,counter,m)
                end      
    |   typeCheck(itree(inode("assignment_statement",_),
                        [
                            variableId,
                            itree(inode("=",_), [] ),
                            expr
                        ]
                    ),
                m
            ) = let
                    val id = getLeaf(variableId)
                    val type1 = typeOf(expr,m)
                    val type2 = getType(accessEnv(id,m))
                in
                    if type1 = type2 andalso type1 <> ERROR then m
                    else raise model_error 
                end
    |   typeCheck(itree(inode("condition_statement",_),
                        [
                           conditional
                        ]
                    ),
                m
            ) = typeCheck(conditional,m)
    |   typeCheck(itree(inode("if_then",_),
                        [
                            itree(inode("if",_), [] ),
                            itree(inode("(",_), [] ),
                            expr,
                            itree(inode(")",_), [] ),
                         
                            block1
                        ]
                    ),
                m
            ) = let
                    val t1 = typeOf(expr,m)
                    val m1 = typeCheck(block1,m)
                in
                    if t1 = BOOL then m
                    else raise model_error
               end
    |   typeCheck(itree(inode("if_then_else",_),
                        [
                            itree(inode("if",_), [] ),
                            itree(inode("(",_), [] ),
                            expr,
                            itree(inode(")",_), [] ),
                            block1,
                            itree(inode("else",_), [] ),
                            block2
                        ]
                    ),
                m
            ) = let
                    val t1 = typeOf(expr,m)
                    val m1 = typeCheck(block1,m)
                    val m2 = typeCheck(block2,m)
                in
                    if t1 = BOOL then m
                    else raise model_error
               end
    |   typeCheck(itree(inode("iterative_statement",_),
                        [
                           iterative
                        ]
                    ),
                m
            ) = typeCheck(iterative,m)
    |   typeCheck(itree(inode("while_loop",_),
                        [
                            itree(inode("while",_), [] ),
                            itree(inode("(",_), [] ),
                            expr,
                            itree(inode(")",_), [] ),
                            block1   
                        ]
                    ),
                m
            ) = let
                    val t1 = typeOf(expr,m)
                    val m1 = typeCheck(block1,m)
                in
                    if t1 = BOOL then m
                    else raise model_error
                end
    |   typeCheck(itree(inode("for_loop",_),
                        [
                            itree(inode("for",_), [] ),
                            itree(inode("(",_), [] ),
                            assignment_Statement,
                            itree(inode(";",_), [] ),
                            expr,
                            itree(inode(";",_), [] ),
                            prePostStatement,
                            itree(inode(")",_), [] ),
                            block1   
                        ]
                    ),
                m0
            ) = let
                    val m1 = typeCheck(assignment_Statement,m0)
                    val t1 = typeOf(expr,m1)
                    val m2 = typeCheck(prePostStatement,m1)
                    val m3 = typeCheck(block1,m2)
                   
                in
                    if t1 = BOOL then m3
                    else raise model_error
                end
    |   typeCheck(itree(inode("block_statement",_),
                        [
                            itree(inode("{",_), [] ),
                            statement_list,
                            itree(inode("}",_), [] )
                        ]
                    ),
                m
            ) = typeCheck(statement_list,m)
    |   typeCheck(itree(inode("print_statement",_),
                        [
                            itree(inode("print",_), [] ),
                            itree(inode("(",_), [] ),
                            expr,
                            itree(inode(")",_), [] )
                        ]
                    ),
                m
            ) = let
                    val t1 = typeOf(expr,m)
                in
                    if t1 = ERROR then raise model_error
                    else m
                end
   |   typeCheck(itree(inode("pre_post_statement",_),
                        [
                            variableId,
                            itree(inode("++",_), [] )
                        ]
                    ),
                m
            ) = let
                    val t = getType(accessEnv(getLeaf(variableId),m))
                in
                    if t = INT then m
                    else raise model_error
                end
    |   typeCheck(itree(inode("pre_post_statement",_),
                        [
                            variableId,
                            itree(inode("--",_), [] )
                        ]
                    ),
                m
            ) = let
                    val t = getType(accessEnv(getLeaf(variableId),m))
                in
                    if t = INT then m
                    else raise model_error
                end
    |   typeCheck(itree(inode("pre_post_statement",_),
                        [
                            itree(inode("++",_), [] ),
                            variableId
                          
                        ]
                    ),
                m
            ) = let
                    val t = getType(accessEnv(getLeaf(variableId),m))
                in
                    if t = INT then m
                    else raise model_error
                end
   |   typeCheck(itree(inode("pre_post_statement",_),
                        [
                            itree(inode("--",_), [] ),
                            variableId
                          
                        ]
                    ),
                m
            ) = let
                    val t = getType(accessEnv(getLeaf(variableId),m))
                in
                    if t = INT then m
                    else raise model_error
                end              
    |   typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
    |   typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")

(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)

















