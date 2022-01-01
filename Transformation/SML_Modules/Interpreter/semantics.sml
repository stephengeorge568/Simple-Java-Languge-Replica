
(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model;
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
    datatype INODE = inode of string * NODE_INFO
                     | ...  
                                                            
    datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System.
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4:
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *)
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *)
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)
fun exp(x,0) = 1
    | exp(x,n) = x * exp(x, n-1);


fun E(  itree(inode("expression",_),
            [
                disjunction
            ]
        ),m0
    ) = E(disjunction, m0)
    | E(  itree(inode("disjunction",_),
            [
                disjunction,
                itree(inode("or",_), [] ),
                conjunction
            ]
        ),m0
    ) = let
            val (v1,m1) = E(disjunction,m0)
        in
            if  toBool(v1) then (Boolean(toBool(v1)),m1)
            else
                let
                    val(v2,m2) = E(conjunction,m1)
                in
                    (Boolean(toBool(v2)),m2)
                end
        end
    | E(  itree(inode("disjunction",_),
                [
                    conjunction
                ]
             ),
        m0
    ) = E(conjunction, m0)

    | E(  itree(inode("conjunction",_),
            [
                conjunction,
                itree(inode("and",_), [] ),
                equality
            ]
        ),m0
    ) = let
            val (v1,m1) = E(conjunction,m0)
        in
            if  toBool(v1) then
                let
                    val (v2,m2) = E(equality,m1)
                in
                    (Boolean(toBool(v2)),m2)
                end
            else (Boolean(toBool(v1)),m1)        
        end
    | E(  itree(inode("conjunction",_),
                [
                    equality
                ]
             ),
        m0
    ) = E(equality, m0)
    | E(  itree(inode("equality",_),
                [
                    equality,
                    itree(inode("==",_), [] ),
                    relational
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(equality,m0)
                val (v2,m2) = E (relational,m1)
            in
                (Boolean(v1 <> v2), m2)
            end
    | E(  itree(inode("equality",_),
                [
                    equality,
                    itree(inode("!=",_), [] ),
                    relational
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(equality,m0)
                val (v2,m2) = E (relational,m1)
            in
                 (Boolean(v1 <> v2), m2)
            end            
    | E(  itree(inode("equality",_),
                [
                    relational
                ]
             ),
        m0
    ) = E(relational, m0)
    | E(  itree(inode("relational",_),
                [
                    add_sub1,
                    itree(inode("<",_), [] ),
                    add_sub2
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(add_sub1,m0)
                val (v2,m2) = E (add_sub2,m1)
            in
               (Boolean(toInt(v1) < toInt(v2)), m2)
            end
    | E(  itree(inode("relational",_),
                [
                    add_sub1,
                    itree(inode("<=",_), [] ),
                    add_sub2
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(add_sub1,m0)
                val (v2,m2) = E (add_sub2,m1)
            in
                 (Boolean(toInt(v1) <= toInt(v2)), m2)
            end              
    | E(  itree(inode("relational",_),
                [
                    add_sub1,
                    itree(inode(">",_), [] ),
                    add_sub2
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(add_sub1,m0)
                val (v2,m2) = E (add_sub2,m1)
            in
                 (Boolean(toInt(v1) > toInt(v2)), m2)
            end        
    | E(  itree(inode("relational",_),
                [
                    add_sub1,
                    itree(inode(">=",_), [] ),
                    add_sub2
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(add_sub1,m0)
                val (v2,m2) = E (add_sub2,m1)
            in
                 (Boolean(toInt(v1) >= toInt(v2)), m2)
            end       
    | E(  itree(inode("relational",_),
                [
                    add_sub
                ]
             ),
        m0
    ) = E(add_sub, m0)
    | E(  itree(inode("add_sub",_),
                [
                    add_sub,
                    itree(inode("-",_), [] ),
                    mult_div_mod
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(add_sub,m0)
                val (v2,m2) = E (mult_div_mod,m1)
            in
                (Integer(toInt(v1) - toInt(v2)), m2)
            end  
    | E(  itree(inode("add_sub",_),
                [
                    add_sub,
                    itree(inode("+",_), [] ),
                    mult_div_mod
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(add_sub,m0)
                val (v2,m2) = E (mult_div_mod,m1)
            in
                (Integer(toInt(v1) + toInt(v2)), m2)
            end       
    | E(  itree(inode("add_sub",_),
                [
                    mult_div_mod
                ]
             ),
        m0
    ) = E(mult_div_mod, m0)
    | E(  itree(inode("mult_div_mod",_),
                [
                    mult_div_mod,
                    itree(inode("*",_), [] ),
                    unary_minus
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(mult_div_mod,m0)
                val (v2,m2) = E (unary_minus,m1)
            in
               (Integer(toInt(v1) * toInt(v2)), m2)
            end             
    | E(  itree(inode("mult_div_mod",_),
                [
                    mult_div_mod,
                    itree(inode("/",_), [] ),
                    unary_minus
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(mult_div_mod,m0)
                val (v2,m2) = E (unary_minus,m1)
            in
              (Integer(toInt(v1) div toInt(v2)), m2)
            end                   
    | E(  itree(inode("mult_div_mod",_),
                [
                    mult_div_mod,
                    itree(inode("%",_), [] ),
                    unary_minus
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(mult_div_mod,m0)
                val (v2,m2) = E (unary_minus,m1)
            in
                (Integer(toInt(v1) mod toInt(v2)), m2)
            end    
    | E(  itree(inode("mult_div_mod",_),
                [
                   unary_minus
                ]
             ),
        m0
    ) = E(unary_minus, m0)    
    | E(  itree(inode("unary_minus",_),
                [
                    itree(inode("-",_), [] ),
                    unary_minus
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(unary_minus,m0)
            in
                (Integer(~(toInt(v1))),m1)
            end
    | E(  itree(inode("unary_minus",_),
                [
                   exponent
                ]
             ),
        m0
    ) = E(exponent, m0)    
    | E(  itree(inode("exponent",_),
                [
                    negation,
                    itree(inode("^",_), [] ),
                    exponent
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(exponent,m0)
                val (v2,m2) = E(negation,m1)
            in
                (Integer (exp(toInt(v2),toInt(v1))),m1)
            end
    | E(  itree(inode("exponent",_),
                [
                   negation
                ]
             ),
        m0
    ) = E(negation, m0)    
    | E(  itree(inode("negation",_),
                [
                    itree(inode("!",_), [] ),
                    negation
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(negation,m0)
               
            in
                (Boolean(not(toBool(v1))),m1)
            end            
    | E(  itree(inode("negation",_),
                [
                   primary_expr
                ]
             ),
        m0
    ) = E(primary_expr, m0)   
    | E(  itree(inode("primary_expr",_),
                [
                    itree(inode("(",_), [] ),
                    expr,
                    itree(inode(")",_), [] )
                ]
             ),
        m0
    ) = E(expr,m0)
    | E(  itree(inode("primary_expr",_),
                [
                    itree(inode("|",_), [] ),
                    expr,
                    itree(inode("|",_), [] )
                ]
             ),
        m0
    ) = let
                val (v1,m1) = E(expr,m0)
            in
                ( Integer(Int.abs(toInt(v1))),m1)
            end

    | E(  itree(inode("primary_expr",_),
                [
                   primary_expr
                ]
             ),
        m0
    ) = E( primary_expr,m0)
   | E(  itree(inode("value",_),
                [
                    itree(inode("true",_),[])
                ]
             ),
        m0
    ) =(Boolean true,m0)
    | E(  itree(inode("value",_),
                [
                    itree(inode("false",_),[])
                ]
             ),
        m0
    ) = (Boolean false,m0)
   | E( itree(inode("value",_),
                [
                    integer
                ]
            ),
        m
    ) = let
          
          val v = getLeaf(integer)
          val v_int = valOf(Int.fromString(v))
        in
          (Integer v_int, m)
        end
    | E(  itree(inode("variable_id",_),
                [
                   variable_id
                ]
             ),
        m0
    ) = let
                val id = getLeaf(variable_id)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
               
            in
                (v,m0)
            end  

    | E(  itree(inode("pre_post_statement",_),
                [
                    variable_id,
                    itree(inode("++",_), [] )
                ]
             ),
        m0
    ) = let
                val id = getLeaf(variable_id)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
                val rslt = Integer(toInt(v) + 1)
                val m1 = updateStore(loc, rslt, m0)
            in
                (rslt, m1)
            end
    | E(  itree(inode("pre_post_statement",_),
                [
                    variable_id,
                    itree(inode("--",_), [] )
                ]
             ),
        m0
    ) = let
                val id = getLeaf(variable_id)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
                val rslt = Integer(toInt(v) - 1)
                val m1 = updateStore(loc, rslt, m0)
            in
                (rslt, m1)
            end    
    | E(  itree(inode("pre_post_statement",_),
                [
                    itree(inode("++",_), [] ),
                    variable_id                   
                ]
             ),
        m0
    ) = let
                val id = getLeaf(variable_id)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
                val rslt = Integer(toInt(v) + 1)
                val m1 = updateStore(loc, rslt, m0)
            in
                (rslt, m1)
            end
    | E(  itree(inode("pre_post_statement",_),
                [
                    itree(inode("--",_), [] ),
                    variable_id
                ]
             ),
        m0
    ) = let
                val id = getLeaf(variable_id)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
                val rslt = Integer(toInt(v) - 1)
                val m1 = updateStore(loc, rslt, m0)
            in
                (rslt, m1)
            end               

 
  | E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
 
  | E _ = raise Fail("error in Semantics.E - this should never occur")                
        

fun M(  itree(inode("program",_),
            [
               statement_list
            ]
        ), m
    )   = M( statement_list, m )
    | M( itree(inode("statement_list", _),
            [
                statement,                                                                        
                statement_list                                       
            ]
            ),m
    )   =   let
                val m1 = M(statement,m)
                val m2 = M(statement_list,m1)
            in
                m2
            end
    | M( itree(inode("statement_list", _),[itree(inode("epsilon", _),  _)]),m) = m
    | M( itree(inode("statement",_),
            [
            statement
            ]
    ),
    m
    ) = M(statement,m)
    | M( itree(inode("statement",_),
            [
                statement,
                itree(inode(";",_), [] )
            ]
    ),
    m
    ) = M(statement,m)
   | M( itree(inode("pre_post_statement",_),
            [
                    variableId,
                    itree(inode("++",_), [] )
            ]
    ),
    m0
    ) = let
            val id = getLeaf(variableId)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
                val rslt = Integer(toInt(v) + 1)
                val m1 = updateStore(loc, rslt, m0)
        in
            m1
        end   
    | M( itree(inode("pre_post_statement",_),
            [
                    variableId,
                    itree(inode("--",_), [] )
            ]
    ),
    m0
    ) = let
            val id = getLeaf(variableId)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
                val rslt = Integer(toInt(v) - 1)
                val m1 = updateStore(loc, rslt, m0)
        in
            m1
        end  
    | M( itree(inode("pre_post_statement",_),
            [
                    itree(inode("++",_), [] ),
                    variableId
            ]
    ),
    m0
    ) = let
            val id = getLeaf(variableId)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
                val rslt = Integer(toInt(v) + 1)
                val m1 = updateStore(loc, rslt, m0)
        in
            m1
        end
  | M( itree(inode("pre_post_statement",_),
            [
                    itree(inode("--",_), [] ),
                    variableId
            ]
    ),
    m0
    ) = let
                val id = getLeaf(variableId)
                val loc = getLoc(accessEnv(id, m0))
                val v = accessStore(loc, m0)
                val rslt = Integer(toInt(v) - 1)
                val m1 = updateStore(loc, rslt, m0)
        in
            m1
        end                   
    | M( itree(inode("declaration_statement",_),
            [
            declaration_statement
            ]
    ),
    m
    ) = M(declaration_statement,m)
   | M( itree(inode("bool_declaration",_),
        [
                    itree(inode("bool",_), [] ),
                    variableID
        ]
        ),(env, counter, s)
    ) =    let
            val id = getLeaf(variableID)
        in
            updateEnv( id, BOOL,counter, (env, counter, s))
    end
    | M( itree(inode("int_declaration",_),
        [
                    itree(inode("int",_), [] ),
                    variableID
        ]
        ),(env, counter, s)
    ) =    let
            val id = getLeaf(variableID)
        in
            updateEnv( id, INT, counter, (env, counter, s))
    end
    | M( itree(inode("assignment_statement",_),
            [
                variableID,
                itree(inode("=",_), [] ),
            expression
            ]
    ),
    m0
    )= let
            val id = getLeaf(variableID)
            val (v1, m1) = E(expression, m0)

            val loc = getLoc(accessEnv(id, m1))            
            val m2 = updateStore(loc, v1, m1)
            
        in
            m2
        end
   | M( itree(inode("condition_statement",_),
            [
            condition_statement
            ]
    ),
    m
    ) = M(condition_statement,m)        
    | M( itree(inode("if_then",_),
            [
            itree(inode("if",_), [] ),
                itree(inode("(",_), [] ),
                expr,
                itree(inode(")",_), [] ),
                block
            ]
    ),
    m0
    ) = let
            val (v,m1) = E(expr,m0)
        in
            if toBool(v) then M(block,m1)
            else m1
        end
    | M( itree(inode("if_then_else",_),
            [
            itree(inode("if",_), [] ),
                itree(inode("(",_), [] ),
                expr,
                itree(inode(")",_), [] ),
                block1,
                itree(inode("else",_), []),
                block2
            ]
    ),
    m0
    ) = let
            val (v,m1) = E(expr,m0)
        in
            if toBool(v) then M(block1,m1)
            else M(block2,m1)
        end
    | M( itree(inode("iterative_statement",_),
            [
            iterative_statement
            ]
    ),
    m
    ) = M(iterative_statement,m)    
    | M( itree(inode("while_loop",_),
            [
                itree(inode("while",_), [] ),
                itree(inode("(",_), [] ),
                expression,
                itree(inode(")",_), [] ),
                block
            ]
    ),
    m0
    ) = let
          fun loop(m) = 
            let
                val (v, m2) = E(expression, m)
            in
                if toBool(v) then
                    let
                        val m3 = M(block, m2)
                        val m4 = loop(m3)
                    in
                        m4
                    end
                else m2
            end
        in
          loop(m0)
        end
    | M( itree(inode("for_loop",_),
            [
                itree(inode("for",_), [] ),
                itree(inode("(",_), [] ),
                assignment,
                itree(inode(";",_), [] ),
                expr,
                itree(inode(";",_), [] ),
                prePost       ,        
                itree(inode(")",_), [] ),
                block
            ]
    ),
    m0
    ) = let
            val m1 = M(assignment,m0)
            fun aux(m2) =
                let
                    val (v,m3) = E(expr,m2)
                in
                    if toBool(v) then
                        let
                            val m4 = M(block, m3)
                            val m5 = M(prePost, m4)
                            val m6 = aux(m5)
                        in
                            m6
                        end
                    else m3
                end       
        in
           aux (m1)
        end
    | M( itree(inode("block_statement",_),
            [
                itree(inode("{",_), [] ),
                statement_list,
                itree(inode("}",_), [] )
            ]
    ),
    (env0,counter0,s0)
    ) = let
            val (_,counter1,s1) = M(statement_list,(env0,counter0,s0))
            val m = (env0,counter1,s1)
        in
            m
        end
    | M( itree(inode("print_statement",_),
            [
                itree(inode("print",_), [] ),
            itree(inode("(",_), [] ),
                expr,
                itree(inode(")",_), [] )
            ]
    ),
    m
    ) = let
            val (v1,m1) = E(expr,m)
            val str = varToString(v1)
        in
            (print(str ^ "\n"); m1)
        end
    

    | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
 
    | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)





