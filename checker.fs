//
// Analyzer for simple C programs.  This component performs
// type checking.  The analyzer returns a string denoting
// success or failure. The string "success" if the input 
// program is legal, otherwise the string "type_error: ..." 
// is returned denoting an invalid simple C program.
//
// Modified by:
//   Syed Amaan Shah
//
// Original author:
//   Prof. Joe Hummel
//   U. of Illinois, Chicago
//   CS 341, Spring 2022
//

namespace compiler

module checker =
  //
  // NOTE: all functions in the module must be indented.
  //

  let rec inSymTab symtab var=
    match symtab with
    | [] -> (false, var, "n/a")
    | (name, vartype)::rest when name = var -> (true, name, vartype)
    | (name, vartype)::rest -> inSymTab rest var

  //
  // matchToken
  //
  let private matchToken expected_token (tokens: string list) =
    //
    // if the next token matches the expected token,  
    // keep parsing by returning the rest of the tokens.
    // Otherwise throw an exception because there's a 
    // syntax error, effectively stopping compilation:
    //
    // NOTE: identifier, int_literal and str_literal
    // are special cases because they are followed by
    // the name or literal value. In these cases exact
    // matching will not work, so we match the start 
    // of the token in these cases.
    //
    let next_token = List.head tokens

    if expected_token = "identifier" && next_token.StartsWith("identifier") then
      //
      // next_token starts with identifier, so we have a match:
      //
      List.tail tokens
    elif expected_token = "int_literal" && next_token.StartsWith("int_literal") then
      //
      // next_token starts with int_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = "str_literal" && next_token.StartsWith("str_literal") then
      //
      // next_token starts with str_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = "real_literal" && next_token.StartsWith("real_literal") then
      //
      // next_token starts with real_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = next_token then  
      List.tail tokens
    else
      failwith ("expecting " + expected_token + ", but found " + next_token)


  //
  // <expr-value> -> identifier
  //               | int_literal
  //               | real_literal
  //               | str_literal
  //               | true
  //               | false
  //
  let rec private expr_value tokens symtab=
    let next_token = List.head tokens
    //
    if next_token = "false" then
      let T2 = matchToken "false" tokens
      (T2, "bool")
    elif next_token = "true" then
      let T2 = matchToken "true" tokens
      (T2, "bool")
    //
    // the others are trickier since we have to look 
    // at the start of the string for a match:
    //
    elif next_token.StartsWith("identifier") then
      let id = List.head tokens
      let var = id.[11..]

      let (found, name, vartype) = inSymTab symtab var
      if found then
        let T2 = matchToken "identifier" tokens
        (T2, vartype)
      else
        failwith ("variable '" + var + "' undefined")

    elif next_token.StartsWith("int_literal") then
      let T2 = matchToken "int_literal" tokens
      (T2, "int")
    elif next_token.StartsWith("str_literal") then
      let T2 = matchToken "str_literal" tokens
      (T2, "str")
    elif next_token.StartsWith("real_literal") then
      let T2 = matchToken "real_literal" tokens
      (T2, "real")
    else
      failwith ("expecting identifier or literal, but found " + next_token)


  //
  // <expr-op> -> +
  //            | -
  //            | *
  //            | /
  //            | ^
  //            | <
  //            | <=
  //            | >
  //            | >=
  //            | ==
  //            | !=
  //
  let rec private expr_op tokens = 
    let next_token = List.head tokens
    //
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
      //
      let T2 = matchToken next_token tokens
      T2
    else
      // error
      failwith ("expecting expression operator, but found " + next_token)


  //
  // <expr> -> <expr-value> <expr-op> <expr-value>
  //         | <expr-value>
  //
  let rec private expr tokens symtab= 
    //
    // first we have to match expr-value, since both
    // rules start with this:
    //
    let (T2, left_type) = expr_value tokens symtab
    //
    // now let's see if there's more to the expression:
    //
    let next_token = List.head T2
    //
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
      //
      let T3 = expr_op T2
      let (T4, right_type) = expr_value T3 symtab

      if next_token = "+"  || next_token = "-"  || next_token = "*"  || next_token = "/"  || next_token = "^" then
        //check arithmetic types
        if left_type = "int" && right_type = "int" then
          (T4, left_type)
        elif left_type = "real" && right_type = "real" then
          (T4, left_type)
        else
          failwith ("operator " + next_token + " must involve 'int' or 'real'")

      else
        //check comparison types
        if next_token = "==" then

          if left_type = right_type then
            if left_type = "real" then
              printfn "warning: comparing real numbers with == may never be true"
              (T4, "bool")
            else
              (T4, "bool")
          else
            failwith ("type mismatch '" + left_type + "' " + next_token + " '" + right_type + "'")
        
        else 
          if left_type = right_type then
            (T4, "bool")
          else
            failwith ("type mismatch '" + left_type + "' " + next_token + " '" + right_type + "'")
    else
      // just expr_value, that's it
      (T2, left_type)


  //
  // <empty> -> ;
  //
  let rec private empty tokens = 
    let T2 = matchToken ";" tokens
    T2


  //
  // <vardecl> -> int identifier ;
  //            | real identifier ;
  //
  let rec private vardecl tokens =
    let next = List.head tokens

    if next = "int" then
      let T2 = matchToken "int" tokens
      let T3 = matchToken "identifier" T2
      let T4 = matchToken ";" T3
      T4
    else
      let T2 = matchToken "real" tokens
      let T3 = matchToken "identifier" T2
      let T4 = matchToken ";" T3
      T4

  //
  // <input> -> cin >> identifier ;
  //
  let rec private input tokens symtab= 
    let T2 = matchToken "cin" tokens
    let T3 = matchToken ">>" T2
    let id = List.head T3
    let var = id.[11..]

    let (found, var, vartype) = inSymTab symtab var
    if found then
      let T4 = matchToken "identifier" T3
      let T5 = matchToken ";" T4
      T5
    else
      failwith ("variable '" + var + "' undefined")

  //
  // <output-value> -> <expr-value>
  //                 | endl
  //
  let rec private output_value tokens symtab= 
    let next_token = List.head tokens
    //
    if next_token = "endl" then
      let T2 = matchToken "endl" tokens
      T2
    else
      let (T2, vartype) = expr_value tokens symtab
      T2


  //
  // <output> -> cout << <output-value> ;
  //
  let rec private output tokens symtab= 
    let T2 = matchToken "cout" tokens
    let T3 = matchToken "<<" T2
    let T4 = output_value T3 symtab
    let T5 = matchToken ";" T4
    T5


  //
  // <assignment> -> identifier = <expr> ;
  //
  let rec private assignment tokens symtab= 
    let (id: string) = List.head tokens
    let name = id.[11..]
    let (found, var, vartype) = inSymTab symtab name

    if found then
      let T2 = matchToken "identifier" tokens
      let T3 = matchToken "=" T2
      let (T4, extype) = expr T3 symtab

      if vartype = extype then
        let T5 = matchToken ";" T4
        (T5, vartype)
      elif vartype = "real" && extype = "int" then
        let T5 = matchToken ";" T4
        (T5, vartype)
      else
        failwith ("cannot assign '" + extype + "' to variable of type '" + vartype + "'")

    else
      failwith ("variable '" + var + "' undefined")

  //
  // <stmt> -> <empty>
  //         | <vardecl>
  //         | <input>
  //         | <output>
  //         | <assignment>
  //         | <ifstmt>
  //
  let rec private stmt tokens symtab= 
    let next_token = List.head tokens
    //
    // use the next token to determine which rule
    // to call; if none match then it's a syntax
    // error:
    //
    if next_token = ";" then
      let T2 = empty tokens
      T2
    elif next_token = "int" || next_token = "real" then
      let T2 = vardecl tokens
      T2
    elif next_token = "cin" then
      let T2 = input tokens symtab
      T2
    elif next_token = "cout" then
      let T2 = output tokens symtab
      T2
    elif next_token.StartsWith("identifier") then
      let (T2, atype) = assignment tokens symtab
      T2
    elif next_token = "if" then
      let T2 = ifstmt tokens symtab
      T2
    else
      failwith ("expecting statement, but found " + next_token)
  //
  // <ifstmt> -> if ( <condition> ) <then-part> <else-part>
  //
  and private ifstmt tokens symtab= 
    let T2 = matchToken "if" tokens
    let T3 = matchToken "(" T2
    let (T4, condtype) = condition T3 symtab
    if condtype = "bool" then
      let T5 = matchToken ")" T4
      let T6 = then_part T5 symtab
      let T7 = else_part T6 symtab
      T7
    else
      failwith ("if condition must be 'bool', but found '" + condtype + "'")
  //
  // <condition> -> <expr>
  //
  and private condition tokens symtab= 
    let (T2, extype) = expr tokens symtab
    (T2,extype)
  //
  // <then-part> -> <stmt>
  //
  and private then_part tokens symtab= 
    let T2 = stmt tokens symtab
    T2
  //
  // <else-part> -> else <stmt>
  //              | EMPTY
  //
  and private else_part tokens symtab= 
    let next_token = List.head tokens
    //
    if next_token = "else" then
      let T2 = matchToken "else" tokens
      let T3 = stmt T2 symtab
      T3
    else
      // EMPTY, do nothing but return tokens back
      tokens


  //
  // <morestmts> -> <stmt> <morestmts>
  //              | EMPTY
  //
  let rec private morestmts tokens symtab= 
    //
    // if the next token denotes the start of a stmt 
    // then process stmt and morestmts, otherwise apply
    // EMPTY
    //
    let next_token = List.head tokens
    //
    if next_token = ";"    ||
       next_token = "int"  ||
       next_token = "real" ||
       next_token = "cin"  ||
       next_token = "cout" ||
       next_token.StartsWith("identifier") ||
       next_token = "if" then
      //
      let T2 = stmt tokens symtab
      let T3 = morestmts T2 symtab
      T3
    else 
      // EMPTY => do nothing, just return tokens back
      tokens


  //
  // <stmts> -> <stmt> <morestmts>
  // 
  let rec private stmts tokens symtab= 
    let T2 = stmt tokens symtab
    let T3 = morestmts T2 symtab
    T3

  

  let private simpleC tokens symboltable = 
    let T2 = matchToken "void" tokens
    let T3 = matchToken "main" T2
    let T4 = matchToken "(" T3
    let T5 = matchToken ")" T4
    let T6 = matchToken "{" T5
    let T7 = stmts T6 symboltable
    let T8 = matchToken "}" T7
    let T9 = matchToken "$" T8  // $ => EOF, there should be no more tokens
    T9


  //
  // typecheck tokens symboltable
  //
  // Given a list of tokens and a symbol table, type-checks 
  // the program to ensure program's variables and expressions
  // are type-compatible. If the program is valid, returns 
  // the string "success". If the program contains a semantic
  // error or warning, returns a string of the form
  // "type_error: ...".
  //
  let typecheck tokens symboltable = 
    try
      let T2 = simpleC tokens symboltable
      "success"
    with 
      | ex -> "type_error: " + ex.Message

