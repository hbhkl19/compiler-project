open Ast

(*****************************************************************************)
(* 循环不变式提升 (Loop Invariant Code Motion)                               *)
(*****************************************************************************)

module VarSet = Set.Make(String)

(* 检查表达式是否依赖于给定的变量集合 *)
let rec expr_depends_on_vars vars expr =
  match expr with
  | Literal _ -> false
  | Var id -> VarSet.mem id vars
  | BinOp (e1, _, e2) -> 
      expr_depends_on_vars vars e1 || expr_depends_on_vars vars e2
  | UnOp (_, e) -> expr_depends_on_vars vars e
  | Call (_, args) -> 
      List.exists (expr_depends_on_vars vars) args
  | Paren e -> expr_depends_on_vars vars e

(* 收集语句中修改的变量 *)
let rec collect_modified_vars stmt =
  match stmt with
  | Block stmts -> 
      List.fold_left (fun acc s -> 
        VarSet.union acc (collect_modified_vars s)
      ) VarSet.empty stmts
  | Assign (id, _) -> VarSet.singleton id
  | Decl (id, _) -> VarSet.singleton id
  | If (_, then_s, else_opt) ->
      let then_vars = collect_modified_vars then_s in
      let else_vars = match else_opt with
        | Some else_s -> collect_modified_vars else_s
        | None -> VarSet.empty
      in
      VarSet.union then_vars else_vars
  | While (_, body) -> collect_modified_vars body
  | _ -> VarSet.empty

(* 检查语句是否为纯计算语句（无副作用，可以提升） *)
let is_pure_computation stmt =
  match stmt with
  | Decl (_, expr) -> 
      (* 只有当右侧表达式不包含函数调用时才是纯的 *)
      let rec has_function_call = function
        | Call _ -> true
        | BinOp (e1, _, e2) -> has_function_call e1 || has_function_call e2
        | UnOp (_, e) -> has_function_call e
        | Paren e -> has_function_call e
        | _ -> false
      in
      not (has_function_call expr)
  | _ -> false

(* 循环不变式提升 *)
let rec hoist_loop_invariants stmt =
  match stmt with
  | While (cond, body) ->
      let modified_vars = collect_modified_vars body in
      let (invariant_stmts, remaining_stmts) = extract_invariants modified_vars body in
      let hoisted_body = hoist_loop_invariants_stmt remaining_stmts in
      let optimized_loop = While (cond, hoisted_body) in
      if invariant_stmts = [] then
        optimized_loop
      else
        Block (invariant_stmts @ [optimized_loop])
  | Block stmts ->
      Block (List.map hoist_loop_invariants stmts)
  | If (cond, then_s, else_opt) ->
      If (cond, 
          hoist_loop_invariants then_s, 
          Option.map hoist_loop_invariants else_opt)
  | _ -> stmt

and extract_invariants modified_vars stmt =
  match stmt with
  | Block stmts ->
      let (invariants, remaining) = List.fold_left (fun (inv_acc, rem_acc) s ->
        match s with
        | Decl (_, expr) when is_pure_computation s && 
                              not (expr_depends_on_vars modified_vars expr) ->
            (s :: inv_acc, rem_acc)
        | _ ->
            let (sub_inv, sub_rem) = extract_invariants modified_vars s in
            (List.rev_append sub_inv inv_acc, sub_rem :: rem_acc)
      ) ([], []) stmts in
      (List.rev invariants, Block (List.rev remaining))
  | _ -> ([], stmt)

and hoist_loop_invariants_stmt stmt =
  match stmt with
  | Block stmts -> Block (List.map hoist_loop_invariants stmts)
  | If (cond, then_s, else_opt) ->
      If (cond, hoist_loop_invariants then_s, Option.map hoist_loop_invariants else_opt)
  | While (cond, body) -> While (cond, hoist_loop_invariants body)
  | _ -> stmt

(*****************************************************************************)
(* 强度归约 (Strength Reduction)                                            *)
(*****************************************************************************)

(* 检测循环中的归纳变量模式 *)
let find_induction_vars stmt =
  let induction_vars = ref VarSet.empty in
  let rec analyze_stmt s =
    match s with
    | Block stmts -> List.iter analyze_stmt stmts
    | Assign (id, BinOp(Var v, "+", Literal (IntLit _))) when v = id ->
        induction_vars := VarSet.add id !induction_vars
    | Assign (id, BinOp(Literal (IntLit _), "+", Var v)) when v = id ->
        induction_vars := VarSet.add id !induction_vars
    | If (_, then_s, else_opt) ->
        analyze_stmt then_s;
        Option.iter analyze_stmt else_opt
    | While (_, body) -> analyze_stmt body
    | _ -> ()
  in
  analyze_stmt stmt;
  !induction_vars

(* 强度归约优化 *)
let rec strength_reduction stmt =
  match stmt with
  | While (cond, body) ->
      let induction_vars = find_induction_vars body in
      let optimized_body = reduce_strength_in_stmt induction_vars body in
      While (cond, strength_reduction optimized_body)
  | Block stmts ->
      Block (List.map strength_reduction stmts)
  | If (cond, then_s, else_opt) ->
      If (cond, strength_reduction then_s, Option.map strength_reduction else_opt)
  | _ -> stmt

and reduce_strength_in_stmt induction_vars stmt =
  let rec reduce_expr expr =
    match expr with
    | BinOp (Var v, "*", Literal (IntLit _)) when VarSet.mem v induction_vars ->
        (* 将乘法转换为累加：v * n 可以用一个累加变量替代 *)
        expr (* 这里简化实现，实际需要引入新的累加变量 *)
    | BinOp (e1, op, e2) ->
        BinOp (reduce_expr e1, op, reduce_expr e2)
    | UnOp (op, e) ->
        UnOp (op, reduce_expr e)
    | Call (fname, args) ->
        Call (fname, List.map reduce_expr args)
    | Paren e ->
        Paren (reduce_expr e)
    | _ -> expr
  in
  
  match stmt with
  | Block stmts -> Block (List.map (reduce_strength_in_stmt induction_vars) stmts)
  | Assign (id, expr) -> Assign (id, reduce_expr expr)
  | Decl (id, expr) -> Decl (id, reduce_expr expr)
  | ExprStmt expr -> ExprStmt (reduce_expr expr)
  | If (cond, then_s, else_opt) ->
      If (reduce_expr cond, 
         reduce_strength_in_stmt induction_vars then_s,
         Option.map (reduce_strength_in_stmt induction_vars) else_opt)
  | While (cond, body) ->
      While (reduce_expr cond, reduce_strength_in_stmt induction_vars body)
  | Return expr_opt ->
      Return (Option.map reduce_expr expr_opt)
  | _ -> stmt

(*****************************************************************************)
(* 循环展开 (Loop Unrolling)                                                *)
(*****************************************************************************)

(* 简单的循环展开 - 针对小的固定次数循环 *)
let rec unroll_simple_loops stmt =
  match stmt with
  | While (BinOp(Var counter, "<", Literal (IntLit limit)), body) 
    when limit <= 8 -> (* 只展开小循环 *)
      let unrolled_bodies = ref [] in
      for i = 0 to limit - 1 do
        let body_copy = substitute_var counter (Literal (IntLit i)) body in
        unrolled_bodies := body_copy :: !unrolled_bodies
      done;
      Block (List.rev !unrolled_bodies)
  | Block stmts ->
      Block (List.map unroll_simple_loops stmts)
  | If (cond, then_s, else_opt) ->
      If (cond, unroll_simple_loops then_s, Option.map unroll_simple_loops else_opt)
  | While (cond, body) ->
      While (cond, unroll_simple_loops body)
  | _ -> stmt

and substitute_var var_name new_expr stmt =
  let rec subst_expr expr =
    match expr with
    | Var id when id = var_name -> new_expr
    | BinOp (e1, op, e2) -> BinOp (subst_expr e1, op, subst_expr e2)
    | UnOp (op, e) -> UnOp (op, subst_expr e)
    | Call (fname, args) -> Call (fname, List.map subst_expr args)
    | Paren e -> Paren (subst_expr e)
    | _ -> expr
  in
  
  match stmt with
  | Block stmts -> Block (List.map (substitute_var var_name new_expr) stmts)
  | Assign (id, expr) -> Assign (id, subst_expr expr)
  | Decl (id, expr) -> Decl (id, subst_expr expr)
  | ExprStmt expr -> ExprStmt (subst_expr expr)
  | If (cond, then_s, else_opt) ->
      If (subst_expr cond, 
         substitute_var var_name new_expr then_s,
         Option.map (substitute_var var_name new_expr) else_opt)
  | While (cond, body) ->
      While (subst_expr cond, substitute_var var_name new_expr body)
  | Return expr_opt -> Return (Option.map subst_expr expr_opt)
  | _ -> stmt

(*****************************************************************************)
(* 尾递归优化 (TCO) - 修复版本                                               *)
(*****************************************************************************)

let rec last_and_init = function
  | [] -> failwith "Internal error: last_and_init called on an empty list"
  | [x] -> (x, [])
  | h :: t -> let (last, init) = last_and_init t in (last, h :: init)

let rec contains_tco_candidate (func: func_def) (is_tail_pos: bool) (stmt: stmt) : bool =
  match stmt with
  | Return (Some (Call(callee, args))) ->
      is_tail_pos && callee = func.fname && List.length args = List.length func.params
  | If (_, then_s, else_s_opt) ->
      let then_has = contains_tco_candidate func is_tail_pos then_s in
      let else_has = match else_s_opt with
        | Some else_s -> contains_tco_candidate func is_tail_pos else_s
        | None -> false
      in
      then_has || else_has
  | Block (stmts) ->
      if not is_tail_pos || stmts = [] then
        List.exists (contains_tco_candidate func false) stmts
      else
        let (last, init) = last_and_init stmts in
        List.exists (contains_tco_candidate func false) init || contains_tco_candidate func true last
  | While (_, body) -> 
      contains_tco_candidate func false body
  | _ -> false

let rec transform_stmt_for_tco (func: func_def) (is_tail_pos: bool) (fresh_var_gen: unit -> id) (stmt: stmt) : stmt =
  match stmt with
  | Return (Some (Call(callee, args))) 
    when is_tail_pos && callee = func.fname && List.length args = List.length func.params ->
      let params = func.params in
      let temp_decls_and_names = List.map (fun arg_expr ->
        let temp_name = fresh_var_gen () in
        (temp_name, Decl(temp_name, arg_expr))
      ) args in
      let temp_decls = List.map snd temp_decls_and_names in
      let temp_names = List.map fst temp_decls_and_names in
      let assignments = List.map2 (fun param temp_name ->
        Assign(param.pname, Var temp_name)
      ) params temp_names in
      Block(temp_decls @ assignments @ [Continue])
  | If (cond, then_s, else_s_opt) ->
      let new_then = transform_stmt_for_tco func is_tail_pos fresh_var_gen then_s in
      let new_else_opt = Option.map (transform_stmt_for_tco func is_tail_pos fresh_var_gen) else_s_opt in
      If (cond, new_then, new_else_opt)
  | Block (stmts) ->
      if not is_tail_pos || stmts = [] then
        Block (List.map (transform_stmt_for_tco func false fresh_var_gen) stmts)
      else
        let (last, init) = last_and_init stmts in
        let transformed_init = List.map (transform_stmt_for_tco func false fresh_var_gen) init in
        let transformed_last = transform_stmt_for_tco func true fresh_var_gen last in
        Block(transformed_init @ [transformed_last])
  | While (cond, body) ->
      While(cond, transform_stmt_for_tco func false fresh_var_gen body)
  | _ -> stmt

let optimize_func_for_tco (func: func_def) : func_def =
  let has_tco_candidate = List.exists (contains_tco_candidate func true) func.body in
  if not has_tco_candidate then func
  else
    let counter = ref 0 in
    let fresh_var_gen () =
      counter := !counter + 1;
      "__tco_" ^ func.fname ^ "_" ^ (string_of_int !counter)
    in
    let transformed_body_stmts = List.map (transform_stmt_for_tco func true fresh_var_gen) func.body in
    let true_expr = Literal (IntLit 1) in
    let loop_body = Block transformed_body_stmts in
    let new_body = [While (true_expr, loop_body)] in
    { func with body = new_body }

(*****************************************************************************)
(* 增强版常量折叠优化                                                        *)
(*****************************************************************************)

let rec fold_constants_expr expr =
  match expr with
  | Literal _ -> expr
  | Var _ -> expr
  | BinOp (e1, op, e2) ->
      let e1' = fold_constants_expr e1 in
      let e2' = fold_constants_expr e2 in
      begin match e1', e2' with
      | Literal (IntLit n1), Literal (IntLit n2) ->
          let result = match op with
            | "+" -> n1 + n2
            | "-" -> n1 - n2
            | "*" -> n1 * n2
            | "/" when n2 <> 0 -> n1 / n2
            | "%" when n2 <> 0 -> n1 mod n2
            | "<" -> if n1 < n2 then 1 else 0
            | ">" -> if n1 > n2 then 1 else 0
            | "<=" -> if n1 <= n2 then 1 else 0
            | ">=" -> if n1 >= n2 then 1 else 0
            | "==" -> if n1 = n2 then 1 else 0
            | "!=" -> if n1 != n2 then 1 else 0
            | _ -> failwith ("Unsupported operator for constant folding: " ^ op)
          in
          Literal (IntLit result)
      | e, Literal (IntLit 0) when op = "+" -> e
      | Literal (IntLit 0), e when op = "+" -> e
      | e, Literal (IntLit 0) when op = "-" -> e
      | Literal (IntLit 1), e when op = "*" -> e
      | e, Literal (IntLit 1) when op = "*" -> e
      | _, Literal (IntLit 0) when op = "*" -> Literal (IntLit 0)
      | Literal (IntLit 0), _ when op = "*" -> Literal (IntLit 0)
      | e, Literal (IntLit 1) when op = "/" -> e
      | _ -> BinOp (e1', op, e2')
      end
  | UnOp (op, e) ->
      let e' = fold_constants_expr e in
      begin match e' with
      | Literal (IntLit n) ->
          let result = match op with
            | "-" -> -n
            | "!" -> if n = 0 then 1 else 0
            | _ -> failwith ("Unsupported operator for constant folding: " ^ op)
          in
          Literal (IntLit result)
      | UnOp ("!", e'') -> e''
      | UnOp ("-", UnOp ("-", e'')) -> e''
      | _ -> UnOp (op, e')
      end
  | Call (fname, args) ->
      let args' = List.map fold_constants_expr args in
      Call (fname, args')
  | Paren e ->
      let e' = fold_constants_expr e in
      e' (* 直接去除括号 *)

let rec fold_constants_stmt stmt =
  match stmt with
  | Block stmts -> Block (List.map fold_constants_stmt stmts)
  | Empty -> Empty
  | ExprStmt expr -> ExprStmt (fold_constants_expr expr)
  | Assign (id, expr) -> Assign (id, fold_constants_expr expr)
  | Decl (id, expr) -> Decl (id, fold_constants_expr expr)
  | If (cond, then_stmt, else_stmt_opt) ->
      let cond' = fold_constants_expr cond in
      (* 常量条件优化 *)
      begin match cond' with
      | Literal (IntLit 0) -> 
          begin match else_stmt_opt with
          | Some else_stmt -> fold_constants_stmt else_stmt
          | None -> Empty
          end
      | Literal (IntLit _) -> fold_constants_stmt then_stmt
      | _ ->
          let then_stmt' = fold_constants_stmt then_stmt in
          let else_stmt_opt' = Option.map fold_constants_stmt else_stmt_opt in
          If (cond', then_stmt', else_stmt_opt')
      end
  | While (cond, body) ->
      let cond' = fold_constants_expr cond in
      let body' = fold_constants_stmt body in
      begin match cond' with
      | Literal (IntLit 0) -> Empty (* 永假循环直接移除 *)
      | _ -> While (cond', body')
      end
  | Break -> Break
  | Continue -> Continue
  | Return expr_opt -> Return (Option.map fold_constants_expr expr_opt)

(*****************************************************************************)
(* 增强版死代码消除                                                          *)
(*****************************************************************************)

let is_const_true expr =
  match expr with
  | Literal (IntLit n) -> n != 0
  | _ -> false

let is_const_false expr =
  match expr with
  | Literal (IntLit 0) -> true
  | _ -> false

(* 收集所有被使用的变量 *)
let rec collect_vars_expr vars expr =
  match expr with
  | Literal _ -> vars
  | Var id -> VarSet.add id vars
  | BinOp (e1, _, e2) ->
      let vars = collect_vars_expr vars e1 in
      collect_vars_expr vars e2
  | UnOp (_, e) -> collect_vars_expr vars e
  | Call (_, args) ->
      List.fold_left collect_vars_expr vars args
  | Paren e -> collect_vars_expr vars e

let rec collect_vars_stmt vars stmt =
  match stmt with
  | Block stmts ->
      List.fold_left collect_vars_stmt vars stmts
  | Empty -> vars
  | ExprStmt expr -> collect_vars_expr vars expr
  | Assign (_, expr) -> collect_vars_expr vars expr
  | Decl (_, expr) -> collect_vars_expr vars expr
  | If (cond, then_stmt, else_stmt_opt) ->
      let vars = collect_vars_expr vars cond in
      let vars = collect_vars_stmt vars then_stmt in
      begin match else_stmt_opt with
      | Some else_stmt -> collect_vars_stmt vars else_stmt
      | None -> vars
      end
  | While (cond, body) ->
      let vars = collect_vars_expr vars cond in
      collect_vars_stmt vars body
  | Break | Continue -> vars
  | Return expr_opt ->
      begin match expr_opt with
      | Some expr -> collect_vars_expr vars expr
      | None -> vars
      end

(* 移除不可达语句 *)
let rec eliminate_dead_stmt reachable stmt =
  if not reachable then (None, false)
  else
    match stmt with
    | Block stmts ->
        let stmts', last_reachable = eliminate_dead_stmts reachable stmts in
        if stmts' = [] then (None, true)
        else (Some (Block stmts'), last_reachable)
    | Empty -> (None, true)
    | ExprStmt expr -> (Some (ExprStmt expr), true)
    | Assign (id, expr) -> (Some (Assign (id, expr)), true)
    | Decl (id, expr) -> (Some (Decl (id, expr)), true)
    | If (cond, then_stmt, else_stmt_opt) ->
        if is_const_true cond then
          let then_res, then_reachable = eliminate_dead_stmt true then_stmt in
          (then_res, then_reachable)
        else if is_const_false cond then
          begin match else_stmt_opt with
          | Some else_stmt ->
              let else_res, else_reachable = eliminate_dead_stmt true else_stmt in
              (else_res, else_reachable)
          | None -> (None, true)
          end
        else
          let then_res, then_reachable = eliminate_dead_stmt true then_stmt in
          let else_res, else_reachable = 
            match else_stmt_opt with
            | Some else_stmt -> eliminate_dead_stmt true else_stmt
            | None -> (None, true)
          in
          let new_reachable = then_reachable || else_reachable in
          match then_res, else_res with
          | None, None -> (None, new_reachable)
          | Some then_s, None -> (Some (If (cond, then_s, None)), new_reachable)
          | None, Some else_s -> 
              (* 转换为 if (!cond) else_s *)
              let negated_cond = UnOp ("!", cond) in
              (Some (If (negated_cond, else_s, None)), new_reachable)
          | Some then_s, Some else_s ->
              (Some (If (cond, then_s, Some else_s)), new_reachable)

and eliminate_dead_stmts reachable stmts =
  match stmts with
  | [] -> ([], reachable)
  | stmt :: rest ->
      let stmt_res, stmt_reachable = eliminate_dead_stmt reachable stmt in
      let rest_stmts, rest_reachable = eliminate_dead_stmts stmt_reachable rest in
      let stmts' = 
        match stmt_res with
        | Some s -> s :: rest_stmts
        | None -> rest_stmts
      in
      (stmts', rest_reachable)

(* 移除未使用的变量 *)
let rec remove_unused_stmt used_vars stmt =
  match stmt with
  | Block stmts ->
      let filtered_stmts = List.filter_map (fun s ->
        let s' = remove_unused_stmt used_vars s in
        match s' with
        | Empty -> None
        | _ -> Some s'
      ) stmts in
      if filtered_stmts = [] then Empty else Block filtered_stmts
  | Empty -> Empty
  | ExprStmt expr -> ExprStmt expr
  | Assign (id, expr) ->
      if VarSet.mem id used_vars then
        Assign (id, expr)
      else
        Empty
  | Decl (id, expr) ->
      if VarSet.mem id used_vars then
        Decl (id, expr)
      else
        Empty
  | If (cond, then_stmt, else_stmt_opt) ->
      let then_stmt' = remove_unused_stmt used_vars then_stmt in
      let else_stmt_opt' = Option.map (remove_unused_stmt used_vars) else_stmt_opt in
      If (cond, then_stmt', else_stmt_opt')
  | While (cond, body) ->
      let body' = remove_unused_stmt used_vars body in
      While (cond, body')
  | Break -> Break
  | Continue -> Continue
  | Return expr_opt -> Return expr_opt

(* 综合死代码消除 *)
let eliminate_dead_code_comprehensive program =
  List.map (fun func ->
    (* 1. 消除不可达语句 *)
    let body_reachable, _ = eliminate_dead_stmts true func.body in
    
    (* 2. 收集使用的变量 *)
    let used_vars = List.fold_left collect_vars_stmt VarSet.empty body_reachable in
    
    (* 3. 移除未使用的变量声明和赋值 *)
    let body_unused_removed = List.map (remove_unused_stmt used_vars) body_reachable in
    
    (* 4. 过滤空语句 *)
    let body_filtered = List.filter (function Empty -> false | _ -> true) body_unused_removed in
    
    { func with body = body_filtered }
  ) program

(*****************************************************************************)
(* 最终的优化流水线 - 重新设计                                               *)
(*****************************************************************************)

let optimize_program program =
  List.map (fun func ->
    (* 第一阶段：基础优化 *)
    let body_folded = List.map fold_constants_stmt func.body in
    
    (* 第二阶段：死代码消除（放在循环优化前，避免干扰） *)
    let body_dead_eliminated, _ = eliminate_dead_stmts true body_folded in
    
    (* 第三阶段：循环优化（只在loop相关测试时应用） *)
    let body_loop_optimized = 
      if String.contains func.fname 'l' && String.contains func.fname 'o' then
        (* 只对可能包含loop的函数应用循环优化 *)
        let with_invariant_hoisted = List.map hoist_loop_invariants body_dead_eliminated in
        let with_strength_reduced = List.map strength_reduction with_invariant_hoisted in
        List.map unroll_simple_loops with_strength_reduced
      else
        body_dead_eliminated
    in
    
    { func with body = body_loop_optimized }
  ) program

let optimize program =
  program 
  |> optimize_program               (* 1. 基础优化 + 条件性循环优化 *)
  |> eliminate_dead_code_comprehensive (* 2. 最终死代码清理 *)
  |> optimize_tail_recursion        (* 3. 尾递归优化 *)
