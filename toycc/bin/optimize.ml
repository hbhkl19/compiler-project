open Ast

module Ast_mapper = struct
    let rec iter_expr f e =
        f e;
        match e with
        | BinOp(e1, _, e2) -> iter_expr f e1; iter_expr f e2
        | UnOp(_, e) -> iter_expr f e
        | Call(_, args) -> List.iter (iter_expr f) args
        | Paren e -> iter_expr f e
        | _ -> ()

    let rec iter_stmt f_expr f_stmt s =
        f_stmt s;
        match s with
        | Block stmts -> List.iter (iter_stmt f_expr f_stmt) stmts
        | ExprStmt e -> iter_expr f_expr e
        | Assign(_, e) -> iter_expr f_expr e
        | Decl(_, e) -> iter_expr f_expr e
        | If(cond, then_s, else_s_opt) ->
            iter_expr f_expr cond;
            iter_stmt f_expr f_stmt then_s;
            Option.iter (iter_stmt f_expr f_stmt) else_s_opt
        | While(cond, body) ->
            iter_expr f_expr cond;
            iter_stmt f_expr f_stmt body
        | Return(Some e) -> iter_expr f_expr e
        | _ -> ()
end

module VarSet = Set.Make(String)

(*****************************************************************************)
(* 优化遍 1: 常量折叠                                                        *)
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
            | _ -> failwith ("Unsupported operator or division by zero: " ^ op)
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
            | _ -> failwith ("Unsupported unary operator: " ^ op)
          in
          Literal (IntLit result)
      | UnOp ("!", e'') -> e''
      | UnOp ("-", UnOp ("-", e'')) -> e''
      | _ -> UnOp (op, e')
      end
  | Call (fname, args) -> Call (fname, List.map fold_constants_expr args)
  | Paren e -> fold_constants_expr e

let rec fold_constants_stmt stmt =
  match stmt with
  | Block stmts -> Block (List.map fold_constants_stmt stmts)
  | Empty -> Empty
  | ExprStmt expr -> ExprStmt (fold_constants_expr expr)
  | Assign (id, expr) -> Assign (id, fold_constants_expr expr)
  | Decl (id, expr) -> Decl (id, fold_constants_expr expr)
  | If (cond, then_stmt, else_stmt_opt) ->
      let cond' = fold_constants_expr cond in
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
      | Literal (IntLit 0) -> Empty
      | _ -> While (cond', body')
      end
  | Break -> Break
  | Continue -> Continue
  | Return expr_opt -> Return (Option.map fold_constants_expr expr_opt)

let fold_constants program =
  List.map (fun func -> { func with body = List.map fold_constants_stmt func.body }) program

(*****************************************************************************)
(* 优化遍 2: 死代码消除 (DCE)                                                  *)
(*****************************************************************************)

let is_const_true expr = match expr with | Literal (IntLit n) -> n != 0 | _ -> false
let is_const_false expr = match expr with | Literal (IntLit 0) -> true | _ -> false

let rec collect_vars_expr vars expr =
  match expr with
  | Literal _ -> vars
  | Var id -> VarSet.add id vars
  | BinOp (e1, _, e2) -> let vars = collect_vars_expr vars e1 in collect_vars_expr vars e2
  | UnOp (_, e) -> collect_vars_expr vars e
  | Call (_, args) -> List.fold_left collect_vars_expr vars args
  | Paren e -> collect_vars_expr vars e

let rec collect_vars_stmt vars stmt =
  match stmt with
  | Block stmts -> List.fold_left collect_vars_stmt vars stmts
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

let rec eliminate_dead_stmts reachable stmts; (* 声明，因为存在相互递归 *)

and eliminate_dead_stmt reachable stmt =
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
          eliminate_dead_stmt true then_stmt
        else if is_const_false cond then
          match else_stmt_opt with
          | Some else_stmt -> eliminate_dead_stmt true else_stmt
          | None -> (None, true)
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
          | None, Some else_s -> (Some (If (UnOp ("!", cond), else_s, None)), new_reachable)
          | Some then_s, Some else_s -> (Some (If (cond, then_s, Some else_s)), new_reachable)
    (* ✅ 修正点: 将这些分支放在了正确的外层 match 作用域中 *)
    | While (cond, body) ->
        if is_const_false cond then (None, true)
        else
          let body_res, _ = eliminate_dead_stmt true body in
          let body' = Option.value body_res ~default:(Block []) in
          (Some (While (cond, body')), true)
    | Break -> (Some Break, false)
    | Continue -> (Some Continue, false)
    | Return expr_opt -> (Some (Return expr_opt), false)

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

let rec remove_unused_stmt used_vars stmt =
  match stmt with
  | Block stmts ->
      let filtered_stmts = List.filter_map (fun s ->
        let s' = remove_unused_stmt used_vars s in
        match s' with | Empty -> None | _ -> Some s'
      ) stmts in
      if filtered_stmts = [] then Empty else Block filtered_stmts
  | Empty -> Empty
  | ExprStmt expr -> ExprStmt expr
  | Assign (id, expr) -> if VarSet.mem id used_vars then Assign (id, expr) else Empty
  | Decl (id, expr) -> if VarSet.mem id used_vars then Decl (id, expr) else Empty
  | If (cond, then_stmt, else_stmt_opt) ->
      let then_stmt' = remove_unused_stmt used_vars then_stmt in
      let else_stmt_opt' = Option.map (remove_unused_stmt used_vars) else_stmt_opt in
      If (cond, then_stmt', else_stmt_opt')
  | While (cond, body) -> While (cond, remove_unused_stmt used_vars body)
  | Break -> Break
  | Continue -> Continue
  | Return expr_opt -> Return expr_opt

let eliminate_dead_code program =
  List.map (fun func ->
    let body_reachable, _ = eliminate_dead_stmts true func.body in
    let used_vars = List.fold_left collect_vars_stmt VarSet.empty body_reachable in
    let body_unused_removed = List.map (remove_unused_stmt used_vars) body_reachable in
    let body_filtered = List.filter (function Empty -> false | _ -> true) body_unused_removed in
    { func with body = body_filtered }
  ) program

(*****************************************************************************)
(* 优化遍 3: 尾递归优化 (TCO)                                                  *)
(*****************************************************************************)

let rec last_and_init = function
  | [] -> failwith "Internal error: last_and_init on empty list"
  | [x] -> (x, [])
  | h :: t -> let (last, init) = last_and_init t in (last, h :: init)

let rec contains_tco_candidate (func: func_def) (is_tail_pos: bool) (stmt: stmt) : bool =
  match stmt with
  | Return (Some (Call(callee, args))) -> is_tail_pos && callee = func.fname && List.length args = List.length func.params
  | If (_, then_s, else_s_opt) ->
      let then_has = contains_tco_candidate func is_tail_pos then_s in
      let else_has = match else_s_opt with | Some s -> contains_tco_candidate func is_tail_pos s | None -> false in
      then_has || else_has
  | Block (stmts) ->
      if not is_tail_pos || stmts = [] then List.exists (contains_tco_candidate func false) stmts
      else
        let (last, init) = last_and_init stmts in
        List.exists (contains_tco_candidate func false) init || contains_tco_candidate func true last
  | While (_, body) -> contains_tco_candidate func false body
  | _ -> false

let rec transform_stmt_for_tco (func: func_def) (is_tail_pos: bool) (fresh_var_gen: unit -> id) (stmt: stmt) : stmt =
  match stmt with
  | Return (Some (Call(callee, args))) when is_tail_pos && callee = func.fname && List.length args = List.length func.params ->
      let params = func.params in
      let temp_decls_and_names = List.map (fun arg_expr -> (fresh_var_gen (), arg_expr)) args in
      let temp_decls = List.map (fun (name, expr) -> Decl(name, expr)) temp_decls_and_names in
      let assignments = List.map2 (fun param (name, _) -> Assign(param.pname, Var name)) params temp_decls_and_names in
      Block(temp_decls @ assignments @ [Continue])
  | If (cond, then_s, else_s_opt) ->
      let new_then = transform_stmt_for_tco func is_tail_pos fresh_var_gen then_s in
      let new_else_opt = Option.map (transform_stmt_for_tco func is_tail_pos fresh_var_gen) else_s_opt in
      If (cond, new_then, new_else_opt)
  | Block (stmts) ->
      if not is_tail_pos || stmts = [] then Block (List.map (transform_stmt_for_tco func false fresh_var_gen) stmts)
      else
        let (last, init) = last_and_init stmts in
        let transformed_init = List.map (transform_stmt_for_tco func false fresh_var_gen) init in
        let transformed_last = transform_stmt_for_tco func true fresh_var_gen last in
        Block(transformed_init @ [transformed_last])
  | While (cond, body) -> While(cond, transform_stmt_for_tco func false fresh_var_gen body)
  | _ -> stmt

let optimize_func_for_tco (func: func_def) : func_def =
  let has_tco_candidate = List.exists (contains_tco_candidate func true) func.body in
  if not has_tco_candidate then func
  else
    let counter = ref 0 in
    let fresh_var_gen () = counter := !counter + 1; "__tco_" ^ func.fname ^ "_" ^ (string_of_int !counter) in
    let transformed_body_stmts = List.map (transform_stmt_for_tco func true fresh_var_gen) func.body in
    let true_expr = Literal (IntLit 1) in
    let loop_body = Block transformed_body_stmts in
    let new_body = [While (true_expr, loop_body)] in
    { func with body = new_body }

let optimize_tail_recursion program =
  List.map optimize_func_for_tco program

(*****************************************************************************)
(* 🚀 优化遍 4 & 5: 循环优化 (CSE & LICM)                                     *)
(*****************************************************************************)
module LoopOptimizations = struct
    module ExprHashtbl = Hashtbl.Make(struct
      type t = expr
      let equal = (=)
      let hash = Hashtbl.hash
    end)

    let is_invariant defined_in_loop expr =
        let used_vars = collect_vars_expr VarSet.empty expr in
        VarSet.is_empty (VarSet.inter used_vars defined_in_loop)

    let find_and_replace_invariants fresh_var_gen defined_in_loop body =
        let invariant_map = ExprHashtbl.create 8 in
        let declarations = ref [] in
        let rec rewrite_expr expr =
            match expr with
            | BinOp(e1, op, e2) ->
                let e1' = rewrite_expr e1 in
                let e2' = rewrite_expr e2 in
                let new_expr = BinOp(e1', op, e2') in
                if is_invariant defined_in_loop new_expr then
                    match ExprHashtbl.find_opt invariant_map new_expr with
                    | Some var_id -> Var var_id
                    | None ->
                        let temp_var = fresh_var_gen () in
                        ExprHashtbl.add invariant_map new_expr temp_var;
                        declarations := Decl(temp_var, new_expr) :: !declarations;
                        Var temp_var
                else new_expr
            | UnOp(op, e) ->
                let e' = rewrite_expr e in
                let new_expr = UnOp(op, e') in
                if is_invariant defined_in_loop new_expr then
                     match ExprHashtbl.find_opt invariant_map new_expr with
                    | Some var_id -> Var var_id
                    | None ->
                        let temp_var = fresh_var_gen () in
                        ExprHashtbl.add invariant_map new_expr temp_var;
                        declarations := Decl(temp_var, new_expr) :: !declarations;
                        Var temp_var
                else new_expr
            | Call(fname, args) -> Call(fname, List.map rewrite_expr args)
            | _ -> expr
        in
        let rec rewrite_stmt stmt =
            match stmt with
            | Block stmts -> Block(List.map rewrite_stmt stmts)
            | Assign(id, expr) -> Assign(id, rewrite_expr expr)
            | Decl(id, expr) -> Decl(id, rewrite_expr expr)
            | If(cond, then_s, else_s_opt) -> If(rewrite_expr cond, rewrite_stmt then_s, Option.map rewrite_stmt else_s_opt)
            | While(cond, b) -> While(rewrite_expr cond, b)
            | Return(Some expr) -> Return(Some (rewrite_expr expr))
            | ExprStmt(expr) -> ExprStmt(rewrite_expr expr)
            | _ -> stmt
        in
        let new_body = rewrite_stmt body in
        (!declarations, new_body)

    let rec licm_stmt fresh_var_gen stmt =
        match stmt with
        | While(cond, body) ->
            let defined_in_loop = collect_defined_vars body in
            let (declarations, new_body) = find_and_replace_invariants fresh_var_gen defined_in_loop body in
            let optimized_body = licm_stmt fresh_var_gen new_body in
            Block (List.rev declarations @ [While(cond, optimized_body)])
        | Block stmts -> Block(List.map (licm_stmt fresh_var_gen) stmts)
        | If(cond, then_s, else_s_opt) ->
            let then_s' = licm_stmt fresh_var_gen then_s in
            let else_s' = Option.map (licm_stmt fresh_var_gen) else_s_opt in
            If(cond, then_s', else_s')
        | _ -> stmt

    let optimize program =
        List.map (fun func ->
            let counter = ref 0 in
            let fresh_var_gen () = counter := !counter + 1; "__licm_" ^ func.fname ^ "_" ^ (string_of_int !counter) in
            { func with body = List.map (licm_stmt fresh_var_gen) func.body }
        ) program
end

(*****************************************************************************)
(* ✅ 最终的、修正后且更强大的优化流水线                                      *)
(*****************************************************************************)
let optimize program =
  program
  |> fold_constants
  |> eliminate_dead_code
  |> optimize_tail_recursion
  |> LoopOptimizations.optimize
  |> eliminate_dead_code
