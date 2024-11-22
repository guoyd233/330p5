open Ast
open Utils

let extend env x v = (x, v) :: env

let rec lookup env x =
  match env with
  | [] -> None
  | (var, value) :: t -> if x = var then Some value else lookup t x

let do_binop op p1 p2 =
  match (p1, p2) with
  | (Int a, Int b) ->
      (match op with
        | Add -> Some (Int (a + b))
        | Sub -> Some (Int (a - b))
        | Mult -> Some (Int (a * b))
        | Div ->
            if b = 0 then raise DivByZeroError
            else Some (Int (a / b))
        | Greater -> Some (Bool (a > b))
        | Less -> Some (Bool (a < b))
        | GreaterEqual -> Some (Bool (a >= b))
        | LessEqual -> Some (Bool (a <= b))
        | Equal -> Some (Bool (a = b))
        | NotEqual -> Some (Bool (a <> b))
        | _ -> None)

  | (Bool a, Bool b) ->
      (match op with
        | Or -> Some (Bool (a || b))
        | And -> Some (Bool (a && b))
        | Equal -> Some (Bool (a = b))
        | NotEqual -> Some (Bool (a <> b))
        | _ -> None)
  | _ -> None

let do_arith op p1 p2 =
  match op, p1, p2 with
  | Add, e, Int 0 -> Some e
  | Add, Int 0, e -> Some e

  | Sub, e, Int 0 -> Some e

  | Mult, _, Int 0 -> Some (Int 0)
  | Mult, Int 0, _ -> Some (Int 0)
  | Mult, e, Int 1 -> Some e
  | Mult, Int 1, e -> Some e

  | Div, e, Int 1 -> Some e
  | Div, Int 0, _ -> Some (Int 0)
  | _ -> None

let do_bool op p1 p2 =
  match op, p1, p2 with
  | And, Bool false, _ -> Some (Bool false)
  | And, _, Bool false -> Some (Bool false)

  | Or, Bool true, _ -> Some (Bool true)
  | Or, _, Bool true -> Some (Bool true)
  | _ -> None

let simp_binop op p1 p2 =
  match do_arith op p1 p2 with
  | Some simplified -> Some simplified
  | None -> (match do_bool op p1 p2 with
       | Some simplified -> Some simplified
       | None -> None)

let rec rm_binding env x =
  match env with
  | [] -> []
  | (a, v) :: t -> if a = x then rm_binding t x else (a, v) :: rm_binding t x

let rec is_constant e =
  match e with
  | Int _ | Bool _ | Fun _ -> true
  | Record fields -> List.for_all (fun ( _ , expr) -> is_constant expr) fields
  | _ -> false

let rec optimize env e =
  match e with
  | Int _ | Bool _ -> e
  | ID x ->
      (match lookup env x with
       | Some v -> v
       | None -> e)

  | Binop (op, p1, p2) ->
      let p1' = optimize env p1 in
      let p2' = optimize env p2 in
      (match op, p2' with                     (*constant folding*)
       | Div, Int 0 -> raise DivByZeroError
       | _ ->
           (match do_binop op p1' p2' with
            | Some folded -> folded
            | None ->
                (match simp_binop op p1' p2' with
                 | Some simplified -> simplified
                 | None -> Binop (op, p1', p2'))))

  | Not p1 ->
      let p1' = optimize env p1 in
      (match p1' with
       | Bool b -> Bool (not b)
       | _ -> Not p1')

  | If (cond, then_exp, else_exp) ->
      let cond' = optimize env cond in
      let then_exp' = optimize env then_exp in
      let else_exp' = optimize env else_exp in
      (match cond' with
       | Bool true -> then_exp'
       | Bool false -> else_exp'
       | _ -> If (cond', then_exp', else_exp'))

  | Let (x, e1, e2) ->
      let e1' = optimize env e1 in
      if is_constant e1' then
        let env' = extend env x e1' in
        optimize env' e2
      else
        Let (x, e1', optimize env e2)

  | LetRec (f, ty, e1, e2) ->
      let e1' = optimize env e1 in
      LetRec (f, ty, e1', optimize env e2)

  | Fun (x, ty, body) ->
      let env' = rm_binding env x in
      Fun (x, ty, optimize env' body)

  | App (e1, e2) ->
      let e1' = optimize env e1 in
      let e2' = optimize env e2 in
      (match e1' with
     | Fun (x, ty, body) ->
         (*to substitute*)
         let env' = extend env x e2' in
         optimize env' body
     | _ -> App (e1', e2'))

  | Record fields ->
      let optimized_fields = List.map (fun (Lab x, expr) -> (Lab x, optimize env expr)) fields in
      Record optimized_fields

  | Select (Lab x, p1) ->
      let p1' = optimize env p1 in
      (match p1' with
       | Record fields ->
           (try List.assoc (Lab x) fields
            with Not_found -> Select (Lab x, p1'))
       | _ -> Select (Lab x, p1'))
