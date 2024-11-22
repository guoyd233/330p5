open Ast
open Utils

let extend env x v = (x, v) :: env

let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound type for " ^ x))
  | (var, value) :: t -> if x = var then value else lookup t x


let rec find_labels x labels =
  match labels with
  | [] -> None
  | (Lab lab, ty) :: t -> if lab = x then Some ty else find_labels x t

let rec is_subtype t1 t2 =
  match (t1, t2) with
  | (TInt, TInt) -> true
  | (TBool, TBool) -> true

  | (TArrow (s1, s2), TArrow (t1, t2)) ->
      is_subtype t1 s1 && is_subtype s2 t2

  | (TRec fields_s, TRec fields_t) ->
      List.for_all (fun (Lab x, ty_t) ->
        match find_labels x fields_s with
        | Some ty_s -> is_subtype ty_s ty_t
        | None -> false
      ) fields_t
  | _ -> false

let rec typecheck gamma e =
  match e with
  | Int _ -> TInt
  | Bool _ -> TBool
  | ID x ->
      (try lookup gamma x
       with DeclareError info -> raise (TypeError info))

  | Binop (op, e1, e2) ->
      let ty1 = typecheck gamma e1 in
      let ty2 = typecheck gamma e2 in
      (match op with
       | Add | Sub | Mult | Div ->        (*arith*)
           if ty1 <> TInt then
             raise (TypeError ("check ty1 " ^ string_of_type ty1))
           else if ty2 <> TInt then
             raise (TypeError ("check ty2 " ^ string_of_type ty2))
           else
             (match (e1, e2) with         (*if the op is constant *)
              | (Int _ , Int 0) -> raise DivByZeroError
              | _ -> TInt)
       
       | Greater | Less | GreaterEqual | LessEqual ->
           if ty1 <> TInt then
             raise (TypeError ("check ty1 " ^ string_of_type ty1))
           else if ty2 <> TInt then
             raise (TypeError ("check ty2 " ^ string_of_type ty2))
           else
             TBool

       | Or | And ->
           if ty1 <> TBool then
             raise (TypeError (""))
           else if ty2 <> TBool then
             raise (TypeError ("or and"))
           else
             TBool
            
       | Equal | NotEqual ->
           if ty1 <> ty2 then
             raise (TypeError (string_of_type ty1 ^ string_of_type ty2))
           else
             TBool
      )

  | Not e1 ->
      let ty = typecheck gamma e1 in
      if ty <> TBool then
        raise (TypeError ("check not"))
      else
        TBool

  | If (cond, then_exp, else_exp) ->
      let ty_cond = typecheck gamma cond in
      if ty_cond <> TBool then
        raise (TypeError (string_of_type ty_cond))
      else
        let ty_then = typecheck gamma then_exp in
        let ty_else = typecheck gamma else_exp in
        if is_subtype ty_then ty_else then ty_else
        else if is_subtype ty_else ty_then then ty_then
        else
          raise (TypeError ("check if"))

  | Let (x, e1, e2) ->
      let ty1 = typecheck gamma e1 in
      let gamma' = extend gamma x ty1 in
      typecheck gamma' e2
  | LetRec (f, ty_f, e1, e2) ->
      let gamma' = extend gamma f ty_f in
      let ty_e1 = typecheck gamma' e1 in
      if is_subtype ty_e1 ty_f then
        typecheck gamma' e2
      else
        raise (TypeError ("LetRec"))

  | Fun (x, ty_p, body) ->
      let gamma' = extend gamma x ty_p in
      let ty_body = typecheck gamma' body in
      TArrow (ty_p, ty_body)

  | App (e1, e2) ->
      let ty_func = typecheck gamma e1 in
      let ty_arg = typecheck gamma e2 in
      (match ty_func with
       | TArrow (ty_p, ty_return) ->
           if is_subtype ty_arg ty_p then
             ty_return
           else
             raise (TypeError ("App"))
       | _ -> raise (TypeError (string_of_type ty_func))
      )

  | Record fields ->
      let ty_fields = List.map (fun (Lab x, expr) ->
        let ty = typecheck gamma expr in
        (Lab x, ty)
      ) fields in
      TRec ty_fields

  | Select (Lab x, e1) ->
      let ty_rec = typecheck gamma e1 in
      (match ty_rec with
       | TRec fields ->
           (try
              List.assoc (Lab x) fields
            with Not_found ->
              raise (SelectError ("Select")))
       | _ -> raise (TypeError (string_of_type ty_rec))
      )