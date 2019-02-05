module U = Unification

module T = Term

module M = T.M

type 'a result =
  | Success of ('a T.exp * 'a T.exp) list
  | Fail of 'a T.exp * 'a T.exp

type 'a lazy_result =
  | Cons of 'a * 'a lazy_result Lazy.t
  | Nil

exception Fail_exn of (string T.exp * string T.exp)

let sizep (a, b) = T.size a * T.size b

let cost p r memo =
  U.critical_pairs (p::r)
  |> List.filter (fun xy -> not (M.mem xy memo))
  |> List.map sizep
  |> List.fold_left ( * ) (sizep p)

let orient order (e, r, memo) =
  match e with
  | (x, y) :: rest when order x y ->
     rest, (x, y) :: r, memo
  | (x, y) :: rest when order y x ->
     rest, (y, x) :: r, memo
  | (x, y) :: _ ->
     raise (Fail_exn (x, y))
  | [] -> e, r, memo

let delete (e, r, memo) =
  List.filter (fun (x, y) -> not (x = y)) e, r, memo

let simplify_identity (e, r, memo) =
  List.map (fun (x, y) -> U.normal_form r x, U.normal_form r y) e, r, memo
          
let deduce (e, r, memo) =
  (U.critical_pairs r
  |> List.filter (fun xy -> not (M.mem xy memo)))
  @ e,
  r,
  memo

let r_simplify (e, r, memo) =
  match r with
  | (x, y) :: rest ->
     let xy' = x, U.normal_form rest y in
     let memo' = if M.mem (x, y) memo then M.add xy' memo else memo in
     e, xy' :: rest, memo'
  | [] -> e, r, memo

let l_simplify (e, r, memo) =
  match r with
  | (x, y) :: rest ->
     begin match 
       List.map
         begin fun (l, r) ->
         match U.rewrite (l, r) x, U.rewrite (x, y) l with
         | u::_, [] -> Some u
         | _, _ -> None
         end
         rest
       |> List.find_opt (function Some _ -> true | None  -> false)
     with
     | Some (Some u) ->
        (u, y) :: e, rest, memo
     | None -> 
        e, r, memo
     | _ -> failwith "l_simplify"
     end
  | [] -> e, r, memo

let simple (e, r, memo) =
  List.sort_uniq compare e,
  List.sort_uniq compare r,
  memo
         
let select (e, r, memo) =
  match
    List.sort (fun a b -> cost a r memo - cost b r memo) e
  with
  | x::_ as e -> e, r, M.add x memo
  | [] -> [], r, memo

let debug_print (e, r, memo) =
  let () = print_endline "" in
  let () = print_endline "E" in
  let () = T.print_pairs e in
  let () = print_endline "R" in
  let () = T.print_pairs r in e, r, memo
                            
let step order er = 
  select er
  |> orient order
  |> r_simplify
  |> deduce
  |> l_simplify
  |> simplify_identity
  |> delete
  |> simple

let complete order eqs =
  let rec iter er =
    match step order er with
    | [], r', _ -> r'
    | er' -> iter er'
  in
  try
    Success (iter (eqs, [], M.empty))
  with
  | Fail_exn (lhs, rhs) -> Fail (lhs, rhs)

let rec of_list = function
  | x :: xs ->
     Cons (x, lazy (of_list xs))
  | [] -> Nil

let concat x y =
  let rec iter = function
  | x :: xs ->
     Cons (x, lazy (iter xs))
  | [] -> Lazy.force y
  in iter x

let rec map f = function
  | Cons (x, lazy xs) ->
     Cons (f x, lazy (map f xs))
  | Nil -> Nil
         
let rec traverse = function
  | Cons ([], lazy r) ->
     traverse r
  | Cons (r::_, _) ->
     Some r
  | Nil -> None

let complete_lazy order eqs =
  let rec iter er =
    match step order er with
    | [], r', _ -> of_list r'
    | e, r, memo ->
       concat 
       (List.filter (fun x -> M.mem x memo) r)
       (lazy (iter (e, r, memo)))
  in iter (eqs, [], M.empty)

let rec check_eq eqs x y = 
  let redex = map U.rewrite eqs in
  x = y
  || match
      traverse (map (fun f -> f x) redex),
      traverse (map (fun f -> f y) redex)
     with
     | Some _, None -> false
     | None, Some _ -> false
     | None, None -> false
     | Some x, Some y ->
        check_eq eqs x y
