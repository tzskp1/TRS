module U = Unification
module T = Term
module M = Set.Make(struct
               type t = string T.exp * string T.exp
               let compare = compare
             end)

type 'a result =
  | Success of ('a T.exp * 'a T.exp) list
  | Fail of 'a T.exp * 'a T.exp

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

let complete order eqs =
  let step er = 
    select er
    |> orient order
    |> r_simplify
    |> deduce
    |> l_simplify
    |> simplify_identity
    |> delete
    |> simple
    |> debug_print
  in
  let rec iter er =
    match step er with
    | [], r', _ -> r'
    | er' -> iter er'
  in
  try
    Success (iter (eqs, [], M.empty))
  with
  | Fail_exn (lhs, rhs) -> Fail (lhs, rhs)
