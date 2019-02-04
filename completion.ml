module U = Unification
module T = Term

type 'a result =
  | Success of ('a T.exp * 'a T.exp) list
  | Fail of 'a T.exp * 'a T.exp

exception Fail_exn of (string T.exp * string T.exp)

let sizep (a, b) = T.size a + T.size b

let orient order (e, r) =
  match e with
  | (lhs, rhs) :: rest when order lhs rhs ->
     rest, (lhs, rhs) :: r
  | (lhs, rhs) :: rest when order rhs lhs ->
     rest, (rhs, lhs) :: r
  | (lhs, rhs) :: _ ->
     raise (Fail_exn (lhs, rhs))
  | [] -> e, r

let delete (e, r) =
  List.filter (fun (x, y) -> not (x = y)) e, r

let simplify_identity (e, r) =
  List.map (fun (x, y) -> U.normal_form r x, U.normal_form r y) e
  |> List.sort_uniq compare,
  r
          
let deduce (e, r) =
  U.critical_pairs r @ e,
  r

let r_simplify (e, r) =
  let rec iter = function
  | (x, y) :: rest ->
     (x, U.normal_form rest y) :: iter rest
  | [] -> r
  in e,
     iter r
     |> List.sort_uniq compare

let l_simplify (e, r) =
  let rec iter acc = function
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
          iter ((u, y) :: acc) rest
       | None -> 
          iter acc rest
       | _ -> failwith "l_simplify"
       end
    | [] -> acc
  in 
  let exclude = iter [] r in
  exclude @ e,
  List.filter (fun x -> not (List.mem x exclude)) r
  |> List.sort_uniq compare

let complete order eqs =
  let step er = 
    er
    |> orient order
    |> deduce
    |> simplify_identity
    |> delete 
    |> (fun (e,r) ->
      let () = print_endline "" in
      let () = print_endline "teste" in
      let () = T.print_pairs e in
      let () = print_endline "testr" in
      let () = T.print_pairs r in e, r)
    |> r_simplify
    |> deduce
    |> l_simplify
  in
  let rec greedy_orient (e, r) =
    match e with
    | [] -> e, r
    | _ -> 
       let e', r' = 
         (e, r)
         |> orient order
         |> deduce
         |> simplify_identity
         |> delete 
       in
       if List.length e > List.length e'
       then greedy_orient (e', r')
       else e, r
  in
  let rec iter er =
    let er' = step er in 
    match er', step er' with
    | ([], r'), _  -> r'
    | (e', r'), (e, r) ->
       if List.length e >= List.length e'
       then greedy_orient (e', r')
            |> iter
       else iter (e, r)
  in
  try
    Success (iter (eqs, []))
  with
  | Fail_exn (lhs, rhs) -> Fail (lhs, rhs)
