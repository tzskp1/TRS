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
  (* match e with
   * | (x, y) :: rest when x = y ->
   *    rest, r
   * | _ -> e, r *)

let simplify_identity (e, r) =
  List.map (fun (x, y) -> U.normal_form r x, U.normal_form r y) e, r
  (* match e with
   * | (x, y) :: rest -> 
   *    (U.normal_form r x, U.normal_form r y) :: rest, r
   * | [] -> e, r *)
          
let deduce (e, r) =
  U.critical_pairs r @ e,
  r

let r_simplify (e, r) =
  match r with
  | (x, y) :: rest ->
     e, (x, U.normal_form rest y) :: rest
  | [] -> e, r

let l_simplify (e, r) =
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
        (u, y) :: e, rest
     | None -> 
        e, r
     | _ -> failwith "l_simplify"
     end
  | [] -> e, r

module M = Set.Make(struct
               type t = string T.exp * string T.exp
               let compare = compare
             end)
         
let simple (e, r) =
  List.sort_uniq compare e,
  List.sort_uniq compare r
         
let select memo (e, r) =
  match
    List.filter (fun (x, y) -> not (M.mem (x, y) memo || x = y)) e
    |> List.sort (fun a b -> sizep a - sizep b)
  with
  | x::_ as e ->
     (e, r), M.add x memo 
  | [] -> 
     ([], r), memo

let debug_print (e, r) =
  let () = print_endline "" in
  let () = print_endline "E" in
  let () = List.map (fun (x, y) -> U.normal_form r x, U.normal_form r y) e
           |> List.filter (fun (x, y) -> not (x = y))
           |> T.print_pairs
  in
  let () = print_endline "R" in
  let () = T.print_pairs r in e, r

let complete order eqs =
  let step memo er = 
    let er, memo = select memo er in
    er
    |> orient order
    |> l_simplify
    |> r_simplify
    |> deduce
    |> simplify_identity
    |> delete
    |> simple
    |> debug_print,
    memo
  in
  let rec iter memo er =
    match step memo er with
    | ([], r'), _ -> r'
    | er', memo ->
       iter memo er'
  in
  try
    Success (iter M.empty (eqs, []))
  with
  | Fail_exn (lhs, rhs) -> Fail (lhs, rhs)
