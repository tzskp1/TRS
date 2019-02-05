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

let sizep (a, b) = T.size a + T.size b

let sort_by_size x = List.fast_sort (fun a b -> sizep a - sizep b) x

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
  (* match e with
   * | (x, y) :: e ->
   *    (U.normal_form r x, U.normal_form r y) :: e, r, memo
   * | [] -> e, r, memo *)

let deduce (e, r, memo) =
  U.critical_pairs r @ e,
  r,
  List.fold_left (fun m x -> M.add x m) memo r

let r_simplify (e, r, memo) =
  match List.rev (sort_by_size r) with
  | (x, y) :: rest ->
     let xy' = x, U.normal_form rest y in
     let memo' = if M.mem (x, y) memo then M.add xy' memo else memo in
     e, xy' :: rest, memo'
  | [] -> e, r, memo

let l_simplify_org (e, r, memo) =
  match (List.sort (fun a b -> sizep b - sizep a) r) with
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
      
let l_simplify (e, r, memo) =
  let rec iter acc memo e = function
    | (x, y) :: rest ->
       begin match 
         List.map
           begin fun (l, r) ->
           match U.rewrite (l, r) x, U.rewrite (x, y) l with
           | u::_, [] -> Some u
           | _, _ -> None
           end
           (acc @ rest)
         |> List.find_opt (function Some _ -> true | None  -> false)
       with
       | Some (Some u) ->
          (u, y) :: e, acc @ rest, memo 
       | None ->
          iter ((x, y) :: acc) memo e rest
       | _ -> failwith "l_simplify"
       end
    | [] -> e, acc, memo
  in iter [] memo e r
         
let select (e, r, memo) =
  sort_by_size e, r, memo
  
let mgenp (x, y) (x', y') = Orders.more_general x x' && Orders.more_general y y'
  
let rec filter_by_generality = function
  | (x, y) :: e ->
     (x, y)
     :: begin
        e
        |> List.filter
             begin fun (x', y') ->
             not (mgenp (x, y) (x', y'))
             end
        |> filter_by_generality
      end
  | [] -> []

let symm_compare (l, r) (l', r') =
  compare (l, l') (r, r') * compare (l, r') (r, l')
        
let simple (e, r, memo) =
  List.sort_uniq symm_compare e
  |> List.sort (fun a b -> if mgenp a b then 1 else -1)
  |> filter_by_generality
  |> sort_by_size,
  List.sort_uniq compare r
  |> List.sort (fun a b -> if mgenp a b then 1 else -1)
  |> filter_by_generality
  |> sort_by_size,
  memo

let debug_print (e, r, memo) =
  let () = print_endline "";
           print_endline "E";
           T.print_pairs e;
           print_endline "R";
           T.print_pairs r
  in e, r, memo
                            
let step order er = 
  select er
  |> orient order
  |> r_simplify
  |> l_simplify
  |> deduce
  |> simplify_identity
  |> delete
  |> simple

let complete order eqs =
  let rec iter er =
    match step order er with
    | [], r', memo ->
       if List.for_all (fun x -> M.mem x memo) r'
       then r'
       else iter ([], r', memo)
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
         
let complete_lazy order eqs =
  let rec iter er =
    match step order er with
    | [], r', _ -> of_list r'
    | e, r, memo ->
       concat
         (sort_by_size r
          |> List.filter (fun xy -> M.mem xy memo))
         (lazy (iter (e, r, memo)))
  in iter (eqs, [], M.empty)

let rec check_eq eqs (x, y) = 
  (* let eqs = map (fun (x, y) -> let () = T.string_of_exp x ^ " " ^ T.string_of_exp y |> print_endline in x, y) eqs in *)
  let redex = map U.rewrite eqs
              |> map (fun f -> f x, f y) in
  (* let redex = map (fun (x, y) ->
   *                 let () =
   *                   print_endline "x";
   *                   List.map T.string_of_exp x
   *                   |> List.iter print_endline;
   *                   print_endline "y";
   *                   List.map T.string_of_exp y
   *                   |> List.iter print_endline
   *                   in x, y) redex in *)
  let rec traverse = function
    | Cons (([], []), lazy r) ->
       traverse r
    | Cons (([], y::_), lazy r) ->
       check_eq eqs (x, y)
    | Cons ((x::_, []), lazy r) ->
       check_eq eqs (x, y)
    | Cons ((x::_, y::_), lazy r) ->
       check_eq eqs (x, y)
    | Nil -> false
  in x = y || traverse redex
