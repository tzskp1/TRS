module T = Term
module U = Utils

let delete eqs = List.filter (function (lhs, rhs) -> not (lhs = rhs)) eqs 

let decompose eqs =
  let rec iter acc = function
  | (T.Fun (ls, la), T.Fun (rs, ra)) :: rest when ls = rs ->
     iter (List.map2 (fun a b -> (a, b)) la ra @ acc) rest
  | eq :: rest ->
     iter (eq :: acc) rest
  | [] -> acc
  in iter [] eqs 

let orient eqs =
  let rec iter acc = function
  | ((T.Fun _ as lhs), (T.Var _ as rhs)) :: rest ->
     iter ((rhs, lhs) :: acc) rest
  | eq :: rest ->
     iter (eq :: acc) rest
  | [] -> acc
  in iter [] eqs 

let variables_eqs eqs =
  List.map (function (a,b) -> T.variables a @ T.variables b) eqs
  |> List.flatten
                      
let apply_eq f =
  function (a, b) -> (f a, f b)
  
let eliminate eqs =
  let rec iter acc = function
    | (T.Var x, rhs) as eq :: rest
         when List.mem x (variables_eqs rest) && not (List.mem x (T.variables rhs)) ->
       iter (eq :: acc) (List.map (apply_eq (T.expand (x, rhs))) rest)
  | eq :: rest ->
     iter (eq :: acc) rest
  | [] -> acc
  in iter [] eqs 

let eq_simplified_eqs (l, r) (l', r') =
  match l, l' with
  | T.Var s, T.Var s' ->
     r = T.expand (s', T.Var s) r'
  | _, _ -> failwith "error: eq_eqs"

let eq_list a b =
  let a' = List.sort compare a in
  let b' = List.sort compare b in
  List.length a = List.length b
  && List.fold_left (&&) true (List.map2 (=) a' b')
  
let fresh xs =
  List.hd xs ^ string_of_int (List.length xs)

let comp_subst a b exp =
  T.expand b (a exp)

let rename vars = 
  let rec iter vars subst = function
    | sym :: rest ->
      let sym' = fresh (sym::vars) in
      iter (sym'::sym::vars) (comp_subst subst (sym, Var sym')) rest
    | [] -> subst
  in iter vars (fun a -> a) vars

let simplify eqs =
  let rec fixed eqs =
    let eqs' =
      eqs
      |> eliminate
      |> delete
      |> decompose
      |> orient
    in
    if eq_list eqs' eqs
    then eqs'
    else fixed eqs'
  in fixed eqs
              
let solve eqs =
  let rec iter acc acc' = function
    | (T.Var x, t) :: rest ->
       iter
         (not (List.mem x (T.variables t))
          && not (List.mem x (variables_eqs rest))
          && acc)
         ((x, t) :: acc')
         rest
    | [] -> if acc then acc' else []
    | _ -> []
  in
  let solved_form = iter true [] in
  match
    simplify eqs
    |> solved_form
  with
  | [] -> None
  | substs -> Some (List.fold_left comp_subst (fun a -> a) substs)

let critical_pair (l, r) (l', r') =
  let match' l r =
    let rec iter acc l = 
      if l = r
      then [List.rev acc, fun a -> a]
      else match solve [l, r], l with
      | _, Var _ -> []
      | None, Fun (s, args) -> 
         List.map2 (fun c a -> iter (c :: acc) a)
           (U.range (List.length args))
           args 
         |> List.flatten
      | Some unifier, _ ->  
         [List.rev acc, unifier]
    in iter [] l
  in     
  match match' l l' with
  | (path, unifier) :: _ ->
     Some (unifier r, T.replace (unifier l) (unifier r') path)
  | [] -> None
  
let rec critical_pairs eqs =
  let cp eq eq' =
    let req' = apply_eq (rename (variables_eqs [eq])) eq'
    in match critical_pair eq req' with
       | Some x -> [x]
       | None -> []
  in
  eqs
  |> List.map
       begin fun eq -> 
       List.map (cp eq) eqs
       |> List.flatten
       end
  |> List.flatten
  |> List.filter (fun (a,b) -> not (a = b))
  
let rec recover s = function
  | T.Fun (s', []) when s = s' ->
     T.Var s
  | T.Fun (s', args) -> 
     T.Fun (s', List.map (recover s) args)
  | T.Var s' -> T.Var s'

let temporary_save e = 
  let vars = T.variables e in
  let subst = List.map (fun s -> s, T.Fun(s, [])) vars
              |> List.fold_left comp_subst (fun a -> a) in
  let recover = List.map recover vars
                |> List.fold_left (fun f g x -> f (g x)) (fun a -> a) in
  recover, subst e 

let rec rewrite (l, r) s =
  T.positions s
  |> List.map
       begin fun p ->
       let recover, l' = temporary_save (T.cut s p) in
       if l' = l
       then [T.replace s r p]
       else match solve [l', l] with
            | Some subst ->
               [T.replace s (recover (subst r)) p]
            | None -> []
       end
  |> List.flatten
  |> List.filter (fun y -> not (s = y))
       
let rec normal_form eqs x = 
  match
    List.map rewrite eqs
    |> List.map (fun f -> f x)
    |> List.flatten
  with
  | r :: _ -> normal_form eqs r
  | [] -> x
