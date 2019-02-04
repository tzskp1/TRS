type term = { label: string;
              succs: term list;
              rep: term ref;}
type subterm = term list

let rec cart xs ys =
  match (xs,ys) with
  | (_,[]) | ([],_) -> []
  | (x::xs,ys) ->
     (List.map (fun y -> (x,y)) ys) @ cart xs ys

let rec string_of_term (t: term) =
  t.label ^
  match t.succs with
  | [] -> ""
  | x :: xs -> List.fold_left(fun res a -> res ^ "," ^ (string_of_term a)) ("(" ^ string_of_term x) xs ^ ")"

let rec find (tr: term) =
  if !(tr.rep) == tr then
    tr.rep
  else
    find !(tr.rep)

let make_term (label:string) (succs: term list) =
  let rec tmp = {label=label;succs=succs;rep=ref tmp} in tmp

let equals (a: term) (b: term) =
  !(find a) == !(find b)

let contains (tr: term) (a: term) = 
  List.exists (fun k -> equals k a) tr.succs 

let rec preds (g: subterm) (a: term) =
  List.filter (fun t -> contains t a) g

let rec length (t: term) =
  if !(t.rep) == t then
    0
  else
    1 + length !(t.rep)

let union (a: term) (b: term) =
  if length a > length b then
    find a := !(find b)
  else 
    find b := !(find a)

let congruent (p: term) (q: term) =
  p.label = q.label &&
    List.length p.succs = List.length q.succs &&
    List.map2 (fun u v -> (u,v)) p.succs q.succs
    |> List.for_all (fun (u,v) -> equals u v)

let rec merge (c: subterm) (a: term) (b: term) =
  if not (equals a b) then
    let () = union a b in
    let p = preds c a in
    let q = preds c b in
    cart p q
    |> List.iter
         begin fun (p,q) ->
         if (not (equals p q)) && (congruent p q) then
           merge c p q
         end

let rec subterms (t: term) =
  t :: List.concat (List.map (fun t -> subterms t) t.succs)

let subterms_of_eq (lhs,rhs:term*term) =
  subterms lhs @ subterms rhs

let constants (g: subterm) =
  List.filter (fun t -> t.succs = []) g

let initialize (g: subterm) =
  let consts = constants g in
  let identified = cart consts consts
                   |> List.filter (fun (a,b) ->
                          a.label = b.label &&
                            a.succs = [] && b.succs = []) in
  List.iter (fun (a,b) -> merge g a b) identified

let rec terma = {label="a";succs=[];rep=ref terma}
let rec termf1 = {label="f";succs=[terma];rep=ref termf1}
let rec termf2 = {label="f";succs=[termf1];rep=ref termf2}
let rec termf3 = {label="f";succs=[termf2];rep=ref termf3}
let rec termf4 = {label="f";succs=[termf3];rep=ref termf4}
let rec termf5 = {label="f";succs=[termf4];rep=ref termf5}

(* let rec terma1 = {label="a";succs=[];rep=ref terma1}
 * let rec terma2 = {label="a";succs=[];rep=ref terma2}
 * let rec termg1 = {label="g";succs=[terma1];rep=ref termg1}
 * let rec termg2 = {label="g";succs=[terma2];rep=ref termg2}
 * let rec termf = {label="f";succs=[termg1;termg2];rep=ref termf} *)

let congruence_clojure (eqs:(term * term) list) =
  let subs = List.map subterms_of_eq eqs
             |> List.concat in
  let () = initialize subs in
  List.iter (fun (lhs,rhs) -> merge subs lhs rhs) eqs

let () = congruence_clojure [(termf5,terma);(termf3,terma)]
let test = equals termf1 terma
