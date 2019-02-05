module T = Term

let strict order x y = order x y && not (order y x)
let eq order x y = order x y && order y x

let rec lex order xs ys =
  match xs, ys with
  | x :: xs', y :: ys' -> 
     strict order x y || (eq order x y && lex order xs' ys')
  | _, [] -> true
  | _, _ -> false

let rec rpo ext order s t =
  match s, t with
  | T.Fun (ss, sa), T.Fun (ts, ta) ->
     List.exists (fun a -> rpo ext order a t) sa
     || (strict order ss ts && List.for_all (strict (rpo ext order) s) ta)
     || (eq order ss ts && ext (rpo ext order) sa ta)
  | T.Var ss, T.Var ts -> ss = ts
  | T.Var _, _ -> false
  | T.Fun _, T.Var ts -> 
     List.mem ts (T.variables s)

let more_general s t =
  s = t
  || let t' = Unification.rename (T.variables t) t in
     match Unification.solve [s, t'] with
     | Some b ->
        b s = t'
     | None -> false
