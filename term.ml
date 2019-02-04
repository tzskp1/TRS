module U = Utils

type 'a exp =
  | Fun of 'a * 'a exp list
  | Var of 'a

let (-->) a b = (a, b)
      
let const sym = Fun (sym, [])

let rec expand (base : 'a * 'a exp) = function
  | Fun (sym, args) ->
     Fun (sym, List.map (expand base) args)
  | Var sym ->
     let target, rep = base in
     if target = sym
     then rep
     else Var sym

let rec string_of_exp = function
  | Fun (sym, []) -> 
     sym 
  | Fun (sym, [a;b]) -> 
     String.concat "" [
         "(";
         string_of_exp a;
         " ";
         sym;
         " ";
         string_of_exp b;
         ")";
       ]
  | Fun (sym, a::args) -> 
     String.concat "" [
         sym; "(";
         string_of_exp a;
         List.fold_left (fun a b -> a ^ "," ^ b) "" (List.map (string_of_exp) args);
         ")";
       ]
  | Var sym ->
     sym
    
let print_pairs crps =
  crps
  |> List.map (fun (a,b) -> string_of_exp a ^ " --> " ^ string_of_exp b)
  |> List.iter print_endline

let rec replace exp rep path = 
  match path, exp with
  | c :: path', Fun (s, args) -> 
     begin match U.partition c args with
     | l, t :: r ->
        Fun (s, l @ replace t rep path' :: r)
     | _, _ ->
        List.map string_of_int (c :: path')
        |> List.fold_left (^) ("replace " ^ s ^ " ")
        |> failwith
     end
  | [], _ -> rep
  | p, Var s -> 
     List.map string_of_int p
     |> List.fold_left (^) ("replace " ^ s ^ " ")
     |> failwith

let rec positions = function
  | Var _ -> [[]]
  | Fun (_, args) ->
     [] :: begin
        List.map2
          begin fun c arg ->
          List.map (fun xs -> c :: xs)
            (positions arg)
          end
          (U.range (List.length args))
          args
        |> List.flatten
      end

let rec cut exp path = 
  match path, exp with
  | c :: path', Fun (_, args) -> 
     begin match U.partition c args with
     | _, t :: _ -> cut t path'
     | _ -> failwith "cut"
     end
  | [], _ -> exp
  | _, Var _ -> failwith "cut"
  
let sub_terms t = 
  positions t
  |> List.map (cut t)

let rec variables = function
  | Fun (_, args) ->
     List.map variables args
     |> List.flatten
  | Var sym -> [sym]

let rec size = function
  | Fun (_, args) ->
     List.map size args
     |> List.fold_left (+) 1
  | Var sym -> 1
