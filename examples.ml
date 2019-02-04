open Term
open Unification
open Completion
   
module Examples = 
  struct 
    let x = Var "x"
    let y = Var "y"
    let z = Var "z"
    let f x = Fun ("f", [x])
    let g x y = Fun ("g", [x; y])
    let a = const "a"
    let example1 = [
        x --> f a;
        g x x --> g x y;
      ]
    let example1_sol = solve example1
    let m x y = Fun ("*", [x;y])
    let i x = Fun ("i", [x])
    let e = const "e"
    let () = [
        m (m x y) z --> m x (m y z);
        m (i x) x --> e;
      ]
      |> critical_pairs 
      |> print_pairs 
  end 

module CombinatoryLogic =
  struct
    let x = Var "x"
    let y = Var "y"
    let z = Var "z"
    let ( * ) a b = Fun (".", [a;b])
    let k a b = (const "K" * a) * b
    let s x y z = ((const "S" * x) * y) * z
    let () = [
        s x y z --> (x * z) * (y * z);
        k x y --> x;
      ]
      |> critical_pairs 
      |> print_pairs 
  end

module Test1 = 
  struct
    let x = Var "x"
    let f x = Fun ("f", [x])
    let g x = Fun ("g", [x])
    let () = [
        f (g (f x)) --> x;
        f (g x) --> g (f x);
      ]
      |> critical_pairs 
      |> print_pairs 
  end

module Test2 =
  struct 
    let (+) a b = Fun ("+", [a; b])
    let x = Var "x"
    let y = Var "y"
    let s x = Fun ("s", [x])
    let () = [
        const "0" + y --> y;
        x + const "0" --> x;
        s x + y --> s (x + y);
        x + s y --> s (x + y);
      ]
      |> critical_pairs 
      |> print_pairs 
  end

module Test3 =
  struct 
    let x = Var "x"
    let a = const "a"
    let b = const "b"
    let f x y = Fun ("f", [x;y])
    let g x = Fun ("g", [x])
    let () = [
        f x x --> a;
        f x (g x) --> b;
      ]
      |> critical_pairs 
      |> print_pairs 
  end

module Test4 =
  struct 
    let x = Var "x"
    let y = Var "y"
    let z = Var "z"
    let f x y = Fun ("f", [x;y])
    let () = [
        f (f x y) z --> f x (f y z);
        f x (const "1") --> x;
      ]
      |> critical_pairs 
      |> print_pairs 
    let () = [
        f (f x y) z --> f x (f y z);
        f (const "1") x --> x;
      ]
      |> critical_pairs 
      |> print_pairs 
  end

module Test5 =
  struct 
    let x = Var "x"
    let y = Var "y"
    let z = Var "z"
    let f x y = Fun ("f", [x;y])
    let () = [
        f x (f y z) --> f (f x y) (f x z);
        f (f x y) z --> f (f x z) (f y z);
        f (f x y) (f y z) --> y;
      ]
      |> critical_pairs 
      |> print_pairs 
  end

module Or =
  struct
    let x = Var "x"
    let y = Var "y"
    let or' x y = Fun("or", [x;y])
    let () = [
        or' (const "true") (const "true") --> const "true";
        or' x y --> or' y x;
      ]
      |> critical_pairs 
      |> print_pairs 
  end

module Ex618 =
  struct
    let x = Var "x"
    let y = Var "y"
    let a = const "a"
    let b = const "b"
    let c = const "c"
    let d = const "d"
    let f x = Fun ("f", [x])
    let g x y z = Fun ("g", [x;y;z])
    let h x y = Fun ("h", [x;y])
    let p x = Fun ("p", [x])
    let q x = Fun ("q", [x])
    let not_confluent = [
        f (g x a b) --> x;
        g (f (h c d)) x y --> h (p x) (q x);
        p a --> c;
        q b --> d;
      ]
    let confluent = [
        f (g x a b) --> x;
        g (f (h c d)) x y --> h (p x) (q y);
        p a --> c;
        q b --> d;
      ]
    let () = 
      confluent
      |> critical_pairs 
      |> print_pairs 
  end

module Ex619b =
  struct
    let x = Var "x"
    let y = Var "y"
    let or' x y = Fun("or", [x;y])
    let not' x = Fun("not", [x])
    let () = [
        or' (const "true") x --> or' x (not' x);
        or' x (const "true") --> or' (not' x) x;
        or' x y --> or' y x;
      ]
      |> critical_pairs 
      |> print_pairs 
  end

let x = Var "x"
let y = Var "y"
let f x y = Fun ("f", [x;y])
let t = f (f x x) x
let pos = positions t
let () = print_endline ""
let rep = List.map (replace t y) pos
let () = List.map string_of_exp rep
         |> List.iter print_endline
let subs = sub_terms t
let () = List.map string_of_exp subs
         |> List.iter print_endline
       
       
module Group =
  struct
    let x = Var "x"
    let y = Var "y"
    let z = Var "z"
    let ( * ) a b = Fun ("*", [a;b])
    let i x = Fun ("i", [x])
    let e = Fun ("e", [])
    let axioms = [
        (x * y) * z --> x * (y * z);
        (i x) * x --> e;
        e * x --> x;
      ]
    let axioms' = [
        (x * y) * z --> x * (y * z);
        x * (i x) --> e;
        e * x --> x;
      ]
    let order = Orders.strict (Orders.rpo Orders.lex (fun sx sy -> sx = sy || sx = "i" || sy = "e"))
    let () = axioms
      |> critical_pairs 
      |> print_pairs 
    (* let () = 
     *   match complete order axioms' with
     *   | Success p ->
     *      print_string "results: ";
     *      print_pairs p
     *   | Fail (lhs, rhs) ->
     *      print_string "fail : ";
     *      print_pairs [lhs, rhs] *)
    let Success rules = complete order axioms
    let () = print_pairs rules 
    let check (s, t) =
      let () = 
      normal_form rules s
      |> string_of_exp
      |> print_endline;
      normal_form rules t
      |> string_of_exp
      |> print_endline
      in
      normal_form rules s = normal_form rules t
    let eqs = [
        (i x) * x, x * (i x);
      ]
    let () = eqs
             |> List.map check
             |> List.map string_of_bool
             |> List.iter print_endline
  end
