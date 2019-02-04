let range cnt =
  let rec iter cnt =
    if cnt = 0
    then []
    else cnt :: iter (cnt - 1)
  in List.rev (iter cnt)
   
let partition cnt ls =
  let l,r = 
    List.combine ls (range (List.length ls))
    |> List.partition (fun (_,c) -> c < cnt)  
  in List.map fst l, List.map fst r

let rec prod = function
  | [] -> []
  | x :: xs ->
     List.map (fun y -> (x,y)) xs @ prod xs
    
