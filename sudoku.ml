open Graph.Pack.Graph;;
open Format;;

exception Found;;

(*set of legal values for a vertex *)
let domain = [1;2;3;4;5;6;7;8;9];;

(* type of vertex : x and y position in sudoku + available domain *)
type vt = {
    x: int; 
    y: int;
    mutable d: int list;
};;

(* Abstract graph type*)
module G = Graph.Imperative.Graph.Abstract(struct type t = vt end)

(* The Sudoku grid = a graph with 9x9 nodes *)
let g = G.create ();;

(* We create the 9x9 nodes, add them to the graph and keep them in a matrix 
   for later access *)
let nodes = 
    let new_node i j = let r = {x=i; y=j; d=domain} in let v = G.V.create (r) in 
    G.add_vertex g v; v in
    Array.init 9 (fun i -> Array.init 9 (new_node i))
;;

(* shortcuts for easier access *)
let node i j = nodes.(i).(j);;

(* Constraints : one value by unit, grid and row *)
let rec invalid ?(i=0) x y n = 
    i<9 && ( (G.Mark.get (node x i)) = n || (G.Mark.get (node i y)) = n || (G.Mark.get (node (x/3*3 + i/3) (y/3*3 + i mod 3))) = n || invalid ~i:(i+1) x y n )   
;;

(* remove element e from list l and returns l *)
let listRemoveElement e l = List.filter (fun x -> x <> e) l;;     

(* apply constraints on other concerned nodes - AC-3 *)
let applyInitConstraints () =
    let applyConstraints n () = 
        match (G.V.label n).d with
        | [a] -> G.iter_succ (fun vt -> (G.V.label vt).d <- listRemoveElement a (G.V.label vt).d;) g n;
        | _ -> ();
    in    
    G.iter_vertex (fun vt -> applyConstraints vt ();) g;
;;   

(* We read the initial constraints from standard input *)
let createFromStdin () =
    for i = 0 to 8 do
        let s = read_line () in
        for j = 0 to 8 do 
            match s.[j] with
            | '1'..'9' as ch -> 
                let value = (Char.code ch - Char.code '0') in
                if (invalid i j value) then failwith "invalid grid" else
                    (G.V.label (node i j)).d <- [value];
                    G.Mark.set (node i j) value;
            | _ -> ()
        done
    done
;;

(* We add the 810 constraint edges: 
   two nodes are connected whenever they can't have the same value,
   i.e. they belong to the same line, the same column or the same 3x3 group *)
let initConstraints () =
    for i = 0 to 8 do
        for j = 0 to 8 do
            for k = 0 to 8 do
                if k <> i then G.add_edge g (node i j) (node k j); 
                if k <> j then G.add_edge g (node i j) (node i k); 
            done;
            let gi = 3 * (i / 3) and gj = 3 * (j / 3) in
            for di = 0 to 2 do 
                for dj = 0 to 2 do
                    let i' = gi + di and j' = gj + dj in
                    if i' <> i || j' <> j then G.add_edge g (node i j) (node i' j'); 
                done
            done
        done 
    done    
;;     

(* Displaying the current state of the graph *)
let display () =
  for i = 0 to 8 do
    for j = 0 to 8 do printf "%d" (G.Mark.get (node i j)) done;
    printf "\n";
  done;
  printf "@?"
;;  

(* is t include in l ? *)
let varInclude t l =
	List.fold_right (fun vt vq -> (t = vt) || vq) l false;
;;   
 
(* get unassigned variables in csp *) 
let getUnassigned g = G.fold_vertex (fun vt q -> if (G.Mark.get vt = 0) then vt::q else q) g;
;;

(* minimum remaining values + degree heuristic strategy between 2 vertexes *)
let selectStrategy v1 v2 =
    if (List.length (G.V.label v1).d) = (List.length (G.V.label v2).d) then
        let nbAdjCons v = List.fold_right (fun vt q -> 
            if (varInclude (G.Mark.get v) (G.V.label vt).d) then 1 + q else q
        ) (G.succ g v) 0 in
        if ((nbAdjCons v1) <= (nbAdjCons v2)) then v1 else v2
    else if (List.length (G.V.label v1).d) < (List.length (G.V.label v2).d) then v1
    else v2
;;    

(* select the best vertex in the list : minimum remaining values + degree heuristic strategy *)
let selectVarStrategy l =
    match l with
    | [x] -> x
    | h::t -> List.fold_left (fun hs ts -> selectStrategy hs ts) h l
;; 

let nbConstraints a n = List.fold_right (fun vt q ->
    let d = (G.V.label vt).d in
    match d with
    | [x] -> q
    | _ -> if (varInclude a d) then 1 + q else q) (G.succ g n) 0
;; 

(* least constraining value *)
let orderDomainLeastConstraining n =
    List.sort (fun a b -> let nb_a = (nbConstraints a n) in let nb_b = (nbConstraints b n) in
        if (nb_a < nb_b) then -1 else
    (if (nb_a = nb_b) then 0 else 1)) ((G.V.label n).d)
;;    

(* number of test *)
let i = ref 0;;    

(*
 * Backtracking solver using no strategy
 * @param remaining assigments to do
 *)
let rec backtrack0 ltodo = 
match ltodo with
    | [] -> display (); (* Found a solution *)
    | h::t ->
        List.iter (fun n ->
            i := (!i + 1); (* test number *)
            if (not (invalid (G.V.label h).x (G.V.label h).y n)) then
                (G.Mark.set h n;
                backtrack0 t;
                G.Mark.set h 0;
        )) domain
;;

(*
 * Backtracking solver using MRV + degree heuristic + leastconstraingvalue + AC-3
 * @param remaining assigments to do
 *)
let rec backtrack1 ltodo = 
match ltodo with
    | [] -> raise Found; (* Found a solution *)
    | h::t -> let h = selectVarStrategy ltodo in
        List.iter (fun value ->
            i := (!i + 1); (* test number *)
            if (not (invalid (G.V.label h).x (G.V.label h).y value)) then
                (G.Mark.set h value;
                backtrack1 (listRemoveElement h ltodo);
                G.Mark.set h 0;
        )) (orderDomainLeastConstraining h)
;;

let solveFromStdin () =
    createFromStdin ();
    initConstraints ();
    applyInitConstraints ();
    try
        backtrack1 ((getUnassigned g) []);
    with
    | Found -> display (); printf "\nDone in %d iter \n" (!i);
;;    
solveFromStdin ();;



