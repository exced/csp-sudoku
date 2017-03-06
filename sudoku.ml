open Graph;;
open Format;;

exception Found;;
exception Success;;
exception Failure;;

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

(* t contains l ? *)
let contains t l =
	List.fold_right (fun vt vq -> (t = vt) || vq) l false;
;;   

(* number of common elements of 2 lists *)
let nbCommonElements l1 l2 =
    List.fold_right (fun vt q -> if (List.mem vt l2) then 1 + q else q) l1 0
;;

(* how many times is a value in a list *)
let nbValsIn v l =
    List.fold_right (fun vt q -> if (v == vt) then 1 + q else q) l 0
;;    

(* apply constraints on successor nodes *)
let applyConstraintsSucc n () = 
    G.iter_succ (fun vt -> 
        let d = (G.V.label vt).d in
        if (List.length d = 1) then
            (G.Mark.set vt (List.hd d);)
        else ( if (List.length d >= 2) then
            ((G.V.label vt).d <- listRemoveElement (G.Mark.get n) d;)
        )
    ) g n;
;;

let applyInitConstraints () = G.iter_vertex (fun vt -> applyConstraintsSucc vt ();) g;
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
let initGraph () =
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

(* number of constraints on listed nodes *)
let nbConstraints g v unassigned =
    List.fold_right (fun vt q -> if (contains v unassigned) then 1 + q else q) (G.succ g v) 0 
;;

let degreeHeuristic g l =
    match l with
    | [] -> invalid_arg "empty list"
    | [x] -> x
    | h::t -> List.fold_left (fun a b -> if ((nbConstraints g a l) < (nbConstraints g b l)) then b else a) h t
;; 

(* return the node which have the smallest domain *)
let minDomain = function
    [] -> invalid_arg "empty list"
  | h::t -> List.fold_left (fun a b -> if ((List.length (G.V.label a).d) < (List.length (G.V.label b).d)) then a else b) h t
;;

(* MRV + Degree Heuristic *)
let select g l =
    match l with
    | [] -> invalid_arg "empty list"
    | _ -> let min = minDomain l in
    let mrvs = List.filter (fun x -> (List.length (G.V.label x).d) == (List.length (G.V.label min).d)) l in
    degreeHeuristic g mrvs
;;

(* least constraining value *)
let orderDomainLeastConstraining n unassigned =
    (* number of common values between domain and other nodes *)
    let nb value = List.fold_right (fun vt q -> 
        if (contains n unassigned) then nbValsIn value (G.V.label vt).d + q else q
    ) (G.succ g n) 0 in
    List.sort (fun a b -> let nb_a = (nb a) in let nb_b = (nb b) in
        if (nb_a < nb_b) then -1 else (if (nb_a = nb_b) then 0 else 1)
    ) ((G.V.label n).d)
;;    

(* number of test *)
let i = ref 0;;    

(*
 * Backtracking solver using no strategy
 * @param remaining assigments to do
 *)
let rec backtrack0 unassigned = 
match unassigned with
    | [] -> raise Found; (* Found a solution *)
    | h::t ->
        List.iter (fun n ->
            i := (!i + 1); (* iteration number *)
            if (not (invalid (G.V.label h).x (G.V.label h).y n)) then
                (G.Mark.set h n;
                backtrack0 t;
                G.Mark.set h 0;
        )) domain
;;

(*
 * Backtracking solver using MRV + degree heuristic + leastconstraingvalue without AC-3
 * @param list of remaining assigments to do
 *)
let rec backtrack1 g unassigned = 
match unassigned with
    | [] -> raise Found; (* Found a solution *)
    | _ -> let h = select g unassigned in
        List.iter (fun value ->
            i := (!i + 1); (* iteration number *)
            if (not (invalid (G.V.label h).x (G.V.label h).y value)) then (
                G.Mark.set h value;
                backtrack1 g (listRemoveElement h unassigned); (* backtrack *)
                G.Mark.set h 0;
        )) (orderDomainLeastConstraining h unassigned)
;;

(* Arcs consistency, work with a copy of the graph *)
let ac3 v g () =
    let remove_inconsistent_values xi xj =
        let removed = ref false in
        List.iter (fun x ->
            if (not ((nbCommonElements (G.V.label xj).d (G.V.label xi).d) == (List.length (G.V.label xj).d))) then
                (G.V.label xi).d <- listRemoveElement x (G.V.label xi).d;
                removed := true;
        ) (G.V.label xi).d;
        !removed
    in
    (* fill the queue with neighbors of input vertex *)
    let q = Queue.create () in
    G.iter_succ (fun v1 -> Queue.add (v, v1) q) g v;

    while (not (Queue.is_empty q)) do
        let (xi, xj) = Queue.pop q in
            match (G.V.label xi).d with
            | [] -> raise Failure;
            | _ ->
            if (remove_inconsistent_values xi xj) then
                List.iter (fun xk -> Queue.add (xk, xi) q;) (G.succ g xi);
    done
;;   

(*
 * Backtracking solver using MRV + degree heuristic + leastconstraingvalue + AC-3
 * @param graph = csp 
 * @param list of remaining assigments to do
 *)
let rec backtrack2 g unassigned = 
let gc = G.copy g in 
match unassigned with
    | [] -> raise Found; (* Found a solution *)
    | _ -> let h = select g unassigned in
        let hc = select gc ((getUnassigned gc) []) in (* copy value and scope *)
        List.iter (fun value ->
            i := (!i + 1); (* iteration number *)
            if (not (invalid (G.V.label h).x (G.V.label h).y value)) then (
                try ac3 hc gc () with 
                | Failure ->
                    G.Mark.set h 0;
                | _ ->                    
                    G.Mark.set h value;
                    backtrack1 g (listRemoveElement h unassigned); (* backtrack *)    
        )) (orderDomainLeastConstraining h unassigned)
;;

let solveFromStdin () =
    createFromStdin ();
    initGraph ();
    applyInitConstraints ();
;;

(* We solve the Sudoku by 9-coloring the graph *)
module C = Coloring.Mark(G)

let main () =
    try
        solveFromStdin ();
        if (Array.length Sys.argv >= 2) then (
            match Sys.argv.(1) with
            | "0" -> printf "Simple Backtrack:\n"; backtrack0 ((getUnassigned g) []);
            | "1" -> printf "Backtrack with MRV + DH + LCV:\n"; backtrack1 g ((getUnassigned g) []);
            | "2" -> printf "Backtrack with MRV + DH + LCV + AC3 strategies:\n"; backtrack2 g ((getUnassigned g) []);
            | "c" -> printf "Graph coloring:\n"; C.coloring g 9; display ();
            | _ -> printf "help : ./sudoku 1 <grids/grid1"
        )
    with
    | Found -> display (); printf "\nDone in %d iter \n" (!i);
;;
main ();; 
