open Graph;;
open Format;;

exception Found;;
exception False;;
exception Failure;;
exception Success;;

(* set of legal values for a vertex *)
let all_domain = [1;2;3;4;5;6;7;8;9];;

(* type of vertex : x and y position in sudoku + available domain *)
type vt = {
    x: int;
    y: int;
    mutable d: int list;
    mutable backup: int list;
};;

(* Abstract graph type *)
module G = Graph.Imperative.Graph.Abstract(struct type t = vt end)

(* The Sudoku grid = a graph with 9x9 nodes *)
let g = G.create ();;

(* We create the 9x9 nodes, add them to the graph and keep them in a matrix for later access *)
let nodes = 
    let new_node i j = let r = {x=i; y=j; d=all_domain; backup=all_domain} in let v = G.V.create (r) in 
    G.add_vertex g v; v in
    Array.init 9 (fun i -> Array.init 9 (new_node i))
;;

(* shortcuts for easier access *)
let node i j = nodes.(i).(j);;

(* shortcut for access domain : return 0 if not singleton *)
let domain v =
    match (G.V.label v).d with
    | [a] -> a
    | _ -> 0
;;

(* Constraints : one value by unit, grid and row *)
let rec invalid ?(i=0) x y n = 
    i<9 && ( (domain (node x i)) = n || (domain (node i y)) = n || (domain (node (x/3*3 + i/3) (y/3*3 + i mod 3))) = n || invalid ~i:(i+1) x y n )   
;;

(* remove element e from list l and returns l *)
let listRemoveElement e l = List.filter (fun x -> x <> e) l;;

(* t contains l ? *)
let contains t l =
	List.fold_right (fun vt vq -> (t = vt) || vq) l false;
;;   

(* how many times is a value in a list *)
let nbValsIn v l =
    List.fold_right (fun vt q -> if (v = vt) then 1 + q else q) l 0
;;    

(* apply constraints on successor nodes *)
let applyConstraintsSucc n () = 
    G.iter_succ (fun vt -> 
        let d = (G.V.label vt).d in
        if (List.length d = 1) then
            (G.Mark.set vt (List.hd d);)
        else ( if (List.length d >= 2) then
            ((G.V.label vt).d <- listRemoveElement (domain n) d;
            (G.V.label vt).backup <- (G.V.label vt).d;
            )
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
                    (G.V.label (node i j)).backup <- [value];
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
    for j = 0 to 8 do
        printf "%d" (domain (node i j)) 
    done;
    printf "\n";
  done;
  printf "@?"
;;   
 
(* get unassigned variables in csp *) 
let getUnassigned g = G.fold_vertex (fun vt q -> if (domain vt = 0) then vt::q else q) g;
;;

(* number of constraints on listed nodes *)
let nbConstraints g v unassigned =
    List.fold_right (fun vt q -> if ((contains v unassigned) && (domain v) != 0) then 1 + q else q) (G.succ g v) 0 
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
    let mrvs = List.filter (fun x -> (List.length (G.V.label x).d) = (List.length (G.V.label min).d)) l in
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
        let backupDomain = (G.V.label h).d in
        List.iter (fun value ->
            i := (!i + 1); (* iteration number *)
            if (not (invalid (G.V.label h).x (G.V.label h).y value)) then
                ((G.V.label h).d <- [value];
                backtrack0 t;
                (G.V.label h).d <- backupDomain;
        )) all_domain
;;

(*
 * Backtracking solver using MRV + degree heuristic + leastconstraingvalue without AC-3
 * @param list of remaining assigments to do
 *)
let rec backtrack1 g unassigned = 
match unassigned with
    | [] -> raise Found; (* Found a solution *)
    | _ -> let h = select g unassigned in
        let backupDomain = (G.V.label h).d in
        List.iter (fun value ->
            i := (!i + 1); (* iteration number *)
            if (not (invalid (G.V.label h).x (G.V.label h).y value)) then (
                (G.V.label h).d <- [value];
                backtrack1 g (listRemoveElement h unassigned); (* backtrack *)
                (G.V.label h).d <- backupDomain;
        )) (orderDomainLeastConstraining h unassigned)
;;

(* Arcs consistency *)
let ac3 g () =
    let remove_inconsistent_values xi xj =
        let removed = ref false in
        List.iter (fun x ->
            match (G.V.label xj).d with
            | [y] -> if (y = x) then (
                if (List.length (G.V.label xi).d = 1) then
                    (raise Failure;)
                else
                    (G.V.label xi).d <- listRemoveElement x (G.V.label xi).d; removed := true)
            | _ -> ()
        ) (G.V.label xi).d;
        !removed
    in
    (* fill the queue with all constraints *)
    let queue = Queue.create () in
    G.iter_edges (fun xi xj -> Queue.add (xi, xj) queue;) g;

    while (not (Queue.is_empty queue)) do
        let (xi, xj) = Queue.pop queue in
        if (remove_inconsistent_values xi xj) then
            List.iter (fun xk -> Queue.add (xk, xi) queue;) (G.succ g xi);
    done;
    raise Success;
;;

let doBackup unassigned () =
    List.iter (fun v ->
        (G.V.label v).d <- (G.V.label v).backup;
    ) unassigned;
;;

(*
 * Backtracking solver using MRV + degree heuristic + leastconstraingvalue + AC-3
 * @param graph = csp 
 * @param list of remaining assigments to do
 *)
let rec backtrack2 g unassigned =
match unassigned with
    | [] -> raise Found; (* Found a solution *)
    | _ -> let h = select g unassigned in
        List.iter (fun value ->
            i := (!i + 1); (* iteration number *)
            (G.V.label h).d <- [value];
            try (ac3 g ()) with
            | Failure -> doBackup unassigned ();
            | Success -> backtrack2 g (listRemoveElement h unassigned); (* backtrack *)
        ) (orderDomainLeastConstraining h unassigned)
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
            | "2" -> printf "Backtrack with MRV + DH + LCV + AC3 strategies:\n"; backtrack2 g ((getUnassigned g) []); display ();
            | "c" -> printf "Graph coloring:\n"; C.coloring g 9; display ();
            | _ -> printf "help : ./sudoku 1 <grids/grid1"
        )
    with
    | Found -> display (); printf "\nDone in %d iter \n" (!i);
;;
main ();; 
