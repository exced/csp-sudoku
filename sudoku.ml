open Graph;;
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

(* remove assigned variables *)
let removeAssigned l = List.filter (fun x -> (G.Mark.get x) = 0) l;;

(* set the mark for the nodes which have singleton domain *)
let markSingletons ltodo () = List.iter (fun vt ->
    match (G.V.label vt).d with
       | [a] -> G.Mark.set vt a;
       | _ -> ()
    ) ltodo
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

(* apply constraints on listed nodes *)
let applyConstraints n ltodo =
    List.iter (fun vt ->
    if (List.length (G.V.label vt).d >= 2) then
        if ( (G.V.label n).x = (G.V.label vt).x || (G.V.label n).y = (G.V.label vt).y || ((G.V.label n).x/3*3 = (G.V.label vt).x/3*3 && (G.V.label n).y/3*3 = (G.V.label vt).y/3*3) ) then
             (G.V.label vt).d <- listRemoveElement (G.Mark.get n) (G.V.label vt).d;
    ) ltodo
;;

(* release constraints on listed nodes *)
let releaseConstraints n ltodo =
    List.iter (fun vt ->
        if ( (G.V.label n).x = (G.V.label vt).x || (G.V.label n).y = (G.V.label vt).y || ((G.V.label n).x/3*3 = (G.V.label vt).x/3*3 && (G.V.label n).y/3*3 = (G.V.label vt).y/3*3) ) then
            (G.V.label vt).d <- (G.V.label vt).d@[(G.Mark.get n)];
    ) ltodo
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

(* least constraining value *)
let orderDomainLeastConstraining n ltodo =
    let nbConstraints a n = List.fold_right (fun vt q ->
        if (((G.V.label vt).x = (G.V.label n).x) || ((G.V.label vt).y = (G.V.label n).y)) then
            (let d = (G.V.label vt).d in
            match d with
            | [x] -> q
            | _ -> if (varInclude a d) then 1 + q else q)
        else 0)            
        ltodo 0
    in        
    List.sort (fun a b -> let nb_a = (nbConstraints a n) in let nb_b = (nbConstraints b n) in
    if (nb_a < nb_b) then -1 else (if (nb_a = nb_b) then 0 else 1)) ((G.V.label n).d)
;;    

(* number of test *)
let i = ref 0;;    

(*
 * Backtracking solver using no strategy
 * @param remaining assigments to do
 *)
let rec backtrack0 ltodo = 
match ltodo with
    | [] -> raise Found; (* Found a solution *)
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
let printIntList l = List.map (fun v -> printf "%d , " v;) l;;
let displayDomain { x = x; y = y; d = d } () = List.map (fun v -> printf "%d, " v) d;;
let displayVertex { x = x; y = y; d = d } () = printf "|x: %d, y: %d, d:" x y; displayDomain { x = x; y = y; d = d } ();;
let displayVertexes () = G.iter_vertex (fun vt -> displayVertex (G.V.label vt) (); printf "\n";) g;;
let printVertexesList l = List.map (fun v -> printf "|x: %d, y: %d, mark: %d, d: " (G.V.label v).x (G.V.label v).y (G.Mark.get v); displayDomain (G.V.label v) (); ();) l;;
let displayEdge v () = G.iter_succ (fun v2 -> displayVertex (G.V.label v) (); printf " -- "; displayVertex (G.V.label v2) (); printf "\n";) g v;;
let displayEdges () = G.iter_edges (fun v1 v2 -> displayVertex (G.V.label v1) (); printf " -- "; displayVertex (G.V.label v2) (); printf "\n";) g;;
let displayDomains () =
    for i = 0 to 8 do
        for j = 0 to 8 do
            printf "---- i: %d, j: %d ------\n" i j;
            printf "["; 
            displayDomain (G.V.label (node i j)) ();
            printf "]\n";
        done;
    done
;;    
*)

(*
 * Backtracking solver using MRV + degree heuristic + leastconstraingvalue + AC-3
 * @param list of remaining assigments to do
 *)
let rec backtrack1 ltodo = 
match ltodo with
    | [] -> raise Found; (* Found a solution *)
    | _ -> let h = selectVarStrategy ltodo in
        List.iter (fun value ->
            i := (!i + 1); (* test number *)
            (*printf "\n i: %d" !i;*)
            (*printf "\n Length ltodo %d" (List.length ltodo);*)
            if (not (invalid (G.V.label h).x (G.V.label h).y value)) then
                (G.Mark.set h value;
                applyConstraints h ltodo;
                backtrack1 (listRemoveElement h ltodo); (* backtrack *)
                releaseConstraints h ltodo;
                G.Mark.set h 0;
        )) (orderDomainLeastConstraining h ltodo)
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
            | "1" -> printf "Backtrack with MRV + DH + LCV + AC3 strategies:\n"; backtrack1 ((getUnassigned g) []);
            | "2" -> printf "Graph coloring:\n"; C.coloring g 9; display ();
            | _ -> printf "help :"
        )
    with
    | Found -> display (); printf "\nDone in %d iter \n" (!i);
;;
main ();; 
