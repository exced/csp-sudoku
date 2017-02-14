open Graph.Pack.Graph;;
open Format;;

exception Fail;;

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

(* remove element e from list l and returns l *)
let listRemoveElement e l = List.filter (fun x -> x <> e) l;; 

(* set domain and apply constraints on other concerned nodes *)
let setDomain n d () = 
    (G.V.label n).d <- d;
    match d with
    | [a] -> G.iter_succ (fun vt -> (G.V.label vt).d <- listRemoveElement a (G.V.label vt).d;) g n;
    | _ -> ();
;;

(* We read the initial constraints from standard input *)
let createFromStdin () =
    for i = 0 to 8 do
        let s = read_line () in
        for j = 0 to 8 do 
            match s.[j] with
            | '1'..'9' as ch -> (G.V.label (node i j)).d <- [(Char.code ch - Char.code '0')];
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

let applyInitConstraints () =
    G.iter_vertex (fun vt -> setDomain vt (G.V.label vt).d ();) g;
;;        

(*
 * Constraints: is n value invalid ? check line, row and unit.
*) 
let rec valid ?(i=0) n value =
    let x = (G.V.label n).x in let y = (G.V.label n).y in
    not (i<9 && ( (G.V.label (node y i)).d = [value] || (G.V.label (node i x)).d = [value] || (G.V.label (node (y/3*3 + i/3) (x/3*3 + i mod 3))).d = [value] || valid ~i:(i+1) n value ))
;;    

let isConsistent val l = 
    List.fold_right (fun vt vq -> (valid vt val) && vq) l true;
;;    
 
(* get unassigned variables in csp *) 
let getAssigned g =
    G.fold_vertex (fun vt q -> 
        match (G.V.label vt).d  with
        | [a] -> vt::q
        | _ -> q
    ) g;
;;    

(* minimum remaining values + degree heuristic strategy *)
let selectStrategy v1 v2 =
    if (List.length (G.V.label v1).d) = (List.length (G.V.label v2).d) then
        let nbConsRestCsp v = G.fold_succ (fun vt q -> List.length (G.V.label vt).d + q) g v in 
        if (nbConsRestCsp v1) <= (nbConsRestCsp v2) then v1 else v2
    else if (List.length (G.V.label v1).d) < (List.length (G.V.label v2).d) then v1
    else v2
;;    

let selectVarStrategy l =
    match l with
    | [x] -> x
    | h::t -> List.fold_left (fun hs ts -> selectStrategy hs ts) h t
;;    

(* is t include in l ? *)
let varInclude t l =
	List.fold_right (fun vt vq -> (t = vt) || vq) l false;
;;


let nbConstraints a n = List.fold_right (fun vt q ->
    let d = (G.V.label vt).d in
    match d with
    | [x] -> q
    | _ ->
        if (varInclude a d) then 1 + q else q) (G.succ g n) 0;; 

(* least constraining value *)
let orderDomainLeastConstraining n =
    List.sort (fun a b -> if ((nbConstraints a n) > (nbConstraints b n)) then -1 else
    (if (nbConstraints a n) < (nbConstraints b n) then 1 else 0)) ((G.V.label n).d)
;;    

(*
 * Backtracking solver
 * @param lrem = list of unassigned variables
 * @param g = csp
 *)
let rec backtrack l () =
    if (List.length l = 81) then () else
        let var = selectVarStrategy l in 
        let ldom = orderDomainLeastConstraining var in
        let rec recdomain ldom =
            match ldom with
            | [] -> raise Failure
            | h::t -> if (isConsistent h l) then
                (*setDomain var [h] ();*)
                let recbacktrack = backtrack (listRemoveElement var l) () in
                try recbacktrack  with
                | Failure -> ()
                | _ -> recbacktrack
    in recdomain 
;;    


(* Displaying the current state of the graph *)
let display () =
    for i = 0 to 8 do
        for j = 0 to 8 do
            let s =
            match (G.V.label (node i j)).d with
            | [a] -> string_of_int a
            | _ -> "."
            in
            printf "%s" s done;
        printf "\n";
    done
;;

let printIntList l = List.map (fun v -> printf "%d , " v;) l;;
let displayDomain { x = x; y = y; d = d } () = List.map (fun v -> printf "%d, " v) d;;
let displayVertex { x = x; y = y; d = d } () = printf "x: %d, y: %d, |d:" x y; displayDomain { x = x; y = y; d = d } ();;
let displayVertexes () = G.iter_vertex (fun vt -> displayVertex (G.V.label vt) (); printf "\n";) g;;
let printVertexesList l = List.map (fun v -> printf "x: %d, y: %d, " (G.V.label v).x (G.V.label v).y; ();) l;;
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

(*
 * ac3
 *)
 (*
let ac3 () =
    List.fold_right (
        fun (xi, xj) q1 -> if (rmInconsistentValues xi xj) then 
            List.fold_right (fun xk q2 -> q1@[(xk, xi)]) (G.find_all_edges g xk xi) ()
    ) arcsQ ();
;;
*)
(*
let rmInconsistentValues xi xj = 

;;    
*)

 let solveFromStdin () =
    createFromStdin ();
    initConstraints ();
    applyInitConstraints ();
    display (); 
    try backtrack ((getAssigned g) []) (); with
    | Failure -> printf "backtrack failure";
    | _ -> display ();
;;    
solveFromStdin ();;

(*
displayEdge (node 0 0) ();;

displayVertex (G.V.label (node 0 0)) ();;
let nb = nbConstraints 9 (node 0 0);;
printf "nbConstraint %d : \n\n" nb;;   

let l = orderDomainLeastConstraining (node 0 0);;
printIntList l;;
*)

(*
printVertexesList ((getAssigned g) []);
displayDomains ();;
displayEdge (node 0 0) ();;
*)


