From Coq Require Import List ZArith Lia.
Import ListNotations.

Module MarginCollapse.

(* === BASIC DATA TYPES === *)

Record Box := mkBox {
  mt : Z;      (* margin-top *)
  mb : Z;      (* margin-bottom *)
  h  : Z       (* content height (>= 0) *)
}.

Definition nonneg (b : Box) := (0 <= h b)%Z.

(* Layout result after BFC placement *)
Record Placed := mkPlaced {
  top  : Z;
  pb_box  : Box
}.

(* === COLLAPSING SEMANTICS (CSS 2.1 §8.3.1) === *)

(* Collapse a list of margins according to the "max of positives + min of negatives" rule *)
Definition collapse (ms : list Z) : Z :=
  let pos := filter (fun m => Z.geb m 0) ms in
  let neg := filter (fun m => Z.ltb m 0) ms in
  match pos, neg with
  | [], [] => 0%Z
  | ps, [] => fold_right Z.max (hd 0%Z ps) ps
  | [], ns => fold_right Z.min (hd 0%Z ns) ns 
  | ps, ns => (fold_right Z.max (hd 0%Z ps) ps + 
               fold_right Z.min (hd 0%Z ns) ns)%Z
  end.

(* Empty block according to spec *)
Definition empty_block (b : Box) : bool :=
  (h b =? 0)%Z. (* Simple version: no height collapses *)

(* === FSM STATE === *)

Record State := mkState {
  y      : Z;              (* current pen position *)
  stack  : list Box;       (* pending block chain for collapses *)
  placed : list Placed     (* output already laid out *)
}.

Definition init : State := mkState 0 [] [].

(* Utility: push current block into stack *)
Definition push (b : Box) (s : State) :=
  mkState (y s) (b :: stack s) (placed s).

(* Commit stack: compute collapsed chain, update y *)
Definition commit (s : State) : State :=
  match rev (stack s) with
  | [] => s
  | b :: rest =>
      let collapsed :=
        (collapse (map mt (b :: rest)) +
        h b +
        collapse (map mb (b :: rest)))%Z in
      mkState (y s + collapsed)%Z [] (placed s)
  end.

(* === FSM TRANSITIONS (Deterministic) === *)

Definition step (s : State) (b : Box) : State :=
  if empty_block b then
    push b s
  else
    match stack s with
    | [] =>
        let y' := (y s + mt b)%Z in
        mkState (y' + h b + mb b)%Z [] (mkPlaced y' b :: placed s)
    | _ =>
        let s1 := commit s in
        let y' := (y s1 + mt b)%Z in
        mkState (y' + h b + mb b)%Z [] (mkPlaced y' b :: placed s1)
    end.

Fixpoint run (s : State) (bs : list Box) : State :=
  match bs with
  | [] => commit s
  | b :: bs' => run (step s b) bs'
  end.

End MarginCollapse.
