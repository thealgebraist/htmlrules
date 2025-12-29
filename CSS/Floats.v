Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Module Floats.

Record Rect := mkRect { rx: Z; ry: Z; rw: Z; rh: Z }.

Record FloatState := mkFloatState {
  y_pos : Z;
  max_w : Z;
  left_floats : list Rect;
  right_floats : list Rect
}.

Definition init (w : Z) := mkFloatState 0 w [] [].

(* Available horizontal range at a specific y and height h *)
Definition get_available_range (s : FloatState) (y : Z) (h : Z) : (Z * Z) :=
  let left_bound := fold_right (fun r acc => 
    if (andb (Z.ltb y (ry r + rh r)) (Z.ltb (ry r) (y + h)))
    then Z.max acc (rx r + rw r) else acc) 0%Z (left_floats s) in
  let right_bound := fold_right (fun r acc => 
    if (andb (Z.ltb y (ry r + rh r)) (Z.ltb (ry r) (y + h)))
    then Z.min acc (rx r) else acc) (max_w s) (right_floats s) in
  (left_bound, right_bound).

Definition fits_at (s : FloatState) (y : Z) (w : Z) (h : Z) : bool :=
  let '(l, r) := get_available_range s y h in
  (l + w <=? r)%Z.

(* Find the first Y >= y_start where a box (w, h) fits *)
Fixpoint find_y (s : FloatState) (y_start : Z) (w : Z) (h : Z) (fuel : nat) : Z :=
  match fuel with
  | O => y_start
  | S f => if fits_at s y_start w h then y_start 
           else find_y s (y_start + 1)%Z w h f
  end.

Inductive FloatSide := f_left | f_right.

Definition add_float (s : FloatState) (side : FloatSide) (w h : Z) : FloatState :=
  let y_start := find_y s (y_pos s) w h 1000%nat in
  let '(l, r) := get_available_range s y_start h in
  match side with
  | f_left => 
      let new_r := mkRect l y_start w h in
      mkFloatState (y_pos s) (max_w s) (new_r :: left_floats s) (right_floats s)
  | f_right =>
      let new_r := mkRect (r - w) y_start w h in
      mkFloatState (y_pos s) (max_w s) (left_floats s) (new_r :: right_floats s)
  end.

(* Clearance: jump Y to the bottom of all floats on specified side *)
Definition get_clearance_y (s : FloatState) (side : FloatSide) : Z :=
  let list := match side with f_left => left_floats s | f_right => right_floats s end in
  fold_right (fun r acc => Z.max acc (ry r + rh r)) (y_pos s) list.

Definition disjoint (r1 r2 : Rect) : Prop :=
  (rx r1 + rw r1 <= rx r2 \/ rx r2 + rw r2 <= rx r1 \/
   ry r1 + rh r1 <= ry r2 \/ ry r2 + rh r2 <= ry r1)%Z.

Theorem floats_disjoint : forall s side w h,
  (forall r1 r2, In r1 (match side with f_left => left_floats s | f_right => right_floats s end) -> 
                 In r2 (match side with f_left => left_floats s | f_right => right_floats s end) -> 
                 r1 <> r2 -> disjoint r1 r2) ->
  let s' := add_float s side w h in
  (forall r1 r2, In r1 (match side with f_left => left_floats s' | f_right => right_floats s' end) -> 
                 In r2 (match side with f_left => left_floats s' | f_right => right_floats s' end) -> 
                 r1 <> r2 -> disjoint r1 r2).
Proof. Admitted.

End Floats.
