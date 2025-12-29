Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** * CSS Layout FSM 
    Modeling both Block and Inline layout rules.
*)

Inductive DisplayType := d_block | d_inline.

(** 1. DOM Definition *)
Record Box := mkBox {
  h : nat;      (* Content Height *)
  w : nat;      (* Content Width *)
  mt : nat;     (* Margin Top *)
  mb : nat;     (* Margin Bottom *)
  disp : DisplayType
}.

(** 2. Layout State *)
Inductive FSM_Status := InProgress | Done.

Record PlacedBox := mkPlacedBox {
  pb_box : Box;
  pb_top : nat;
  pb_left : nat
}.

Record State := mkState {
  x_pos : nat;          (* Current X position *)
  y_pos : nat;          (* Current Y position *)
  line_h : nat;         (* Current Line Height *)
  pending_margin : nat; (* The margin carried over *)
  max_w : nat;          (* Container Width *)
  status : FSM_Status;
  history : list PlacedBox
}.

Definition init_state (mw : nat) := mkState 0 0 0 0 mw InProgress [].

(** 3. FSM Transition *)

Definition step (s : State) (b : Box) : State :=
  match disp b with
  | d_block =>
      (* Always break line before block *)
      let base_y := y_pos s + line_h s in
      let collapsed := max (pending_margin s) (mt b) in
      let box_top := base_y + collapsed in
      let box_bottom := box_top + (h b) in
      mkState 0 box_bottom 0 (mb b) (max_w s) InProgress ((mkPlacedBox b box_top 0) :: (history s))
  | d_inline =>
      (* Check if it fits horizontally *)
      if (x_pos s + w b <=? max_w s) then
        (* Fits in current line *)
        let box_top := y_pos s in
        mkState (x_pos s + w b) (y_pos s) (Init.Nat.max (line_h s) (h b)) (pending_margin s) (max_w s) InProgress ((mkPlacedBox b box_top (x_pos s)) :: (history s))
      else
        (* Wrap to new line *)
        let new_y := y_pos s + line_h s in
        mkState (w b) new_y (h b) (pending_margin s) (max_w s) InProgress ((mkPlacedBox b new_y 0) :: (history s))
  end.

Fixpoint layout_fsm_internal (s : State) (boxes : list Box) : State :=
  match boxes with
  | [] => mkState (x_pos s) (y_pos s + line_h s) (line_h s) (pending_margin s) (max_w s) Done (history s)
  | b :: bs => layout_fsm_internal (step s b) bs
  end.

Definition layout_fsm (mw : nat) (boxes : list Box) : State :=
  layout_fsm_internal (init_state mw) boxes.

(** 4. Formal Verification Checks *)

(* Check 1: Vertical Monotonicity (CSS 2.1 9.4.1) *)
Fixpoint check_v_monotonicity (h_list : list PlacedBox) : Prop :=
  match h_list with
  | [] => True
  | [_] => True
  | b_next :: (b_curr :: rest as l) => 
      (pb_top b_curr <= pb_top b_next) /\ check_v_monotonicity l
  end.

(* Check 5: Horizontal Monotonicity (Inline elements in same line) *)
Fixpoint check_h_monotonicity (h_list : list PlacedBox) : Prop :=
  match h_list with
  | [] => True
  | [_] => True
  | b_next :: (b_curr :: rest as l) => 
      (if (pb_top b_curr =? pb_top b_next) then (pb_left b_curr + w (pb_box b_curr) <= pb_left b_next) else True) /\ 
      check_h_monotonicity l
  end.

(* Check 6: Containment within Width *)
Fixpoint check_width_containment (h_list : list PlacedBox) (mw : nat) : Prop :=
  match h_list with
  | [] => True
  | b :: rest => (pb_left b + w (pb_box b) <= mw) /\ check_width_containment rest mw
  end.

Definition verify_layout (input : list Box) (mw : nat) (s : State) : Prop :=
  status s = Done /\
  check_v_monotonicity (history s) /\
  check_h_monotonicity (history s) /\
  check_width_containment (history s) mw.

Theorem fsm_is_correct : forall mw boxes, verify_layout boxes mw (layout_fsm mw boxes).
Proof.
  Admitted.
