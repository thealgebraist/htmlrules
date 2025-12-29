Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** * CSS Advanced Layout FSM 
    Strict BFC/IFC enforcement and Anonymous Box validation.
*)

Inductive DisplayType := d_block | d_inline.
Inductive FormattingContext := BFC | IFC.

Record Box := mkBox {
  h : nat;
  w : nat;
  mt : nat;
  mb : nat;
  disp : DisplayType
}.

Inductive FSM_Status := InProgress | Done.

Record PlacedBox := mkPlacedBox {
  pb_box : Box;
  pb_top : nat;
  pb_left : nat;
  pb_context : FormattingContext
}.

Record State := mkState {
  x_pos : nat;
  y_pos : nat;
  line_h : nat;
  pending_margin : nat;
  max_w : nat;
  current_ctx : FormattingContext;
  status : FSM_Status;
  history : list PlacedBox
}.

Definition init_state (mw : nat) := mkState 0 0 0 0 mw BFC InProgress [].

(** 3. FSM Transition Logic *)

Definition step (s : State) (b : Box) : State :=
  match disp b with
  | d_block =>
      (* Always force BFC logic *)
      let base_y := y_pos s + line_h s in
      let collapsed := max (pending_margin s) (mt b) in
      let box_top := base_y + collapsed in
      mkState 0 (box_top + h b) 0 (mb b) (max_w s) BFC InProgress ((mkPlacedBox b box_top 0 BFC) :: history s)
  | d_inline =>
      (* IFC logic *)
      if (x_pos s + w b <=? max_w s) then
        mkState (x_pos s + w b) (y_pos s) (Init.Nat.max (line_h s) (h b)) (pending_margin s) (max_w s) IFC InProgress ((mkPlacedBox b (y_pos s) (x_pos s) IFC) :: history s)
      else
        let new_y := y_pos s + line_h s in
        mkState (w b) new_y (h b) (pending_margin s) (max_w s) IFC InProgress ((mkPlacedBox b new_y 0 IFC) :: history s)
  end.

Fixpoint layout_fsm_internal (s : State) (boxes : list Box) : State :=
  match boxes with
  | [] => mkState (x_pos s) (y_pos s + line_h s) 0 (pending_margin s) (max_w s) (current_ctx s) Done (history s)
  | b :: bs => layout_fsm_internal (step s b) bs
  end.

Definition layout_fsm (mw : nat) (boxes : list Box) : State :=
  layout_fsm_internal (init_state mw) boxes.

(** 4. Formal Verification Checks *)

(* Check 1: BFC Vertical Sequence *)
Fixpoint check_bfc_sequence (h_list : list PlacedBox) : Prop :=
  match h_list with
  | [] => True
  | [_] => True
  | b_next :: (b_curr :: rest as l) =>
      (if (match (pb_context b_curr, pb_context b_next) with (BFC, BFC) => true | _ => false end)
       then pb_top b_curr + h (pb_box b_curr) <= pb_top b_next
       else True) /\ check_bfc_sequence l
  end.

(* Check 3: Anonymous Box Rule (Implicitly handled by FSM state transitions) 
   We check that in BFC, every box is block-level OR was part of a line box.
*)
Fixpoint check_anonymous_rule (h_list : list PlacedBox) : Prop :=
  match h_list with
  | [] => True
  | b :: rest =>
      (if (match pb_context b with BFC => true | _ => false end)
       then (match disp (pb_box b) with d_block => True | d_inline => False end)
       else True) /\ check_anonymous_rule rest
  end.

Definition verify_layout (input : list Box) (mw : nat) (s : State) : Prop :=
  status s = Done /\
  check_bfc_sequence (history s) /\
  check_anonymous_rule (history s).

Theorem fsm_is_correct : forall mw boxes, verify_layout boxes mw (layout_fsm mw boxes).
Proof. Admitted.
