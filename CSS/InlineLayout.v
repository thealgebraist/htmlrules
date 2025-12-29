From Coq Require Import List ZArith Lia.
Require Import CSS.Floats.
Import ListNotations.
Import Floats.

Module InlineLayout.

Record InlineBox := mkIBox {
  iw : Z;
  ih : Z;
  is_text : bool
}.

Record PlacedInline := mkPInline {
  pi_box : InlineBox;
  pi_x : Z;
  pi_y : Z
}.

Record IFCState := mkIFCState {
  fs : FloatState;
  y_cursor : Z;
  x_cursor : Z;
  line_h : Z;
  history : list PlacedInline
}.

Definition init (s : FloatState) (y : Z) := 
  let '(l, r) := get_available_range s y 20 in (* assume default line height 20 *)
  mkIFCState s y l 0 [].

Definition step (s : IFCState) (b : InlineBox) : IFCState :=
  let '(l, r) := get_available_range (fs s) (y_cursor s) (ih b) in
  if (x_cursor s + iw b <=? r)%Z then
    (* Fits on current line *)
    mkIFCState (fs s) (y_cursor s) (x_cursor s + iw b) (Z.max (line_h s) (ih b))
               (mkPInline b (x_cursor s) (y_cursor s) :: history s)
  else
    (* Wrap to next line *)
    let new_y := (y_cursor s + Z.max (line_h s) 20)%Z in
    let '(nl, nr) := get_available_range (fs s) new_y (ih b) in
    mkIFCState (fs s) new_y (nl + iw b) (ih b)
               (mkPInline b nl new_y :: history s).

Fixpoint run_ifc (s : IFCState) (is : list InlineBox) : IFCState :=
  match is with
  | [] => s
  | b :: bs => run_ifc (step s b) bs
  end.

Theorem line_wrapping : forall fs y b1 b2,
  let '(l, r) := get_available_range fs y 20 in
  (iw b1 + iw b2 > r - l)%Z ->
  let s := run_ifc (init fs y) [b1; b2] in
  exists p1 p2, In p1 (history s) /\ In p2 (history s) /\ pi_y p1 <> pi_y p2.
Proof. Admitted.

End InlineLayout.
