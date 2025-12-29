Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import CSS.Semantics.
Import ListNotations.

(** * Proof of Visual Order Reversal
    This theorem proves that the layout engine allows elements to appear in a 
    visual order that is reversed relative to their DOM order.
*)

Theorem visual_order_reversal : exists (n : Node) (css : CSS),
  match n with
  | elem t attrs (child1 :: child2 :: []) =>
      let lb := render 1000 n css in
      match lb with
      | mkLBox _ (lb1 :: lb2 :: []) =>
          (* child1 is before child2 in DOM *)
          (* but lb1.y > lb2.y visually *)
          ry (get_rect lb1) > ry (get_rect lb2)
      | _ => False
      end
  | _ => False
  end.
Proof.
  (* Parent DIV contains [Div A, Div B] *)
  (* Div A is shifted down by 50px using 'top' *)
  (* Div B follows Div A in the flow, so its base Y is height(A) = 20px *)
  (* Final positions: A.y = 50, B.y = 20 *)
  
  exists (elem div [] [elem div [Build_Attr "id" "A"] []; 
                      elem div [Build_Attr "id" "B"] []]).
  exists ([mk_mq mq_always [mk_rule (sel_id "A") [mk_decl p_top (v_px 50) false]]]).
  
  vm_compute.
  (* 50 > 20 *)
  repeat constructor.
Qed.

Theorem matrix_order_reversal : exists (n : Node) (css : CSS),
  match n with
  | elem t_table _ (elem t_row1 _ (c11 :: c12 :: []) :: 
                    elem t_row2 _ (c21 :: c22 :: []) :: []) =>
      let lb := render 1000 n css in
      match lb with
      | mkLBox _ (row1_box :: row2_box :: []) =>
          match get_kids row1_box, get_kids row2_box with
          | lb11 :: lb12 :: [], lb21 :: lb22 :: [] =>
              (* DOM order: index 1 before index 2 *)
              (* Visual order: rx(lb12) < rx(lb11) and rx(lb22) < rx(lb21) *)
              rx (get_rect lb12) < rx (get_rect lb11) /\
              rx (get_rect lb22) < rx (get_rect lb21)
          | _, _ => False
          end
      | _ => False
      end
  | _ => False
  end.
Proof.
  (* Construct 2x2 table with swapped horizontal order *)
  (* Cell 11: left=200. Cell 12: left=0. (assuming width=100) *)
  (* Result: rx(11)=200, rx(12)=100. Visual order is 12 then 11. *)

  exists (elem table [] [
    elem tr [] [elem td [Build_Attr "id" "C11"] []; elem td [Build_Attr "id" "C12"] []];
    elem tr [] [elem td [Build_Attr "id" "C21"] []; elem td [Build_Attr "id" "C22"] []]
  ]).
  exists ([
    mk_mq mq_always [
      mk_rule (sel_id "C11") [mk_decl p_width (v_px 100) false; mk_decl p_left (v_px 200) false];
      mk_rule (sel_id "C12") [mk_decl p_width (v_px 100) false];
      mk_rule (sel_id "C21") [mk_decl p_width (v_px 100) false; mk_decl p_left (v_px 200) false];
      mk_rule (sel_id "C22") [mk_decl p_width (v_px 100) false]
    ]
  ]).
  
  vm_compute.
  split; repeat constructor.
Qed.
