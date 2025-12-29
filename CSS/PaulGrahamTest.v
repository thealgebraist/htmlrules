Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import CSS.Semantics.
Import ListNotations.

(** * Paul Graham Layout Verification 
    Proving that the 3-column table structure places content to the right of the navbar.
*)

(* 1. Define the specific nodes from pg.html *)
(* <img src="img-32.gif" width="69" ...> *)
Definition left_bar_img : Node :=
  elem img [Build_Attr "id" "left_bar"; Build_Attr "width" "69"] [].

(* <td ...> <img ...> </td> *)
Definition left_td : Node :=
  elem td [Build_Attr "valign" "top"] [left_bar_img].

(* <img ... width="26"> spacer *)
Definition spacer_img : Node :=
  elem img [Build_Attr "id" "spacer"; Build_Attr "width" "26"] [].

Definition spacer_td : Node :=
  elem td [] [spacer_img].

(* <img src="bel-8.gif" width="410" ...> *)
Definition content_img : Node :=
  elem img [Build_Attr "id" "content_header"; Build_Attr "width" "410"] [].

(* Yellow Box: <table width=410><tr><td bgcolor=#ffcc33>...</td></tr></table> *)
Definition yellow_cell : Node :=
  elem td [Build_Attr "id" "yellow_cell"] [
    text "New:" 
  ].

Definition yellow_row : Node := elem tr [] [yellow_cell].
Definition yellow_table : Node := elem table [] [yellow_row].

Definition content_td : Node :=
  elem td [] [content_img; yellow_table].

(* Row containing the three columns *)
Definition pg_row : Node :=
  elem tr [Build_Attr "valign" "top"] [left_td; spacer_td; content_td].

(* Table wrapper *)
Definition pg_table : Node :=
  elem table [] [pg_row].

(* 2. Define CSS to mimic attributes (since Coq model ignores attrs) *)
Definition pg_css : CSS := [
  mk_mq mq_always [
    (* Semantic Table Layout *)
    mk_rule (sel_tag tr) [mk_decl p_display (v_str "table-row") false];
    
    (* Simulating w=69 for left bar image *)
    mk_rule (sel_id "left_bar") [mk_decl p_width (v_px 69) false];
    
    (* Simulating w=26 for spacer *)
    mk_rule (sel_id "spacer") [mk_decl p_width (v_px 26) false];
    
    (* Simulating w=410 for content *)
    mk_rule (sel_id "content_header") [mk_decl p_width (v_px 410) false; mk_decl p_height (v_px 45) false];

    (* Yellow box style *)
    mk_rule (sel_id "yellow_cell") [
      mk_decl p_width (v_px 410) false; 
      mk_decl p_height (v_px 15) false; 
      mk_decl p_color (v_str "#ffcc33") false
    ]
  ]
].

(* 
   Note: In our restricted model, 'td' width defaults to 'content width' (kw).
   So 'left_td' width = width of 'left_bar_img' = 69.
   'spacer_td' width = 26.
   'content_td' width = 410.
*)

(* 3. The Proof *)
(* We want to prove that the content_img (in 3rd cell) is at x >= 69 + 26 = 95. *)
(* Specifically, we inspect the LayoutBox tree produced by render. *)

(* Structure of output: 
   mkLBox (Table) [
     mkLBox (TR) [
       mkLBox (TD1) [ mkLBox (IMG1) ... ]
       mkLBox (TD2) [ ... ]
       mkLBox (TD3) [ mkLBox (IMG); mkLBox (TABLE_YELLOW) ]
     ]
   ]
*)

Definition pg_render_tree := render 800 pg_table pg_css.

Theorem pg_image_right_of_bar : 
  match pg_render_tree with
  | mkLBox _ (tr_box :: []) => (* Table has 1 row *)
      match get_kids tr_box with
      | td1 :: td2 :: td3 :: _ => 
          rx (get_rect td3) >= (rw (get_rect td1) + rw (get_rect td2))
      | _ => False
      end
  | _ => False
  end.
Proof.
  (* Unfold definitions to force computation *)
  vm_compute.
  (* 95 <= 95 *)
  apply le_n.
Qed.

(* Also prove it's NOT under (y=0) *)
Theorem pg_image_top_aligned : 
  match pg_render_tree with
  | mkLBox _ (tr_box :: []) => 
      match get_kids tr_box with
      | td1 :: td2 :: td3 :: _ => 
          ry (get_rect td3) = ry (get_rect td1)
      | _ => False
      end
  | _ => False
  end.
Proof.
  vm_compute. reflexivity.
Qed.

Theorem yellow_area_rendered_under_image : 
  match pg_render_tree with
  | mkLBox _ (_ :: _ :: td3_box :: _) => (* Get 3rd TD (content) *)
      match get_kids td3_box with
      | img_box :: table_box :: _ => (* Img and Table *)
          let img_rect := get_rect img_box in
          let table_rect := get_rect table_box in
          (* 1. Rendered (height > 0). Table height depends on content (TR->TD->15px) *)
          (* 2. Under image (y >= y + h). In vertical stack, y2 = y1 + h1 *)
          rh table_rect > 0 /\
          ry table_rect >= ry img_rect + rh img_rect
      | _ => False
      end
  | _ => False
  end.
Proof. Admitted.
