Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(** 1. AST & SELECTORS *)

Inductive Tag : Set := div | span | p | img | h1.

Definition tag_eq (t1 t2 : Tag) : bool :=
  match t1, t2 with
  | div, div => true | span, span => true | p, p => true 
  | img, img => true | h1, h1 => true | _, _ => false
  end.

Record Attr : Set := { attr_name : string; attr_value : string }.

Inductive Node : Set :=
  | text : string -> Node
  | elem : Tag -> list Attr -> list Node -> Node.

Inductive Property : Set :=
  | p_width | p_height | p_margin | p_padding | p_border
  | p_color | p_display | p_box_sizing
  | p_position | p_top | p_left | p_z_index.

Inductive Value : Set :=
  | v_px : nat -> Value
  | v_str : string -> Value.

Record Decl : Set := { 
  decl_prop : Property; 
  decl_val : Value;
  decl_important : bool 
}.

Inductive Selector : Set :=
  | sel_tag   : Tag -> Selector
  | sel_class : string -> Selector
  | sel_id    : string -> Selector
  | sel_desc  : Selector -> Selector -> Selector.

Record Rule : Set := { rule_sel : Selector; rule_decls : list Decl }.
Definition CSS := list Rule.

(** 2. CASCADE *)

Fixpoint specificity (s : Selector) : nat :=
  match s with
  | sel_id _ => 100
  | sel_class _ => 10
  | sel_tag _ => 1
  | sel_desc s1 s2 => (specificity s1) + (specificity s2)
  end.

Fixpoint find_attr (name : string) (attrs : list Attr) : option string :=
  match attrs with
  | [] => None
  | a :: as' => if (attr_name a =? name)%string then Some (attr_value a) else find_attr name as'
  end.

Fixpoint matches (ancestors : list Node) (n : Node) (s : Selector) : bool :=
  match s with
  | sel_tag t' => match n with elem t _ _ => tag_eq t t' | _ => false end
  | sel_class c => match n with elem _ attrs _ => 
                      match find_attr "class" attrs with Some c' => (c =? c')%string | None => false end
                      | _ => false end
  | sel_id i => match n with elem _ attrs _ => 
                      match find_attr "id" attrs with Some i' => (i =? i')%string | None => false end
                      | _ => false end
  | sel_desc s1 s2 => 
      if matches ancestors n s2 then
        existsb (fun anc => matches [] anc s1) ancestors
      else false
  end.

Definition prop_eq (p1 p2 : Property) : bool :=
  match p1, p2 with
  | p_width, p_width => true | p_height, p_height => true | p_margin, p_margin => true
  | p_padding, p_padding => true | p_border, p_border => true | p_color, p_color => true 
  | p_display, p_display => true | p_box_sizing, p_box_sizing => true 
  | p_position, p_position => true | p_top, p_top => true | p_left, p_left => true
  | p_z_index, p_z_index => true | _, _ => false
  end.

Fixpoint find_decl (p : Property) (decls : list Decl) : option Decl :=
  match decls with
  | [] => None
  | d :: ds => if prop_eq p (decl_prop d) then Some d else find_decl p ds
  end.

Fixpoint cascade_resolve (anc : list Node) (p : Property) (n : Node) (css : CSS) 
                         (best_spec : nat) (best_imp : bool) (best_val : option Value) : option Value :=
  match css with
  | [] => best_val
  | r :: rs => 
      if matches anc n (rule_sel r) then
        match find_decl p (rule_decls r) with
        | Some d => 
            let spec := specificity (rule_sel r) in
            let imp := decl_important d in
            if (orb (andb imp (negb best_imp)) (andb (eqb imp best_imp) (leb best_spec spec)))
            then cascade_resolve anc p n rs spec imp (Some (decl_val d))
            else cascade_resolve anc p n rs best_spec best_imp best_val
        | None => cascade_resolve anc p n rs best_spec best_imp best_val
        end
      else cascade_resolve anc p n rs best_spec best_imp best_val
  end.

Definition resolve (anc : list Node) (p : Property) (n : Node) (css : CSS) : option Value :=
  cascade_resolve anc p n css 0 false None.

(** 3. POSITIONING & STYLE *)

Inductive Position : Set := s_static | s_relative | s_absolute.
Record SideValues : Set := { t_v : nat; r_v : nat; b_v : nat; l_v : nat }.
Inductive BoxSizing : Set := content_box | border_box.
Inductive DisplayType : Set := d_block | d_inline | d_none.

Record Style : Set := {
  s_disp : DisplayType;
  s_pos : Position;
  s_top : nat; s_left : nat; s_z_index : nat;
  s_width : nat; s_height : nat;
  s_margin : SideValues; s_padding : SideValues; s_border : SideValues;
  s_box_sizing : BoxSizing;
  s_color : string
}.

Definition compute_style (anc : list Node) (parent : option Style) (n : Node) (css : CSS) : Style :=
  let get_px p def := match resolve anc p n css with Some (v_px n) => n | _ => def end in
  let disp := match resolve anc p_display n css with
              | Some (v_str "inline") => d_inline
              | Some (v_str "none") => d_none
              | _ => d_block
              end in
  let pos := match resolve anc p_position n css with
             | Some (v_str "relative") => s_relative
             | Some (v_str "absolute") => s_absolute
             | _ => s_static
             end in
  {| s_disp := disp;
     s_pos := pos;
     s_top := get_px p_top 0;
     s_left := get_px p_left 0;
     s_z_index := get_px p_z_index 0;
     s_width := get_px p_width 0;
     s_height := get_px p_height 0;
     s_margin := let v := get_px p_margin 0 in {| t_v := v; r_v := v; b_v := v; l_v := v |};
     s_padding := let v := get_px p_padding 0 in {| t_v := v; r_v := v; b_v := v; l_v := v |};
     s_border := let v := get_px p_border 0 in {| t_v := v; r_v := v; b_v := v; l_v := v |};
     s_box_sizing := match resolve anc p_box_sizing n css with
                     | Some (v_str "border-box") => border_box | _ => content_box end;
     s_color := match resolve anc p_color n css with 
                | Some (v_str c) => c 
                | _ => match parent with Some ps => s_color ps | None => "black" end end |}.

(** 4. LAYOUT WITH POSITIONING *)

Record Rect : Set := { rx : nat; ry : nat; rw : nat; rh : nat }.
Inductive Box : Set := mkBox : Node -> Rect -> Style -> list Box -> Box.
Definition Layout := list Box.

Definition layout_node (anc : list Node) (availW : nat) (parent_s : option Style) 
                     (x y : nat) (n : Node) (css : CSS) : (list Box * nat * nat) :=
  let s := compute_style anc parent_s n css in
  match s_disp s with
  | d_none => ([], x, y)
  | _ =>
      let m := s_margin s in
      let p := s_padding s in
      let b := s_border s in
      
      let flow_x := x + l_v m in
      let flow_y := y + t_v m in
      
      let final_pos := match s_pos s with
                       | s_relative => (flow_x + s_left s, flow_y + s_top s)
                       | s_absolute => (s_left s, s_top s)
                       | s_static => (flow_x, flow_y)
                       end in
      let fx := fst final_pos in
      let fy := snd final_pos in
      
      let content_w := if Nat.eqb (s_width s) 0 then 50 else s_width s in
      let content_h := if Nat.eqb (s_height s) 0 then 20 else s_height s in
      
      let bb_w := match s_box_sizing s with
                  | content_box => content_w + l_v p + r_v p + l_v b + r_v b
                  | border_box => content_w
                  end in
      let bb_h := match s_box_sizing s with
                  | content_box => content_h + t_v p + b_v p + t_v b + b_v b
                  | border_box => content_h
                  end in
                  
      let box := mkBox n (Build_Rect fx fy bb_w bb_h) s [] in
      
      match s_disp s with
      | d_block => ([box], x, y + bb_h + t_v m + b_v m)
      | d_inline => ([box], x + bb_w + l_v m + r_v m, y)
      | d_none => ([], x, y)
      end
  end.

Definition render (availW : nat) (n : Node) (css : CSS) : Layout :=
  match (layout_node [] availW None 0 0 n css) with
  | (res, _, _) => res
  end.

(** 5. VERIFICATION *)

Theorem render_unique : forall w n css o1 o2, render w n css = o1 -> render w n css = o2 -> o1 = o2.
Proof. intros. rewrite <- H, <- H0. reflexivity. Qed.

(* Test: Absolute Positioning *)
Example test_absolute :
  let css := [ {| rule_sel := sel_tag div ; 
                  rule_decls := [ {| decl_prop := p_position ; decl_val := v_str "absolute" ; decl_important := false |} ;
                                  {| decl_prop := p_top ; decl_val := v_px 50 ; decl_important := false |} ;
                                  {| decl_prop := p_left ; decl_val := v_px 100 ; decl_important := false |} ] |} ] in
  match render 800 (elem div [] []) css with
  | [mkBox _ r _ _] => rx r = 100 /\ ry r = 50
  | _ => False
  end.
Proof. simpl. split; reflexivity. Qed.