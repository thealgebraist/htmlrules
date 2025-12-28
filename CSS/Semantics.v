Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(** 1. ADVANCED NEWS-SITE AST (CNN/DR.DK FULL) *)

Inductive Tag : Set := div | span | p | img | h1 | body | nav | ol | li | article | section.

Definition tag_eq (t1 t2 : Tag) : bool :=
  match t1, t2 with
  | div, div => true | span, span => true | p, p => true 
  | img, img => true | h1, h1 => true | body, body => true 
  | nav, nav => true | ol, ol => true | li, li => true
  | article, article => true | section, section => true | _, _ => false
  end.

Inductive Side : Set := s_top | s_right | s_bottom | s_left.

Inductive Property : Set :=
  | p_width | p_height 
  | p_margin : Side -> Property
  | p_padding : Side -> Property
  | p_border : Side -> Property
  | p_color | p_bg_color | p_display | p_box_sizing
  | p_position | p_pos_top | p_pos_left | p_z_index
  | p_flex_direction | p_flex_grow | p_justify_content | p_align_items
  | p_font_size | p_line_height | p_custom : string -> Property.

Inductive Value : Set :=
  | v_px : nat -> Value
  | v_pct : nat -> Value
  | v_rem : nat -> Value
  | v_vw  : nat -> Value
  | v_vh  : nat -> Value
  | v_rgba : nat -> nat -> nat -> nat -> Value (* r g b a *)
  | v_str : string -> Value
  | v_var : string -> Value 
  | v_calc : Value -> string -> Value -> Value. (* calc(v1 + v2) *)

Record Decl : Set := { 
  decl_prop : Property; 
  decl_val : Value;
  decl_important : bool 
}.

Inductive Selector : Set :=
  | sel_univ  : Selector (* * *)
  | sel_tag   : Tag -> Selector
  | sel_class : string -> Selector
  | sel_id    : string -> Selector
  | sel_and   : Selector -> Selector -> Selector (* .a.b *)
  | sel_group : Selector -> Selector -> Selector (* s1, s2 *)
  | sel_desc  : Selector -> Selector -> Selector
  | sel_pseudo : Selector -> string -> Selector. 

Record Rule : Set := { rule_sel : Selector; rule_decls : list Decl }.

Inductive MediaQuery : Set :=
  | mq_always : MediaQuery
  | mq_min_width : nat -> MediaQuery
  | mq_max_width : nat -> MediaQuery.

Record MQRule : Set := { mq_cond : MediaQuery; mq_rules : list Rule }.
Definition CSS := list MQRule.

Record Attr : Set := { attr_name : string; attr_value : string }.
Inductive Node : Set :=
  | text : string -> Node
  | elem : Tag -> list Attr -> list Node -> Node.

(** 2. CASCADE & MATCHING *)

Fixpoint contains_token (target : string) (s : string) (current : string) : bool :=
  match s with
  | "" => (target =? current)%string
  | String c rest =>
      if Ascii.ascii_dec c " " then
        if (target =? current)%string then true
        else contains_token target rest ""
      else contains_token target rest (current ++ String c "")%string
  end.

Fixpoint find_attr (name : string) (attrs : list Attr) : option string :=
  match attrs with
  | [] => None
  | a :: as' => if (attr_name a =? name)%string then Some (attr_value a) else find_attr name as'
  end.

Fixpoint matches (anc : list Node) (n : Node) (s : Selector) : bool :=
  match s with
  | sel_univ => true
  | sel_tag t' => match n with elem t _ _ => tag_eq t t' | _ => false end
  | sel_class c => match n with elem _ attrs _ => 
                      match find_attr "class" attrs with Some v => contains_token c v "" | None => false end
                      | _ => false end
  | sel_id i => match n with elem _ attrs _ => 
                      match find_attr "id" attrs with Some v => (i =? v)%string | None => false end
                      | _ => false end
  | sel_and s1 s2 => matches anc n s1 && matches anc n s2
  | sel_group s1 s2 => matches anc n s1 || matches anc n s2
  | sel_desc s1 s2 => if matches anc n s2 then existsb (fun a => matches [] a s1) anc else false
  | sel_pseudo s1 _ => matches anc n s1 
  end.

Fixpoint specificity (s : Selector) : nat :=
  match s with
  | sel_univ => 0
  | sel_tag _ => 1
  | sel_class _ => 10
  | sel_id _ => 100
  | sel_and s1 s2 => specificity s1 + specificity s2
  | sel_group s1 s2 => specificity s1 (* Per-selector in group *)
  | sel_desc s1 s2 => specificity s1 + specificity s2
  | sel_pseudo s1 _ => specificity s1 + 1
  end.

Definition prop_eq (p1 p2 : Property) : bool :=
  match p1, p2 with
  | p_width, p_width => true | p_height, p_height => true 
  | p_margin s1, p_margin s2 => match s1, s2 with s_top,s_top => true | s_right,s_right => true | s_bottom,s_bottom => true | s_left,s_left => true | _,_ => false end
  | p_padding s1, p_padding s2 => match s1, s2 with s_top,s_top => true | s_right,s_right => true | s_bottom,s_bottom => true | s_left,s_left => true | _,_ => false end
  | p_border s1, p_border s2 => match s1, s2 with s_top,s_top => true | s_right,s_right => true | s_bottom,s_bottom => true | s_left,s_left => true | _,_ => false end
  | p_color, p_color => true | p_bg_color, p_bg_color => true
  | p_display, p_display => true | p_box_sizing, p_box_sizing => true 
  | p_position, p_position => true | p_pos_top, p_pos_top => true | p_pos_left, p_pos_left => true
  | p_z_index, p_z_index => true 
  | p_flex_direction, p_flex_direction => true | p_flex_grow, p_flex_grow => true
  | p_justify_content, p_justify_content => true | p_align_items, p_align_items => true
  | p_font_size, p_font_size => true | p_line_height, p_line_height => true
  | p_custom s1, p_custom s2 => (s1 =? s2)%string
  | _, _ => false
  end.

Definition eval_mq (mq : MediaQuery) (vw vh : nat) : bool :=
  match mq with
  | mq_always => true
  | mq_min_width w => leb w vw
  | mq_max_width w => leb vw w
  end.

Fixpoint find_decl (p : Property) (decls : list Decl) : option Decl :=
  match decls with
  | [] => None
  | d :: ds => if prop_eq p (decl_prop d) then Some d else find_decl p ds
  end.

Fixpoint cascade_resolve (vw vh : nat) (anc : list Node) (p : Property) (n : Node) (css : CSS) 
                         (best_spec : nat) (best_imp : bool) (best_val : option Value) : option Value :=
  match css with
  | [] => best_val
  | mq_r :: rest => 
      if eval_mq (mq_cond mq_r) vw vh then
        let fix resolve_rules rules spec imp val :=
          match rules with
          | [] => (spec, imp, val)
          | r :: rs => 
              if matches anc n (rule_sel r) then
                match find_decl p (rule_decls r) with
                | Some d => 
                    let r_spec := specificity (rule_sel r) in
                    let r_imp := decl_important d in
                    if (orb (andb r_imp (negb imp)) (andb (eqb r_imp imp) (leb spec r_spec)))
                    then resolve_rules rs r_spec r_imp (Some (decl_val d))
                    else resolve_rules rs spec imp val
                | None => resolve_rules rs spec imp val
                end
              else resolve_rules rs spec imp val
          end
        in
        let res := resolve_rules (mq_rules mq_r) best_spec best_imp best_val in
        let '(nspec, nimp, nval) := res in
        cascade_resolve vw vh anc p n rest nspec nimp nval
      else cascade_resolve vw vh anc p n rest best_spec best_imp best_val
  end.

(** 3. STYLE & INHERITANCE *)

Inductive Position : Set := s_static | s_relative | s_absolute | s_fixed.
Inductive BoxSizing : Set := content_box | border_box.
Inductive DisplayType : Set := d_block | d_inline | d_none | d_flex | d_list_item.

Record Style : Set := {
  s_disp : DisplayType;
  s_pos : Position;
  s_width : Value; s_height : Value;
  s_color : Value; s_font_size : Value;
  s_z_index : nat
}.

Definition is_inherited (p : Property) : bool :=
  match p with
  | p_color | p_font_size | p_line_height => true
  | _ => false
  end.

Definition resolve (vw vh : nat) (anc : list Node) (p : Property) (n : Node) (css : CSS) (parent : option Value) : option Value :=
  match cascade_resolve vw vh anc p n css 0 false None with
  | Some v => Some v
  | None => if is_inherited p then parent else None
  end.

Definition compute_style (vw vh : nat) (anc : list Node) (parent : option Style) (n : Node) (css : CSS) : Style :=
  let get p par def := match resolve vw vh anc p n css par with Some v => v | None => def end in
  {| s_disp := match get p_display None (v_str "block") with v_str "inline" => d_inline | v_str "none" => d_none | v_str "flex" => d_flex | _ => d_block end;
     s_pos := match get p_position None (v_str "static") with v_str "relative" => s_relative | v_str "absolute" => s_absolute | v_str "fixed" => s_fixed | _ => s_static end;
     s_width := get p_width None (v_px 0);
     s_height := get p_height None (v_px 0);
     s_color := get p_color (match parent with Some ps => Some (s_color ps) | _ => None end) (v_str "black");
     s_font_size := get p_font_size (match parent with Some ps => Some (s_font_size ps) | _ => None end) (v_px 16);
     s_z_index := match get p_z_index None (v_px 0) with v_px n => n | _ => 0 end |}.

(** 4. VERIFICATION *)

Theorem render_unique : forall vw vh n css s1 s2, 
  compute_style vw vh [] None n css = s1 -> 
  compute_style vw vh [] None n css = s2 -> s1 = s2.
Proof. intros. rewrite <- H, <- H0. reflexivity. Qed.

Example t_univ: specificity sel_univ = 0. Proof. reflexivity. Qed.

Example t_inherit: 
  let css := [Build_MQRule mq_always [Build_Rule (sel_tag body) [{|decl_prop:=p_color; decl_val:=v_str "red"; decl_important:=false|}]]] in
  let body_s := compute_style 800 600 [] None (elem body [] []) css in
  let div_s := compute_style 800 600 [elem body [] []] (Some body_s) (elem div [] []) css in
  s_color div_s = v_str "red".
Proof. reflexivity. Qed.