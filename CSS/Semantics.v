Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(** 1. REFINED AST *)

Inductive Tag : Set := div | span | p | img | h1 | body | nav.

Definition tag_eq (t1 t2 : Tag) : bool :=
  match t1, t2 with
  | div, div => true | span, span => true | p, p => true 
  | img, img => true | h1, h1 => true | body, body => true 
  | nav, nav => true | _, _ => false
  end.

Record Attr : Set := { attr_name : string; attr_value : string }.

Inductive Node : Set :=
  | text : string -> Node
  | elem : Tag -> list Attr -> list Node -> Node.

Inductive Property : Set :=
  | p_width | p_height | p_margin | p_padding | p_border
  | p_color | p_display | p_box_sizing
  | p_position | p_top | p_left | p_z_index
  | p_flex_direction | p_flex_grow
  | p_custom : string -> Property.

Inductive Op : Set := op_add | op_sub.

Inductive Value : Set :=
  | v_px : nat -> Value
  | v_pct : nat -> Value
  | v_rem : nat -> Value
  | v_str : string -> Value
  | v_var : string -> Value 
  | v_calc : Value -> Op -> Value -> Value. 

Record Decl : Set := { 
  decl_prop : Property; 
  decl_val : Value;
  decl_important : bool 
}.

Inductive Selector : Set :=
  | sel_tag   : Tag -> Selector
  | sel_class : string -> Selector
  | sel_id    : string -> Selector
  | sel_and   : Selector -> Selector -> Selector
  | sel_desc  : Selector -> Selector -> Selector
  | sel_pseudo : Selector -> string -> Selector. 

Record Rule : Set := { rule_sel : Selector; rule_decls : list Decl }.

Inductive MediaQuery : Set :=
  | mq_always : MediaQuery
  | mq_min_width : nat -> MediaQuery.

Record MQRule : Set := {
  mq_cond : MediaQuery;
  mq_rules : list Rule
}.

Definition CSS := list MQRule.

(** 2. MATCHING *)

Fixpoint contains_token (target : string) (s : string) (current : string) : bool :=
  match s with
  | "" => (target =? current)%string
  | String c rest =>
      if Ascii.ascii_dec c " " then
        if (target =? current)%string then true
        else contains_token target rest ""
      else contains_token target rest (current ++ String c "")%string
  end.

Definition has_class (target : string) (attr_val : string) : bool :=
  contains_token target attr_val "".

Fixpoint find_attr (name : string) (attrs : list Attr) : option string :=
  match attrs with
  | [] => None
  | a :: as' => if (attr_name a =? name)%string then Some (attr_value a) else find_attr name as'
  end.

Fixpoint matches (anc : list Node) (n : Node) (s : Selector) : bool :=
  match s with
  | sel_tag t' => match n with elem t _ _ => tag_eq t t' | _ => false end
  | sel_class c => match n with elem _ attrs _ => 
                      match find_attr "class" attrs with Some v => has_class c v | None => false end
                      | _ => false end
  | sel_id i => match n with elem _ attrs _ => 
                      match find_attr "id" attrs with Some v => (i =? v)%string | None => false end
                      | _ => false end
  | sel_and s1 s2 => matches anc n s1 && matches anc n s2
  | sel_desc s1 s2 => 
      if matches anc n s2 then existsb (fun a => matches [] a s1) anc else false
  | sel_pseudo s1 p => matches anc n s1 
  end.

Fixpoint specificity (s : Selector) : nat :=
  match s with
  | sel_id _ => 100
  | sel_class _ => 10
  | sel_tag _ => 1
  | sel_and s1 s2 => specificity s1 + specificity s2
  | sel_desc s1 s2 => specificity s1 + specificity s2
  | sel_pseudo s1 _ => specificity s1 + 1
  end.

Definition eval_mq (mq : MediaQuery) (availW : nat) : bool :=
  match mq with
  | mq_always => true
  | mq_min_width w => leb w availW
  end.

Definition prop_eq (p1 p2 : Property) : bool :=
  match p1, p2 with
  | p_width, p_width => true | p_height, p_height => true | p_margin, p_margin => true
  | p_padding, p_padding => true | p_border, p_border => true | p_color, p_color => true 
  | p_display, p_display => true | p_box_sizing, p_box_sizing => true 
  | p_position, p_position => true | p_top, p_top => true | p_left, p_left => true
  | p_z_index, p_z_index => true 
  | p_flex_direction, p_flex_direction => true | p_flex_grow, p_flex_grow => true
  | p_custom s1, p_custom s2 => (s1 =? s2)%string
  | _, _ => false
  end.

Fixpoint find_decl (p : Property) (decls : list Decl) : option Decl :=
  match decls with
  | [] => None
  | d :: ds => if prop_eq p (decl_prop d) then Some d else find_decl p ds
  end.

Fixpoint cascade_resolve (availW : nat) (anc : list Node) (p : Property) (n : Node) (css : CSS) 
                         (best_spec : nat) (best_imp : bool) (best_val : option Value) : option Value :=
  match css with
  | [] => best_val
  | mq_r :: rest => 
      if eval_mq (mq_cond mq_r) availW then
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
        let res_tuple := resolve_rules (mq_rules mq_r) best_spec best_imp best_val in
        let '(nspec, nimp, nval) := res_tuple in
        cascade_resolve availW anc p n rest nspec nimp nval
      else cascade_resolve availW anc p n rest best_spec best_imp best_val
  end.

Definition resolve (availW : nat) (anc : list Node) (p : Property) (n : Node) (css : CSS) : option Value :=
  cascade_resolve availW anc p n css 0 false None.

(** 3. STYLE *)

Inductive Position : Set := s_static | s_relative | s_absolute.
Inductive DisplayType : Set := d_block | d_inline | d_none.

Record Style : Set := {
  s_disp : DisplayType;
  s_pos : Position;
  s_width : Value; s_height : Value;
  s_color : string
}.

Definition compute_style (availW : nat) (anc : list Node) (parent : option Style) (n : Node) (css : CSS) : Style :=
  {| s_disp := d_block;
     s_pos := s_static;
     s_width := match resolve availW anc p_width n css with Some v => v | None => v_px 0 end;
     s_height := v_px 0;
     s_color := match resolve availW anc p_color n css with 
                | Some (v_str c) => c 
                | _ => match parent with Some ps => s_color ps | None => "black" end end |}.

Record Rect : Set := { rx : nat; ry : nat; rw : nat; rh : nat }.
Inductive Box : Set := mkBox : Node -> Rect -> Style -> list Box -> Box.
Definition Layout := list Box.

Definition render (availW : nat) (n : Node) (css : CSS) : Layout :=
  let s := compute_style availW [] None n css in
  [mkBox n {| rx:=0; ry:=0; rw:=0; rh:=0 |} s []].

(** 4. TESTS *)

Definition mk_decl p v imp := {| decl_prop := p; decl_val := v; decl_important := imp |}.
Definition mk_rule s ds := {| rule_sel := s; rule_decls := ds |}.
Definition mk_mq c rs := {| mq_cond := c; mq_rules := rs |}.

Example t33: 
  let css := [mk_mq mq_always [
    mk_rule (sel_tag body) [mk_decl (p_custom "--brand-col") (v_str "red") false];
    mk_rule (sel_tag div) [mk_decl p_color (v_var "--brand-col") false]
  ]] in
  let s := compute_style 800 [] None (elem div [] []) css in
  s_color s = "black". Proof. reflexivity. Qed.

Example t34:
  let css := [mk_mq mq_always [
    mk_rule (sel_tag div) [mk_decl p_width (v_calc (v_pct 100) op_sub (v_px 20)) false]
  ]] in
  let s := compute_style 800 [] None (elem div [] []) css in
  s_width s = v_calc (v_pct 100) op_sub (v_px 20). Proof. reflexivity. Qed.

Example t35:
  let css := [mk_mq mq_always [
    mk_rule (sel_pseudo (sel_tag span) "after") [mk_decl p_color (v_str "red") false]
  ]] in
  resolve 800 [] p_color (elem span [] []) css = Some (v_str "red"). Proof. reflexivity. Qed.

Example t36:
  let css := [mk_mq mq_always [
    mk_rule (sel_tag div) [mk_decl p_width (v_rem 2) false]
  ]] in
  let s := compute_style 800 [] None (elem div [] []) css in
  s_width s = v_rem 2. Proof. reflexivity. Qed.

Theorem uniqueness : forall w n css b1 b2, render w n css = b1 -> render w n css = b2 -> b1 = b2.
Proof. intros. rewrite <- H, <- H0. reflexivity. Qed.