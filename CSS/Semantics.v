Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(** 1. FORMAL AST *)

Inductive Tag : Set := div | span | p | img | body.

Definition tag_eq (t1 t2 : Tag) : bool :=
  match t1, t2 with
  | div, div => true | span, span => true | p, p => true 
  | img, img => true | body, body => true | _, _ => false
  end.

Record Attr : Set := { attr_name : string; attr_value : string }.

Inductive Node : Set :=
  | text : string -> Node
  | elem : Tag -> list Attr -> list Node -> Node.

Inductive Property : Set :=
  | p_width | p_height | p_margin | p_padding | p_color | p_display.

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
  | sel_class : string -> Selector.

Record Rule : Set := { rule_sel : Selector; rule_decls : list Decl }.

Inductive MediaQuery : Set :=
  | mq_always : MediaQuery
  | mq_min_width : nat -> MediaQuery.

Record MQRule : Set := {
  mq_cond : MediaQuery;
  mq_rules : list Rule
}.

Definition CSS := list MQRule.

(** 2. RENDERING FSM DEFINITION *)

Inductive State : Set :=
  | S_Start : State
  | S_EvalMQ : State
  | S_MatchSelectors : State
  | S_Cascade : State
  | S_Inherit : State
  | S_Layout : State
  | S_Paint : State
  | S_End : State.

Definition transition (s : State) : State :=
  match s with
  | S_Start => S_EvalMQ
  | S_EvalMQ => S_MatchSelectors
  | S_MatchSelectors => S_Cascade
  | S_Cascade => S_Inherit
  | S_Inherit => S_Layout
  | S_Layout => S_Paint
  | S_Paint => S_End
  | S_End => S_End
  end.

(** 3. CORE SEMANTICS *)

Definition eval_mq (mq : MediaQuery) (availW : nat) : bool :=
  match mq with
  | mq_always => true
  | mq_min_width w => leb w availW
  end.

Fixpoint find_attr (name : string) (attrs : list Attr) : option string :=
  match attrs with
  | [] => None
  | a :: as' => if (attr_name a =? name)%string then Some (attr_value a) else find_attr name as'
  end.

Definition matches (n : Node) (s : Selector) : bool :=
  match s with
  | sel_tag t' => match n with elem t _ _ => tag_eq t t' | _ => false end
  | sel_class c => match n with elem _ attrs _ => 
                      match find_attr "class" attrs with Some v => (c =? v)%string | None => false end
                      | _ => false end
  end.

Definition prop_eq (p1 p2 : Property) : bool :=
  match p1, p2 with
  | p_width, p_width => true | p_height, p_height => true | p_margin, p_margin => true
  | p_padding, p_padding => true | p_color, p_color => true | p_display, p_display => true
  | _, _ => false
  end.

Fixpoint find_decl (p : Property) (decls : list Decl) : option Decl :=
  match decls with
  | [] => None
  | d :: ds => if prop_eq p (decl_prop d) then Some d else find_decl p ds
  end.

(** RESOLVE logic mapped to S_EvalMQ, S_MatchSelectors, S_Cascade *)
Fixpoint resolve (availW : nat) (p : Property) (n : Node) (css : CSS) 
                 (best_spec : nat) (best_imp : bool) (best_val : option Value) : option Value :=
  match css with
  | [] => best_val
  | mq_r :: rest => 
      if eval_mq (mq_cond mq_r) availW then
        let fix resolve_rules rules spec imp val :=
          match rules with
          | [] => (spec, imp, val)
          | r :: rs => 
              if matches n (rule_sel r) then
                match find_decl p (rule_decls r) with
                | Some d => 
                    let r_imp := decl_important d in
                    if (orb (andb r_imp (negb imp)) (andb (eqb r_imp imp) (leb spec 1))) (* simplified spec *)
                    then resolve_rules rs 1 r_imp (Some (decl_val d))
                    else resolve_rules rs spec imp val
                | None => resolve_rules rs spec imp val
                end
              else resolve_rules rs spec imp val
          end
        in
        let '(nspec, nimp, nval) := resolve_rules (mq_rules mq_r) best_spec best_imp best_val in
        resolve availW p n rest nspec nimp nval
      else resolve availW p n rest best_spec best_imp best_val
  end.

(** 4. STYLE & LAYOUT *)

Record Rect : Set := { rx : nat; ry : nat; rw : nat; rh : nat }.
Record Style : Set := { s_color : string; s_width : nat }.
Inductive Box : Set := mkBox : Node -> Rect -> Style -> Box.

Definition compute_style (availW : nat) (parent_col : string) (n : Node) (css : CSS) : Style :=
  let col := match resolve availW p_color n css 0 false None with
             | Some (v_str c) => c | _ => parent_col end in
  let w := match resolve availW p_width n css 0 false None with
           | Some (v_px n) => n | _ => 50 end in
  {| s_color := col; s_width := w |}.

Definition layout_node (availW : nat) (parent_col : string) (x y : nat) (n : Node) (css : CSS) : Box :=
  let s := compute_style availW parent_col n css in
  mkBox n (Build_Rect x y (s_width s) 20) s.

Definition render (availW : nat) (n : Node) (css : CSS) : Box :=
  layout_node availW "black" 0 0 n css.

(** 5. UNIQUENESS PROOFS *)

Theorem transition_unique : forall s s1 s2, transition s = s1 -> transition s = s2 -> s1 = s2.
Proof. intros. rewrite <- H, <- H0. reflexivity. Qed.

Theorem render_unique : forall w n css b1 b2, render w n css = b1 -> render w n css = b2 -> b1 = b2.
Proof. intros. rewrite <- H, <- H0. reflexivity. Qed.

(** Test Case: Media Query + !important *)
Example test_verified_cascade :
  let css := [ {| mq_cond := mq_always ; mq_rules := [ {| rule_sel := sel_tag div ; rule_decls := [ {| decl_prop := p_color ; decl_val := v_str "blue" ; decl_important := false |} ] |} ] |} ;
               {| mq_cond := mq_min_width 600 ; mq_rules := [ {| rule_sel := sel_tag div ; rule_decls := [ {| decl_prop := p_color ; decl_val := v_str "red" ; decl_important := true |} ] |} ] |} ] in
  let b := render 800 (elem div [] []) css in
  match b with mkBox _ _ s => s_color s = "red" end.
Proof. simpl. reflexivity. Qed.
