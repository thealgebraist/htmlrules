Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(** 1. REFINED AST *)

Inductive Tag : Set := div | span | p | body.

Definition tag_eq (t1 t2 : Tag) : bool :=
  match t1, t2 with
  | div, div => true | span, span => true | p, p => true | body, body => true
  | _, _ => false
  end.

Record Attr : Set := { attr_name : string; attr_value : string }.

Inductive Node : Set :=
  | text : string -> Node
  | elem : Tag -> list Attr -> list Node -> Node.

Inductive Property : Set := p_color | p_width.

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
  | sel_and   : Selector -> Selector -> Selector. (* .a.b *)

Record Rule : Set := { rule_sel : Selector; rule_decls : list Decl }.
Definition CSS := list Rule.

(** 2. TOKEN-BASED CLASS MATCHING *)

(* Recursive check if 'target' is a space-separated token in 's' *)
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

Fixpoint matches (n : Node) (s : Selector) : bool :=
  match s with
  | sel_tag t' => match n with elem t _ _ => tag_eq t t' | _ => false end
  | sel_class c => match n with elem _ attrs _ => 
                      match find_attr "class" attrs with Some v => has_class c v | None => false end
                      | _ => false end
  | sel_and s1 s2 => matches n s1 && matches n s2
  end.

Fixpoint specificity (s : Selector) : nat :=
  match s with
  | sel_tag _ => 1
  | sel_class _ => 10
  | sel_and s1 s2 => specificity s1 + specificity s2
  end.

(** 3. STYLE RESOLUTION *)

Fixpoint find_decl (p : Property) (decls : list Decl) : option Decl :=
  match decls with
  | [] => None
  | d :: ds => match d, p with
               | {| decl_prop := p_color |}, p_color => Some d
               | {| decl_prop := p_width |}, p_width => Some d
               | _, _ => find_decl p ds
               end
  end.

Fixpoint cascade (p : Property) (n : Node) (css : CSS) (best_spec : nat) (best_imp : bool) (best_val : option Value) : option Value :=
  match css with
  | [] => best_val
  | r :: rs => 
      if matches n (rule_sel r) then
        match find_decl p (rule_decls r) with
        | Some d => 
            let spec := specificity (rule_sel r) in
            let imp := decl_important d in
            if (orb (andb imp (negb best_imp)) (andb (eqb imp best_imp) (leb best_spec spec)))
            then cascade p n rs spec imp (Some (decl_val d))
            else cascade p n rs best_spec best_imp best_val
        | None => cascade p n rs best_spec best_imp best_val
        end
      else cascade p n rs best_spec best_imp best_val
  end.

(** 4. VERIFICATION *)

Theorem render_unique : forall p n css v1 v2, 
  cascade p n css 0 false None = v1 -> 
  cascade p n css 0 false None = v2 -> v1 = v2.
Proof. intros. rewrite <- H, <- H0. reflexivity. Qed.

(* Test: Multi-class string matching *)
Example test_multi_class :
  has_class "active" "nav-item active main" = true.
Proof. simpl. reflexivity. Qed.

(* Test: Compound Selector Intersection (.a.b) *)
Example test_intersection :
  let n := elem div [ {| attr_name := "class" ; attr_value := "a b" |} ] [] in
  let s := sel_and (sel_class "a") (sel_class "b") in
  matches n s = true.
Proof. simpl. reflexivity. Qed.
