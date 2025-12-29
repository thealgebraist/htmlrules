Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(** 1. UNIFIED FORMAL AST *)

Inductive Tag : Set := 
  | div | span | img | body | table | tr | td 
  | header | footer | main | section | article | nav | aside 
  | other.

Definition tag_eq (t1 t2 : Tag) : bool :=
  match t1, t2 with
  | div, div => true | span, span => true | img, img => true 
  | body, body => true | table, table => true | tr, tr => true | td, td => true
  | header, header => true | footer, footer => true | main, main => true
  | section, section => true | article, article => true | nav, nav => true | aside, aside => true
  | other, other => true
  | _, _ => false
  end.

Inductive DisplayType : Set := d_block | d_inline | d_none | d_table | d_table_row | d_table_cell.

Definition default_display (t : Tag) : DisplayType :=
  match t with
  | span | img => d_inline
  | tr => d_table_row
  | td => d_table_cell
  | table => d_table
  | other => d_none
  | _ => d_block
  end.

Record Attr : Set := { attr_name : string; attr_value : string }.

Inductive Node : Set :=
  | text : string -> Node
  | elem : Tag -> list Attr -> list Node -> Node.

Inductive Property : Set :=
  | p_width | p_height | p_margin_top | p_margin_bottom | p_padding | p_border
  | p_color | p_display | p_box_sizing
  | p_position | p_top | p_left | p_z_index.

Inductive Value : Set :=
  | v_px : nat -> Value
  | v_pct : nat -> Value
  | v_str : string -> Value.

Record Decl : Set := { 
  decl_prop : Property; 
  decl_val : Value;
  decl_important : bool 
}.

Inductive Selector : Set :=
  | sel_univ  : Selector
  | sel_tag   : Tag -> Selector
  | sel_class : string -> Selector
  | sel_id    : string -> Selector
  | sel_and   : Selector -> Selector -> Selector
  | sel_desc  : Selector -> Selector -> Selector.

Record Rule : Set := { rule_sel : Selector; rule_decls : list Decl }.

Inductive MediaQuery : Set :=
  | mq_always : MediaQuery
  | mq_min_width : nat -> MediaQuery.

Record MQRule : Set := {
  mq_cond : MediaQuery;
  mq_rules : list Rule
}.

Definition CSS := list MQRule.

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
  | sel_desc s1 s2 => 
      if matches anc n s2 then existsb (fun a => matches [] a s1) anc else false
  end.

Fixpoint specificity (s : Selector) : nat :=
  match s with
  | sel_id _ => 100
  | sel_class _ => 10
  | sel_tag _ => 1
  | sel_univ => 0
  | sel_and s1 s2 => specificity s1 + specificity s2
  | sel_desc s1 s2 => specificity s1 + specificity s2
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
  | p_z_index, p_z_index => true | _, _ => false
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

(** 3. STYLE & MULTI-PASS LAYOUT *)

Inductive Position : Set := s_static | s_relative | s_absolute.


Record Style : Set := {
  s_disp : DisplayType;
  s_pos : Position;
  s_top_v : nat; s_left_v : nat;
  s_width : Value; s_height : Value;
  s_margin_top : nat; s_margin_bottom : nat;
  s_color : string
}.

Definition compute_style (availW : nat) (anc : list Node) (n : Node) (css : CSS) : Style :=
  let get_val p def := match resolve availW anc p n css with Some v => v | None => def end in
  let get_px p def := match get_val p (v_px def) with v_px n => n | _ => def end in
  {| s_disp := match resolve availW anc p_display n css with
              | Some (v_str "inline") => d_inline | Some (v_str "none") => d_none 
              | Some (v_str "table") => d_table | Some (v_str "table-row") => d_table_row 
              | Some (v_str "table-cell") => d_table_cell | Some (v_str "block") => d_block
              | _ => match n with elem t _ _ => default_display t | text _ => d_inline end end;
     s_pos := match resolve availW anc p_position n css with
              | Some (v_str "relative") => s_relative | Some (v_str "absolute") => s_absolute | _ => s_static end;
     s_top_v := get_px p_top 0; s_left_v := get_px p_left 0;
     s_width := get_val p_width (v_px 0); s_height := get_val p_height (v_px 0);
     s_margin_top := get_px p_margin_top 0; s_margin_bottom := get_px p_margin_bottom 0;
     s_color := match resolve availW anc p_color n css with | Some (v_str c) => c | _ => "black" end |}.

Record Rect : Set := { rx : nat; ry : nat; rw : nat; rh : nat }.
Inductive LayoutBox : Set := mkLBox : Rect -> list LayoutBox -> LayoutBox.

Definition resolve_len (v : Value) (parent_len : nat) (def : nat) : nat :=
  match v with v_px n => n | v_pct n => (n * parent_len) / 100 | _ => def end.

Fixpoint measure (availW : nat) (anc : list Node) (n : Node) (css : CSS) : (nat * nat) :=
  let s := compute_style availW anc n css in
  match n with
  | text _ => (0, 20)
  | elem t attrs kids =>
      let fix measure_kids l w pending :=
        match l with
        | [] => (0, 0)
        | k :: ks => 
            let '(kw, kh) := measure w (n :: anc) k css in
            let sk := compute_style w (n :: anc) k css in
            let collapsed := max pending (s_margin_top sk) in
            let '(restw, resth) := measure_kids ks w (s_margin_bottom sk) in
            match s_disp s with
            | d_table_row => (kw + restw, Init.Nat.max kh resth)
            | _           => (Init.Nat.max kw restw, collapsed + kh + resth)
            end
        end
      in
      let cw_val := resolve_len (s_width s) availW 0 in
      let content_w := if Nat.eqb cw_val 0 then availW else cw_val in
      let '(kw, kh) := measure_kids kids content_w 0 in
      (if Nat.eqb cw_val 0 then match s_disp s with d_block => availW | _ => kw end else cw_val,
       let ch_val := resolve_len (s_height s) 0 0 in
       if Nat.eqb ch_val 0 then (if Nat.eqb kh 0 then 20 else kh) else ch_val)
  end.

Fixpoint position (availW : nat) (x y : nat) (anc : list Node) (n : Node) (css : CSS) {struct n} : LayoutBox :=
  let s := compute_style availW anc n css in
  let '(mw, mh) := measure availW anc n css in
  match n with
  | text _ => mkLBox {| rx := x + s_left_v s; ry := y + s_top_v s; rw := mw; rh := mh |} []
  | elem _ _ kids =>
      let fix pos_kids l (container_w : nat) cx cy pending :=
        match l with
        | [] => []
        | k :: ks =>
            let sk := compute_style container_w (n :: anc) k css in
            let collapsed := max pending (s_margin_top sk) in
            let lb := position container_w cx (cy + collapsed) (n :: anc) k css in
            let '(kmw, kmh) := measure container_w (n :: anc) k css in
            match s_disp s with
            | d_table_row => lb :: pos_kids ks container_w (cx + kmw) cy 0
            | _           => lb :: pos_kids ks container_w cx (cy + collapsed + kmh) (s_margin_bottom sk)
            end
        end
      in
      mkLBox {| rx := x + s_left_v s; ry := y + s_top_v s; rw := mw; rh := mh |} 
             (pos_kids kids mw (x + s_left_v s) (y + s_top_v s) 0)
  end.

Definition render (availW : nat) (n : Node) (css : CSS) : LayoutBox :=
  position availW 0 0 [] n css.

Definition is_block_flow (s : Style) : Prop :=
  s_disp s = d_block /\ s_pos s = s_static /\ s_top_v s = 0 /\ s_left_v s = 0.

(** 4. 50 SANITY TESTS *)

Definition mk_mq c rs := {| mq_cond := c; mq_rules := rs |}.
Definition mk_rule s ds := {| rule_sel := s; rule_decls := ds |}.
Definition mk_decl p v imp := {| decl_prop := p; decl_val := v; decl_important := imp |}.

Definition get_rect (lb : LayoutBox) : Rect := match lb with mkLBox r _ => r end.
Definition get_kids (lb : LayoutBox) : list LayoutBox := match lb with mkLBox _ k => k end.

Example t1: resolve 800 [] p_color (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t2: contains_token "a" "a b c" "" = true. Proof. reflexivity. Qed.
Example t3: specificity (sel_and (sel_class "a") (sel_tag div)) = 11. Proof. reflexivity. Qed.
Example t4: eval_mq (mq_min_width 600) 800 = true. Proof. reflexivity. Qed.
Example t5: resolve_len (v_pct 50) 800 0 = 400. Proof. reflexivity. Qed.
Example t6: match render 800 (elem div [] [elem div [] []; elem div [] []]) [] with mkLBox _ (c1 :: c2 :: []) => ry (get_rect c2) = 20 | _ => False end. Proof. reflexivity. Qed.
Example t7: let css := [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_width (v_px 100) false]]] in rw (get_rect (render 800 (elem div [] []) css)) = 100. Proof. reflexivity. Qed.
Example t8: matches [elem div [] []] (elem div [] []) (sel_desc (sel_tag div) (sel_tag div)) = true. Proof. reflexivity. Qed.
Example t9: specificity sel_univ = 0. Proof. reflexivity. Qed.
Example t10: let css := [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_display (v_str "none") false]]] in s_disp (compute_style 800 [] (elem div [] []) css) = d_none. Proof. reflexivity. Qed.
Example t11: let css := [mk_mq mq_always [mk_rule (sel_tag tr) [mk_decl p_display (v_str "table-row") false]]] in s_disp (compute_style 800 [] (elem tr [] []) css) = d_table_row. Proof. reflexivity. Qed.
Example t12: match render 800 (elem tr [] [elem td [] []; elem td [] []]) [mk_mq mq_always [mk_rule (sel_tag tr) [mk_decl p_display (v_str "table-row") false]]] with mkLBox _ (c1 :: c2 :: []) => ry (get_rect c1) = ry (get_rect c2) | _ => False end. Proof. vm_compute. reflexivity. Qed.
Example t13: let css := [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") true]; mk_rule (sel_id "i") [mk_decl p_color (v_str "blue") false]]] in resolve 800 [] p_color (elem div [{|attr_name:="id";attr_value:="i"|}] []) css = Some (v_str "red"). Proof. reflexivity. Qed.
Example t14: specificity (sel_class "c") = 10. Proof. reflexivity. Qed.
Example t15: matches [] (elem div [{|attr_name:="class";attr_value:="a b"|}] []) (sel_class "b") = true. Proof. reflexivity. Qed.
Example t16: prop_eq p_width p_width = true. Proof. reflexivity. Qed.
Example t17: tag_eq div div = true. Proof. reflexivity. Qed.
Example t18: tag_eq div span = false. Proof. reflexivity. Qed.
Example t19: let s := compute_style 800 [] (elem div [] []) [] in s_color s = "black". Proof. reflexivity. Qed.
Example t20: resolve_len (v_px 50) 800 0 = 50. Proof. reflexivity. Qed.
Example t21: match render 800 (elem div [] []) [] with mkLBox r _ => rw r = 800 end. Proof. reflexivity. Qed.
Example t22: match render 800 (elem div [] []) [] with mkLBox r _ => rh r = 20 end. Proof. reflexivity. Qed.
Example t23: let css := [mk_mq (mq_min_width 1000) [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]]] in resolve 800 [] p_color (elem div [] []) css = None. Proof. reflexivity. Qed.
Example t24: let css := [mk_mq (mq_min_width 600) [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]]] in resolve 800 [] p_color (elem div [] []) css = Some (v_str "red"). Proof. reflexivity. Qed.
Example t25: matches [] (elem div [] []) (sel_tag div) = true. Proof. reflexivity. Qed.
Example t26: matches [] (elem div [] []) (sel_tag span) = false. Proof. reflexivity. Qed.
Example t27: specificity (sel_tag body) = 1. Proof. reflexivity. Qed.
Example t28: specificity (sel_id "i") = 100. Proof. reflexivity. Qed.
Example t29: specificity (sel_desc (sel_tag div) (sel_tag div)) = 2. Proof. reflexivity. Qed.
Example t30: match render 800 (elem tr [] [elem td [] []; elem td [] []]) [mk_mq mq_always [mk_rule (sel_tag tr) [mk_decl p_display (v_str "table-row") false]; mk_rule (sel_tag td) [mk_decl p_width (v_px 100) false]]] with mkLBox _ (c1 :: c2 :: []) => rx (get_rect c2) = 100 | _ => False end. Proof. vm_compute. reflexivity. Qed.

Definition empty_css : CSS := [].

Definition t_div_img : Node :=
  elem div [Build_Attr "width" "100"] [
    elem img [Build_Attr "width" "50"; Build_Attr "height" "50"] []
  ].

Example unit_test_div_img :
  measure 1000 [] t_div_img empty_css = (1000, 20).
Proof. vm_compute. reflexivity. Qed.
Example t31: let css := [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]; mk_rule (sel_tag div) [mk_decl p_color (v_str "blue") false]]] in resolve 800 [] p_color (elem div [] []) css = Some (v_str "blue"). Proof. reflexivity. Qed.
Example t32: specificity (sel_and (sel_class "a") (sel_class "b")) = 20. Proof. reflexivity. Qed.
Example t33: let css := [mk_mq mq_always [mk_rule (sel_tag body) [mk_decl p_width (v_px 1000) false]]] in rw (get_rect (render 800 (elem body [] []) css)) = 1000. Proof. reflexivity. Qed.
Example t34: match render 800 (elem div [] [elem div [] []]) [] with mkLBox _ (c1 :: []) => ry (get_rect c1) = 0 | _ => False end. Proof. reflexivity. Qed.
Example t35: match render 800 (elem div [] [elem div [] []]) [] with mkLBox r _ => rh r = 20 end. Proof. reflexivity. Qed.
Example t36: contains_token "active" "active" "" = true. Proof. reflexivity. Qed.
Example t37: contains_token "active" "inactive" "" = false. Proof. reflexivity. Qed.
Example t38: contains_token "active" "nav-item active" "" = true. Proof. reflexivity. Qed.
Example t39: specificity (sel_desc (sel_id "i") (sel_class "c")) = 110. Proof. reflexivity. Qed.
Example t40: matches [] (elem div [] []) (sel_tag div) = true. Proof. reflexivity. Qed.
Example t41: matches [] (elem img [] []) (sel_tag img) = true. Proof. reflexivity. Qed.
Example t42: eval_mq mq_always 0 = true. Proof. reflexivity. Qed.
Example t43: resolve_len (v_pct 100) 500 0 = 500. Proof. reflexivity. Qed.
Example t44: let css := [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_height (v_px 100) false]]] in rh (get_rect (render 800 (elem div [] []) css)) = 100. Proof. reflexivity. Qed.
Example t45: match render 800 (elem div [] [text "hi"]) [] with mkLBox r _ => rh r = 20 end. Proof. reflexivity. Qed.
Example t46: matches [elem body [] []] (elem div [] []) (sel_desc (sel_tag body) (sel_tag div)) = true. Proof. reflexivity. Qed.
Example t47: matches [elem div [] []] (elem div [] []) (sel_desc (sel_tag body) (sel_tag div)) = false. Proof. reflexivity. Qed.
Example t48: let css := [mk_mq mq_always [mk_rule (sel_class "c") [mk_decl p_color (v_str "red") true]]] in resolve 800 [] p_color (elem div [{|attr_name:="class";attr_value:="c"|}] []) css = Some (v_str "red"). Proof. reflexivity. Qed.
Example t49: let css := [mk_mq mq_always [mk_rule (sel_univ) [mk_decl p_color (v_str "gray") false]]] in resolve 800 [] p_color (elem span [] []) css = Some (v_str "gray"). Proof. reflexivity. Qed.
Example t50: tag_eq body body = true. Proof. reflexivity. Qed.

Theorem uniqueness : forall w n css b1 b2, render w n css = b1 -> render w n css = b2 -> b1 = b2.
Proof. intros. rewrite <- H, <- H0. reflexivity. Qed.

(** 5. ORDER PRESERVATION PROOFS *)

Fixpoint sorted_y (lbs : list LayoutBox) : Prop :=
  match lbs with
  | [] => True
  | b1 :: rest =>
      match rest with
      | [] => True
      | b2 :: _ => ry (get_rect b1) <= ry (get_rect b2) /\ sorted_y rest
      end
  end.

Fixpoint sorted_x (lbs : list LayoutBox) : Prop :=
  match lbs with
  | [] => True
  | b1 :: rest =>
      match rest with
      | [] => True
      | b2 :: _ => rx (get_rect b1) + rw (get_rect b1) <= rx (get_rect b2) /\ sorted_x rest
      end
  end.

Theorem structural_preservation : forall w n css,
  match n with
  | elem _ _ kids => List.length (get_kids (render w n css)) = List.length kids
  | text _ => List.length (get_kids (render w n css)) = 0
  end.
Proof.
  intros. destruct n.
  - simpl. reflexivity.
  - Admitted.

Lemma compute_style_ignore_kids : forall w anc t attrs k1 k2 css,
   compute_style w anc (elem t attrs k1) css = compute_style w anc (elem t attrs k2) css.
Proof. Admitted.

Theorem table_rows_sorted : forall w attrs kids css,
  let parent := elem table attrs kids in
  let s := compute_style w [] parent css in
  s_disp s = d_table -> 
  sorted_y (get_kids (render w parent css)).
Proof. Admitted.

Theorem table_cells_sorted : forall w attrs kids css,
  let parent := elem tr attrs kids in
  let s := compute_style w [] parent css in
  s_disp s = d_table_row -> 
  sorted_x (get_kids (render w parent css)).
Proof. Admitted.