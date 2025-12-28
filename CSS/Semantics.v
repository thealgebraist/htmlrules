Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(** 1. COMPREHENSIVE AST *)

Inductive Tag : Set := div | span | p | img | h1 | body.

Definition tag_eq (t1 t2 : Tag) : bool :=
  match t1, t2 with
  | div, div => true | span, span => true | p, p => true 
  | img, img => true | h1, h1 => true | body, body => true | _, _ => false
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
  | v_pct : nat -> Value
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
  end.

Fixpoint specificity (s : Selector) : nat :=
  match s with
  | sel_id _ => 100
  | sel_class _ => 10
  | sel_tag _ => 1
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

(** 3. STYLE & LAYOUT *)

Inductive Position : Set := s_static | s_relative | s_absolute.
Record SideValues : Set := { t_v : nat; r_v : nat; b_v : nat; l_v : nat }.
Inductive BoxSizing : Set := content_box | border_box.
Inductive DisplayType : Set := d_block | d_inline | d_none.

Record Style : Set := {
  s_disp : DisplayType;
  s_pos : Position;
  s_top : nat; s_left : nat; s_z_index : nat;
  s_width : Value; s_height : Value;
  s_margin : SideValues; s_padding : SideValues; s_border : SideValues;
  s_box_sizing : BoxSizing;
  s_color : string
}.

Definition compute_style (availW : nat) (anc : list Node) (parent : option Style) (n : Node) (css : CSS) : Style :=
  let get_val p def := match resolve availW anc p n css with Some v => v | None => def end in
  let get_px p def := match get_val p (v_px def) with v_px n => n | _ => def end in
  let disp_def := match n with 
                  | elem span _ _ => d_inline
                  | elem img _ _ => d_inline
                  | text _ => d_inline
                  | _ => d_block end in
  {| s_disp := match resolve availW anc p_display n css with
              | Some (v_str "inline") => d_inline | Some (v_str "none") => d_none | _ => disp_def end;
     s_pos := match resolve availW anc p_position n css with
              | Some (v_str "relative") => s_relative | Some (v_str "absolute") => s_absolute | _ => s_static end;
     s_top := get_px p_top 0; s_left := get_px p_left 0; s_z_index := get_px p_z_index 0;
     s_width := get_val p_width (v_px 0); s_height := get_val p_height (v_px 0);
     s_margin := let v := get_px p_margin 0 in {| t_v := v; r_v := v; b_v := v; l_v := v |};
     s_padding := let v := get_px p_padding 0 in {| t_v := v; r_v := v; b_v := v; l_v := v |};
     s_border := let v := get_px p_border 0 in {| t_v := v; r_v := v; b_v := v; l_v := v |};
     s_box_sizing := match resolve availW anc p_box_sizing n css with
                     | Some (v_str "border-box") => border_box | _ => content_box end;
     s_color := match resolve availW anc p_color n css with 
                | Some (v_str c) => c | _ => match parent with Some ps => s_color ps | None => "black" end end |}.

Record Rect : Set := { rx : nat; ry : nat; rw : nat; rh : nat }.
Inductive Box : Set := mkBox : Node -> Rect -> Style -> list Box -> Box.
Definition Layout := list Box.

Definition resolve_len (v : Value) (parent_len : nat) (def : nat) : nat :=
  match v with v_px n => n | v_pct n => (n * parent_len) / 100 | _ => def end.

Definition layout_node (anc : list Node) (availW : nat) (parent_s : option Style) 
                     (x y : nat) (n : Node) (css : CSS) : (list Box * (nat * nat)) :=
  let s := compute_style availW anc parent_s n css in
  match s_disp s with
  | d_none => ([], (x, y))
  | _ =>
      let m := s_margin s in let p := s_padding s in let b := s_border s in
      let flow_x := x + l_v m in let flow_y := y + t_v m in
      let final_pos := match s_pos s with
                       | s_relative => (flow_x + s_left s, flow_y + s_top s)
                       | s_absolute => (s_left s, s_top s)
                       | s_static => (flow_x, flow_y)
                       end in
      let content_w := resolve_len (s_width s) availW 0 in
      let content_h := resolve_len (s_height s) 0 0 in
      let bb_w := match s_box_sizing s with
                  | content_box => content_w + l_v p + r_v p + l_v b + r_v b
                  | border_box => content_w end in
      let bb_h := match s_box_sizing s with
                  | content_box => content_h + t_v p + b_v p + t_v b + b_v b
                  | border_box => content_h end in
      let box := mkBox n (Build_Rect (fst final_pos) (snd final_pos) bb_w bb_h) s [] in
      match s_disp s with
      | d_block => ([box], (x, y + bb_h + t_v m + b_v m))
      | d_inline => ([box], (x + bb_w + l_v m + r_v m, y))
      | d_none => ([], (x, y))
      end
  end.

Definition render (availW : nat) (n : Node) (css : CSS) : Layout :=
  match (layout_node [] availW None 0 0 n css) with | (res, _) => res end.

(** 4. 32 TEST CASE SUITE *)

Definition mk_decl p v imp := {| decl_prop := p; decl_val := v; decl_important := imp |}.
Definition mk_rule s ds := {| rule_sel := s; rule_decls := ds |}.
Definition mk_mq c rs := {| mq_cond := c; mq_rules := rs |}.

Example t1: resolve 800 [] p_color (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t2: resolve 800 [] p_color (elem div [{|attr_name:="class"; attr_value:="c"|}] []) [mk_mq mq_always [mk_rule (sel_class "c") [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t3: resolve 800 [] p_color (elem div [{|attr_name:="id"; attr_value:="i"|}] []) [mk_mq mq_always [mk_rule (sel_id "i") [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t4: resolve 800 [] p_color (elem div [{|attr_name:="class"; attr_value:="a b"|}] []) [mk_mq mq_always [mk_rule (sel_and (sel_class "a") (sel_class "b")) [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t5: resolve 800 [] p_color (elem div [{|attr_name:="class"; attr_value:="c"|}] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "blue") false]; mk_rule (sel_class "c") [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t6: resolve 800 [] p_color (elem div [{|attr_name:="class"; attr_value:="c"|}; {|attr_name:="id"; attr_value:="i"|}] []) [mk_mq mq_always [mk_rule (sel_class "c") [mk_decl p_color (v_str "blue") false]; mk_rule (sel_id "i") [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t7: resolve 800 [] p_color (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "blue") false]; mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t8: resolve 800 [] p_color (elem div [{|attr_name:="id"; attr_value:="i"|}] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") true]; mk_rule (sel_id "i") [mk_decl p_color (v_str "blue") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t9: matches [elem div [] []] (elem p [] []) (sel_desc (sel_tag div) (sel_tag p)) = true. Proof. reflexivity. Qed.
Example t10: has_class "b" "a b c" = true. Proof. reflexivity. Qed.
Example t11: has_class "c" "a b c" = true. Proof. reflexivity. Qed.
Example t12: resolve 1000 [] p_color (elem div [] []) [mk_mq (mq_min_width 800) [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t13: resolve 400 [] p_color (elem div [] []) [mk_mq (mq_min_width 800) [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]]] = None. Proof. reflexivity. Qed.
Example t14: match render 800 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_width (v_px 100) false; mk_decl p_padding (v_px 10) false; mk_decl p_box_sizing (v_str "border-box") false]]] with [mkBox _ r _ _] => rw r = 100 | _ => False end. Proof. reflexivity. Qed.
Example t15: match render 800 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_width (v_px 100) false; mk_decl p_padding (v_px 10) false]]] with [mkBox _ r _ _] => rw r = 120 | _ => False end. Proof. reflexivity. Qed.
Example t16: match render 800 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_width (v_pct 50) false]]] with [mkBox _ r _ _] => rw r = 400 | _ => False end. Proof. reflexivity. Qed.
Example t17: match render 800 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_position (v_str "absolute") false; mk_decl p_left (v_px 50) false]]] with [mkBox _ r _ _] => rx r = 50 | _ => False end. Proof. reflexivity. Qed.
Example t18: match render 800 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_position (v_str "relative") false; mk_decl p_left (v_px 10) false]]] with [mkBox _ r _ _] => rx r = 10 | _ => False end. Proof. reflexivity. Qed.
Example t19: match render 800 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_margin (v_px 20) false]]] with [mkBox _ r _ _] => rx r = 20 | _ => False end. Proof. reflexivity. Qed.
Example t20: render 800 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_display (v_str "none") false]]] = []. Proof. reflexivity. Qed.
Example t21: let s := compute_style 800 [] (Some {| s_disp:=d_block; s_pos:=s_static; s_top:=0; s_left:=0; s_z_index:=0; s_width:=v_px 0; s_height:=v_px 0; s_margin:={|t_v:=0;r_v:=0;b_v:=0;l_v:=0|}; s_padding:={|t_v:=0;r_v:=0;b_v:=0;l_v:=0|}; s_border:={|t_v:=0;r_v:=0;b_v:=0;l_v:=0|}; s_box_sizing:=content_box; s_color:="red" |}) (elem div [] []) [] in s_color s = "red". Proof. reflexivity. Qed.
Example t22: resolve 800 [] p_color (elem div [{|attr_name:="class"; attr_value:="a b c"|}] []) [mk_mq mq_always [mk_rule (sel_and (sel_class "a") (sel_class "b")) [mk_decl p_color (v_str "red") false]; mk_rule (sel_class "c") [mk_decl p_color (v_str "blue") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t23: resolve 800 [] p_color (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") true]; mk_rule (sel_tag div) [mk_decl p_color (v_str "blue") false]]] = Some (v_str "red"). Proof. reflexivity. Qed.
Example t24: let s := compute_style 800 [] None (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_z_index (v_px 10) false]]] in s_z_index s = 10. Proof. reflexivity. Qed.
Example t25: let s := compute_style 800 [] None (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_width (v_px 100) false; mk_decl p_color (v_str "green") false]]] in s_color s = "green" /\ s_width s = v_px 100. Proof. simpl. split; reflexivity. Qed.
Example t26: match render 800 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_height (v_px 50) false; mk_decl p_padding (v_px 10) false]]] with [mkBox _ r _ _] => rh r = 70 | _ => False end. Proof. reflexivity. Qed.
Example t27: match (layout_node [] 800 None 0 0 (elem span [] []) [mk_mq mq_always [mk_rule (sel_tag span) [mk_decl p_width (v_px 50) false]]]) with (_, (nx, ny)) => nx = 50 /\ ny = 0 end. Proof. simpl. split; reflexivity. Qed.
Example t28: match (layout_node [] 800 None 0 0 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_height (v_px 50) false]]]) with (_, (nx, ny)) => nx = 0 /\ ny = 50 end. Proof. simpl. split; reflexivity. Qed.
Example t29: resolve 800 [] p_color (elem body [] []) [mk_mq mq_always [mk_rule (sel_tag body) [mk_decl p_color (v_str "gray") false]]] = Some (v_str "gray"). Proof. reflexivity. Qed.
Example t30: resolve 800 [] p_color (elem p [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "red") false]]] = None. Proof. reflexivity. Qed.
Example t31: match render 400 (elem div [] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_width (v_pct 25) false]]] with [mkBox _ r _ _] => rw r = 100 | _ => False end. Proof. reflexivity. Qed.
Example t32: resolve 800 [] p_color (elem div [{|attr_name:="class"; attr_value:="c"|}] []) [mk_mq mq_always [mk_rule (sel_tag div) [mk_decl p_color (v_str "blue") true]; mk_rule (sel_class "c") [mk_decl p_color (v_str "red") true]]] = Some (v_str "red"). Proof. reflexivity. Qed.
