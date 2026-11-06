(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
From Ltac2 Require Ltac2 FMap FSet.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SLN.
  Inductive lexp : Set :=
  | LA (i : nat) | LC (z : Z) | LN (n : nat) | LNz (z : Z) | LAdd (a b : lexp) | LSub (a b : lexp) | LMul (z : Z) (a : lexp) | LMulr (a : lexp) (z : Z).
  Fixpoint eval (env : list Z) (e : lexp) : Z :=
    match e with
    | LA i => nth i env 0 | LC z => z | LN n => Z.of_nat n | LNz z => Z.of_nat (Z.to_nat z)
    | LAdd a b => eval env a + eval env b | LSub a b => eval env a - eval env b
    | LMul z a => z * eval env a | LMulr a z => eval env a * z
    end.
  (* [comment removed for export] *)
  Definition lf := (list Z * Z)%type.
  Fixpoint dot (ks : list Z) (env : list Z) : Z :=
    match ks with
    | [] => 0
    | k :: ks' => k * hd 0 env + dot ks' (tl env)
    end.
  Definition eval_lf (env : list Z) (f : lf) : Z := dot (fst f) env + snd f.
  Fixpoint vadd (a b : list Z) : list Z :=
    match a, b with
    | [], _ => b
    | _, [] => a
    | x :: a', y :: b' => (x + y) :: vadd a' b'
    end.
  Definition vscale (c : Z) (a : list Z) : list Z := map (Z.mul c) a.
  Fixpoint unit_at (i : nat) : list Z := match i with O => [1] | S j => 0 :: unit_at j end.
  Definition lf_add (a b : lf) : lf := (vadd (fst a) (fst b), snd a + snd b).
  Definition lf_scale (c : Z) (a : lf) : lf := (vscale c (fst a), c * snd a).
  Definition lf_sub (a b : lf) : lf := lf_add a (lf_scale (-1) b).
  Fixpoint norm (e : lexp) : lf :=
    match e with
    | LA i => (unit_at i, 0) | LC z => ([], z) | LN n => ([], Z.of_nat n) | LNz z => ([], Z.max 0 z)
    | LAdd a b => lf_add (norm a) (norm b) | LSub a b => lf_sub (norm a) (norm b)
    | LMul z a => lf_scale z (norm a) | LMulr a z => lf_scale z (norm a)
    end.
  Lemma dot_vadd : forall a b env, dot (vadd a b) env = dot a env + dot b env.
  Proof. induction a as [|x a IH]; intros [|y b] env; cbn [vadd dot]; try lia. rewrite IH. lia. Qed.
  Lemma dot_vscale : forall c a env, dot (vscale c a) env = c * dot a env.
  Proof. intros c a; induction a as [|x a IH]; intros env; cbn [vscale map dot]; [lia|]. unfold vscale in IH. rewrite IH. lia. Qed.
  Lemma dot_unit : forall i env, dot (unit_at i) env = nth i env 0.
  Proof. induction i as [|i IH]; intros [|x env]; cbn [unit_at dot hd tl nth]; try lia; rewrite IH; try lia. destruct i; cbn; lia. Qed.
  Lemma lf_add_ok : forall env a b, eval_lf env (lf_add a b) = eval_lf env a + eval_lf env b.
  Proof. intros env [a ca] [b cb]; unfold eval_lf, lf_add; cbn [fst snd]. rewrite dot_vadd. lia. Qed.
  Lemma lf_scale_ok : forall env c a, eval_lf env (lf_scale c a) = c * eval_lf env a.
  Proof. intros env c [a ca]; unfold eval_lf, lf_scale; cbn [fst snd]. rewrite dot_vscale. lia. Qed.
  Lemma lf_sub_ok : forall env a b, eval_lf env (lf_sub a b) = eval_lf env a - eval_lf env b.
  Proof. intros; unfold lf_sub. rewrite lf_add_ok, lf_scale_ok. lia. Qed.
  Lemma norm_ok : forall env e, eval env e = eval_lf env (norm e).
  Proof.
    intros env e; induction e; cbn [eval norm].
    - unfold eval_lf; cbn [fst snd]. rewrite dot_unit. lia.
    - reflexivity.
    - reflexivity.
    - unfold eval_lf; cbn [fst snd dot]. destruct z as [|p|p]; [reflexivity| |reflexivity].
      rewrite Z2Nat.id by (apply Pos2Z.is_nonneg). rewrite Z.max_r by (apply Pos2Z.is_nonneg). reflexivity.
    - rewrite lf_add_ok. lia.
    - rewrite lf_sub_ok. lia.
    - rewrite lf_scale_ok. lia.
    - rewrite lf_scale_ok. lia.
  Qed.
  (* [comment removed for export] *)
  Record fact : Set := mkF { f_l : lexp; f_r : lexp; f_strict : bool; f_mul : Z }.
  Definition interp_fact (env : list Z) (f : fact) : Prop := if f_strict f then eval env (f_l f) < eval env (f_r f) else eval env (f_l f) <= eval env (f_r f).
  (* [comment removed for export] *)
  Definition fact_lf (f : fact) : lf := let d := lf_sub (norm (f_l f)) (norm (f_r f)) in if f_strict f then lf_add d ([], 1) else d.
  Lemma fact_lf_ok : forall env f, interp_fact env f -> eval_lf env (fact_lf f) <= 0.
  Proof.
    intros env f H. unfold interp_fact, fact_lf in *. destruct (f_strict f).
    - rewrite lf_add_ok, lf_sub_ok, <- !norm_ok. unfold eval_lf; cbn. lia.
    - rewrite lf_sub_ok, <- !norm_ok. lia.
  Qed.
  Fixpoint sum_facts (fs : list fact) : lf :=
    match fs with [] => ([], 0) | f :: r => lf_add (lf_scale (f_mul f) (fact_lf f)) (sum_facts r) end.
  Definition is_zero (ks : list Z) : bool := forallb (Z.eqb 0) ks.
  Lemma is_zero_ok : forall ks env, is_zero ks = true -> dot ks env = 0.
  Proof. induction ks as [|k ks IH]; intros env H; cbn [is_zero forallb dot] in *; [reflexivity|]. apply andb_true_iff in H. destruct H as [Hk H]. apply Z.eqb_eq in Hk. subst k. fold (is_zero ks) in H. rewrite (IH _ H). lia. Qed.
  (* [comment removed for export] *)
  Definition sum_chk (fs : list fact) (gl gr : lexp) : bool :=
    forallb (fun f => 0 <=? f_mul f) fs &&
    (let d := lf_sub (lf_sub (norm gl) (norm gr)) (sum_facts fs) in is_zero (fst d) && (snd d <=? 0)).
  Fixpoint impl_facts (env : list Z) (fs : list fact) (G : Prop) : Prop :=
    match fs with [] => G | f :: r => interp_fact env f -> impl_facts env r G end.
  Lemma sum_facts_le0 : forall env fs, forallb (fun f => 0 <=? f_mul f) fs = true -> Forall (interp_fact env) fs -> eval_lf env (sum_facts fs) <= 0.
  Proof.
    intros env fs; induction fs as [|f r IH]; intros Hm Hf; cbn [sum_facts].
    - unfold eval_lf; cbn; lia.
    - cbn [forallb] in Hm. apply andb_true_iff in Hm. destruct Hm as [Hm1 Hm2]. apply Z.leb_le in Hm1.
      inversion Hf as [|? ? H1 H2]; subst. rewrite lf_add_ok, lf_scale_ok.
      pose proof (fact_lf_ok env f H1). pose proof (IH Hm2 H2). nia.
  Qed.
  Lemma impl_intro : forall env fs (G : Prop), (Forall (interp_fact env) fs -> G) -> impl_facts env fs G.
  Proof.
    intros env fs; induction fs as [|f r IH]; intros G H; cbn [impl_facts].
    - apply H. constructor.
    - intros Hf. apply IH. intros Hr. apply H. constructor; assumption.
  Qed.
  Theorem sum_sound : forall env fs gl gr, sum_chk fs gl gr = true -> impl_facts env fs (eval env gl <= eval env gr).
  Proof.
    intros env fs gl gr H. apply impl_intro. intros Hf. unfold sum_chk in H.
    apply andb_true_iff in H. destruct H as [Hm H]. apply andb_true_iff in H. destruct H as [Hz Hc]. apply Z.leb_le in Hc.
    pose proof (sum_facts_le0 env fs Hm Hf) as HS.
    pose proof (is_zero_ok _ env Hz) as HZ.
    set (d := lf_sub (lf_sub (norm gl) (norm gr)) (sum_facts fs)) in *.
    assert (E : eval_lf env d = eval env gl - eval env gr - eval_lf env (sum_facts fs)).
    { subst d. rewrite !lf_sub_ok, <- !norm_ok. reflexivity. }
    unfold eval_lf in E at 1. rewrite HZ in E. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma z2n_ge : forall t : Z, t <= Z.of_nat (Z.to_nat t).
  Proof. intros t. destruct t as [|p|p]; [apply Z.le_refl| rewrite Z2Nat.id by (apply Pos2Z.is_nonneg); apply Z.le_refl| transitivity 0; [apply Pos2Z.neg_is_nonpos| apply Nat2Z.is_nonneg]]. Qed.
  Lemma z2n_le : forall t : Z, 0 <= t -> Z.of_nat (Z.to_nat t) <= t.
  Proof. intros t H. rewrite Z2Nat.id by exact H. apply Z.le_refl. Qed.
  Lemma eq_ge_incl : forall l r : Z, l = r -> r <= l. Proof. intros l r H; rewrite H; apply Z.le_refl. Qed.
  (* [comment removed for export] *)
  Lemma sep_use : forall b1 a2 b2 a1 e1 a e2 A : Z,
    (b1 <= a2 \/ b2 <= a1) -> a1 <= A -> e1 <= b1 -> a2 <= a -> e2 <= b2 -> (e1 <= a \/ e2 <= A).
  Proof. intros. lia. Qed.
  Lemma sep_use' : forall b1 a2 b2 a1 e1 a e2 A : Z,
    (b1 <= a2 \/ b2 <= a1) -> a2 <= A -> e1 <= b2 -> a1 <= a -> e2 <= b1 -> (e1 <= a \/ e2 <= A).
  Proof. intros. lia. Qed.
End SLN.

Module SL2.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 mutable sl_skip_hyps : unit -> ident list := fun () => [].
  Ltac2 Type cx := { hc : (constant, int) FMap.t; hi : (inductive, int) FMap.t; z_add : constr; z_sub : constr; z_mul : constr; z_ofnat : constr; z_tonat : constr; z_le : constr; z_lt : constr; z_ty : constr; z_pow : constr;
                     p_or : constr; p_and : constr; p_eq : constr; p_proj1 : constr; p_proj2 : constr; p_introl : constr; p_intror : constr;
                     p_eq_le : constr; p_eq_ge : constr; p_le_refl : constr; p_nonneg : constr; p_z2n_ge : constr; p_z2n_le : constr; p_id : constr; p_hide : constr; p_use : constr; p_use' : constr;
                     k_LA : constr; k_LC : constr; k_LN : constr; k_LNz : constr; k_LAdd : constr; k_LSub : constr; k_LMul : constr; k_LMulr : constr;
                     k_mkF : constr; k_fact : constr; k_chk : constr; k_sound : constr; k_true : constr; k_false : constr; k_bool : constr; k_refl : constr;
                     k_nil : constr; k_cons : constr; k_O : constr; k_S : constr; k_z0 : constr; k_zpos : constr; k_xH : constr; k_xO : constr; k_xI : constr }.
  Ltac2 gref (r : Std.reference) : constr := Env.instantiate r.
  Ltac2 mk_app (f : constr) (a : constr array) : constr := Constr.Unsafe.make (Constr.Unsafe.App f a).
  Ltac2 cadd (r : Std.reference) (k : int) (m : (constant, int) FMap.t) : (constant, int) FMap.t := match r with Std.ConstRef c => FMap.add c k m | _ => m end.
  Ltac2 iadd (r : Std.reference) (k : int) (m : (inductive, int) FMap.t) : (inductive, int) FMap.t := match r with Std.IndRef c => FMap.add c k m | _ => m end.
  (* [comment removed for export] *)
  Ltac2 mk_cx () : cx :=
    { hc := cadd reference:(Z.add) 1 (cadd reference:(Z.sub) 2 (cadd reference:(Z.mul) 3 (cadd reference:(Z.le) 4 (cadd reference:(Z.lt) 5 (FMap.empty FSet.Tags.constant_tag)))));
      hi := iadd reference:(and) 6 (iadd reference:(eq) 7 (FMap.empty FSet.Tags.inductive_tag));
      z_add := gref reference:(Z.add); z_sub := gref reference:(Z.sub); z_mul := gref reference:(Z.mul); z_ofnat := gref reference:(Z.of_nat);
      z_tonat := gref reference:(Z.to_nat); z_le := gref reference:(Z.le); z_lt := gref reference:(Z.lt); z_ty := gref reference:(Z); z_pow := gref reference:(Z.pow);
      p_or := gref reference:(or); p_and := gref reference:(and); p_eq := gref reference:(eq); p_proj1 := gref reference:(proj1); p_proj2 := gref reference:(proj2);
      p_introl := gref reference:(or_introl); p_intror := gref reference:(or_intror);
      p_eq_le := gref reference:(Z.eq_le_incl); p_le_refl := gref reference:(Z.le_refl); p_nonneg := gref reference:(Nat2Z.is_nonneg);
      p_z2n_ge := gref reference:(SLN.z2n_ge); p_z2n_le := gref reference:(SLN.z2n_le); p_eq_ge := gref reference:(SLN.eq_ge_incl); p_id := gref reference:(id); p_hide := gref reference:(StoreFast.sf_hide);
      p_use := gref reference:(SLN.sep_use); p_use' := gref reference:(SLN.sep_use');
      k_LA := gref reference:(SLN.LA); k_LC := gref reference:(SLN.LC); k_LN := gref reference:(SLN.LN); k_LNz := gref reference:(SLN.LNz);
      k_LAdd := gref reference:(SLN.LAdd); k_LSub := gref reference:(SLN.LSub); k_LMul := gref reference:(SLN.LMul);
      k_LMulr := gref reference:(SLN.LMulr); k_mkF := gref reference:(SLN.mkF); k_fact := gref reference:(SLN.fact);
      k_chk := gref reference:(SLN.sum_chk); k_sound := gref reference:(SLN.sum_sound);
      k_true := gref reference:(true); k_false := gref reference:(false); k_bool := gref reference:(bool);
      k_refl := mk_app (gref reference:(eq_refl)) [| gref reference:(bool); gref reference:(true) |];
      k_nil := gref reference:(nil); k_cons := gref reference:(cons); k_O := gref reference:(O); k_S := gref reference:(S);
      k_z0 := gref reference:(Z0); k_zpos := gref reference:(Zpos); k_xH := gref reference:(xH); k_xO := gref reference:(xO); k_xI := gref reference:(xI) }.
  Ltac2 nope () := Control.zero (Tactic_failure None).
  Ltac2 head_code (x : cx) (f : constr) : int :=
    match Constr.Unsafe.kind f with
    | Constr.Unsafe.Constant c _ => (match FMap.find_opt c (x.(hc)) with Some k => k | None => 0 end)
    | Constr.Unsafe.Ind i _ => (match FMap.find_opt i (x.(hi)) with Some k => k | None => 0 end)
    | _ => 0
    end.
  Ltac2 rec ctor_closed (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Constructor _ _ => true
    | Constr.Unsafe.App f args =>
        (match Constr.Unsafe.kind f with Constr.Unsafe.Constructor _ _ => Array.for_all ctor_closed args | _ => false end)
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 rec pos_int (x : cx) (p : constr) (fuel : int) : int :=
    if Int.le fuel 0 then -1 else
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.Constructor _ _ => if Constr.equal p (x.(k_xH)) then 1 else -1
    | Constr.Unsafe.App f args =>
        let r := pos_int x (Array.get args 0) (Int.sub fuel 1) in
        if Int.lt r 0 then -1
        else if Constr.equal f (x.(k_xO)) then Int.mul 2 r
        else if Constr.equal f (x.(k_xI)) then Int.add (Int.mul 2 r) 1 else -1
    | _ => -1
    end.
  Ltac2 zlit_int (x : cx) (z : constr) : int :=
    match Constr.Unsafe.kind z with
    | Constr.Unsafe.App f args => if Constr.equal f (x.(k_zpos)) then pos_int x (Array.get args 0) 24 else -1
    | _ => -1
    end.
  Ltac2 rec pos_of_int (x : cx) (n : int) : constr :=
    if Int.le n 1 then x.(k_xH)
    else if Int.equal (Int.mod n 2) 0 then mk_app (x.(k_xO)) [| pos_of_int x (Int.div n 2) |]
    else mk_app (x.(k_xI)) [| pos_of_int x (Int.div n 2) |].
  Ltac2 z_of_int (x : cx) (n : int) : constr := if Int.equal n 0 then x.(k_z0) else mk_app (x.(k_zpos)) [| pos_of_int x n |].
  Ltac2 rec nat_of_int (x : cx) (n : int) : constr := if Int.le n 0 then x.(k_O) else mk_app (x.(k_S)) [| nat_of_int x (Int.sub n 1) |].

  (* [comment removed for export] *)
  Ltac2 Type atbl := { mutable a_list : (constr * (int * ident)) list; mutable a_n : int; mutable a_avoid : Fresh.Free.t }.
  Ltac2 rec a_find (l : (constr * (int * ident)) list) (c : constr) : (int * ident) option :=
    match l with [] => None | p :: r => let (a, v) := p in if Constr.equal a c then Some v else a_find r c end.
  Ltac2 atom (t : atbl) (c : constr) : int * ident :=
    match a_find (t.(a_list)) c with
    | Some v => v
    | None =>
        let id := Fresh.fresh (t.(a_avoid)) @slx in
        t.(a_avoid) := Fresh.Free.union (t.(a_avoid)) (Fresh.Free.of_ids [id]);
        let v := (t.(a_n), id) in
        t.(a_list) := (c, v) :: t.(a_list); t.(a_n) := Int.add (t.(a_n)) 1; v
    end.
  (* [comment removed for export] *)
  Ltac2 rec l_add1 (i : int) (c : int) (l : (int * int) list) : (int * int) list :=
    match l with
    | [] => [(i, c)]
    | p :: r => let (j, d) := p in
                if Int.equal i j then (let s := Int.add c d in if Int.equal s 0 then r else (j, s) :: r) else p :: l_add1 i c r
    end.
  Ltac2 l_addm (m : int) (a : (int * int) list) (b : (int * int) list) : (int * int) list :=
    List.fold_left (fun acc p => let (i, c) := p in l_add1 i (Int.mul m c) acc) a b.
  Ltac2 rec l_coef (i : int) (l : (int * int) list) : int :=
    match l with [] => 0 | p :: r => let (j, d) := p in if Int.equal i j then d else l_coef i r end.

  (* [comment removed for export] *)
  Ltac2 rec parse (x : cx) (t : atbl) (c : constr) : constr * constr * (int * int) list :=
    let as_atom () :=
      let (i, id) := atom t c in (mk_app (x.(k_LA)) [| nat_of_int x i |], Constr.Unsafe.make (Constr.Unsafe.Var id), [(i, 1)]) in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        let n := Array.length args in
        if (if Int.equal n 2 then Constr.equal f (x.(z_add)) else false) then
          (let (la, ta, va) := parse x t (Array.get args 0) in let (lb, tb, vb) := parse x t (Array.get args 1) in
           (mk_app (x.(k_LAdd)) [| la; lb |], mk_app f [| ta; tb |], l_addm 1 va vb))
        else if (if Int.equal n 2 then Constr.equal f (x.(z_sub)) else false) then
          (let (la, ta, va) := parse x t (Array.get args 0) in let (lb, tb, vb) := parse x t (Array.get args 1) in
           (mk_app (x.(k_LSub)) [| la; lb |], mk_app f [| ta; tb |], l_addm (-1) va vb))
        else if (if Int.equal n 2 then Constr.equal f (x.(z_mul)) else false) then
          (let a := Array.get args 0 in let b := Array.get args 1 in
           let ka := if ctor_closed a then zlit_int x a else -1 in
           if Int.le 0 ka then (let (lb, tb, vb) := parse x t b in (mk_app (x.(k_LMul)) [| a; lb |], mk_app f [| a; tb |], l_addm ka [] vb))
           else (let kb := if ctor_closed b then zlit_int x b else -1 in
                 if Int.le 0 kb then (let (la, ta, va) := parse x t a in (mk_app (x.(k_LMulr)) [| la; b |], mk_app f [| ta; b |], l_addm kb [] va))
                 else as_atom ()))
        else if (if Int.equal n 1 then Constr.equal f (x.(z_ofnat)) else false) then
          (let a := Array.get args 0 in
           if ctor_closed a then (mk_app (x.(k_LN)) [| a |], c, [])
           else match Constr.Unsafe.kind a with
                | Constr.Unsafe.App g gargs =>
                    if (if Int.equal (Array.length gargs) 1 then (if Constr.equal g (x.(z_tonat)) then ctor_closed (Array.get gargs 0) else false) else false)
                    then (mk_app (x.(k_LNz)) [| Array.get gargs 0 |], c, []) else as_atom ()
                | _ => as_atom ()
                end)
        else if ctor_closed c then (mk_app (x.(k_LC)) [| c |], c, [])
        else if (if Int.equal n 2 then (if Constr.equal f (x.(z_pow)) then (if ctor_closed (Array.get args 0) then ctor_closed (Array.get args 1) else false) else false) else false)
        then (mk_app (x.(k_LC)) [| c |], c, [])
        else as_atom ()
    | Constr.Unsafe.Constructor _ _ => (mk_app (x.(k_LC)) [| c |], c, [])
    | _ => as_atom ()
    end.

  (* [comment removed for export] *)
  Ltac2 Type fct := { f_pf : constr; f_l : constr; f_r : constr; f_abs : constr; f_strict : bool; f_lin : (int * int) list }.
  Ltac2 rec facts_of (x : cx) (t : atbl) (pf : constr) (ty : constr) (acc : fct list) : fct list :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App f args =>
        let n := Array.length args in
        if (if Int.equal n 2 then Constr.equal f (x.(p_and)) else false) then
          (let p := Array.get args 0 in let q := Array.get args 1 in
           facts_of x t (mk_app (x.(p_proj1)) [| p; q; pf |]) p (facts_of x t (mk_app (x.(p_proj2)) [| p; q; pf |]) q acc))
        else if (if Int.equal n 2 then (if Constr.equal f (x.(z_le)) then true else Constr.equal f (x.(z_lt))) else false) then
          (let (ll, tl, vl) := parse x t (Array.get args 0) in let (lr, tr, vr) := parse x t (Array.get args 1) in
           { f_pf := pf; f_l := ll; f_r := lr; f_abs := mk_app f [| tl; tr |]; f_strict := Constr.equal f (x.(z_lt)); f_lin := l_addm (-1) vl vr } :: acc)
        else if (if Int.equal n 3 then (if Constr.equal f (x.(p_eq)) then Constr.equal (Array.get args 0) (x.(z_ty)) else false) else false) then
          (let l := Array.get args 1 in let r := Array.get args 2 in
           let (ll, tl, vl) := parse x t l in let (lr, tr, vr) := parse x t r in
           { f_pf := mk_app (x.(p_eq_le)) [| l; r; pf |]; f_l := ll; f_r := lr; f_abs := mk_app (x.(z_le)) [| tl; tr |]; f_strict := false; f_lin := l_addm (-1) vl vr }
           :: { f_pf := mk_app (x.(p_eq_ge)) [| l; r; pf |]; f_l := lr; f_r := ll; f_abs := mk_app (x.(z_le)) [| tr; tl |]; f_strict := false; f_lin := l_addm (-1) vr vl }
           :: acc)
        else acc
    | _ => acc
    end.
  Ltac2 rec mk_list (x : cx) (ty : constr) (l : constr list) : constr :=
    match l with [] => mk_app (x.(k_nil)) [| ty |] | a :: r => mk_app (x.(k_cons)) [| ty; a; mk_list x ty r |] end.

  (* [comment removed for export] *)
  Ltac2 arith_head (x : cx) (ty : constr) : bool :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App f args =>
        (match head_code x f with
         | 4 => true | 5 => true | 6 => true
         | 7 => Constr.equal (Array.get args 0) (x.(z_ty))
         | _ => false
         end)
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 Type pend := { pd_id : ident; pd_ty : constr; mutable pd_leaves : constr list option }.
  Ltac2 Type st := { s_t : atbl; mutable s_pending : pend list option; mutable s_facts : fct list; mutable s_done : int list; mutable s_busy : bool }.
  Ltac2 rec leaves_of (x : cx) (c : constr) (acc : constr list) : constr list :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        (match head_code x f with
         | 0 => if ctor_closed c then acc else c :: acc
         | 7 => leaves_of x (Array.get args 1) (leaves_of x (Array.get args 2) acc)
         | _ => leaves_of x (Array.get args 0) (leaves_of x (Array.get args 1) acc)
         end)
    | Constr.Unsafe.Constructor _ _ => acc
    | _ => c :: acc
    end.
  (* [comment removed for export] *)
  Ltac2 mk_st () : st := { s_t := { a_list := []; a_n := 0; a_avoid := Fresh.Free.of_ids [] }; s_pending := None; s_facts := []; s_done := []; s_busy := false }.
  Ltac2 pending (x : cx) (s : st) : pend list :=
    match s.(s_pending) with
    | Some l => l
    | None =>
        let skips := sl_skip_hyps () in
        let l := List.map_filter (fun h => let (id, body, ty) := h in
                   match body with
                   | Some _ => None
                   | None => if arith_head x ty then
                               (if (match skips with [] => false | _ :: _ => List.exist (Ident.equal id) skips end) then None
                                else Some { pd_id := id; pd_ty := ty; pd_leaves := None })
                             else None
                   end) (Control.hyps ()) in
        s.(s_pending) := Some l; l
    end.
  Ltac2 rec vars_of (c : constr) (acc : ident list) : ident list :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var id => if List.exist (Ident.equal id) acc then acc else id :: acc
    | Constr.Unsafe.App f args => Array.fold_left (fun a t => vars_of t a) (vars_of f acc) args
    | Constr.Unsafe.Cast t _ _ => vars_of t acc
    | Constr.Unsafe.Prod b body => vars_of body (vars_of (Constr.Binder.type b) acc)
    | _ => acc
    end.
  Ltac2 mentions (vs : ident list) (c : constr) : bool := if Constr.Unsafe.closedn 0 (Constr.Unsafe.closenl vs 1 c) then false else true.
  Ltac2 has_leaf (x : cx) (p : pend) (a : constr) : bool :=
    let ls := match p.(pd_leaves) with Some l => l | None => let l := leaves_of x (p.(pd_ty)) [] in p.(pd_leaves) := Some l; l end in
    List.exist (Constr.equal a) ls.
  Ltac2 rec atom_term (l : (constr * (int * ident)) list) (i : int) : constr option :=
    match l with [] => None | p :: r => let (a, v) := p in let (j, _) := v in if Int.equal i j then Some a else atom_term r i end.
  (* [comment removed for export] *)
  Ltac2 fetch (x : cx) (s : st) (nonneg : constr -> constr option) (i : int) : unit :=
    if List.exist (Int.equal i) (s.(s_done)) then () else
    (s.(s_done) := i :: s.(s_done);
     match atom_term ((s.(s_t)).(a_list)) i with
     | None => ()
     | Some a =>
         let l := pending x s in
         (* [comment removed for export] *)
         let vs := vars_of a [] in
         s.(s_pending) := Some (List.filter (fun p =>
           if (if (match vs with [] => true | _ :: _ => mentions vs (p.(pd_ty)) end) then has_leaf x p a else false)
           then (s.(s_facts) := facts_of x (s.(s_t)) (Constr.Unsafe.make (Constr.Unsafe.Var (p.(pd_id)))) (p.(pd_ty)) (s.(s_facts)); false) else true) l);
         (* [comment removed for export] *)
         (match Constr.Unsafe.kind a with
          | Constr.Unsafe.App f args =>
              if (if Int.equal (Array.length args) 1 then Constr.equal f (x.(z_ofnat)) else false) then
                (let n := Array.get args 0 in
                 s.(s_facts) := facts_of x (s.(s_t)) (mk_app (x.(p_nonneg)) [| n |]) (mk_app (x.(z_le)) [| x.(k_z0); a |]) (s.(s_facts));
                 match Constr.Unsafe.kind n with
                 | Constr.Unsafe.App g gargs =>
                     if (if Int.equal (Array.length gargs) 1 then Constr.equal g (x.(z_tonat)) else false) then
                       (let t := Array.get gargs 0 in
                        s.(s_facts) := facts_of x (s.(s_t)) (mk_app (x.(p_z2n_ge)) [| t |]) (mk_app (x.(z_le)) [| t; a |]) (s.(s_facts));
                        match nonneg t with
                        | Some p => s.(s_facts) := facts_of x (s.(s_t)) (mk_app (x.(p_z2n_le)) [| t; p |]) (mk_app (x.(z_le)) [| a; t |]) (s.(s_facts))
                        | None => ()
                        end)
                     else ()
                 | _ => ()
                 end)
              else ()
          | _ => ()
          end)
     end).

  (* [comment removed for export] *)
  Ltac2 Type res := [ Proof (constr) | Lit_false | No ].
  Ltac2 rec prove_le (x : cx) (s : st) (depth : int) (l : constr) (r : constr) : res :=
    let t := s.(s_t) in
    let (gl, tgl, vl) := parse x t l in let (gr, tgr, vr) := parse x t r in
    let g := l_addm (-1) vl vr in
    let nodes := Ref.ref 0 in let checks := Ref.ref 0 in
    let result := Ref.ref None in
    let finish (used : (fct * int) list) : bool :=
      Ref.set checks (Int.add (Ref.get checks) 1);
      let used := List.rev used in
      let fs := mk_list x (x.(k_fact)) (List.map (fun p => let (f, m) := p in
                  mk_app (x.(k_mkF)) [| f.(f_l); f.(f_r); (if f.(f_strict) then x.(k_true) else x.(k_false)); z_of_int x m |]) used) in
      if Constr.equal (Std.eval_vm None (mk_app (x.(k_chk)) [| fs; gl; gr |])) (x.(k_true)) then (Ref.set result (Some (used, fs)); true) else false in
    let rec dfs (res : (int * int) list) (used : (fct * int) list) (depth : int) : bool :=
      match res with
      | [] => finish used
      | p :: _ =>
          if Int.le depth 0 then false
          else if Int.lt 80 (Ref.get nodes) then false
          else if Int.lt 6 (Ref.get checks) then false
          else
            let (a, c) := p in
            fetch x s (fun t => if s.(s_busy) then None
                                 else (s.(s_busy) := true;
                                       let r := prove_le x s 2 (x.(k_z0)) t in
                                       s.(s_busy) := false;
                                       match r with Proof p => Some p | _ => None end)) a;
            let rec try_facts (fs : fct list) : bool :=
              match fs with
              | [] => false
              | f :: rest =>
                  let cf := l_coef a (f.(f_lin)) in
                  if (if Int.equal cf 0 then false
                      else if (if Int.lt 0 cf then Int.lt 0 c else Int.lt c 0) then
                        (if Int.equal (Int.mod c cf) 0 then (if List.exist (fun q => let (f', _) := q in Constr.equal (f'.(f_pf)) (f.(f_pf))) used then false else true) else false)
                      else false)
                  then (let m := Int.div c cf in
                        Ref.set nodes (Int.add (Ref.get nodes) 1);
                        if dfs (l_addm (Int.sub 0 m) res (f.(f_lin))) ((f, m) :: used) (Int.sub depth 1) then true else try_facts rest)
                  else try_facts rest
              end in
            try_facts (s.(s_facts))
      end in
    if dfs g [] depth then
      match Ref.get result with
      | None => No
      | Some ru =>
          let (used, fs) := ru in
          (* [comment removed for export] *)
          let al := List.rev (t.(a_list)) in
          let ids := List.map (fun p => let (_, v) := p in let (_, id) := v in id) al in
          let mkv (id : ident) := Constr.Unsafe.make (Constr.Unsafe.Var id) in
          let env := mk_list x (x.(z_ty)) (List.map mkv ids) in
          let anon (ty : constr) := Constr.Binder.make None ty in
          let stmt := List.fold_right (fun p acc => let (f, _) := p in Constr.Unsafe.make (Constr.Unsafe.Prod (anon (f.(f_abs))) acc))
                                      used (mk_app (x.(z_le)) [| tgl; tgr |]) in
          let body := Constr.Unsafe.make (Constr.Unsafe.Cast (mk_app (x.(k_sound)) [| env; fs; gl; gr; x.(k_refl) |]) Constr.Cast.default stmt) in
          let lam := List.fold_left (fun acc id => Constr.Unsafe.make (Constr.Unsafe.Lambda (Constr.Binder.make (Some id) (x.(z_ty))) acc))
                                    (Constr.Unsafe.closenl ids 1 body) ids in
          (* [comment removed for export] *)
          let live := vars_of stmt [] in
          let atoms := List.rev (List.map (fun p => let (a, v) := p in let (_, id) := v in if List.exist (Ident.equal id) live then a else x.(k_z0)) al) in
          Proof (mk_app lam (Array.of_list (List.append atoms (List.map (fun p => let (f, _) := p in f.(f_pf)) used))))
      end
    else (match g with [] => Lit_false | _ :: _ => No end).

  (* [comment removed for export] *)
  Ltac2 le_parts (x : cx) (c : constr) : (constr * constr) option :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f a => if (if Int.equal (Array.length a) 2 then Int.equal (head_code x f) 4 else false) then Some (Array.get a 0, Array.get a 1) else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 conj_parts (x : cx) (g : constr) : (constr * constr * constr * constr) option :=
    match Constr.Unsafe.kind g with
    | Constr.Unsafe.App o oargs =>
        if (if Int.equal (Array.length oargs) 2 then Constr.equal o (x.(p_or)) else false) then
          (match le_parts x (Array.get oargs 0) with
           | Some pl => (match le_parts x (Array.get oargs 1) with
                         | Some pr => let (e1, a) := pl in let (e2, aa) := pr in Some (e1, a, e2, aa)
                         | None => None end)
           | None => None end)
        else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 solve_depth (depth : int) : unit :=
    let x := mk_cx () in
    let g := Control.goal () in
    let s := mk_st () in
    match conj_parts x g with
    | Some c =>
        let (e1, a, e2, aa) := c in
        (match prove_le x s depth e1 a with
         | Proof p => Std.exact_no_check (mk_app (x.(p_introl)) [| mk_app (x.(z_le)) [| e1; a |]; mk_app (x.(z_le)) [| e2; aa |]; p |])
         | _ => (match prove_le x s depth e2 aa with
                 | Proof q => Std.exact_no_check (mk_app (x.(p_intror)) [| mk_app (x.(z_le)) [| e1; a |]; mk_app (x.(z_le)) [| e2; aa |]; q |])
                 | _ => nope ()
                 end)
         end)
    | None =>
        (match le_parts x g with
         | Some lr => let (l, r) := lr in (match prove_le x s depth l r with Proof p => Std.exact_no_check p | _ => nope () end)
         | None => nope ()
         end)
    end.
  (* [comment removed for export] *)
  Ltac2 sl_not_conj () : unit := let x := mk_cx () in match conj_parts x (Control.goal ()) with Some _ => nope () | None => () end.
  Ltac2 sl_same () : unit := solve_depth 0.
  Ltac2 sl_chain () : unit := solve_depth 4.

  (* [comment removed for export] *)
  Ltac2 rec base_of (x : cx) (t : constr) : constr :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        (match head_code x f with
         | 1 => base_of x (Array.get args 0)
         | 2 => base_of x (Array.get args 0)
         | _ => t
         end)
    | _ => t
    end.
  Ltac2 is_zlit_head (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Constructor _ _ => true
    | Constr.Unsafe.App f _ => (match Constr.Unsafe.kind f with Constr.Unsafe.Constructor _ _ => true | _ => false end)
    | _ => false
    end.
  Ltac2 same (u : constr) (v : constr) : bool := if Constr.equal u v then true else (if is_zlit_head u then is_zlit_head v else false).
  Ltac2 Type cand := { c_h : ident; c_b1 : constr; c_a2 : constr; c_b2 : constr; c_a1 : constr }.
  (* [comment removed for export] *)
  Ltac2 sl_sep (tac : unit -> unit) : unit :=
    let x := mk_cx () in
    match conj_parts x (Control.goal ()) with
    | None => nope ()
    | Some c0 =>
    let (e1, a, e2, aa) := c0 in
    let ba := base_of x aa in let bl := base_of x a in
    let plain := Ref.ref [] in let ids := Ref.ref [] in let hid := Ref.ref [] in
    List.iter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => ()
      | None =>
          match Constr.Unsafe.kind ty with
          | Constr.Unsafe.App f args =>
              let n := Array.length args in
              let try_add (r : cand list Ref.ref) (p : constr) : unit :=
                match conj_parts x p with
                | Some q => let (b1, a2, b2, a1) := q in Ref.set r ({ c_h := id; c_b1 := b1; c_a2 := a2; c_b2 := b2; c_a1 := a1 } :: Ref.get r)
                | None => ()
                end in
              if (if Int.equal n 2 then Constr.equal f (x.(p_or)) else false) then try_add plain ty
              else if (if Int.equal n 2 then Constr.equal f (x.(p_id)) else false) then try_add ids (Array.get args 1)
              else if (if Int.equal n 1 then Constr.equal f (x.(p_hide)) else false) then try_add hid (Array.get args 0)
              else ()
          | _ => ()
          end
      end) (Control.hyps ());
    (* [comment removed for export] *)
    let cands := List.append (Ref.get plain) (List.append (Ref.get ids) (Ref.get hid)) in
    let s := mk_st () in
    let side (l : constr) (r : constr) : res :=
      if Constr.equal l r then Proof (mk_app (x.(p_le_refl)) [| l |])
      else match prove_le x s 0 l r with
           | No => prove_le x s 2 l r      (* [comment removed for export] *)
           | v => v
           end in
    let attempt (lem : constr) (c : cand) (l1 : constr) (r1 : constr) (l2 : constr) (r2 : constr) (l3 : constr) (r3 : constr) (l4 : constr) (r4 : constr) : unit :=
      let s1 := side l1 r1 in let s2 := side l2 r2 in let s3 := side l3 r3 in let s4 := side l4 r4 in
      let dead (v : res) : bool := match v with Lit_false => true | _ => false end in
      if (if dead s1 then true else if dead s2 then true else if dead s3 then true else dead s4) then nope () else
      let args := [| c.(c_b1); c.(c_a2); c.(c_b2); c.(c_a1); e1; a; e2; aa; Control.hyp (c.(c_h)) |] in
      let all_lit := match s1 with Proof _ => (match s2 with Proof _ => (match s3 with Proof _ => (match s4 with Proof _ => true | _ => false end) | _ => false end) | _ => false end) | _ => false end in
      let pf (v : res) : constr := match v with Proof p => p | _ => Control.throw Not_found end in
      if all_lit then Std.exact_no_check (mk_app lem (Array.append args [| pf s1; pf s2; pf s3; pf s4 |]))
      else
        (let t := mk_app lem args in
         ltac1:(t |- apply t) (Ltac1.of_constr t);
         Control.dispatch (List.map (fun v => match v with Proof p => (fun () => Std.exact_no_check p) | _ => tac end) [s1; s2; s3; s4])) in
    let rec go (cs : cand list) : unit :=
      match cs with
      | [] => nope ()
      | c :: r =>
          let c1 := base_of x (c.(c_a1)) in let c2 := base_of x (c.(c_a2)) in
          Control.plus
            (fun () =>
               (* [comment removed for export] *)
               if (if same c1 ba then same c2 bl else false) then attempt (x.(p_use)) c (c.(c_a1)) aa e1 (c.(c_b1)) (c.(c_a2)) a e2 (c.(c_b2)) else nope ())
            (fun _ =>
               Control.plus
                 (fun () =>
                    (* [comment removed for export] *)
                    if (if same c2 ba then same c1 bl else false) then attempt (x.(p_use')) c (c.(c_a2)) aa e1 (c.(c_b2)) (c.(c_a1)) a e2 (c.(c_b1)) else nope ())
                 (fun _ => go r))
      end in
    Control.once (fun () => go cands)
    end.

  (* [comment removed for export] *)
  Ltac2 try_tac (t : unit -> unit) : bool := Control.once (fun () => Control.plus (fun () => t (); true) (fun _ => false)).
  Ltac2 sl_conj (old_same : unit -> unit) (side_tac : unit -> unit) (old_sep : unit -> unit) : unit :=
    let x := mk_cx () in
    match conj_parts x (Control.goal ()) with
    | None => nope ()
    | Some c0 =>
    let (e1, a, e2, aa) := c0 in
    let s := mk_st () in
    let pl := mk_app (x.(z_le)) [| e1; a |] in let pr := mk_app (x.(z_le)) [| e2; aa |] in
    let intro_l (p : constr) : unit := Std.exact_no_check (mk_app (x.(p_introl)) [| pl; pr; p |]) in
    let intro_r (q : constr) : unit := Std.exact_no_check (mk_app (x.(p_intror)) [| pl; pr; q |]) in
    (* [comment removed for export] *)
    let r1 := prove_le x s 0 e1 a in
    match r1 with
    | Proof p => intro_l p
    | _ =>
    let r2 := prove_le x s 0 e2 aa in
    match r2 with
    | Proof q => intro_r q
    | _ =>
    let ba := base_of x aa in let bl := base_of x a in
    let both_false := match r1 with Lit_false => (match r2 with Lit_false => true | _ => false end) | _ => false end in
    if (if same ba bl then (if both_false then false else try_tac old_same) else false) then () else
    (* [comment removed for export] *)
    let plain := Ref.ref [] in let ids := Ref.ref [] in let hid := Ref.ref [] in
    List.iter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => ()
      | None =>
          match Constr.Unsafe.kind ty with
          | Constr.Unsafe.App f args =>
              let n := Array.length args in
              let try_add (r : cand list Ref.ref) (p : constr) : unit :=
                match conj_parts x p with
                | Some q => let (b1, a2, b2, a1) := q in Ref.set r ({ c_h := id; c_b1 := b1; c_a2 := a2; c_b2 := b2; c_a1 := a1 } :: Ref.get r)
                | None => ()
                end in
              if (if Int.equal n 2 then Constr.equal f (x.(p_or)) else false) then try_add plain ty
              else if (if Int.equal n 2 then Constr.equal f (x.(p_id)) else false) then try_add ids (Array.get args 1)
              else if (if Int.equal n 1 then Constr.equal f (x.(p_hide)) else false) then try_add hid (Array.get args 0)
              else ()
          | _ => ()
          end
      end) (Control.hyps ());
    let cands := List.append (Ref.get plain) (List.append (Ref.get ids) (Ref.get hid)) in
    let passed := Ref.ref false in
    let side (l : constr) (r : constr) : res :=
      if Constr.equal l r then Proof (mk_app (x.(p_le_refl)) [| l |])
      else match prove_le x s 0 l r with
           | No => prove_le x s 2 l r      (* [comment removed for export] *)
           | v => v
           end in
    let attempt (lem : constr) (c : cand) (l1 : constr) (r1 : constr) (l2 : constr) (r2 : constr) (l3 : constr) (r3 : constr) (l4 : constr) (r4 : constr) : bool :=
      Ref.set passed true;
      let s1 := side l1 r1 in let s2 := side l2 r2 in let s3 := side l3 r3 in let s4 := side l4 r4 in
      let dead (v : res) : bool := match v with Lit_false => true | _ => false end in
      if (if dead s1 then true else if dead s2 then true else if dead s3 then true else dead s4) then false else
      let args := [| c.(c_b1); c.(c_a2); c.(c_b2); c.(c_a1); e1; a; e2; aa; Control.hyp (c.(c_h)) |] in
      let all_lit := match s1 with Proof _ => (match s2 with Proof _ => (match s3 with Proof _ => (match s4 with Proof _ => true | _ => false end) | _ => false end) | _ => false end) | _ => false end in
      let pf (v : res) : constr := match v with Proof p => p | _ => Control.throw Not_found end in
      if all_lit then (Std.exact_no_check (mk_app lem (Array.append args [| pf s1; pf s2; pf s3; pf s4 |])); true)
      else
        try_tac (fun () =>
          let t := mk_app lem args in
          ltac1:(t |- apply t) (Ltac1.of_constr t);
          Control.dispatch (List.map (fun v => match v with Proof p => (fun () => Std.exact_no_check p) | _ => side_tac end) [s1; s2; s3; s4])) in
    let rec go (cs : cand list) : bool :=
      match cs with
      | [] => false
      | c :: r =>
          let c1 := base_of x (c.(c_a1)) in let c2 := base_of x (c.(c_a2)) in
          if (if (if same c1 ba then same c2 bl else false) then attempt (x.(p_use)) c (c.(c_a1)) aa e1 (c.(c_b1)) (c.(c_a2)) a e2 (c.(c_b2)) else false) then true
          else if (if (if same c2 ba then same c1 bl else false) then attempt (x.(p_use')) c (c.(c_a2)) aa e1 (c.(c_b2)) (c.(c_a1)) a e2 (c.(c_b1)) else false) then true
          else go r
      end in
    if go cands then ()
    else if (if Ref.get passed then try_tac old_sep else false) then ()
    else
      (* [comment removed for export] *)
      let rec deepen (d : int) : unit :=
        if Int.lt 4 d then nope () else
        match prove_le x s d e1 a with
        | Proof p => intro_l p
        | _ => (match prove_le x s d e2 aa with Proof q => intro_r q | _ => deepen (Int.add d 1) end)
        end in
      deepen 1
    end
    end
    end.

  (* [comment removed for export] *)
  Ltac sl_same_l := ltac2:(Control.enter sl_same).
  Ltac sl_not_conj_l := ltac2:(Control.enter sl_not_conj).
  Ltac sl_chain_l := ltac2:(Control.enter sl_chain).
  Ltac sl_sep_l tac := let f := ltac2:(tac |- Control.enter (fun () => sl_sep (fun () => Ltac1.run tac))) in f tac.
  Ltac sl_conj_l old_same side_tac old_sep :=
    let f := ltac2:(a b c |- Control.enter (fun () => sl_conj (fun () => Ltac1.run a) (fun () => Ltac1.run b) (fun () => Ltac1.run c))) in f old_same side_tac old_sep.
End SL2.
Ltac sl_same := SL2.sl_same_l.
Ltac sl_not_conj := SL2.sl_not_conj_l.
Ltac sl_chain := SL2.sl_chain_l.
Ltac sl_sep tac := SL2.sl_sep_l tac.
Ltac sl_conj old_same side_tac old_sep := SL2.sl_conj_l old_same side_tac old_sep.
