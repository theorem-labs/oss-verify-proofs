(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache.
Open Scope Z_scope.

Module AX2L.

Definition gran2 (a : Z) : Z := Z.shiftr a 6.
Definition fits2 (s e : Z) : bool := if Z.ltb s e then Z.leb (gran2 (e - 1) - gran2 s) 1 else false.
Definition has2 (s e g : Z) : bool := if Z.eqb g (gran2 s) then true else Z.eqb g (gran2 (e - 1)).

Definition vcell (K : kentry) : option (nat * Z * Z) :=
  match K with
  | KWord (SA (EVar v) kk) w _ => if fits2 kk (kk + Z.of_nat w) then Some (v, kk, kk + Z.of_nat w) else None
  | _ => None
  end.
Definition narrow2 (v : nat) (g : Z) (K : kentry) : bool :=
  match vcell K with Some (v', s, e) => if Nat.eqb v v' then has2 s e g else false | None => false end.
Definition wide2 (K : kentry) : bool :=
  if kx_candf K then (match vcell K with Some _ => false | None => true end) else false.
Definition cand2 (v : nat) (g : Z) (K : kentry) : bool := (narrow2 v g K || wide2 K)%bool.

Definition vtab : Type := ptree (ptree (list (positive * kentry))).
Record kix2 : Type := KX2 { k2_w : list (positive * kentry); k2_v : vtab }.
Definition vkey (v : nat) : positive := Pos.of_succ_nat v.
Definition inner2 (t : vtab) (v : nat) : ptree (list (positive * kentry)) :=
  match pt_get t (vkey v) with Some i => i | None => PTLeaf end.
Definition bucket2 (t : vtab) (v : nat) (g : Z) : list (positive * kentry) := kx_bucket (inner2 t v) g.
Definition add2 (v : nat) (g : Z) (x : positive * kentry) (t : vtab) : vtab := pt_set (vkey v) (kx_add g x (inner2 t v)) t.
Fixpoint build2 (kn : list kentry) (i : positive) : list (positive * kentry) * vtab :=
  match kn with
  | [] => ([], PTLeaf)
  | K :: rest =>
      let '(w, t) := build2 rest (Pos.succ i) in
      match vcell K with
      | Some (v, s, e) =>
          let g1 := gran2 s in let g2 := gran2 (e - 1) in
          let t1 := add2 v g1 (i, K) t in
          (w, if Z.eqb g1 g2 then t1 else add2 v g2 (i, K) t1)
      | None => if kx_candf K then ((i, K) :: w, t) else (w, t)
      end
  end.
Definition mk_kix2 (kn : list kentry) : kix2 := let r := build2 kn xH in KX2 (fst r) (snd r).
Definition select2 (kx2 : kix2) (v : nat) (rk : Z) : list kentry :=
  kx_merge (bucket2 (k2_v kx2) v (gran2 rk)) (k2_w kx2).

Definition know_lookupA0I2 (bc : bctx) (kx : kix) (kx2 : kix2) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n, rb with
  | [], S _, EVar v => know_lookupA0B bc segs (select2 kx2 v rk) rb rk n sx [] acc
  | _, _, _ => know_lookupA0I bc kx segs rb rk n sx hints acc
  end.

Lemma gran2_div : forall a, gran2 a = a / 64.
Proof. intros a. unfold gran2. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma gran2_mono : forall a b, a <= b -> gran2 a <= gran2 b.
Proof. intros a b H. rewrite !gran2_div. apply Z.div_le_mono; lia. Qed.
Lemma gran2_between : forall s e x, s <= x -> x < e -> fits2 s e = true -> has2 s e (gran2 x) = true.
Proof.
  intros s e x Hs He Hf. unfold fits2, has2 in *.
  destruct (Z.ltb s e); [|discriminate]. apply Z.leb_le in Hf.
  pose proof (gran2_mono s x Hs) as A. pose proof (gran2_mono x (e - 1) ltac:(lia)) as B.
  destruct (Z.eqb_spec (gran2 x) (gran2 s)); [reflexivity|].
  destruct (Z.eqb_spec (gran2 x) (gran2 (e - 1))); [reflexivity|]. exfalso. lia.
Qed.

Lemma vkey_inj : forall a b, vkey a = vkey b -> a = b.
Proof. intros a b H. apply SuccNat2Pos.inj. exact H. Qed.
Lemma bucket2_add_same : forall v g x t, bucket2 (add2 v g x t) v g = x :: bucket2 t v g.
Proof. intros. unfold bucket2, add2. unfold inner2 at 1. rewrite pt_gss. apply kx_bucket_add_same. Qed.
Lemma bucket2_add_other_g : forall v g g' x t, g <> g' -> bucket2 (add2 v g' x t) v g = bucket2 t v g.
Proof. intros. unfold bucket2, add2. unfold inner2 at 1. rewrite pt_gss. apply kx_bucket_add_other. assumption. Qed.
Lemma bucket2_add_other_v : forall v v' g g' x t, v <> v' -> bucket2 (add2 v' g' x t) v g = bucket2 t v g.
Proof.
  intros v v' g g' x t H. unfold bucket2, add2. unfold inner2 at 1. rewrite pt_gso; [reflexivity|].
  intros E. apply H. apply vkey_inj. exact E.
Qed.
Lemma bucket2_leaf : forall v g, bucket2 PTLeaf v g = [].
Proof. intros. unfold bucket2, inner2. rewrite pt_get_leaf. apply kx_bucket_leaf. Qed.

Lemma build2_spec : forall kn i w t,
  build2 kn i = (w, t) ->
  w = List.filter (fun x => wide2 (snd x)) (tagged kn i)
  /\ (forall v g, bucket2 t v g = List.filter (fun x => narrow2 v g (snd x)) (tagged kn i)).
Proof.
  induction kn as [|K rest IH]; intros i w t H.
  - cbn in H. injection H as <- <-. split; [reflexivity|]. intros v g. rewrite bucket2_leaf. reflexivity.
  - cbn [build2] in H. destruct (build2 rest (Pos.succ i)) as [w' t'] eqn:Hb.
    destruct (IH (Pos.succ i) w' t' Hb) as (A & B). clear IH.
    cbn [tagged List.filter snd]. unfold wide2, narrow2.
    destruct (vcell K) as [[[v0 s] e]|] eqn:HV.
    + match type of H with (_, ?G) = _ => set (t1 := G) in H end.
      injection H as <- <-.
      replace (if kx_candf K then false else false) with false by (destruct (kx_candf K); reflexivity).
      split; [exact A|]. intros v g.
      assert (STEP : bucket2 t1 v g = if (if Nat.eqb v v0 then has2 s e g else false) then (i, K) :: bucket2 t' v g else bucket2 t' v g).
      { subst t1. destruct (Nat.eqb_spec v v0) as [->|NV].
        - unfold has2. destruct (Z.eqb_spec (gran2 s) (gran2 (e - 1))) as [EQ|NE].
          + destruct (Z.eqb_spec g (gran2 s)) as [->|NE1].
            * rewrite bucket2_add_same. reflexivity.
            * rewrite bucket2_add_other_g by exact NE1. destruct (Z.eqb_spec g (gran2 (e - 1))); [congruence|reflexivity].
          + destruct (Z.eqb_spec g (gran2 s)) as [->|NE1].
            * rewrite bucket2_add_other_g by exact NE. rewrite bucket2_add_same. reflexivity.
            * destruct (Z.eqb_spec g (gran2 (e - 1))) as [->|NE2].
              -- rewrite bucket2_add_same. rewrite bucket2_add_other_g by exact NE1. reflexivity.
              -- rewrite bucket2_add_other_g by exact NE2. rewrite bucket2_add_other_g by exact NE1. reflexivity.
        - destruct (Z.eqb (gran2 s) (gran2 (e - 1))); rewrite ?bucket2_add_other_v by exact NV; reflexivity. }
      rewrite STEP, B. reflexivity.
    + destruct (kx_candf K); injection H as <- <-.
      * split; [rewrite A; reflexivity|]. intros v g. rewrite B. reflexivity.
      * split; [exact A|]. intros v g. rewrite B. reflexivity.
Qed.

Lemma narrow2_not_wide2 : forall v g K, narrow2 v g K = true -> wide2 K = false.
Proof. intros v g K. unfold narrow2, wide2. destruct (vcell K) as [[[v' s] e]|]; [|discriminate]. destruct (kx_candf K); reflexivity. Qed.

Lemma select2_eq : forall kn v rk, select2 (mk_kix2 kn) v rk = List.filter (cand2 v (gran2 rk)) kn.
Proof.
  intros kn v rk. unfold select2, mk_kix2. destruct (build2 kn 1%positive) as [w t] eqn:Hb. cbn [k2_w k2_v fst snd].
  destruct (build2_spec kn 1%positive w t Hb) as (A & B). rewrite B, A.
  apply (kx_merge_filters (narrow2 v (gran2 rk)) wide2 kn 1%positive (narrow2_not_wide2 v (gran2 rk))).
Qed.

Lemma know_lookupA0B_skip2 : forall bc segs K rest v rk n sx acc,
  cand2 v (gran2 rk) K = false ->
  know_lookupA0B bc segs (K :: rest) (EVar v) rk (S n) sx [] acc = know_lookupA0B bc segs rest (EVar v) rk (S n) sx [] acc.
Proof.
  intros bc segs K rest v rk n sx acc HC. unfold cand2 in HC. apply Bool.orb_false_iff in HC as [HN HW].
  unfold wide2 in HW. destruct (kx_candf K) eqn:HF; [|apply know_lookupA0B_skipf; [reflexivity|exact HF]].
  unfold narrow2 in HN. destruct (vcell K) as [[[v' s] e]|] eqn:HV; [|discriminate].
  destruct K as [[kb kk] w val| | | | | | | | |]; try discriminate HV. cbn [vcell] in HV.
  destruct kb as [|v0| | | | | |]; try discriminate HV.
  destruct (fits2 kk (kk + Z.of_nat w)) eqn:FT; [|discriminate]. injection HV as <- <- <-.
  cbn [know_lookupA0B].
  destruct (Nat.eqb_spec v v0) as [->|NV].
  - rewrite rel_lit_same.
    destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w))%bool eqn:E.
    + exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
      rewrite (gran2_between kk (kk + Z.of_nat w) rk) in HN; [discriminate|lia|lia|exact FT].
    + destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
  - rewrite rel_lit_other; [reflexivity|]. cbn [expr_eqb]. apply Nat.eqb_neq. exact NV.
Qed.
Lemma know_lookupA0B_filter2 : forall bc segs l v rk n sx acc,
  know_lookupA0B bc segs (List.filter (cand2 v (gran2 rk)) l) (EVar v) rk (S n) sx [] acc
  = know_lookupA0B bc segs l (EVar v) rk (S n) sx [] acc.
Proof.
  intros bc segs l v rk n sx. induction l as [|K rest IH]; intros acc; [reflexivity|].
  cbn [List.filter]. destruct (cand2 v (gran2 rk) K) eqn:HC.
  - cbn [know_lookupA0B]. rewrite !IH.
    destruct K as [[kb kk] w val|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
  - rewrite know_lookupA0B_skip2 by exact HC. apply IH.
Qed.

Theorem know_lookupA0I2_eq : forall bc kn segs rb rk n sx hints acc,
  know_lookupA0I2 bc (mk_kix kn) (mk_kix2 kn) segs rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof.
  intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I2.
  destruct hints as [|h hs]; [|apply know_lookupA0I_eq]. destruct n as [|n]; [apply know_lookupA0I_eq|].
  destruct rb; try apply know_lookupA0I_eq.
  rewrite select2_eq. apply know_lookupA0B_filter2.
Qed.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.
Section Ctx.
Variable bc : bctx. Variable kx : kix.

Definition stepX_g :=
  ltac:(let t := eval cbv beta delta [sym_stepXBI sym_stepBI sym_readBI know_lookupABI] in (@sym_stepXBI segs bc kx) in
        lazymatch t with context [know_lookupA0I bc kx segs] => idtac | _ => fail "abstraction target does not occur" end;
        let t' := eval pattern (know_lookupA0I bc kx segs) in t in
        lazymatch t' with ?F _ => exact F end).
Lemma stepX_g_ref : stepX_g (know_lookupA0I bc kx segs) = sym_stepXBI segs bc kx.
Proof. reflexivity. Qed.
End Ctx.

Definition sym_stepXBI2 (bc : bctx) (kx : kix) (kx2 : kix2) := stepX_g bc (know_lookupA0I2 bc kx kx2 segs).
Lemma sym_stepXBI2_eq : forall K i ss scr,
  sym_stepXBI2 (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) (mk_kix2 (s_know ss)) K i ss scr = sym_stepX segs K i ss scr.
Proof.
  intros. unfold sym_stepXBI2.
  replace (know_lookupA0I2 (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) (mk_kix2 (s_know ss)) segs)
     with (know_lookupA0I (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) segs).
  - rewrite stepX_g_ref. apply sym_stepXBI_eq.
  - repeat (apply functional_extensionality; intros ?). rewrite know_lookupA0I2_eq, know_lookupA0I_eq. reflexivity.
Qed.

Fixpoint sym_execTXBI2_go (bc : bctx) (kx : kix) (kx2 : kix2) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
         (ss : sym_state) (ck : sym_state) : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBI2 bc kx kx2 K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBI2_go bc kx kx2 t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXBI2 (bc : bctx) (kx : kix) (kx2 : kix2) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
           (ss : sym_state) : sym_state :=
  sym_execTXBI2_go bc kx kx2 t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXBI2_go_eq : forall t K fuel first stops ss ck,
  sym_execTXBI2_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) (mk_kix2 (s_know ss)) t K fuel first stops ss ck
  = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXBI2_go sym_execTX_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXBI2_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  rewrite <- (sym_stepX_know _ _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXBI2_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXBI2 (mkbc (facts_of kn0)) (mk_kix kn0) (mk_kix2 kn0) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXBI2, sym_execTX.
  replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
  apply sym_execTXBI2_go_eq.
Qed.
End WithSegs.

End AX2L.
