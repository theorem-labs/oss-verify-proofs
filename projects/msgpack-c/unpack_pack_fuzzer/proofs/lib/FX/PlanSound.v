(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Acc StepAcc W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundAlu StepSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepA StepS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PlanS.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Definition env_ext (n : int) (E E' : env) : Prop :=
  eb E' = eb E /\ forall k, to_Z k < to_Z n -> ev E' k = ev E k /\ eg E' k = eg E k.

Fixpoint vars_below (n : int) (v : sv) : bool :=
  match v with
  | VL _ => true
  | VP k _ => PrimInt63.ltb k n
  | VAlu _ a b | VAluw _ a b | VMd _ a b | VMdw _ a b | VIns _ _ a b => vars_below n a && vars_below n b
  | VExt _ _ _ a => vars_below n a
  | VBlob _ _ off _ => vars_below n off
  | VBg _ k _ _ => PrimInt63.ltb k n
  | VF1 _ a => vars_below n a
  end.

Definition obl_holds (PB : (int -> list byte) -> Prop) (o : obligation) : Prop :=
  forall E, PB (eb E) -> ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E (fst o) -> fact_holds E (snd o).
Definition obls_hold (PB : (int -> list byte) -> Prop) (os : list obligation) : Prop := Forall (obl_holds PB) os.

Definition contract_sound (MP : Model -> Prop) (PB : (int -> list byte) -> Prop) (ct : contract) : Prop :=
  forall st sts, s_pc st = c_pc ct -> c_apply ct st = Some sts ->
  forall (K : TSet) E ms model,
    st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
    (forall st', In st' sts ->
       forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
       realizes segs (mkCfg ms' model') K) ->
    realizes segs (mkCfg ms model) K.

Definition contracts_ok (C : ctx) (MP : Model -> Prop) (PB : (int -> list byte) -> Prop) : Prop :=
  forall cid ct, IMap.find cid (c_contracts C) = Some ct -> contract_sound MP PB ct.

Fixpoint uses_plain_cut (p : plan) (tid : int) : bool :=
  match p with
  | PRun _ k | PAssume _ k | PForget _ _ _ k | PDropFacts _ k | PSetReg _ _ k | PSubst _ _ k | PName _ k | PSetHi _ _ k => uses_plain_cut k tid
  | PCase k1 k2 => uses_plain_cut k1 tid || uses_plain_cut k2 tid
  | PSplit _ _ ks | PCall _ ks =>
      (fix go (ks : list plan) : bool :=
         match ks with [] => false | k :: ks' => uses_plain_cut k tid || go ks' end) ks
  | PCut tid' _ => PrimInt63.eqb tid tid'
  | PCutDec _ _ | PEcall _ _ | PFail _ => false
  end.

Definition ecall_at (pc : int) : Prop :=
  exists w, fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\ is_ecall w = true.

Definition leaves_ok (C : ctx) (p : plan) (MP : Model -> Prop) (K : TSet) (E : env) (mroot : Z) : Prop :=
  (forall tid T, IMap.find tid (c_cuts C) = Some T ->
     forall E' ms' model', eb E' = eb E -> MP model' -> st_ok segs OPS E' (t_st T) ms' model' ->
       (uses_plain_cut p tid = true \/ bv_unsigned (den E' (t_measure T)) < mroot) ->
       realizes segs (mkCfg ms' model') K)
  /\
  (forall eid T, IMap.find eid (c_ecalls C) = Some T ->
     forall E' ms' model', eb E' = eb E -> MP model' -> st_ok segs OPS E' T ms' model' ->
       ecall_at (s_pc T) ->
       realizes segs (mkCfg ms' model') K).

Definition sg_stable (N : int) (sg : list (int * sv)) : bool :=
  forallb (fun kv => negb (PrimInt63.ltb (fst kv) N)
                     || match snd kv with VP k o => PrimInt63.eqb k (fst kv) && weqb o wzero | _ => false end)%bool sg.

Fixpoint plan_stable (N : int) (p : plan) : bool :=
  match p with
  | PRun _ k | PSetReg _ _ k | PSubst _ _ k | PName _ k | PSetHi _ _ k | PAssume _ k | PForget _ _ _ k | PDropFacts _ k => plan_stable N k
  | PCase kT kF => plan_stable N kT && plan_stable N kF
  | PSplit _ _ ks | PCall _ ks => (fix go (l : list plan) : bool := match l with [] => true | k :: l' => plan_stable N k && go l' end) ks
  | PCut _ sg | PCutDec _ sg | PEcall _ sg => sg_stable N sg
  | PFail _ => true
  end.

Definition stable (N : int) (E0 E : env) : Prop := forall k, to_Z k < to_Z N -> ev E k = ev E0 k /\ eg E k = eg E0 k.

Definition leaves_ok_st (N : int) (C : ctx) (p : plan) (MP : Model -> Prop) (K : TSet) (E : env) (mroot : Z) : Prop :=
  (forall tid T, IMap.find tid (c_cuts C) = Some T ->
     forall E' ms' model', eb E' = eb E -> stable N E E' -> MP model' -> st_ok segs OPS E' (t_st T) ms' model' ->
       (uses_plain_cut p tid = true \/ bv_unsigned (den E' (t_measure T)) < mroot) ->
       realizes segs (mkCfg ms' model') K)
  /\
  (forall eid T, IMap.find eid (c_ecalls C) = Some T ->
     forall E' ms' model', eb E' = eb E -> stable N E E' -> MP model' -> st_ok segs OPS E' T ms' model' ->
       ecall_at (s_pc T) ->
       realizes segs (mkCfg ms' model') K).

Lemma leaves_ok_st_of : forall N C p MP K E mroot, leaves_ok C p MP K E mroot -> leaves_ok_st N C p MP K E mroot.
Proof.
  intros N C p MP K E mroot [H1 H2]. split.
  - intros tid T HT E' ms' model' Heb _ HMP HS HU. exact (H1 tid T HT E' ms' model' Heb HMP HS HU).
  - intros eid T HT E' ms' model' Heb _ HMP HS HA. exact (H2 eid T HT E' ms' model' Heb HMP HS HA).
Qed.

Lemma den_env_ext : forall n E E' v, env_ext n E E' -> vars_below n v = true -> den E' v = den E v.
Proof.
  intros n E E' v [Hb Hk]. induction v; intros Hv; cbn [vars_below] in Hv; cbn [den];
    repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
  - reflexivity.
  - apply ltb_spec in Hv. rewrite (proj1 (Hk _ Hv)). reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv by assumption. reflexivity.
  - rewrite IHv1, IHv2 by assumption. reflexivity.
  - rewrite IHv by assumption. rewrite Hb. reflexivity.
  - apply ltb_spec in Hv. rewrite (proj2 (Hk _ Hv)). reflexivity.
  - rewrite IHv by assumption. reflexivity.
Qed.

Lemma env_ext_refl : forall n E, env_ext n E E.
Proof. intros n E. split; [reflexivity|]. intros; split; reflexivity. Qed.

Lemma env_ext_trans : forall n n' E E' E'', to_Z n <= to_Z n' -> env_ext n E E' -> env_ext n' E' E'' -> env_ext n E E''.
Proof.
  intros n n' E E' E'' Hle [Hb1 H1] [Hb2 H2]. split; [congruence|].
  intros k Hk. destruct (H1 k Hk) as [A1 B1]. destruct (H2 k ltac:(lia)) as [A2 B2]. split; congruence.
Qed.

Lemma keys_increasing_sorted : forall A (l : list (int * A)) prev,
  keys_increasing prev (List.map fst l) = true ->
  Sorted.StronglySorted (fun a b => to_Z (fst a) < to_Z (fst b)) l /\
  forall p, prev = Some p -> Forall (fun kv => to_Z p < to_Z (fst kv)) l.
Proof.
  induction l as [|[k v] l IH]; intros prev H; cbn [List.map fst keys_increasing] in H.
  - split; [constructor| intros; constructor].
  - apply andb_prop in H as [H1 H2]. destruct (IH _ H2) as [S F].
    split.
    + constructor; [exact S| exact (F k eq_refl)].
    + intros p Hp. subst prev. apply ltb_spec in H1. constructor; [exact H1|].
      eapply Forall_impl; [|exact (F k eq_refl)]. cbn [fst]. intros; lia.
Qed.

Lemma bst_b_sound : forall A (m : IMap.t A), bst_b m = true -> IMap.bst m.
Proof.
  intros A m H. apply IMap.bst_iff_sorted. exact (proj1 (keys_increasing_sorted A _ None H)).
Qed.

Lemma rf_forallb2_get : forall A B (p : A -> B -> bool) x y,
  rf_forallb2 p x y = true -> forall r, p (rf_get x r) (rf_get y r) = true.
Proof.
  intros A B p x y H r. unfold rf_forallb2 in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  destruct r; cbn [rf_get]; assumption.
Qed.

Lemma int_eqb_eq' : forall a b : int, PrimInt63.eqb a b = true -> a = b.
Proof. intros a b H. apply Uint63.eqb_correct. exact H. Qed.
Lemma int_eqb_neq : forall a b : int, PrimInt63.eqb a b = false -> a <> b.
Proof. intros a b H E. subst. rewrite Uint63.eqb_refl in H. discriminate. Qed.

Lemma privs_eqb_eq : forall a b, privs_eqb a b = true -> a = b.
Proof.
  induction a as [|[x1 y1] a IH]; intros [|[x2 y2] b] H; cbn [privs_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply int_eqb_eq' in H1. apply int_eqb_eq' in H2. subst. rewrite (IH b H3). reflexivity.
Qed.

Lemma Forall_firstn : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l H. revert n. induction H; intros [|n]; cbn; constructor; auto.
Qed.

Definition subst_env (E : env) (sg : subst) : env :=
  Env (fun k => match IMap.find k sg with Some u => den E u | None => ev E k end)
      (eb E)
      (fun k => match svar sg k with Some k' => eg E k' | None => eg E k end).

Lemma svar_find : forall sg k k', svar sg k = Some k' -> IMap.find k sg = Some (VP k' wzero).
Proof.
  intros sg k k' H. unfold svar in H.
  destruct (IMap.find k sg) as [u|]; [|discriminate]. destruct u; try discriminate.
  destruct (weqb off wzero) eqn:W; [|discriminate]. apply (proj1 (weqb_ok _ _)) in W. subst.
  injection H as ->. reflexivity.
Qed.

Lemma subst_env_ev : forall E sg k u, IMap.find k sg = Some u -> ev (subst_env E sg) k = den E u.
Proof. intros E sg k u H. cbn [subst_env ev]. rewrite H. reflexivity. Qed.

Lemma wbv_wzero_unsigned : bv_unsigned (wbv wzero) = 0.
Proof. rewrite wbv_unsigned. reflexivity. Qed.

Lemma subst_env_svar : forall E sg k k', svar sg k = Some k' -> ev (subst_env E sg) k = ev E k'.
Proof.
  intros E sg k k' H. rewrite (subst_env_ev E sg k (VP k' wzero) (svar_find _ _ _ H)).
  cbn [den]. apply bv_add_0_r. apply wbv_wzero_unsigned.
Qed.

Lemma subst_env_eg : forall E sg k k', svar sg k = Some k' -> eg (subst_env E sg) k = eg E k'.
Proof. intros E sg k k' H. cbn [subst_env eg]. rewrite H. reflexivity. Qed.

Lemma subst_env_eb : forall E sg, eb (subst_env E sg) = eb E.
Proof. reflexivity. Qed.

Lemma width_okb_sound : forall lo n, width_okb lo n = true -> width_ok (to_Z lo) (to_Z n).
Proof.
  intros lo n H. unfold width_okb in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply leb_spec in H1. apply leb_spec in H2. apply leb_spec in H3. apply leb_spec in H4.
  change (to_Z 1%uint63) with 1 in H1. change (to_Z 8%uint63) with 8 in *.
  rewrite add_spec in H4. pose proof (int_range lo). pose proof (int_range n). rewrite two63_eq in *.
  rewrite Z.mod_small in H4 by (change wB with (2 ^ 63); lia).
  unfold width_ok. lia.
Qed.

Lemma den_sv_ext_c : forall E sx lo n a, den E (sv_ext_c sx lo n a) = den E (VExt sx lo n a).
Proof.
  intros E sx lo n a. unfold sv_ext_c. destruct (width_okb lo n) eqn:W; [|reflexivity].
  rewrite (den_sv_ext E sx lo n a (width_okb_sound lo n W)). reflexivity.
Qed.

Lemma den_sv_ins_c : forall E lo n a v, den E (sv_ins_c lo n a v) = den E (VIns lo n a v).
Proof.
  intros E lo n a v. unfold sv_ins_c. destruct (width_okb lo n) eqn:W; [|reflexivity].
  rewrite (den_sv_ins E lo n a v (width_okb_sound lo n W)). reflexivity.
Qed.

Lemma sapply_sound : forall E sg tv v, sapply sg tv = Some v -> den E v = den (subst_env E sg) tv.
Proof.
  intros E sg tv. induction tv; intros v H; cbn [sapply] in H.
  - injection H as <-. reflexivity.
  - destruct (IMap.find k sg) as [u|] eqn:F; [|discriminate]. injection H as <-.
    rewrite den_sv_alu. cbn [den alu64 alu]. rewrite (subst_env_ev E sg k u F). reflexivity.
  - destruct (sapply sg tv1) as [a'|] eqn:A; [|discriminate]. destruct (sapply sg tv2) as [b'|] eqn:B; [|discriminate].
    injection H as <-. rewrite den_sv_alu. cbn [den]. rewrite (IHtv1 a' eq_refl), (IHtv2 b' eq_refl). reflexivity.
  - destruct (sapply sg tv1) as [a'|] eqn:A; [|discriminate]. destruct (sapply sg tv2) as [b'|] eqn:B; [|discriminate].
    injection H as <-. rewrite den_sv_aluw. cbn [den]. rewrite (IHtv1 a' eq_refl), (IHtv2 b' eq_refl). reflexivity.
  - destruct (sapply sg tv1) as [a'|] eqn:A; [|discriminate]. destruct (sapply sg tv2) as [b'|] eqn:B; [|discriminate].
    injection H as <-. rewrite den_sv_md. cbn [den]. rewrite (IHtv1 a' eq_refl), (IHtv2 b' eq_refl). reflexivity.
  - destruct (sapply sg tv1) as [a'|] eqn:A; [|discriminate]. destruct (sapply sg tv2) as [b'|] eqn:B; [|discriminate].
    injection H as <-. rewrite den_sv_mdw. cbn [den]. rewrite (IHtv1 a' eq_refl), (IHtv2 b' eq_refl). reflexivity.
  - destruct (sapply sg tv) as [a'|] eqn:A; [|discriminate]. injection H as <-.
    rewrite den_sv_ext_c. cbn [den]. rewrite (IHtv a' eq_refl). reflexivity.
  - destruct (sapply sg tv1) as [a'|] eqn:A; [|discriminate]. destruct (sapply sg tv2) as [b'|] eqn:B; [|discriminate].
    injection H as <-. rewrite den_sv_ins_c. cbn [den]. rewrite (IHtv1 a' eq_refl), (IHtv2 b' eq_refl). reflexivity.
  - destruct (sapply sg tv) as [a'|] eqn:A; [|discriminate]. injection H as <-.
    cbn [den subst_env eb]. rewrite (IHtv a' eq_refl). reflexivity.
  - destruct (svar sg k) as [k'|] eqn:S; [|discriminate]. injection H as <-.
    cbn [den]. rewrite (subst_env_eg E sg k k' S). reflexivity.
  - destruct (sapply sg tv) as [a'|] eqn:A; [|discriminate]. injection H as <-.
    cbn [den]. rewrite (IHtv a' eq_refl). reflexivity.
Qed.

Lemma smatch_sound : forall E sg tv v, smatch sg tv v = true -> den (subst_env E sg) tv = den E v.
Proof.
  intros E sg tv v H. unfold smatch in H. destruct (sapply sg tv) as [tv'|] eqn:S; [|discriminate].
  apply sv_eqb_eq in H. subst tv'. symmetry. apply sapply_sound. exact S.
Qed.

Lemma implied_sound : forall E fs f, ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs -> implied fs f = true -> fact_holds E f.
Proof. intros E fs f Hz Hfs H. exact (ValP.implied_sound E fs f Hfs Hz H). Qed.

Lemma decide_eq_t_sound : forall E fs, facts_hold E fs -> forall a b r, decide_eq_t fs a b = Some r -> bv_eqb (den E a) (den E b) = r.
Proof.
  intros E fs Hfs a b r H. unfold decide_eq_t in H. cbv zeta in H.
  destruct (decide_eq (rel_facts (sv_vs a (sv_vs b [])) fs) a b) as [[|]|] eqn:D.
  1: { injection H as <-. exact (decide_eq_sound E _ (rel_facts_hold E _ fs Hfs) _ _ _ D). }
  all: destruct (decide_eq (rel_facts (close_vs fs (sv_vs a (sv_vs b [])) (sv_vs a (sv_vs b []))) fs) a b) as [[|]|] eqn:D1;
       try exact (decide_eq_sound E fs Hfs _ _ _ H);
       injection H as <-; exact (decide_eq_sound E _ (rel_facts_hold E _ fs Hfs) _ _ _ D1).
Qed.
Lemma decide_ltu_t_sound : forall E fs, facts_hold E fs -> forall a b r, decide_ltu_t fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros E fs Hfs a b r H. unfold decide_ltu_t in H. cbv zeta in H.
  destruct (decide_ltu (rel_facts (sv_vs a (sv_vs b [])) fs) a b) as [[|]|] eqn:D.
  1: { injection H as <-. exact (decide_ltu_sound E _ (rel_facts_hold E _ fs Hfs) _ _ _ D). }
  all: destruct (decide_ltu (rel_facts (close_vs fs (sv_vs a (sv_vs b [])) (sv_vs a (sv_vs b []))) fs) a b) as [[|]|] eqn:D1;
       try exact (decide_ltu_sound E fs Hfs _ _ _ H);
       injection H as <-; exact (decide_ltu_sound E _ (rel_facts_hold E _ fs Hfs) _ _ _ D1).
Qed.
Lemma has_fact_implied : forall f fs, has_fact f fs = true -> implied fs f = true.
Proof.
  intros f fs H. unfold implied.
  assert (X : existsb (fact_eqb f) fs = true).
  { induction fs as [|g fs IH]; [discriminate H|]. cbn [has_fact] in H. cbn [existsb].
    destruct (fact_eqb f g); [reflexivity|]. cbn [orb]. exact (IH H). }
  rewrite X. reflexivity.
Qed.
Lemma implied_t_sound : forall E fs f, ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs -> implied_t fs f = true -> fact_holds E f.
Proof.
  intros E fs f Hz Hfs H. unfold implied_t in H.
  destruct (has_fact f fs) eqn:I0; [exact (implied_sound E fs f Hz Hfs (has_fact_implied f fs I0))|].
  destruct (implied (rel_facts (fact_vs f) fs) f) eqn:I1; [exact (implied_sound E _ f Hz (rel_facts_hold E _ fs Hfs) I1)|].
  destruct (implied (rel_facts1 (fact_vs f) fs) f) eqn:I2; [exact (implied_sound E _ f Hz (rel_facts_hold E _ fs Hfs) I2)|].
  exact (implied_sound E fs f Hz Hfs H).
Qed.

Lemma sapply_fact_sound : forall E sg f f', sapply_fact sg f = Some f' -> fact_holds E f' -> fact_holds (subst_env E sg) f.
Proof.
  intros E sg f f' H Hf.
  assert (AUX : forall a b a' b', sapply sg a = Some a' -> sapply sg b = Some b' ->
            den (subst_env E sg) a = den E a' /\ den (subst_env E sg) b = den E b').
  { intros. split; symmetry; apply sapply_sound; assumption. }
  destruct f; cbn [sapply_fact] in H.
  1,2: destruct (svar sg k) as [k'|] eqn:S; [|discriminate]; injection H as <-; cbn [fact_holds] in Hf |- *;
       rewrite (subst_env_svar E sg k k' S); exact Hf.
  all: destruct (sapply sg a) as [a'|] eqn:Sa; [|discriminate]; destruct (sapply sg b) as [b'|] eqn:Sb; [|discriminate];
       injection H as <-; cbn [fact_holds] in Hf |- *; destruct (AUX a b a' b' Sa Sb) as [-> ->]; exact Hf.
Qed.

Lemma fact_entailed_sound : forall E fs sg f,
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs -> fact_entailed fs sg f = true -> fact_holds (subst_env E sg) f.
Proof.
  intros E fs sg f Hz Hfs H. unfold fact_entailed in H.
  destruct (sapply_fact sg f) as [f'|] eqn:SF.
  - apply (sapply_fact_sound E sg f f' SF). exact (implied_t_sound E fs f' Hz Hfs H).
  - destruct f; try discriminate H.
    + destruct (IMap.find k sg) as [u|] eqn:F; [|discriminate].
      apply andb_prop in H as [H1 H2].
      pose proof (implied_t_sound E fs _ Hz Hfs H1) as P1. pose proof (implied_t_sound E fs _ Hz Hfs H2) as P2.
      cbn [fact_holds] in P1, P2 |- *. rewrite (subst_env_ev E sg k u F).
      rewrite ValP.den_VL in P1. rewrite ValP.den_VL in P2. lia.
    + destruct (IMap.find k sg) as [u|] eqn:F; [|discriminate].
      apply andb_prop in H as [H1 H2]. apply leb_spec in H1. change (to_Z 62%uint63) with 62 in H1.
      cbn [fact_holds]. rewrite (subst_env_ev E sg k u F).
      exact (ValP.aligned_sound E fs Hfs u m H2 H1).
Qed.

Lemma cell_match_sound : forall E sg tc c, cell_match sg tc c = true ->
  c_idx c = c_idx tc /\ c_w c = c_w tc /\ den (subst_env E sg) (c_v tc) = den E (c_v c).
Proof.
  intros E sg tc c H. unfold cell_match in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply int_eqb_eq' in H1. apply int_eqb_eq' in H2.
  split; [congruence|]. split; [congruence|]. apply smatch_sound. exact H3.
Qed.

Lemma slot_match_sub_In : forall sg ts s tc, slot_match_sub sg ts s = true -> In tc ts ->
  exists c, In c s /\ cell_match sg tc c = true.
Proof.
  induction ts as [|t ts IH]; intros s tc H Hin; [destruct Hin|].
  cbn [slot_match_sub] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [<-|Hin].
  - apply existsb_exists in H1. exact H1.
  - exact (IH s tc H2 Hin).
Qed.

Lemma slot_match_exact_In : forall sg ts s tc, slot_match_exact sg ts s = true -> In tc ts ->
  exists c, In c s /\ cell_match sg tc c = true.
Proof.
  induction ts as [|t ts IH]; intros [|c s] tc H Hin; cbn [slot_match_exact] in H; try discriminate; [destruct Hin|].
  apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin].
  - exists c. split; [left; reflexivity| exact H1].
  - destruct (IH s tc H2 Hin) as (c' & Hc' & M). exists c'. split; [right; exact Hc'| exact M].
Qed.

Lemma slot_match_exact_In_r : forall sg ts s c, slot_match_exact sg ts s = true -> In c s ->
  exists tc, In tc ts /\ cell_match sg tc c = true.
Proof.
  induction ts as [|t ts IH]; intros [|c0 s] c H Hin; cbn [slot_match_exact] in H; try discriminate; [destruct Hin|].
  apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin].
  - exists t. split; [left; reflexivity| exact H1].
  - destruct (IH s c H2 Hin) as (tc & Htc & M). exists tc. split; [right; exact Htc| exact M].
Qed.

Definition grans_match (sg : subst) (tr r : region) : bool :=
  IMap.forallb (fun g tgr =>
     match IMap.find g (rg_cells r) with
     | Some gr => if g_dirty tgr then slot_match_sub sg (g_cells tgr) (g_cells gr)
                  else negb (g_dirty gr) && slot_match_exact sg (g_cells tgr) (g_cells gr)
     | None => match g_cells tgr with [] => true | _ => false end
     end) (rg_cells tr).

Definition grans_back (tr r : region) : bool :=
  IMap.forallb (fun g gr => match IMap.find g (rg_cells tr) with
                            | Some _ => true
                            | None => negb (g_dirty gr) && match g_cells gr with [] => true | _ => false end
                            end) (rg_cells r).

Lemma grans_match_corr : forall sg tr r, IMap.bst (rg_cells tr) -> grans_match sg tr r = true ->
  forall g tgr tc, IMap.find g (rg_cells tr) = Some tgr -> In tc (g_cells tgr) ->
  exists gr c, IMap.find g (rg_cells r) = Some gr /\ In c (g_cells gr) /\ cell_match sg tc c = true.
Proof.
  intros sg tr r B H g tgr tc Hf Hin. unfold grans_match in H.
  pose proof (proj1 (IMap.forallb_spec _ _ B) H g tgr Hf) as P. cbn beta in P.
  destruct (IMap.find g (rg_cells r)) as [gr|] eqn:Fg.
  - exists gr. destruct (g_dirty tgr).
    + destruct (slot_match_sub_In sg _ _ tc P Hin) as (c & Hc & M). exists c. auto.
    + apply andb_prop in P as [_ P]. destruct (slot_match_exact_In sg _ _ tc P Hin) as (c & Hc & M). exists c. auto.
  - destruct (g_cells tgr); [destruct Hin| discriminate].
Qed.

Lemma uncovered_transfer : forall sg tr r, IMap.bst (rg_cells tr) -> IMap.bst (rg_cells r) ->
  grans_match sg tr r = true -> grans_back tr r = true ->
  forall o, uncovered tr o -> uncovered r o.
Proof.
  intros sg tr r Bt Br H1 H2 o U g gr Hg Hf.
  unfold grans_match in H1. unfold grans_back in H2.
  destruct (IMap.find g (rg_cells tr)) as [tgr|] eqn:Ft.
  - destruct (U g tgr Hg Ft) as [D F].
    pose proof (proj1 (IMap.forallb_spec _ _ Bt) H1 g tgr Ft) as P. cbn beta in P. rewrite Hf, D in P.
    apply andb_prop in P as [P1 P2]. apply negb_true_iff in P1. split; [exact P1|].
    apply Forall_forall. intros c Hc.
    destruct (slot_match_exact_In_r sg _ _ c P2 Hc) as (tc & Htc & M).
    pose proof (proj1 (Forall_forall _ _) F tc Htc) as NC.
    unfold cell_match in M. apply andb_prop in M as [M _]. apply andb_prop in M as [M1 M2].
    apply int_eqb_eq' in M1. apply int_eqb_eq' in M2.
    unfold covers in *. rewrite <- M1, <- M2. exact NC.
  - pose proof (proj1 (IMap.forallb_spec _ _ Br) H2 g gr Hf) as P. cbn beta in P. rewrite Ft in P.
    apply andb_prop in P as [P1 P2]. apply negb_true_iff in P1. split; [exact P1|].
    destruct (g_cells gr); [constructor| discriminate].
Qed.

Lemma cell_keys_in_sound : forall lo hi cells, IMap.bst cells -> cell_keys_in lo hi cells = true ->
  forall g gr c, IMap.find g cells = Some gr -> In c (g_cells gr) -> 0 <= to_Z (c_w c) <= 8 ->
    keyZ lo <= 8 * keyZ g + to_Z (c_idx c) /\
    match hi with Some h => 8 * keyZ g + to_Z (c_idx c) + to_Z (c_w c) <= keyZ h | None => True end.
Proof.
  intros lo hi cells B H g gr c Hf Hin Hw. unfold cell_keys_in in H.
  pose proof (proj1 (IMap.forallb_spec _ _ B) H g gr Hf) as P. cbn beta in P.
  pose proof (proj1 (forallb_forall _ _) P c Hin) as Q. cbv zeta beta in Q.
  apply andb_prop in Q as [Q HI]. apply andb_prop in Q as [Q LT]. apply andb_prop in Q as [Q L]. apply andb_prop in Q as [G1 G2].
  apply int_eqb_eq' in G1. apply int_eqb_eq' in G2.
  set (k0 := PrimInt63.add (PrimInt63.lsl g 3) (c_idx c)) in *.
  pose proof (MemP.granule_gidx k0) as GG. rewrite MemP.half63 in GG.
  specialize (GG (MemP.keyZ_range k0)). destruct GG as [GG _]. rewrite G1, G2 in GG.
  rewrite MemP.kleb_keyZ in L. apply Z.leb_le in L.
  pose proof (MemP.keyZ_add_nowrap k0 (c_w c) Hw LT) as K1.
  split; [lia|].
  destruct hi as [h|]; [|exact I]. rewrite MemP.kleb_keyZ in HI. apply Z.leb_le in HI. lia.
Qed.

Lemma region_ok_transfer : forall priv E E' m k k' r tr,
  bv_unsigned (ev E' k') = bv_unsigned (ev E k) ->
  PrimInt63.eqb k' 0%uint63 = PrimInt63.eqb k 0%uint63 ->
  IMap.bst (rg_cells tr) ->
  loZ r <= loZ tr -> hiZ E' tr <= hiZ E r ->
  rg_w tr = rg_w r ->
  (forall g tgr, IMap.find g (rg_cells tr) = Some tgr -> slot_sorted (g_cells tgr)) ->
  (forall g tgr tc, IMap.find g (rg_cells tr) = Some tgr -> In tc (g_cells tgr) ->
     exists gr c, IMap.find g (rg_cells r) = Some gr /\ In c (g_cells gr) /\
                  c_idx c = c_idx tc /\ c_w c = c_w tc /\ den E' (c_v tc) = den E (c_v c)) ->
  (forall g tgr tc, IMap.find g (rg_cells tr) = Some tgr -> In tc (g_cells tgr) -> 0 <= to_Z (c_w tc) <= 8 ->
     loZ tr <= 8 * keyZ g + to_Z (c_idx tc) /\
     (hiZ E' tr = hiZ E r \/ 8 * keyZ g + to_Z (c_idx tc) + to_Z (c_w tc) <= hiZ E' tr)) ->
  (forall o, uncovered tr o -> uncovered r o) ->
  (forall o, bg_byte segs E' k' tr o = None \/ bg_byte segs E' k' tr o = bg_byte segs E k r o) ->
  region_ok segs priv E m k r -> region_ok segs priv E' m k' tr.
Proof.
  intros priv E E' m k k' r tr HB HK Bt Hlo Hhi Hw Hsorted Hcorr Hin Hunc Hbg RO.
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  constructor.
  - exact Bt.
  - intros K'. rewrite HK in K'. rewrite HB. pose proof (Rrange K'). lia.
  - intros K' a Ha. rewrite HK in K'. rewrite HB in Ha. rewrite Hw. apply (Rvalid K'). lia.
  - intros g tgr Hf. split; [exact (Hsorted g tgr Hf)|].
    apply Forall_forall. intros tc Htc.
    destruct (Hcorr g tgr tc Hf Htc) as (gr & c & Hgr & Hc & Ei & Ew & Ev).
    destruct (Rcells g gr Hgr) as [_ FC]. pose proof (proj1 (Forall_forall _ _) FC c Hc) as (C1 & C2 & C3 & C4).
    rewrite Ei, Ew in *. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    intros i Hi. rewrite HB, Ev. apply C4. exact Hi.
  - intros g tgr tc i Hf Htc Hi.
    destruct (Hcorr g tgr tc Hf Htc) as (gr & c & Hgr & Hc & Ei & Ew & Ev).
    pose proof (Rin g gr c i Hgr Hc ltac:(rewrite Ew; exact Hi)) as [P1 P2]. cbv zeta in P1, P2.
    rewrite Ei in P1, P2.
    destruct (Rcells g gr Hgr) as [_ FC]. pose proof (proj1 (Forall_forall _ _) FC c Hc) as (C1 & C2 & C3 & _).
    rewrite Ew in C2, C3. rewrite Ei in C1, C3.
    destruct (Hin g tgr tc Hf Htc ltac:(lia)) as [L U].
    split.
    + intros K'. rewrite HK in K'. pose proof (P1 K'). destruct U as [U|U]; lia.
    + intros K'. rewrite HK in K'. exact (P2 K').
  - intros o H1 H2 U.
    destruct (Hbg o) as [N| Eq]; [rewrite N; exact I|]. rewrite Eq, HB.
    apply Rbg.
    + intros K. rewrite <- HK in K. pose proof (H1 K). lia.
    + intros K. rewrite <- HK in K. exact (H2 K).
    + exact (Hunc o U).
Qed.

Lemma bg_match_sound : forall E sg tb b tk k,
  bg_match sg tb b = true -> eg (subst_env E sg) tk = eg E k ->
  forall tr r o, rg_bg tr = tb -> rg_bg r = b ->
  bg_byte segs (subst_env E sg) tk tr o = None \/ bg_byte segs (subst_env E sg) tk tr o = bg_byte segs E k r o.
Proof.
  intros E sg tb b tk k H Heg tr r o Htb Hb. unfold bg_byte. rewrite Htb, Hb.
  destruct tb; [left; reflexivity| | | |]; destruct b; cbn [bg_match] in H; try discriminate; right; try reflexivity.
  - rewrite Heg. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply int_eqb_eq' in H1. apply int_eqb_eq' in H2. subst. reflexivity.
Qed.

Lemma w2Zs_le_w2Z : forall o, w2Zs o <= w2Z o.
Proof. intros o. rewrite ValP.w2Zs_eq. destruct (wt o); pose proof (w2Z_range o); unfold two64 in *; lia. Qed.

Lemma slot_wfb_sorted : forall s p, slot_wfb p s = true -> slot_sorted s.
Proof.
  induction s as [|c s IH]; intros p H; [exact I|].
  cbn [slot_wfb] in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  cbn [slot_sorted]. split; [| exact (IH _ H6)].
  destruct s as [|c' s']; [exact I|].
  cbn [slot_wfb] in H6. apply andb_prop in H6 as [H6 _]. apply andb_prop in H6 as [H6 _]. apply andb_prop in H6 as [H6 _].
  apply andb_prop in H6 as [H6 _]. apply andb_prop in H6 as [H6 _].
  apply leb_spec in H6. apply leb_spec in H3. change (to_Z 8%uint63) with 8 in H3.
  rewrite add_spec in *. pose proof (int_range (c_idx c)). pose proof (int_range (c_w c)).
  apply ltb_spec in H4. apply leb_spec in H5. change (to_Z 8%uint63) with 8 in *.
  rewrite Z.mod_small in * by (change wB with (2 ^ 63); rewrite two63_eq in *; lia). lia.
Qed.

Lemma region_wfb_sound : forall r, region_wfb r = true ->
  IMap.bst (rg_cells r) /\ forall g gr, IMap.find g (rg_cells r) = Some gr -> slot_sorted (g_cells gr).
Proof.
  intros r H. unfold region_wfb in H. apply andb_prop in H as [H1 H2]. apply bst_b_sound in H1.
  split; [exact H1|]. intros g gr Hf.
  pose proof (proj1 (IMap.forallb_spec _ _ H1) H2 g gr Hf) as P. cbn beta in P. exact (slot_wfb_sorted _ _ P).
Qed.

Lemma region_match_sound : forall E sg priv m tk tr k r,
  svar sg tk = Some k ->
  PrimInt63.eqb tk 0%uint63 = PrimInt63.eqb k 0%uint63 ->
  region_wfb tr = true ->
  region_match sg tk tr k r = true ->
  region_ok segs priv E m k r ->
  region_ok segs priv (subst_env E sg) m tk tr
  /\ loZ r <= loZ tr /\ hiZ (subst_env E sg) tr <= hiZ E r.
Proof.
  intros E sg priv m tk tr k r Hsv HK WF RM RO.
  destruct (region_wfb_sound tr WF) as [Bt Sorted].
  unfold region_match in RM.
  apply andb_prop in RM as [RM G2]. apply andb_prop in RM as [RM G1]. apply andb_prop in RM as [RM HI].
  apply andb_prop in RM as [RM LO]. apply andb_prop in RM as [BG W].
  change (IMap.forallb _ (rg_cells tr) = true) with (grans_match sg tr r = true) in G1.
  change (IMap.forallb _ (rg_cells r) = true) with (grans_back tr r = true) in G2.
  assert (Hlo : loZ r <= loZ tr).
  { unfold loZ. rewrite MemP.kleb_keyZ in LO. apply Z.leb_le in LO. exact LO. }

  assert (Hhi : (hiZ (subst_env E sg) tr = hiZ E r /\ cell_keys_in (rg_lo tr) None (rg_cells tr) = true)
                \/ (hiZ (subst_env E sg) tr <= hiZ E r /\
                    exists a, cell_keys_in (rg_lo tr) (Some a) (rg_cells tr) = true /\ keyZ a <= hiZ (subst_env E sg) tr)).
  { destruct (smatch sg (rg_hi tr) (rg_hi r)) eqn:SM.
    - left. split; [|exact HI]. unfold hiZ. rewrite (smatch_sound E sg _ _ SM). reflexivity.
    - right. destruct (rg_hi tr) as [th| | | | | | | | | |] eqn:Eth; try discriminate.
      destruct (rg_hi r) as [h| | | | | | | | | |] eqn:Eh; try discriminate.
      destruct (okey th) as [a|] eqn:Oa; [|discriminate]. destruct (okey h) as [b|] eqn:Ob; [|discriminate].
      apply andb_prop in HI as [LE CK].
      unfold hiZ. rewrite Eth, Eh. cbn [den]. rewrite !wbv_unsigned.
      rewrite wleu_w2Z in LE. apply Z.leb_le in LE. split; [exact LE|].
      exists a. split; [exact CK|]. destruct (MemP.okey_sound th a Oa) as [-> _]. apply w2Zs_le_w2Z. }
  assert (HhiLe : hiZ (subst_env E sg) tr <= hiZ E r) by (destruct Hhi as [[-> _]|[? _]]; lia).
  split; [| split; [exact Hlo| exact HhiLe]].
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  eapply region_ok_transfer with (E := E) (k := k) (r := r).
  - rewrite (subst_env_svar E sg tk k Hsv). reflexivity.
  - exact HK.
  - exact Bt.
  - exact Hlo.
  - exact HhiLe.
  - apply Bool.eqb_prop in W. exact W.
  - exact Sorted.
  - intros g tgr tc Hf Htc. destruct (grans_match_corr sg tr r Bt G1 g tgr tc Hf Htc) as (gr & c & Hgr & Hc & M).
    exists gr, c. split; [exact Hgr|]. split; [exact Hc|]. exact (cell_match_sound E sg tc c M).
  - intros g tgr tc Hf Htc Hw. unfold loZ.
    destruct Hhi as [[EQ CK]|[LE (a & CK & Ka)]].
    + destruct (cell_keys_in_sound _ _ _ Bt CK g tgr tc Hf Htc Hw) as [L _]. split; [exact L| left; exact EQ].
    + destruct (cell_keys_in_sound _ _ _ Bt CK g tgr tc Hf Htc Hw) as [L U]. cbn beta iota in U. split; [exact L| right; lia].
  - exact (uncovered_transfer sg tr r Bt Rbst G1 G2).
  - intros o. exact (bg_match_sound E sg _ _ tk k BG (subst_env_eg E sg tk k Hsv) tr r o eq_refl eq_refl).
  - constructor; assumption.
Qed.

Section Images.
Variable sg : subst.
Let fimg := fun (acc : list int) (kv : int * region) => match svar sg (fst kv) with Some k => k :: acc | None => acc end.

Lemma int_notin_In : forall x l, int_notin x l = true -> forall y, In y l -> x <> y.
Proof.
  induction l as [|z l IH]; intros H y Hy; [destruct Hy|]. cbn [int_notin] in H. apply andb_prop in H as [H1 H2].
  destruct Hy as [<-|Hy]; [| exact (IH H2 y Hy)]. apply negb_true_iff in H1. apply int_eqb_neq in H1. exact H1.
Qed.

Lemma fold_img_inv : forall l acc, int_nodup (fold_left fimg l acc) = true ->
  int_nodup acc = true /\
  (forall x kv k, In x acc -> In kv l -> svar sg (fst kv) = Some k -> x <> k) /\
  (forall i j kvi kvj ki kj, (i < j)%nat -> nth_error l i = Some kvi -> nth_error l j = Some kvj ->
      svar sg (fst kvi) = Some ki -> svar sg (fst kvj) = Some kj -> ki <> kj).
Proof.
  induction l as [|kv l IH]; intros acc H; cbn [fold_left] in H.
  - split; [exact H|]. split; [intros x kv k _ F; destruct F|]. intros i j kvi kvj ki kj _ Hi. destruct i; discriminate Hi.
  - destruct (IH _ H) as (N & X & P).
    unfold fimg in N, X. destruct (svar sg (fst kv)) as [k0|] eqn:S0.
    + cbn [int_nodup] in N. apply andb_prop in N as [N1 N2].
      split; [exact N2|]. split.
      * intros x kv' k Hx [<-|Hin] Hs.
        -- rewrite S0 in Hs. injection Hs as <-. intros E0. subst x. exact (int_notin_In k0 acc N1 k0 Hx eq_refl).
        -- apply (X x kv' k); [right; exact Hx| exact Hin| exact Hs].
      * intros i j kvi kvj ki kj Hij Hi Hj Si Sj. destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
        destruct i as [|i].
        -- cbn [nth_error] in Hi. injection Hi as <-. rewrite S0 in Si. injection Si as <-.
           apply (X k0 kvj kj); [left; reflexivity| eapply nth_error_In; exact Hj| exact Sj].
        -- cbn [nth_error] in Hi. eapply (P i j); [lia| exact Hi| exact Hj| exact Si| exact Sj].
    + split; [exact N|]. split.
      * intros x kv' k Hx [<-|Hin] Hs; [rewrite S0 in Hs; discriminate|]. exact (X x kv' k Hx Hin Hs).
      * intros i j kvi kvj ki kj Hij Hi Hj Si Sj. destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
        destruct i as [|i].
        -- cbn [nth_error] in Hi. injection Hi as <-. rewrite S0 in Si. discriminate.
        -- cbn [nth_error] in Hi. eapply (P i j); [lia| exact Hi| exact Hj| exact Si| exact Sj].
Qed.

Lemma anchor_images_inj : forall TR, IMap.bst TR -> int_nodup (anchor_images sg TR) = true ->
  forall tk1 tr1 tk2 tr2 k1 k2, IMap.find tk1 TR = Some tr1 -> IMap.find tk2 TR = Some tr2 ->
    svar sg tk1 = Some k1 -> svar sg tk2 = Some k2 -> tk1 <> tk2 -> k1 <> k2.
Proof.
  intros TR B H tk1 tr1 tk2 tr2 k1 k2 F1 F2 S1 S2 NE.
  unfold anchor_images in H. rewrite IMap.fold_spec in H.
  change (int_nodup (fold_left fimg (IMap.elements TR) []) = true) in H.
  destruct (fold_img_inv _ _ H) as (_ & _ & P).
  apply (IMap.elements_spec _ _ _ B) in F1. apply (IMap.elements_spec _ _ _ B) in F2.
  destruct (In_nth_error _ _ F1) as [i Hi]. destruct (In_nth_error _ _ F2) as [j Hj].
  destruct (Nat.lt_trichotomy i j) as [L|[E0|L]].
  - exact (P i j _ _ k1 k2 L Hi Hj S1 S2).
  - subst j. rewrite Hi in Hj. injection Hj as E1 E2. congruence.
  - intros EQ. apply (P j i _ _ k2 k1 L Hj Hi S2 S1). congruence.
Qed.
End Images.

Lemma remove_first_spec : forall A (p : A -> bool) l l', remove_first p l = Some l' ->
  exists x, In x l /\ p x = true /\ (forall y, In y l' -> In y l).
Proof.
  induction l as [|a l IH]; intros l' H; cbn [remove_first] in H; [discriminate|].
  destruct (p a) eqn:Pa.
  - injection H as <-. exists a. split; [left; reflexivity|]. split; [exact Pa|]. intros y Hy; right; exact Hy.
  - destruct (remove_first p l) as [l''|] eqn:R; [|discriminate]. injection H as <-.
    destruct (IH l'' eq_refl) as (x & Hx & Px & Sub). exists x. split; [right; exact Hx|]. split; [exact Px|].
    intros y [<-|Hy]; [left; reflexivity| right; apply Sub; exact Hy].
Qed.

Lemma ops_match_In : forall sg ts os, ops_match sg ts os = true ->
  forall t, In t ts -> exists o, In o os /\ op_match sg t o = true.
Proof.
  induction ts as [|t0 ts IH]; intros os H t Hin; [destruct Hin|]. cbn [ops_match] in H.
  destruct (remove_first (op_match sg t0) os) as [os'|] eqn:R; [|discriminate].
  destruct (remove_first_spec _ _ _ _ R) as (x & Hx & Px & Sub).
  destruct Hin as [<-|Hin].
  - exists x. auto.
  - destruct (IH os' H t Hin) as (o & Ho & M). exists o. split; [apply Sub; exact Ho| exact M].
Qed.

Lemma remove_first_spec2 : forall A (p : A -> bool) l l', remove_first p l = Some l' ->
  exists x, p x = true /\ (forall y, In y l -> y = x \/ In y l').
Proof.
  induction l as [|a l IH]; intros l' H; cbn [remove_first] in H; [discriminate|].
  destruct (p a) eqn:Pa.
  - injection H as <-. exists a. split; [exact Pa|]. intros y [<-|Hy]; [left; reflexivity| right; exact Hy].
  - destruct (remove_first p l) as [l''|] eqn:R; [|discriminate]. injection H as <-.
    destruct (IH l'' eq_refl) as (x & Px & Sub). exists x. split; [exact Px|].
    intros y [<-|Hy]; [right; left; reflexivity|]. destruct (Sub y Hy) as [->|Hy']; [left; reflexivity| right; right; exact Hy'].
Qed.

Lemma ops_match_In_rev : forall sg ts os, ops_match sg ts os = true ->
  forall o, In o os -> exists t, In t ts /\ op_match sg t o = true.
Proof.
  induction ts as [|t0 ts IH]; intros os H o Hin; cbn [ops_match] in H.
  - destruct os; [destruct Hin| discriminate].
  - destruct (remove_first (op_match sg t0) os) as [os'|] eqn:R; [|discriminate].
    destruct (remove_first_spec2 _ _ _ _ R) as (x & Px & Sub).
    destruct (Sub o Hin) as [->|Hin'].
    + exists t0. split; [left; reflexivity| exact Px].
    + destruct (IH os' H o Hin') as (t & Ht & M). exists t. split; [right; exact Ht| exact M].
Qed.

Lemma op_match_sound : forall E sg t o, op_match sg t o = true ->
  op_id t = op_id o /\ List.map (den (subst_env E sg)) (op_args t) = List.map (den E) (op_args o).
Proof.
  intros E sg t o H. unfold op_match in H. apply andb_prop in H as [Hid Hgo]. apply int_eqb_eq' in Hid.
  split; [exact Hid|].
  revert Hgo. generalize (op_args o) as a. generalize (op_args t) as ta.
  induction ta as [|x ta IH]; intros [|y a] H; cbn beta iota in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. cbn [List.map]. rewrite (smatch_sound E sg x y H1), (IH a H2). reflexivity.
Qed.

Lemma entails_sound : forall E st T sg ms model,
  sstate_wfb T = true ->
  entails st T sg = true -> st_ok segs OPS E st ms model ->
  st_ok segs OPS (subst_env E sg) T ms model.
Proof.
  intros E st T sg ms model WF EN HS.
  unfold sstate_wfb in WF. apply andb_prop in WF as [WF WX0]. apply andb_prop in WF as [WB WR]. apply bst_b_sound in WB.
  unfold entails in EN.
  apply andb_prop in EN as [EN Hz0]. apply andb_prop in EN as [EN Hpriv]. apply andb_prop in EN as [EN Hops].
  apply andb_prop in EN as [EN Hfacts]. apply andb_prop in EN as [EN Hregs]. apply andb_prop in EN as [EN Hresv].
  apply andb_prop in EN as [EN Hff]. apply andb_prop in EN as [EN Hrf]. apply andb_prop in EN as [Hpc Hx0].
  apply int_eqb_eq' in Hpc. apply sv_eqb_eq in Hx0. apply privs_eqb_eq in Hpriv.
  unfold regions_match in Hregs. apply andb_prop in Hregs as [Hregs Hinj].
  destruct (svar sg 0%uint63) as [z0|] eqn:Sz0; [|discriminate]. apply int_eqb_eq' in Hz0. subst z0.
  pose proof HS as HS0.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  assert (IMG : forall tk tr, IMap.find tk (s_regs T) = Some tr ->
            exists k r, svar sg tk = Some k /\ IMap.find k (s_regs st) = Some r /\
                        PrimInt63.eqb tk 0%uint63 = PrimInt63.eqb k 0%uint63 /\
                        region_ok segs (s_priv st) (subst_env E sg) (ms_mem ms) tk tr /\
                        loZ r <= loZ tr /\ hiZ (subst_env E sg) tr <= hiZ E r /\
                        bv_unsigned (ev (subst_env E sg) tk) = bv_unsigned (ev E k) /\
                        rg_w tr = rg_w r).
  { intros tk tr Hf.
    pose proof (proj1 (IMap.forallb_spec _ _ WB) Hregs tk tr Hf) as P. cbn beta in P.
    destruct (svar sg tk) as [k|] eqn:Sk; [|discriminate].
    destruct (IMap.find k (s_regs st)) as [r|] eqn:Fk; [|discriminate].
    apply andb_prop in P as [HK RM]. apply Bool.eqb_prop in HK.
    pose proof (proj1 (IMap.forallb_spec _ _ WB) WR tk tr Hf) as WFt. cbn beta in WFt.
    assert (HWeq : rg_w tr = rg_w r).
    { clear -RM. unfold region_match in RM.
      repeat (apply andb_prop in RM as [RM ?X]).
      match goal with G : Bool.eqb (rg_w tr) (rg_w r) = true |- _ => exact (Bool.eqb_prop _ _ G) end. }
    destruct (region_match_sound E sg (s_priv st) (ms_mem ms) tk tr k r Sk HK WFt RM (Preg k r Fk)) as (RO & L & U).
    exists k, r. repeat (split; [first [reflexivity| assumption]|]).
    split; [|exact HWeq]. rewrite (subst_env_svar E sg tk k Sk). reflexivity. }
  constructor.
  -   rewrite <- Hpc. exact Ppc.
  -   exact Hx0.
  -   intros r. rewrite (Pregs r). symmetry. apply smatch_sound. exact (rf_forallb2_get _ _ _ _ _ Hrf r).
  -   intros r. rewrite (Pfregs r). symmetry. apply smatch_sound. exact (rf_forallb2_get _ _ _ _ _ Hff r).
  - exact Psvc.
  -   unfold resv_match in Hresv. unfold resv_ok in Presv |- *.
    destruct (s_resv T) as [|ta|]; destruct (s_resv st) as [|a|]; try discriminate; try exact I; try exact Presv.
    rewrite Presv. rewrite (smatch_sound E sg ta a Hresv). reflexivity.
  - exact Pfcsr.
  - exact Prom.
  -   rewrite (subst_env_svar E sg 0%uint63 0%uint63 Sz0). exact Pz.
  - exact WB.
  -   intros tk tr Hf. destruct (IMG tk tr Hf) as (k & r & _ & _ & _ & RO & _). rewrite Hpriv. exact RO.
  -   intros tk1 r1 tk2 r2 F1 F2 NE K1 K2 W a [A1 A2].
    destruct (IMG tk1 r1 F1) as (k1 & sr1 & S1 & G1 & E1 & _ & L1 & U1 & B1 & W1).
    destruct (IMG tk2 r2 F2) as (k2 & sr2 & S2 & G2 & E2 & _ & L2 & U2 & B2 & W2).
    rewrite B1 in A1. rewrite B2 in A2.
    refine (Pdisj k1 sr1 k2 sr2 G1 G2 _ _ _ _ a _).
    + exact (anchor_images_inj sg (s_regs T) WB Hinj tk1 r1 tk2 r2 k1 k2 F1 F2 S1 S2 NE).
    + rewrite <- E1. exact K1.
    + rewrite <- E2. exact K2.
    + rewrite <- W1, <- W2. exact W.
    + lia.
  -   intros r0 g gr c F0 Fg Hc i Hi. rewrite Hpriv.
    destruct (IMG 0%uint63 r0 F0) as (k & r & S & G & E0 & RO & _).
    rewrite Sz0 in S. injection S as <-.
    pose proof (proj1 (IMap.forallb_spec _ _ WB) Hregs 0%uint63 r0 F0) as P. cbn beta in P. rewrite Sz0, G in P.
    apply andb_prop in P as [_ RM]. unfold region_match in RM.
    apply andb_prop in RM as [RM _]. apply andb_prop in RM as [_ GM].
    change (IMap.forallb _ (rg_cells r0) = true) with (grans_match sg r0 r = true) in GM.
    pose proof (proj1 (IMap.forallb_spec _ _ WB) WR 0%uint63 r0 F0) as WFt. cbn beta in WFt.
    destruct (region_wfb_sound r0 WFt) as [Bt _].
    destruct (grans_match_corr sg r0 r Bt GM g gr c Fg Hc) as (gr' & c' & Hgr' & Hc' & M).
    destruct (cell_match_sound E sg c c' M) as (Ei & Ew & _). rewrite <- Ei, <- Ew in *.
    exact (Ppub r g gr' c' G Hgr' Hc' i Hi).
  -   unfold facts_hold. apply Forall_forall. intros f Hf.
    pose proof (proj1 (forallb_forall _ _) Hfacts f Hf) as P. cbn beta in P.
    exact (fact_entailed_sound E (s_facts st) sg f Pz Pfacts P).
  -   unfold ops_hold. apply Forall_forall. intros t Ht.
    destruct (ops_match_In sg _ _ Hops t Ht) as (o & Ho & M). destruct (op_match_sound E sg t o M) as [-> ->].
    exact (proj1 (Forall_forall _ _) Pops o Ho).
  -   unfold ops_apart. apply Forall_forall. intros t Ht a Ha.
    destruct (ops_match_In sg _ _ Hops t Ht) as (o & Ho & M). destruct (op_match_sound E sg t o M) as [Eid Eargs].
    rewrite Eid, Eargs in Ha.
    destruct (proj1 (Forall_forall _ _) Papart o Ho a Ha) as [NB PR]. rewrite Hpriv. split; [|exact PR].
    intros (tk & tr & Hf & K & Rg). apply NB.
    destruct (IMG tk tr Hf) as (k & r & S & G & E0 & _ & L & U & B & _).
    exists k, r. split; [exact G|]. split; [rewrite <- E0; exact K|]. rewrite B in Rg. lia.
  - exact Pmf.
  -
    intros a FA.
    assert (FA' : fx_acc segs E (s_regs st) a).
    { destruct FA as [(tk & tr & Hf & K & Rg)|SG]; [left| right; exact SG].
      destruct (IMG tk tr Hf) as (k & r & S & G & E0 & _ & L & U & B & _).
      exists k, r. split; [exact G|]. split; [rewrite <- E0; exact K|]. rewrite B in Rg. lia. }
    apply (op_cov_mono OPS (insts E (s_ops st))); [| exact (Pcov a FA')].
    intros o Ho. unfold insts in Ho |- *. apply in_map_iff in Ho as (so & <- & Hso).
    destruct (ops_match_In_rev sg _ _ Hops so Hso) as (t & Ht & M). destruct (op_match_sound E sg t so M) as [Eid Eargs].
    apply in_map_iff. exists t. split; [| exact Ht]. rewrite Eid, Eargs. reflexivity.
  - exact Pminv.
Qed.

Ltac cbn_st := cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setpc setf setresv setregs addfact
                    ms_upd Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
                    ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending
                    with_pc with_regs with_fregs with_resv with_fcsr core_of rget fget rset fset].

Lemma addfact_sound : forall E st ms model f,
  st_ok segs OPS E st ms model -> fact_holds E f -> st_ok segs OPS E (addfact st f) ms model.
Proof.
  intros E st ms model f HS Hf.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn_st; try assumption. constructor; assumption.
Qed.

Lemma dropfacts_sound : forall E st ms model keep,
  st_ok segs OPS E st ms model ->
  st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (firstn keep (s_facts st))
                       (s_ops st) (s_priv st) (s_next st)) ms model.
Proof.
  intros E st ms model keep HS.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn_st; try assumption. apply Forall_firstn. exact Pfacts.
Qed.

Lemma setreg_sound : forall E st ms model r v,
  st_ok segs OPS E st ms model -> r <> X0 -> den E (getr st r) = den E v ->
  st_ok segs OPS E (setr st r v) ms model.
Proof.
  intros E st ms model r v HS Hr Hv.
  assert (Hx : r5_eqb r X0 = false).
  { destruct (r5_eqb r X0) eqn:Q; [|reflexivity]. apply r5_eqb_spec in Q. contradiction. }
  rewrite (setr_eq st r v Hx).
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn_st; try assumption.
  - rewrite rf_get_set_other; [exact Px0| exact Hr].
  - intros r'. destruct (r5_eqb r' r) eqn:Q.
    + apply r5_eqb_spec in Q. subst r'. rewrite rf_get_set_same. rewrite <- Hv. exact (Pregs r).
    + rewrite rf_get_set_other. 2:{ intros EQ. subst. rewrite r5_eqb_refl in Q. discriminate. } exact (Pregs r').
Qed.

Lemma vsubst_sound : forall E x u v, den E (VP x wzero) = den E u -> den E (vsubst x u v) = den E v.
Proof.
  intros E x u v H.
  assert (Hu : den E u = ev E x).
  { rewrite <- H. cbn [den]. apply bv_add_0_r. apply wbv_wzero_unsigned. }
  induction v; cbn [vsubst]; try reflexivity.
  - destruct (PrimInt63.eqb x k) eqn:Q; [|reflexivity]. apply int_eqb_eq' in Q. subst k.
    rewrite den_sv_alu. cbn [den alu64 alu]. rewrite Hu. reflexivity.
  - rewrite den_sv_alu. cbn [den]. rewrite IHv1, IHv2. reflexivity.
  - rewrite den_sv_aluw. cbn [den]. rewrite IHv1, IHv2. reflexivity.
  - rewrite den_sv_md. cbn [den]. rewrite IHv1, IHv2. reflexivity.
  - rewrite den_sv_mdw. cbn [den]. rewrite IHv1, IHv2. reflexivity.
  - rewrite den_sv_ext_c. cbn [den]. rewrite IHv. reflexivity.
  - rewrite den_sv_ins_c. cbn [den]. rewrite IHv1, IHv2. reflexivity.
  - cbn [den]. rewrite IHv. reflexivity.
  - cbn [den]. rewrite IHv. reflexivity.
Qed.

Lemma fact_map_holds : forall E (f : sv -> sv) x, (forall a, den E (f a) = den E a) ->
  fact_holds E x -> fact_holds E (fact_map f x).
Proof.
  intros E f x Hf H. destruct x; cbn [fact_map fact_holds] in *; rewrite ?Hf; exact H.
Qed.

Section RegionMap.
Variable f : sv -> sv.
Variable E : env.
Hypothesis Hf : forall a, den E (f a) = den E a.

Lemma slot_sorted_map : forall s, slot_sorted (List.map (cell_map f) s) <-> slot_sorted s.
Proof.
  induction s as [|c s IH]; cbn [List.map slot_sorted]; [tauto|].
  destruct s as [|c' s']; cbn [List.map]; [tauto|].
  cbn [cell_map c_idx c_w]. tauto.
Qed.

Lemma slot_ok_map : forall m base s, slot_ok segs E m base s -> slot_ok segs E m base (List.map (cell_map f) s).
Proof.
  intros m base s [SS FA]. split; [apply slot_sorted_map; exact SS|].
  apply Forall_map. eapply Forall_impl; [|exact FA]. intros c Hc.
  unfold cell_ok in *. cbn [cell_map c_idx c_w c_v]. rewrite Hf. exact Hc.
Qed.

Lemma hiZ_map : forall r, hiZ E (region_map f r) = hiZ E r.
Proof. intros r. unfold hiZ, region_map. cbn [rg_hi]. rewrite Hf. reflexivity. Qed.
Lemma loZ_map : forall r, loZ (region_map f r) = loZ r.
Proof. reflexivity. Qed.

Lemma uncovered_map : forall r o, uncovered (region_map f r) o <-> uncovered r o.
Proof.
  intros r o. unfold uncovered, region_map. cbn [rg_cells].
  split; intros H g gr Hg F.
  - specialize (H g (gran_map f gr) Hg). rewrite IMap.find_map, F in H. destruct (H eq_refl) as [D FA].
    cbn [gran_map g_dirty g_cells] in D, FA. split; [exact D|].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) FA (cell_map f c) (in_map _ _ _ Hc)) as X.
    exact X.
  - rewrite IMap.find_map in F. destruct (IMap.find g (rg_cells r)) as [gr0|] eqn:F0; [|discriminate F]. cbn [option_map] in F.
    injection F as <-. destruct (H g gr0 Hg F0) as [D FA]. cbn [gran_map g_dirty g_cells]. split; [exact D|].
    apply Forall_map. eapply Forall_impl; [|exact FA]. intros c Hc. exact Hc.
Qed.

Lemma region_ok_map : forall priv m k r, region_ok segs priv E m k r -> region_ok segs priv E m k (region_map f r).
Proof.
  intros priv m k r RO. destruct RO as [Q1 Q2 Q3 Q4 Q5 Q6].
  constructor; rewrite ?hiZ_map, ?loZ_map.
  - unfold region_map; cbn [rg_cells]. apply IMap.bst_map. exact Q1.
  - exact Q2.
  - unfold region_map; cbn [rg_w]. exact Q3.
  - unfold region_map; cbn [rg_cells]. intros g gr F. rewrite IMap.find_map in F.
    destruct (IMap.find g (rg_cells r)) as [gr0|] eqn:F0; [|discriminate F]. cbn [option_map] in F. injection F as <-.
    cbn [gran_map g_cells]. apply slot_ok_map. exact (Q4 g gr0 F0).
  - unfold region_map; cbn [rg_cells]. intros g gr c i F Hc Hi. rewrite IMap.find_map in F.
    destruct (IMap.find g (rg_cells r)) as [gr0|] eqn:F0; [|discriminate F]. cbn [option_map] in F. injection F as <-.
    cbn [gran_map g_cells] in Hc. apply in_map_iff in Hc as (c0 & <- & Hc0).
    cbn [cell_map c_idx c_w] in Hi |- *. exact (Q5 g gr0 c0 i F0 Hc0 Hi).
  - intros o H1 H2 HU. apply (proj1 (uncovered_map r o)) in HU. exact (Q6 o H1 H2 HU).
Qed.
End RegionMap.

Lemma psubst_sound : forall E st ms model x u,
  st_ok segs OPS E st ms model -> den E (VP x wzero) = den E u ->
  st_ok segs OPS E (SS (s_pc st) (rf_map (vsubst x u) (s_rf st)) (rf_map (vsubst x u) (s_ff st))
                       (match s_resv st with RAddr a => RAddr (vsubst x u a) | rv => rv end)
                       (IMap.map (region_map (vsubst x u)) (s_regs st)) (List.map (fact_map (vsubst x u)) (s_facts st))
                       (List.map (op_map (vsubst x u)) (s_ops st)) (s_priv st) (s_next st)) ms model.
Proof.
  intros E st ms model x u HS Hxu.
  pose proof (vsubst_sound E x u) as VS.
  assert (VS' : forall a, den E (vsubst x u a) = den E a) by (intros a; apply VS; exact Hxu).
  assert (MD : forall args, List.map (den E) (List.map (vsubst x u) args) = List.map (den E) args).
  { intros args. rewrite List.map_map. apply List.map_ext. intros a. apply VS'. }
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn_st; try assumption.
  - rewrite rf_get_map, Px0. reflexivity.
  - intros r. rewrite rf_get_map, VS'. exact (Pregs r).
  - intros r. rewrite rf_get_map, VS'. exact (Pfregs r).
  - unfold resv_ok in *. destruct (s_resv st); [exact Presv| | exact Presv]. rewrite VS'. exact Presv.
  - apply IMap.bst_map. exact Pbst.
  - intros k r F. rewrite IMap.find_map in F. destruct (IMap.find k (s_regs st)) as [r0|] eqn:F0; [|discriminate F].
    cbn [option_map] in F. injection F as <-. apply region_ok_map; [exact VS'|]. exact (Preg k r0 F0).
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a. rewrite IMap.find_map in F1, F2.
    destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
    destruct (IMap.find k2 (s_regs st)) as [q2|] eqn:G2; [|discriminate F2].
    cbn [option_map] in F1, F2. injection F1 as <-. injection F2 as <-.
    rewrite !(hiZ_map _ E VS'), !(loZ_map _). apply (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2). exact W.
  - intros r0 g gr c F0 Fg Hc i Hi. rewrite IMap.find_map in F0.
    destruct (IMap.find 0%uint63 (s_regs st)) as [q0|] eqn:G0; [|discriminate F0]. cbn [option_map] in F0. injection F0 as <-.
    unfold region_map in Fg; cbn [rg_cells] in Fg. rewrite IMap.find_map in Fg.
    destruct (IMap.find g (rg_cells q0)) as [gr0|] eqn:Fg0; [|discriminate Fg]. cbn [option_map] in Fg. injection Fg as <-.
    cbn [gran_map g_cells] in Hc. apply in_map_iff in Hc as (c0 & <- & Hc0). cbn [cell_map c_idx c_w] in Hi |- *.
    exact (Ppub q0 g gr0 c0 G0 Fg0 Hc0 i Hi).
  - unfold facts_hold in *. apply Forall_map. eapply Forall_impl; [|exact Pfacts].
    intros f Hf. apply fact_map_holds; [| exact Hf]. intros a. apply VS. exact Hxu.
  - unfold ops_hold in *. apply Forall_map. eapply Forall_impl; [|exact Pops]. cbn beta. intros o Ho.
    unfold op_map; cbn [op_id op_args]. rewrite MD. exact Ho.
  - unfold ops_apart in *. apply Forall_map. eapply Forall_impl; [|exact Papart]. cbn beta. intros o Ho a Ha.
    unfold op_map in Ha; cbn [op_id op_args] in Ha. rewrite MD in Ha.
    destruct (Ho a Ha) as [NB PR]. split; [|exact PR]. intros (k1 & r1 & F1 & K1 & R1). apply NB.
    rewrite IMap.find_map in F1. destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
    cbn [option_map] in F1. injection F1 as <-. rewrite (hiZ_map _ E VS'), (loZ_map _) in R1.
    exists k1, q1. auto.
  -
    apply (cover_transfer segs OPS E E (s_regs st) _ (s_ops st) _); [| | exact Pcov].
    + apply fx_acc_based. intros a (k1 & r1 & F1 & K1 & R1).
      rewrite IMap.find_map in F1. destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
      cbn [option_map] in F1. injection F1 as <-. rewrite (hiZ_map _ E VS'), (loZ_map _) in R1. exists k1, q1. auto.
    + intros o Ho. unfold insts in *. rewrite List.map_map. apply in_map_iff in Ho as (so & <- & Hso).
      apply in_map_iff. exists so. split; [| exact Hso]. unfold op_map; cbn [op_id op_args]. rewrite MD. reflexivity.
Qed.

Section Inst.
Variable E : env.
Variable sg : subst.

Lemma sapply_d_den : forall v, sapply_ok sg v = true -> den E (sapply_d sg v) = den (subst_env E sg) v.
Proof.
  intros v H. unfold sapply_ok, sapply_d in *. destruct (sapply sg v) as [v'|] eqn:S; [|discriminate H].
  exact (sapply_sound E sg v v' S).
Qed.

Lemma slot_ok_inst : forall m base s, List.forallb (fun c => sapply_ok sg (c_v c)) s = true ->
  slot_ok segs (subst_env E sg) m base s -> slot_ok segs E m base (List.map (cell_map (sapply_d sg)) s).
Proof.
  intros m base s OK [SS FA]. split; [apply slot_sorted_map; exact SS|].
  apply Forall_map. apply Forall_forall. intros c Hc.
  pose proof (proj1 (Forall_forall _ _) FA c Hc) as CO. pose proof (proj1 (forallb_forall _ _) OK c Hc) as OKc.
  unfold cell_ok in *. cbn [cell_map c_idx c_w c_v]. rewrite (sapply_d_den _ OKc). exact CO.
Qed.

Lemma region_ok_inst : forall priv m tk k r,
  svar sg tk = Some k -> Bool.eqb (PrimInt63.eqb tk 0%uint63) (PrimInt63.eqb k 0%uint63) = true ->
  region_inst_ok sg r = true ->
  region_ok segs priv (subst_env E sg) m tk r -> region_ok segs priv E m k (region_map (sapply_d sg) r).
Proof.
  intros priv m tk k r SV EQ OK RO.
  apply bool_eqb_eq in EQ.
  unfold region_inst_ok in OK. apply andb_prop in OK as [OKhi OKcells].
  pose proof (subst_env_svar E sg tk k SV) as EV. pose proof (subst_env_eg E sg tk k SV) as EG.
  assert (HZ : hiZ E (region_map (sapply_d sg) r) = hiZ (subst_env E sg) r).
  { unfold hiZ, region_map. cbn [rg_hi]. rewrite (sapply_d_den _ OKhi). reflexivity. }
  assert (LZ : loZ (region_map (sapply_d sg) r) = loZ r) by reflexivity.
  destruct RO as [Q1 Q2 Q3 Q4 Q5 Q6].
  constructor; rewrite ?HZ, ?LZ, <- ?EV, <- ?EQ.
  - unfold region_map; cbn [rg_cells]. apply IMap.bst_map. exact Q1.
  - exact Q2.
  - unfold region_map; cbn [rg_w]. exact Q3.
  - unfold region_map; cbn [rg_cells]. intros g gr F. rewrite IMap.find_map in F.
    destruct (IMap.find g (rg_cells r)) as [gr0|] eqn:F0; [|discriminate F]. cbn [option_map] in F. injection F as <-.
    cbn [gran_map g_cells]. apply slot_ok_inst; [|exact (Q4 g gr0 F0)].
    exact (proj1 (IMap.forallb_inb _ _) OKcells g gr0 (proj1 (IMap.find_inb _ _ _ Q1) F0)).
  - unfold region_map; cbn [rg_cells]. intros g gr c i F Hc Hi. rewrite IMap.find_map in F.
    destruct (IMap.find g (rg_cells r)) as [gr0|] eqn:F0; [|discriminate F]. cbn [option_map] in F. injection F as <-.
    cbn [gran_map g_cells] in Hc. apply in_map_iff in Hc as (c0 & <- & Hc0).
    cbn [cell_map c_idx c_w] in Hi |- *. exact (Q5 g gr0 c0 i F0 Hc0 Hi).
  - intros o H1 H2 HU. apply (proj1 (uncovered_map _ r o)) in HU.
    specialize (Q6 o H1 H2 HU).
    unfold bg_byte in *. unfold region_map; cbn [rg_bg rg_cells]. rewrite <- ?EG. cbn [subst_env eb] in Q6 |- *.
    exact Q6.
Qed.

Lemma find_add_cases' : forall A k (v : A) R k' r', IMap.bst R -> IMap.find k' (IMap.add k v R) = Some r' ->
  (k' = k /\ r' = v) \/ (k' <> k /\ IMap.find k' R = Some r').
Proof.
  intros A k v R k' r' B H. destruct (PrimInt63.eqb k k') eqn:Q.
  - apply int_eqb_eq' in Q. subst k'. rewrite IMap.find_add_same in H by exact B. injection H as <-. left. auto.
  - rewrite IMap.find_add_other_eqb in H by assumption. right. split; [|exact H].
    intros EQ. subst. rewrite Uint63.eqb_refl in Q. discriminate.
Qed.

Definition rinst_rel (TR : IMap.t region) (k : int) (r' : region) : Prop :=
  exists tk tr, IMap.find tk TR = Some tr /\ svar sg tk = Some k /\
    Bool.eqb (PrimInt63.eqb tk 0%uint63) (PrimInt63.eqb k 0%uint63) = true /\
    region_inst_ok sg tr = true /\ r' = region_map (sapply_d sg) tr.

Lemma regs_inst_spec : forall TR R, IMap.bst TR -> regs_inst sg TR = Some R ->
  IMap.bst R /\ forall k r', IMap.find k R = Some r' -> rinst_rel TR k r'.
Proof.
  intros TR R BT H. unfold regs_inst in H.
  destruct (int_nodup _); [|discriminate H].
  rewrite IMap.fold_elements in H.
  set (step := fun (acc : option (IMap.t region)) (kv : int * region) =>
        match acc with
        | None => None
        | Some R0 =>
            match svar sg (fst kv) with
            | Some k =>
                if Bool.eqb (PrimInt63.eqb (fst kv) 0%uint63) (PrimInt63.eqb k 0%uint63) && region_inst_ok sg (snd kv)
                then Some (IMap.add k (region_map (sapply_d sg) (snd kv)) R0) else None
            | None => None
            end
        end) in H.
  set (INV := fun acc : option (IMap.t region) => forall R0, acc = Some R0 ->
         IMap.bst R0 /\ forall k r', IMap.find k R0 = Some r' -> rinst_rel TR k r').
  assert (IND : forall l acc, (forall kv, In kv l -> In kv (IMap.elements TR)) -> INV acc -> INV (fold_left step l acc)).
  { induction l as [|[tk tr] l IH]; intros acc SUB Hacc; cbn [fold_left]; [exact Hacc|].
    apply IH; [intros kv Hkv; apply SUB; right; exact Hkv|].
    intros R0 HR0. destruct acc as [R1|]; [|discriminate HR0].
    destruct (Hacc R1 eq_refl) as [B1 F1].
    cbn [step fst snd] in HR0. destruct (svar sg tk) as [k|] eqn:SV; [|discriminate HR0].
    destruct (Bool.eqb (PrimInt63.eqb tk 0%uint63) (PrimInt63.eqb k 0%uint63) && region_inst_ok sg tr) eqn:C; [|discriminate HR0].
    injection HR0 as <-. apply andb_prop in C as [C1 C2].
    split; [apply IMap.bst_add; exact B1|].
    intros k0 r0 F0. destruct (find_add_cases' _ _ _ _ _ _ B1 F0) as [[-> ->]|[NE F0']].
    - exists tk, tr. split; [|auto].
      apply (proj2 (IMap.find_inb _ _ _ BT)). apply (proj1 (IMap.elements_in _ _ _)). apply SUB. left. reflexivity.
    - exact (F1 k0 r0 F0'). }
  assert (I0 : INV (Some IMap.empty)).
  { intros R0 HR0. injection HR0 as <-. split; [apply IMap.bst_empty|]. intros k r' F. rewrite IMap.find_empty in F. discriminate F. }
  exact (IND _ _ (fun kv H => H) I0 R H).
Qed.

Lemma sapply_fact_complete : forall f f', sapply_fact sg f = Some f' -> fact_holds (subst_env E sg) f -> fact_holds E f'.
Proof.
  intros f f' H Hf.
  assert (AUX : forall a b a' b', sapply sg a = Some a' -> sapply sg b = Some b' ->
            den (subst_env E sg) a = den E a' /\ den (subst_env E sg) b = den E b').
  { intros a b a' b' Ha Hb. split; symmetry; apply sapply_sound; assumption. }
  destruct f; cbn [sapply_fact] in H.
  1-2: destruct (svar sg k) as [k'|] eqn:SV; [|discriminate H]; injection H as <-; cbn [fact_holds] in *;
       rewrite <- (subst_env_svar E sg k k' SV); exact Hf.
  all: destruct (sapply sg a) as [a'|] eqn:Ha; [|discriminate H]; destruct (sapply sg b) as [b'|] eqn:Hb; [|discriminate H];
       injection H as <-; destruct (AUX _ _ _ _ Ha Hb) as [Da Db]; cbn [fact_holds] in *; rewrite <- Da, <- Db; exact Hf.
Qed.

Lemma fact_inst_sound : forall f g, fact_holds (subst_env E sg) f -> In g (fact_inst sg f) -> fact_holds E g.
Proof.
  intros f g Hf Hg. unfold fact_inst in Hg.
  destruct f.
  1: { destruct (svar sg k) as [k'|] eqn:SV.
       + destruct Hg as [<-|[]]. cbn [fact_holds] in *. rewrite <- (subst_env_svar E sg k k' SV). exact Hf.
       + destruct (IMap.find k sg) as [u|] eqn:F; [|destruct Hg].
         cbn [fact_holds] in Hf. rewrite (subst_env_ev E sg k u F) in Hf.
         destruct Hg as [<-|[<-|[]]]; cbn [fact_holds]; rewrite den_VL; lia. }
  1: { destruct (svar sg k) as [k'|] eqn:SV; [|destruct Hg].
       destruct Hg as [<-|[]]. cbn [fact_holds] in *. rewrite <- (subst_env_svar E sg k k' SV). exact Hf. }
  all: match type of Hg with In _ (match ?s with _ => _ end) => destruct s as [f'|] eqn:SF; [|destruct Hg] end;
       destruct Hg as [<-|[]]; exact (sapply_fact_complete _ _ SF Hf).
Qed.

Lemma facts_inst_sound : forall fs, facts_hold (subst_env E sg) fs -> facts_hold E (List.flat_map (fact_inst sg) fs).
Proof.
  intros fs HF. unfold facts_hold in *. apply Forall_forall. intros g Hg.
  apply in_flat_map in Hg as (f & Hf & Hg). exact (fact_inst_sound f g (proj1 (Forall_forall _ _) HF f Hf) Hg).
Qed.

Lemma omap_list_spec : forall A B (f : A -> option B) l l', omap_list f l = Some l' ->
  Forall2 (fun x y => f x = Some y) l l'.
Proof.
  intros A B f l. induction l as [|x l IH]; intros l' H; cbn [omap_list] in H.
  - injection H as <-. constructor.
  - destruct (f x) as [y|] eqn:Fx; [|discriminate H]. destruct (omap_list f l) as [ys|] eqn:Fl; [|discriminate H].
    injection H as <-. constructor; [exact Fx| exact (IH ys eq_refl)].
Qed.

Lemma omap_sapply_den : forall args args', omap_list (sapply sg) args = Some args' ->
  List.map (den E) args' = List.map (den (subst_env E sg)) args.
Proof.
  intros args args' H. apply omap_list_spec in H. induction H as [|x y l l' Hxy _ IH]; [reflexivity|].
  cbn [List.map]. rewrite IH. rewrite (sapply_sound E sg x y Hxy). reflexivity.
Qed.

Lemma rf_allb_get' : forall A (p : A -> bool) x, rf_allb p x = true -> forall r, p (rf_get x r) = true.
Proof.
  intros A p x H r. unfold rf_allb in H. apply (proj1 (forallb_forall _ _)) with (x := rf_get x r) in H; [exact H|].
  destruct x; destruct r; cbn; tauto.
Qed.

Theorem st_inst_sound : forall n T st ms model,
  st_inst sg n T = Some st -> st_ok segs OPS (subst_env E sg) T ms model -> st_ok segs OPS E st ms model.
Proof.
  intros n T st ms model H HS.
  unfold st_inst in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate H] end.
  apply andb_prop in C as [C Cz]. apply andb_prop in C as [C Cx0]. apply andb_prop in C as [Crf Cff].
  destruct (resv_inst sg (s_resv T)) as [rv|] eqn:RV; [|discriminate H].
  destruct (regs_inst sg (s_regs T)) as [R|] eqn:RG; [|discriminate H].
  destruct (omap_list (op_inst sg) (s_ops T)) as [os|] eqn:OS; [|discriminate H].
  injection H as <-.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (regs_inst_spec (s_regs T) R Pbst RG) as [BR FR].
  assert (Z0 : ev E 0%uint63 = Z_to_bv 64 0).
  { destruct (svar sg 0%uint63) as [k|] eqn:SV; [|discriminate Cz]. apply int_eqb_eq' in Cz. subst k.
    rewrite <- (subst_env_svar E sg _ _ SV). exact Pz. }
  apply sv_eqb_eq in Cx0.
  pose proof (omap_list_spec _ _ _ _ _ OS) as OSR.
  assert (OPS2 : forall o', In o' os -> exists o, In o (s_ops T) /\ op_id o' = op_id o /\
                 List.map (den E) (op_args o') = List.map (den (subst_env E sg)) (op_args o)).
  { clear - OSR. induction OSR as [|o o' l l' Ho _ IH]; intros x Hx; [destruct Hx|].
    destruct Hx as [<-|Hx].
    - exists o. split; [left; reflexivity|]. unfold op_inst in Ho.
      destruct (omap_list (sapply sg) (op_args o)) as [args|] eqn:OA; [|discriminate Ho]. injection Ho as <-.
      cbn [op_id op_args]. split; [reflexivity|]. exact (omap_sapply_den _ _ OA).
    - destruct (IH x Hx) as (o0 & Ho0 & E1 & E2). exists o0. split; [right; exact Ho0| split; assumption]. }
  constructor; cbn_st; try assumption.
  - rewrite rf_get_map, Cx0. reflexivity.
  - intros r. rewrite rf_get_map, (sapply_d_den _ (rf_allb_get' _ _ _ Crf r)). exact (Pregs r).
  - intros r. rewrite rf_get_map, (sapply_d_den _ (rf_allb_get' _ _ _ Cff r)). exact (Pfregs r).
  - unfold resv_inst in RV. unfold resv_ok in *. destruct (s_resv T) as [|a|].
    + injection RV as <-. exact Presv.
    + destruct (sapply sg a) as [a'|] eqn:SA; [|discriminate RV]. injection RV as <-. rewrite (sapply_sound E sg a a' SA). exact Presv.
    + injection RV as <-. exact Presv.
  - intros k r' F. destruct (FR k r' F) as (tk & tr & Ftk & SV & EQ & OK & ->).
    apply (region_ok_inst (s_priv T) (ms_mem ms) tk k tr SV EQ OK). exact (Preg tk tr Ftk).
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a.
    destruct (FR k1 r1 F1) as (tk1 & tr1 & G1 & SV1 & EQ1 & OK1 & ->).
    destruct (FR k2 r2 F2) as (tk2 & tr2 & G2 & SV2 & EQ2 & OK2 & ->).
    apply bool_eqb_eq in EQ1. apply bool_eqb_eq in EQ2.
    assert (NT : tk1 <> tk2) by (intros ->; rewrite SV1 in SV2; injection SV2; intros; subst; exact (NE eq_refl)).
    unfold hiZ, loZ, region_map; cbn [rg_lo rg_hi rg_w] in *.
    unfold region_inst_ok in OK1, OK2. apply andb_prop in OK1 as [OH1 _]. apply andb_prop in OK2 as [OH2 _].
    rewrite (sapply_d_den _ OH1), (sapply_d_den _ OH2).
    rewrite <- (subst_env_svar E sg _ _ SV1), <- (subst_env_svar E sg _ _ SV2).
    apply (Pdisj tk1 tr1 tk2 tr2 G1 G2 NT); [rewrite EQ1; exact K1| rewrite EQ2; exact K2| exact W].
  - intros r0 g gr c F0 Fg Hc i Hi. destruct (FR _ _ F0) as (tk & tr & G0 & SV & EQ & OK & ->).
    apply bool_eqb_eq in EQ. rewrite Uint63.eqb_refl in EQ. apply int_eqb_eq' in EQ. subst tk.
    unfold region_map in Fg; cbn [rg_cells] in Fg. rewrite IMap.find_map in Fg.
    destruct (IMap.find g (rg_cells tr)) as [gr0|] eqn:Fg0; [|discriminate Fg]. cbn [option_map] in Fg. injection Fg as <-.
    cbn [gran_map g_cells] in Hc. apply in_map_iff in Hc as (c0 & <- & Hc0). cbn [cell_map c_idx c_w] in Hi |- *.
    exact (Ppub tr g gr0 c0 G0 Fg0 Hc0 i Hi).
  - apply facts_inst_sound. exact Pfacts.
  - unfold ops_hold in *. apply Forall_forall. intros o' Ho'. destruct (OPS2 o' Ho') as (o & Ho & -> & ->).
    exact (proj1 (Forall_forall _ _) Pops o Ho).
  - unfold ops_apart in *. apply Forall_forall. intros o' Ho' a Ha. destruct (OPS2 o' Ho') as (o & Ho & Eid & Eargs).
    rewrite Eid, Eargs in Ha. destruct (proj1 (Forall_forall _ _) Papart o Ho a Ha) as [NB PR]. split; [|exact PR].
    intros (k1 & r1 & F1 & K1 & R1). apply NB. destruct (FR k1 r1 F1) as (tk1 & tr1 & G1 & SV1 & EQ1 & OK1 & ->).
    apply bool_eqb_eq in EQ1. exists tk1, tr1. split; [exact G1|]. split; [rewrite EQ1; exact K1|].
    unfold hiZ, loZ, region_map in R1 |- *; cbn [rg_lo rg_hi] in R1 |- *.
    unfold region_inst_ok in OK1. apply andb_prop in OK1 as [OH1 _].
    rewrite (sapply_d_den _ OH1), <- (subst_env_svar E sg _ _ SV1) in R1. exact R1.
  -
    assert (OPS3 : forall o, In o (s_ops T) -> exists o', In o' os /\ op_id o' = op_id o /\
                 List.map (den E) (op_args o') = List.map (den (subst_env E sg)) (op_args o)).
    { clear - OSR. induction OSR as [|o o' l l' Ho _ IH]; intros x Hx; [destruct Hx|].
      destruct Hx as [<-|Hx].
      - exists o'. split; [left; reflexivity|]. unfold op_inst in Ho.
        destruct (omap_list (sapply sg) (op_args o)) as [args|] eqn:OA; [|discriminate Ho]. injection Ho as <-.
        cbn [op_id op_args]. split; [reflexivity|]. exact (omap_sapply_den _ _ OA).
      - destruct (IH x Hx) as (o0 & Ho0 & E1 & E2). exists o0. split; [right; exact Ho0| split; assumption]. }
    apply (cover_transfer segs OPS (subst_env E sg) E (s_regs T) R (s_ops T) os); [| | exact Pcov].
    + apply fx_acc_based. intros a (k1 & r1 & F1 & K1 & R1). destruct (FR k1 r1 F1) as (tk1 & tr1 & G1 & SV1 & EQ1 & OK1 & ->).
      apply bool_eqb_eq in EQ1. exists tk1, tr1. split; [exact G1|]. split; [rewrite EQ1; exact K1|].
      unfold hiZ, loZ, region_map in R1 |- *; cbn [rg_lo rg_hi] in R1 |- *.
      unfold region_inst_ok in OK1. apply andb_prop in OK1 as [OH1 _].
      rewrite (sapply_d_den _ OH1), <- (subst_env_svar E sg _ _ SV1) in R1. exact R1.
    + intros o Ho. unfold insts in *. apply in_map_iff in Ho as (so & <- & Hso).
      destruct (OPS3 so Hso) as (o' & Ho' & Eid & Eargs). apply in_map_iff. exists o'. split; [| exact Ho']. rewrite Eid, Eargs. reflexivity.
Qed.
End Inst.

Lemma den_getr_lit : forall E st r i, bv_unsigned (den E (getr st r)) = to_Z i -> den E (getr st r) = den E (VL (wlit i)).
Proof.
  intros E st r i H. apply bv_eq. rewrite H. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity.
Qed.

Lemma split_child_sound : forall E st ms model r (i : int),
  st_ok segs OPS E st ms model ->
  bv_unsigned (den E (getr st r)) = to_Z i ->
  st_ok segs OPS E (addfact (setr st r (VL (wlit i))) (FEq (getr st r) (VL (wlit i)))) ms model.
Proof.
  intros E st ms model r i HS Hi.
  pose proof (den_getr_lit E st r i Hi) as D.
  apply addfact_sound.
  - destruct (r5_eqb r X0) eqn:Q.
    + apply r5_eqb_spec in Q. subst r. rewrite setr_x0. exact HS.
    + apply setreg_sound; [exact HS| | exact D]. intros EQ. subst. rewrite r5_eqb_refl in Q. discriminate.
  - cbn [fact_holds]. exact D.
Qed.

Lemma find_add_cases : forall A k (v : A) R k' r', IMap.bst R -> IMap.find k' (IMap.add k v R) = Some r' ->
  (k' = k /\ r' = v) \/ (k' <> k /\ IMap.find k' R = Some r').
Proof.
  intros A k v R k' r' B H. destruct (PrimInt63.eqb k k') eqn:Q.
  - apply int_eqb_eq' in Q. subst k'. rewrite IMap.find_add_same in H by exact B. injection H as <-. left. auto.
  - rewrite IMap.find_add_other_eqb in H by assumption. right. split; [|exact H].
    intros EQ. subst. rewrite Uint63.eqb_refl in Q. discriminate.
Qed.

Lemma forget_sound : forall E st ms model k r glo ghi,
  st_ok segs OPS E st ms model -> IMap.find k (s_regs st) = Some r ->
  st_ok segs OPS E (setregs st (IMap.add k (Mem.region_forget r glo ghi) (s_regs st))) ms model.
Proof.
  intros E st ms model k r glo ghi HS Hk.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (MemP.region_forget_sound segs (s_priv st) E (ms_mem ms) k r glo ghi (Preg k r Hk)) as (RO' & Elo & Ehi & Ew & Ebg).
  set (r' := Mem.region_forget r glo ghi) in *.
  assert (LH : loZ r' = loZ r /\ forall E', hiZ E' r' = hiZ E' r).
  { unfold loZ, hiZ. rewrite Elo, Ehi. split; reflexivity. }
  destruct LH as [Elo' Ehi'].
  assert (OLD : forall k1 r1, IMap.find k1 (IMap.add k r' (s_regs st)) = Some r1 ->
            exists r0, IMap.find k1 (s_regs st) = Some r0 /\ loZ r1 = loZ r0 /\ hiZ E r1 = hiZ E r0 /\
                       (r1 = r0 \/ (k1 = k /\ r0 = r /\ r1 = r'))).
  { intros k1 r1 F. destruct (find_add_cases _ _ _ _ _ _ Pbst F) as [[-> ->]|[NE F']].
    - exists r. rewrite Elo', Ehi'. auto 10.
    - exists r1. auto 10. }
  assert (OLDW : forall k1 r1, IMap.find k1 (IMap.add k r' (s_regs st)) = Some r1 ->
            exists r0, IMap.find k1 (s_regs st) = Some r0 /\ rg_w r1 = rg_w r0).
  { intros k1 r1 F. destruct (OLD k1 r1 F) as (r0 & G0 & _ & _ & C).
    exists r0. split; [exact G0|].
    destruct C as [->|(_ & -> & ->)]; [reflexivity|]. exact Ew. }
  constructor; cbn_st; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k1 r1 F. destruct (find_add_cases _ _ _ _ _ _ Pbst F) as [[-> ->]|[NE F']]; [exact RO'| exact (Preg k1 r1 F')].
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a.
    destruct (OLD k1 r1 F1) as (q1 & G1 & L1 & U1 & _). destruct (OLD k2 r2 F2) as (q2 & G2 & L2 & U2 & _).
    destruct (OLDW k1 r1 F1) as (q1' & G1' & W1). destruct (OLDW k2 r2 F2) as (q2' & G2' & W2).
    rewrite G1 in G1'. injection G1' as <-. rewrite G2 in G2'. injection G2' as <-.
    rewrite L1, U1, L2, U2. apply (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2). rewrite <- W1, <- W2. exact W.
  - intros r0 g gr c F0 Fg Hc i Hi. destruct (OLD 0%uint63 r0 F0) as (q0 & G0 & _ & _ & [E1|(Ek & Eq0 & Er0)]).
    + subst r0. exact (Ppub q0 g gr c G0 Fg Hc i Hi).
    + subst q0 r0. rewrite <- Ek in Hk. pose proof (ro_bst _ _ _ _ _ _ (Preg _ _ Hk)) as RB.
      destruct (MemP.fold_dirty_spec (IMap.find_range glo ghi (rg_cells r)) (rg_cells r) RB) as [_ FD].
      unfold r', Mem.region_forget in Fg. destruct (Mem.is_bgnone (rg_bg r)); cbn [rg_cells] in Fg.
      * rewrite IMap.find_remove_range in Fg by exact RB. destruct (_ && _)%bool; [discriminate Fg|]. exact (Ppub r g gr c Hk Fg Hc i Hi).
      * rewrite FD in Fg. destruct (existsb _ _); [injection Fg as <-; destruct Hc|]. exact (Ppub r g gr c Hk Fg Hc i Hi).
  - unfold ops_apart in *. eapply Forall_impl; [|exact Papart]. cbn beta. intros o Ho a Ha.
    destruct (Ho a Ha) as [NB PR]. split; [|exact PR]. intros (k1 & r1 & F1 & K1 & R1). apply NB.
    destruct (OLD k1 r1 F1) as (q1 & G1 & L1 & U1 & _). exists k1, q1. rewrite <- L1, <- U1. auto.
  -
    intros a FA. apply Pcov. revert a FA. apply fx_acc_based. intros a (k1 & r1 & F1 & K1 & R1).
    destruct (OLD k1 r1 F1) as (q1 & G1 & L1 & U1 & _). exists k1, q1. rewrite <- L1, <- U1. auto.
Qed.

Lemma sethi_sound : forall E st ms model k r v,
  st_ok segs OPS E st ms model -> IMap.find k (s_regs st) = Some r -> PrimInt63.eqb k 0%uint63 = false ->
  den E (rg_hi r) = den E v ->
  st_ok segs OPS E (setregs st (IMap.add k (Region (rg_lo r) v (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st))) ms model.
Proof.
  intros E st ms model k r v HS Hk K0 Hv.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  set (r' := Region (rg_lo r) v (rg_w r) (rg_bg r) (rg_cells r)) in *.
  assert (Elo' : loZ r' = loZ r) by reflexivity.
  assert (Ehi' : hiZ E r' = hiZ E r) by (unfold hiZ; cbn [r' rg_hi]; rewrite Hv; reflexivity).
  assert (RO' : region_ok segs (s_priv st) E (ms_mem ms) k r').
  { pose proof (Preg k r Hk) as RO. destruct RO as [Q1 Q2 Q3 Q4 Q5 Q6].
    constructor; cbn [r' rg_lo rg_hi rg_w rg_bg rg_cells]; rewrite ?Ehi'; try assumption. }
  assert (OLD : forall k1 r1, IMap.find k1 (IMap.add k r' (s_regs st)) = Some r1 ->
            exists r0, IMap.find k1 (s_regs st) = Some r0 /\ loZ r1 = loZ r0 /\ hiZ E r1 = hiZ E r0 /\ rg_w r1 = rg_w r0 /\
                       (r1 = r0 \/ (k1 = k /\ r0 = r /\ r1 = r'))).
  { intros k1 r1 F. destruct (find_add_cases _ _ _ _ _ _ Pbst F) as [[-> ->]|[NE F']].
    - exists r. rewrite Elo', Ehi'. auto 10.
    - exists r1. auto 10. }
  constructor; cbn_st; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k1 r1 F. destruct (find_add_cases _ _ _ _ _ _ Pbst F) as [[-> ->]|[NE F']]; [exact RO'| exact (Preg k1 r1 F')].
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a.
    destruct (OLD k1 r1 F1) as (q1 & G1 & L1 & U1 & W1 & _). destruct (OLD k2 r2 F2) as (q2 & G2 & L2 & U2 & W2 & _).
    rewrite L1, U1, L2, U2. apply (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2). rewrite <- W1, <- W2. exact W.
  - intros r0 g gr c F0 Fg Hc i Hi. destruct (OLD 0%uint63 r0 F0) as (q0 & G0 & _ & _ & _ & [E1|(Ek & Eq0 & Er0)]).
    + subst r0. exact (Ppub q0 g gr c G0 Fg Hc i Hi).
    + exfalso. rewrite <- Ek in K0. rewrite Uint63.eqb_refl in K0. discriminate K0.
  - unfold ops_apart in *. eapply Forall_impl; [|exact Papart]. cbn beta. intros o Ho a Ha.
    destruct (Ho a Ha) as [NB PR]. split; [|exact PR]. intros (k1 & r1 & F1 & K1 & R1). apply NB.
    destruct (OLD k1 r1 F1) as (q1 & G1 & L1 & U1 & _). exists k1, q1. rewrite <- L1, <- U1. auto.
  -
    intros a FA. apply Pcov. revert a FA. apply fx_acc_based. intros a (k1 & r1 & F1 & K1 & R1).
    destruct (OLD k1 r1 F1) as (q1 & G1 & L1 & U1 & _). exists k1, q1. rewrite <- L1, <- U1. auto.
Qed.

Lemma fetch_branch_step : forall E st ms model c rs1 rs2 off w i,
  st_ok segs OPS E st ms model ->
  fetch_word segs (Z_to_bv 64 (to_Z (s_pc st))) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  of_instr i = Some (IBranch c rs1 rs2 off) ->
  RiscvSemantics.step segs ms =
    MachineOk (ms_upd ms (with_pc (if branch_taken c (den E (getr st rs1)) (den E (getr st rs2))
                                   then (Z_to_bv 64 (to_Z (s_pc st)) + wbv off)%bv
                                   else (Z_to_bv 64 (to_Z (s_pc st)) + Z_to_bv 64 4)%bv) (core_of ms)) (ms_mem ms)).
Proof.
  intros E st ms model c rs1 rs2 off w i HS Hf He Hd Hof.
  rewrite <- (so_pc _ _ _ _ _ _ HS) in Hf.
  rewrite (step_exec segs ms w i Hf He Hd).
  destruct i; cbn [of_instr] in Hof; try discriminate Hof;
  repeat match type of Hof with
  | context [match r5_of_reg ?r with _ => _ end] =>
      let d := fresh "d" in let Hd := fresh "Hd" in
      destruct (r5_of_reg r) as [d|] eqn:Hd; [apply reg_of_r5_of_reg in Hd; subst r | discriminate Hof]
  | context [match ?x with _ => _ end] => is_var x; destruct x
  end; try discriminate Hof.
  injection Hof; intros; subst. cbn [Sem.exec]. rewrite (StepA.interp_EDone segs).
  rewrite <- !(StepA.getr_den segs OPS E st ms model _ HS), wbv_w_of_imm.
  rewrite (StepA.pc_core segs OPS E st ms model HS). reflexivity.
Qed.

Lemma take_branch_sound : forall E st ms model it c rs1 rs2 off taken st',
  itab_ok segs it -> st_ok segs OPS E st ms model ->
  PrimInt63.ltb (s_pc st) bit62i = true ->
  IMap.find (s_pc st) it = Some (IBranch c rs1 rs2 off) ->
  branch_taken c (den E (getr st rs1)) (den E (getr st rs2)) = taken ->
  take_branch c (getr st rs1) (getr st rs2) off taken st = Some st' ->
  exists ms', Run.mi_account_step segs ms model = MachineOk (ms', model) /\ st_ok segs OPS E st' ms' model.
Proof.
  intros E st ms model it c rs1 rs2 off taken st' Hit HS Hpc Hfind Hbt Htb.
  destruct (itab_find segs it (s_pc st) _ Hit Hfind) as (w & Hf & [[He Hfi] | (He & i & Hdec & Hof)]); [discriminate Hfi|].

  assert (NM : forall cc a n, ~ Acc.mem_acc i cc a n).
  { intros cc a n. destruct i; cbn [Acc.mem_acc]; auto; unfold of_instr in Hof;
      repeat match type of Hof with context [match r5_of_reg ?r with _ => _ end] => destruct (r5_of_reg r) end; discriminate Hof. }
  assert (ACC : forall ms', RiscvSemantics.step segs ms = MachineOk ms' -> Run.mi_account_step segs ms model = MachineOk (ms', model)).
  { intros ms' Hs. pose proof Hf as Hf'. rewrite <- (so_pc _ _ _ _ _ _ HS) in Hf'.
    exact (Acc.account_step_noacc segs ms w i ms' model Hf' He Hdec NM Hs). }
  pose proof (fetch_branch_step E st ms model c rs1 rs2 off w i HS Hf He Hdec Hof) as FBS. rewrite Hbt in FBS.
  pose proof (addfact_sound E st ms model (fact_of_branch c (getr st rs1) (getr st rs2) taken) HS
                (fact_of_branch_holds E c _ _ taken Hbt)) as HS1.
  unfold take_branch in Htb. destruct taken.
  - destruct (pc_add (s_pc st) off) as [t|] eqn:Ht; [|discriminate]. injection Htb as <-.
    eexists. split; [exact (ACC _ FBS)|].
    rewrite <- (pc_add_ok _ _ _ Ht). apply st_ok_pc. exact HS1.
  - injection Htb as <-. eexists. split; [exact (ACC _ FBS)|].
    unfold pc4. rewrite <- (pc4_ok _ Hpc). apply st_ok_pc. exact HS1.
Qed.

Lemma take_branch_next : forall c a b off taken st st', take_branch c a b off taken st = Some st' -> s_next st' = s_next st.
Proof.
  intros c a b off taken st st' H. unfold take_branch in H. destruct taken.
  - destruct (pc_add (s_pc st) off); [|discriminate]. injection H as <-. reflexivity.
  - injection H as <-. reflexivity.
Qed.

Lemma s_next_setr : forall st r v, s_next (setr st r v) = s_next st.
Proof. intros st r v. destruct r; reflexivity. Qed.

Lemma do_store_next : forall st a w v st', do_store segs st a w v = inl st' -> s_next st' = s_next st.
Proof.
  intros st a w v st' H. unfold do_store in H.
  destruct (addr_of a) as [[k o]|]; [|discriminate]. destruct (IMap.find k (s_regs st)); [|discriminate].
  destruct (okey o); [|discriminate]. destruct (can_write _ _ _ _ _ _ _); [|discriminate].
  injection H as <-. reflexivity.
Qed.

Lemma exec_next : forall fi st st', exec segs fi st = XOk st' -> s_next st' = s_next st.
Proof.
  intros fi st st' H. destruct fi; cbn [exec] in H;
  repeat match type of H with
  | XStop _ = XOk _ => discriminate H
  | XOk _ = XOk _ => injection H as <-
  | (match ?x with _ => _ end) = XOk _ => destruct x eqn:?
  end;
  cbn [s_next setpc setf setresv addfact]; rewrite ?s_next_setr; cbn [s_next setresv];
  try reflexivity;
  repeat match goal with
  | Hd : do_store _ _ _ _ _ = inl ?s |- _ => apply do_store_next in Hd; rewrite ?Hd; clear Hd
  end; cbn [s_next setresv]; rewrite ?s_next_setr; try reflexivity.
  all: fail "exec_next: unsolved".
Qed.

Lemma step_next : forall it st st', step segs it st = SOk st' -> s_next st' = s_next st.
Proof.
  intros it st st' H. unfold step in H.
  destruct (PrimInt63.ltb (s_pc st) bit62i); [|discriminate].
  destruct (IMap.find (s_pc st) it) as [fi|]; [|discriminate].
  destruct (exec segs fi st) as [s|] eqn:X; [|discriminate]. injection H as <-. exact (exec_next fi st s X).
Qed.

Lemma step1_cases : forall it stops st,
  (exists st', step1 segs it stops st = SOk st' /\ s_next st' = s_next st) \/ (exists why, step1 segs it stops st = SStop why st).
Proof.
  intros it stops st. unfold step1. destruct (in_stops (s_pc st) stops); [right; eexists; reflexivity|].
  unfold step. destruct (PrimInt63.ltb (s_pc st) bit62i); [|right; eexists; reflexivity].
  destruct (IMap.find (s_pc st) it) as [fi|]; [|right; eexists; reflexivity].
  destruct (exec segs fi st) as [s|w] eqn:X; [left| right; eexists; reflexivity].
  exists s. split; [reflexivity| exact (exec_next fi st s X)].
Qed.

Lemma runP_next : forall p it stops st,
  match runP segs p it stops st with SOk st' => s_next st' = s_next st | SStop _ st' => s_next st' = s_next st end.
Proof.
  induction p as [q IH|q IH|]; intros it stops st; cbn [runP].
  - pose proof (IH it stops st) as H1. destruct (runP segs q it stops st) as [s1|w1 s1]; [|exact H1].
    pose proof (IH it stops s1) as H2. destruct (runP segs q it stops s1) as [s2|w2 s2]; [|congruence].
    destruct (step1_cases it stops s2) as [(s3 & -> & E3)|(w3 & ->)]; congruence.
  - pose proof (IH it stops st) as H1. destruct (runP segs q it stops st) as [s1|w1 s1]; [|exact H1].
    pose proof (IH it stops s1) as H2. destruct (runP segs q it stops s1) as [s2|w2 s2]; congruence.
  - destruct (step1_cases it stops st) as [(s3 & -> & E3)|(w3 & ->)]; congruence.
Qed.

Lemma run_next : forall it stops st why st', run segs it stops st = SStop why st' -> s_next st' = s_next st.
Proof.
  intros it stops st why st'. unfold run.
  pose proof (runP_next (2^40)%positive it stops st) as H.
  set (r := runP segs _ it stops st) in H |- *. clearbody r.
  destruct r as [s1|w1 s1]; intros Hr; injection Hr as E1 E2; subst; exact H.
Qed.

Lemma decode_Ecall_word : forall w, decode w = Some Ecall -> bv_unsigned w = 0x73.
Proof.
  intros w H. unfold decode in H. cbv zeta beta in H.
  repeat match type of H with
  | context [match ?x with _ => _ end] => destruct x eqn:?; try discriminate H
  end.
  all: try assumption. all: try reflexivity.
Qed.

Lemma of_instr_IEcall : forall i, of_instr i = Some IEcall -> i = Ecall.
Proof.
  intros i Hof. destruct i; cbn [of_instr] in Hof; try discriminate Hof; try reflexivity;
  repeat match type of Hof with
  | context [match r5_of_reg ?r with _ => _ end] => destruct (r5_of_reg r); [| discriminate Hof]
  | context [match ?x with _ => _ end] => is_var x; destruct x
  end; discriminate Hof.
Qed.

Lemma itab_ecall_at : forall it pc, itab_ok segs it -> IMap.find pc it = Some IEcall -> ecall_at pc.
Proof.
  intros it pc Hit Hf. destruct (itab_find segs it pc IEcall Hit Hf) as (w & Hw & [[He _]|(He & i & Hd & Hof)]).
  - exists w. auto.
  - exfalso. apply of_instr_IEcall in Hof. subst i. unfold decode_any in Hd.
    destruct (decide _); [| destruct (decode16 _); [injection Hd; intros; lia| discriminate]].
    destruct (decode w) as [i'|] eqn:D; [|discriminate]. injection Hd as ->.
    apply decode_Ecall_word in D. unfold is_ecall, bv_eqb in He. rewrite D in He. cbn in He. discriminate.
Qed.

Lemma plan_ind2 : forall (P : plan -> Prop),
  (forall stops k, P k -> P (PRun stops k)) ->
  (forall kT kF, P kT -> P kF -> P (PCase kT kF)) ->
  (forall r n ks, Forall P ks -> P (PSplit r n ks)) ->
  (forall r v k, P k -> P (PSetReg r v k)) ->
  (forall x u k, P k -> P (PSubst x u k)) ->
  (forall r k, P k -> P (PName r k)) ->
  (forall rk v k, P k -> P (PSetHi rk v k)) ->
  (forall f k, P k -> P (PAssume f k)) ->
  (forall cid ks, Forall P ks -> P (PCall cid ks)) ->
  (forall tid sg, P (PCut tid sg)) ->
  (forall tid sg, P (PCutDec tid sg)) ->
  (forall eid sg, P (PEcall eid sg)) ->
  (forall k glo ghi kk, P kk -> P (PForget k glo ghi kk)) ->
  (forall keep k, P k -> P (PDropFacts keep k)) ->
  (forall msg, P (PFail msg)) ->
  forall p, P p.
Proof.
  intros P Hrun Hcase Hsplit Hset Hsub Hname Hsethi Hass Hcall Hcut Hdec Hec Hfg Hdrop Hfail.
  fix F 1. intros p. destruct p as [stops k|kT kF|r n ks|r v k|x u k|r k|rk v k|f k|cid ks|tid sg|tid sg|eid sg|k glo ghi kk|keep k|msg].
  - apply Hrun. apply F.
  - apply Hcase; apply F.
  - apply Hsplit. revert ks. fix G 1. intros [|k ks]; [constructor| constructor; [apply F| apply G]].
  - apply Hset. apply F.
  - apply Hsub. apply F.
  - apply Hname. apply F.
  - apply Hsethi. apply F.
  - apply Hass. apply F.
  - apply Hcall. revert ks. fix G 1. intros [|k ks]; [constructor| constructor; [apply F| apply G]].
  - apply Hcut.
  - apply Hdec.
  - apply Hec.
  - apply Hfg. apply F.
  - apply Hdrop. apply F.
  - apply Hfail.
Qed.

Lemma fact_refuted_sound : forall E fs f, facts_hold E fs -> fact_holds E f -> fact_refuted fs f = true -> False.
Proof.
  intros E fs f Hfs Hf R. destruct f; cbn [fact_refuted] in R; cbn [fact_holds] in Hf; try discriminate.
  - rewrite wltu_w2Z in R. apply Z.ltb_lt in R. lia.
  - destruct (decide_ltu fs a b) as [[|]|] eqn:D; try discriminate.
    pose proof (decide_ltu_sound E fs Hfs _ _ _ D) as X. apply (proj1 (ltu_iff _ _ false)) in X. lia.
  - destruct (decide_ltu fs b a) as [[|]|] eqn:D; try discriminate.
    pose proof (decide_ltu_sound E fs Hfs _ _ _ D) as X. apply (proj1 (ltu_iff _ _ true)) in X. lia.
  - destruct (decide_eq fs a b) as [[|]|] eqn:D; try discriminate.
    pose proof (decide_eq_sound E fs Hfs _ _ _ D) as X. apply (proj1 (eqb_iff _ _ false)) in X. exact (X Hf).
  - destruct (decide_eq fs a b) as [[|]|] eqn:D; try discriminate.
    pose proof (decide_eq_sound E fs Hfs _ _ _ D) as X. apply (proj1 (eqb_iff _ _ true)) in X. exact (Hf X).
Qed.
Lemma rev_append_In : forall (A : Type) (pre l : list A) x, In x (rev_append pre l) <-> In x pre \/ In x l.
Proof. intros A pre l x. rewrite rev_append_rev, in_app_iff, <- in_rev. tauto. Qed.
Lemma dead_go_sound : forall E pre l, facts_hold E pre -> facts_hold E l -> dead_go pre l = true -> False.
Proof.
  intros E pre l. revert pre. induction l as [|f l IH]; intros pre Hpre Hl D; cbn [dead_go] in D; [discriminate|].
  inversion Hl as [|f' l' Hf Hl']; subst.
  apply orb_prop in D as [D|D].
  - apply (fact_refuted_sound E (rev_append pre l) f); [| exact Hf| exact D].
    unfold facts_hold. apply Forall_forall. intros x Hx. apply rev_append_In in Hx as [Hx|Hx].
    + exact (proj1 (Forall_forall _ _) Hpre x Hx).
    + exact (proj1 (Forall_forall _ _) Hl' x Hx).
  - apply (IH (f :: pre)); [constructor; assumption| exact Hl'| exact D].
Qed.
Theorem facts_dead_sound : forall E fs, facts_hold E fs -> facts_dead fs = true -> False.
Proof. intros E fs H D. exact (dead_go_sound E [] fs (Forall_nil _) H D). Qed.

Lemma leaves_mono : forall C p p' MP K E m,
  (forall tid, uses_plain_cut p' tid = true -> uses_plain_cut p tid = true) ->
  leaves_ok C p MP K E m -> leaves_ok C p' MP K E m.
Proof.
  intros C p p' MP K E m Hm [H1 H2]. split; [|exact H2].
  intros tid T HT E' ms' model' Heb HMP HS' HU. apply (H1 tid T HT E' ms' model' Heb HMP HS').
  destruct HU as [HU|HU]; [left; apply Hm; exact HU| right; exact HU].
Qed.

Lemma leaves_mono_st : forall N C p p' MP K E m,
  (forall tid, uses_plain_cut p' tid = true -> uses_plain_cut p tid = true) ->
  leaves_ok_st N C p MP K E m -> leaves_ok_st N C p' MP K E m.
Proof.
  intros N C p p' MP K E m Hm [H1 H2]. split; [|exact H2].
  intros tid T HT E' ms' model' Heb HSt HMP HS' HU. apply (H1 tid T HT E' ms' model' Heb HSt HMP HS').
  destruct HU as [HU|HU]; [left; apply Hm; exact HU| right; exact HU].
Qed.

Lemma plan_stable_list : forall N ks k,
  (fix go (l : list plan) : bool := match l with [] => true | k :: l' => plan_stable N k && go l' end) ks = true ->
  In k ks -> plan_stable N k = true.
Proof.
  intros N. induction ks as [|k0 ks IH]; intros k H Hin; [destruct Hin|]. cbn in H. fold (plan_stable N) in H.
  apply andb_prop in H as [H0 H1]. destruct Hin as [<-|Hin]; [exact H0| exact (IH k H1 Hin)].
Qed.

Lemma sg_stable_0 : forall sg, sg_stable 0%uint63 sg = true.
Proof.
  intros sg. unfold sg_stable. apply forallb_forall. intros kv _.
  destruct (PrimInt63.ltb (fst kv) 0%uint63) eqn:L; [| reflexivity]. apply ltb_spec in L. pose proof (int_range (fst kv)). change (to_Z 0%uint63) with 0 in L. lia.
Qed.
Lemma plan_stable_0 : forall p, plan_stable 0%uint63 p = true.
Proof.
  apply plan_ind2; intros; cbn [plan_stable]; try reflexivity; try assumption; try apply sg_stable_0.
  - rewrite H, H0. reflexivity.
  - induction ks as [|k ks IH]; [reflexivity|]. inversion H as [|? ? Hk Hks]; subst. cbn. fold (plan_stable 0%uint63). rewrite Hk. exact (IH Hks).
  - induction ks as [|k ks IH]; [reflexivity|]. inversion H as [|? ? Hk Hks]; subst. cbn. fold (plan_stable 0%uint63). rewrite Hk. exact (IH Hks).
Qed.

Lemma stable_refl : forall N E, stable N E E.
Proof. intros N E k _. split; reflexivity. Qed.
Lemma stable_0 : forall E E', stable 0%uint63 E E'.
Proof. intros E E' k Hk. pose proof (int_range k). change (to_Z 0%uint63) with 0 in Hk. lia. Qed.

Lemma stable_ext : forall N E0 E E' n, env_ext n E E' -> to_Z N <= to_Z n -> stable N E0 E -> stable N E0 E'.
Proof.
  intros N E0 E E' n [_ HX] HN HS k Hk. destruct (HX k ltac:(lia)) as [A B]. destruct (HS k Hk) as [A0 B0].
  split; [rewrite A; exact A0 | rewrite B; exact B0].
Qed.

Lemma mk_subst_find_in : forall (sg : list (int * sv)) k u, IMap.find k (mk_subst sg) = Some u -> In (k, u) sg.
Proof.
  intros sg. unfold mk_subst.
  assert (G : forall acc k u, IMap.bst acc ->
            IMap.find k (fold_left (fun m kv => IMap.add (fst kv) (snd kv) m) sg acc) = Some u ->
            In (k, u) sg \/ IMap.find k acc = Some u).
  { induction sg as [|[k0 v0] l IH]; intros acc k u Hacc Hf; cbn [fold_left] in Hf; [right; exact Hf|].
    destruct (IH _ k u (IMap.add_bst k0 v0 acc Hacc) Hf) as [Hin|Hacc'].
    - left. right. exact Hin.
    - apply (IMap.find_inb k u _ (IMap.add_bst k0 v0 acc Hacc)) in Hacc'.
      apply (IMap.add_inb k0 v0 acc k u Hacc) in Hacc'. destruct Hacc' as [[-> ->]|[_ Hin]].
      + left. left. reflexivity.
      + right. apply (IMap.find_inb k u acc Hacc). exact Hin. }
  intros k u Hf. destruct (G IMap.empty k u I Hf) as [H|H]; [exact H|]. cbn in H. discriminate.
Qed.

Lemma stable_subst : forall N E0 E sg, sg_stable N sg = true -> stable N E0 E -> stable N E0 (subst_env E (mk_subst sg)).
Proof.
  intros N E0 E sg HG HS k Hk. destruct (HS k Hk) as [A B].
  cbn [subst_env ev eg]. unfold svar. destruct (IMap.find k (mk_subst sg)) as [u|] eqn:Hu.
  - assert (Eu : u = VP k wzero).
    { pose proof (proj1 (forallb_forall _ _) HG (k, u) (mk_subst_find_in sg k u Hu)) as Q. cbn [fst snd] in Q.
      apply orb_prop in Q. destruct Q as [Q|Q].
      - apply negb_true_iff in Q. exfalso. assert (Q' : PrimInt63.ltb k N = true) by (apply ltb_spec; exact Hk). rewrite Q' in Q. discriminate Q.
      - destruct u as [|k' o| | | | | | | | |]; try discriminate Q. apply andb_prop in Q as [Q1 Q2].
        apply Uint63.eqb_correct in Q1. apply weqb_eq in Q2. subst. reflexivity. }
    rewrite Eu. rewrite weqb_refl. split; [| exact B]. cbn [den]. rewrite <- A. apply bv_add_0_r. rewrite wbv_unsigned. reflexivity.
  - split; [exact A | exact B].
Qed.

Lemma uses_plain_cut_list : forall ks tid k, In k ks -> uses_plain_cut k tid = true ->
  (fix go (ks : list plan) : bool := match ks with [] => false | k :: ks' => uses_plain_cut k tid || go ks' end) ks = true.
Proof.
  induction ks as [|k0 ks IH]; intros tid k Hin Hk; [destruct Hin|].
  cbn beta iota. destruct Hin as [<-|Hin]; [rewrite Hk; reflexivity|].
  rewrite (IH tid k Hin Hk). apply orb_true_r.
Qed.

Lemma vars_below_mono : forall n n' v, to_Z n <= to_Z n' -> vars_below n v = true -> vars_below n' v = true.
Proof.
  intros n n' v Hle. induction v; cbn [vars_below]; intros H;
    repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end;
    try reflexivity; try (rewrite IHv1, IHv2 by assumption; reflexivity); try (apply IHv; assumption).
  - apply ltb_spec in H. apply (proj2 (ltb_spec _ _)). lia.
  - apply ltb_spec in H. apply (proj2 (ltb_spec _ _)). lia.
Qed.

Lemma find_some_inb : forall A x w (m : IMap.t A), IMap.find x m = Some w -> IMap.inb x w m.
Proof.
  induction m as [|h l IHl k v r IHr]; cbn [IMap.find IMap.inb]; intros H; [discriminate|].
  destruct (PrimInt63.ltb x k) eqn:L1; [left; exact (IHl H)|].
  destruct (PrimInt63.ltb k x) eqn:L2; [right; right; exact (IHr H)|].
  injection H as ->. right; left. split; [|reflexivity].
  apply to_Z_inj. destruct (ltbP x k); [discriminate|]. destruct (ltbP k x); [discriminate|]. lia.
Qed.

Lemma ctx_wfb_cut : forall C tid T, ctx_wfb C = true -> IMap.find tid (c_cuts C) = Some T -> sstate_wfb (t_st T) = true.
Proof.
  intros C tid T W F. unfold ctx_wfb in W. apply andb_prop in W as [W _].
  exact (proj1 (IMap.forallb_inb _ _) W tid T (find_some_inb _ _ _ _ F)).
Qed.

Lemma ctx_wfb_ecall : forall C eid T, ctx_wfb C = true -> IMap.find eid (c_ecalls C) = Some T -> sstate_wfb T = true.
Proof.
  intros C eid T W F. unfold ctx_wfb in W. apply andb_prop in W as [_ W].
  exact (proj1 (IMap.forallb_inb _ _) W eid T (find_some_inb _ _ _ _ F)).
Qed.

Lemma entails_pc : forall st T sg, entails st T sg = true -> s_pc st = s_pc T.
Proof.
  intros st T sg H. unfold entails in H. repeat (apply andb_prop in H; destruct H as [H _]). apply int_eqb_eq'. exact H.
Qed.

Lemma sv_vars_below_eq : forall n v, sv_vars_below n v = vars_below n v.
Proof. intros n v. induction v; cbn [sv_vars_below vars_below]; congruence. Qed.

Definition env_upd (E : env) (n : int) (w : word) : env :=
  Env (fun k => if PrimInt63.eqb k n then w else ev E k) (eb E) (eg E).
Lemma env_upd_ext : forall E n w, env_ext n E (env_upd E n w).
Proof.
  intros E n w. split; [reflexivity|]. intros k Hk. cbn [env_upd ev eg]. split; [|reflexivity].
  destruct (PrimInt63.eqb k n) eqn:Q; [| reflexivity]. apply Uint63.eqb_correct in Q. subst k. lia.
Qed.
Lemma env_upd_same : forall E n w, ev (env_upd E n w) n = w.
Proof. intros. cbn [env_upd ev]. rewrite Uint63.eqb_refl. reflexivity. Qed.

Lemma rf_allb_get : forall A (p : A -> bool) x, rf_allb p x = true -> forall r, p (rf_get x r) = true.
Proof.
  intros A p x H r. unfold rf_allb, rf_to_list in H.
  repeat (apply andb_prop in H; destruct H as [? H]).
  destruct r; cbn [rf_get]; assumption.
Qed.
Lemma forallb_In : forall A (p : A -> bool) l x, forallb p l = true -> In x l -> p x = true.
Proof. intros A p l x H Hx. exact (proj1 (forallb_forall _ _) H x Hx). Qed.
Lemma slot_vars_below_In : forall n s c, slot_vars_below n s = true -> In c s -> sv_vars_below n (c_v c) = true.
Proof.
  induction s as [|c0 s IH]; intros c H Hin; [destruct Hin|]. cbn [slot_vars_below] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [<-|Hin]; [exact H1| exact (IH c H2 Hin)].
Qed.

Section Reval.
Variables (n : int) (E E' : env).
Hypothesis HX : env_ext n E E'.

Lemma den_reval : forall v, sv_vars_below n v = true -> den E' v = den E v.
Proof. intros v Hv. rewrite sv_vars_below_eq in Hv. exact (den_env_ext n E E' v HX Hv). Qed.
Lemma ev_reval : forall k, PrimInt63.ltb k n = true -> ev E' k = ev E k.
Proof. intros k Hk. apply (proj1 (proj2 HX k (proj1 (ltb_spec _ _) Hk))). Qed.
Lemma eg_reval : forall k, PrimInt63.ltb k n = true -> eg E' k = eg E k.
Proof. intros k Hk. apply (proj2 (proj2 HX k (proj1 (ltb_spec _ _) Hk))). Qed.

Lemma fact_holds_reval : forall f, fact_vars_below n f = true -> fact_holds E f -> fact_holds E' f.
Proof.
  intros f Hf H. destruct f; cbn [fact_vars_below] in Hf; cbn [fact_holds] in *;
    try (apply andb_prop in Hf as [Ha Hb]; rewrite (den_reval _ Ha), (den_reval _ Hb); exact H);
    rewrite (ev_reval _ Hf); exact H.
Qed.

Lemma hiZ_reval : forall r, region_vars_below n r = true -> hiZ E' r = hiZ E r.
Proof. intros r Hr. apply andb_prop in Hr as [Hh _]. unfold hiZ. rewrite (den_reval _ Hh). reflexivity. Qed.

Lemma bg_byte_reval : forall k r o, PrimInt63.ltb k n = true -> bg_byte segs E' k r o = bg_byte segs E k r o.
Proof.
  intros k r o Hk. unfold bg_byte. destruct (rg_bg r); try reflexivity.
  - rewrite (eg_reval _ Hk). reflexivity.
  - rewrite (proj1 HX). reflexivity.
Qed.

Lemma region_ok_reval : forall priv m k r,
  PrimInt63.ltb k n = true -> region_vars_below n r = true ->
  region_ok segs priv E m k r -> region_ok segs priv E' m k r.
Proof.
  intros priv m k r Hk Hr HR.
  pose proof (hiZ_reval r Hr) as Hhi. apply andb_prop in Hr as [Hh Hc].
  destruct HR as [Rbst Rrange Rvalid Rcells Rin Rbg].
  assert (Hcv : forall g gr c, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> den E' (c_v c) = den E (c_v c)).
  { intros g gr c Hg Hin. apply den_reval. eapply slot_vars_below_In; [|exact Hin].
    exact (proj1 (IMap.forallb_spec _ _ Rbst) Hc g gr Hg). }
  split.
  - exact Rbst.
  - rewrite (ev_reval _ Hk), Hhi. exact Rrange.
  - rewrite (ev_reval _ Hk), Hhi. exact Rvalid.
  - intros g gr Hg. rewrite (ev_reval _ Hk). destruct (Rcells g gr Hg) as [Hs Hf]. split; [exact Hs|].
    apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hf c Hin) as [H1 [H2 [H3 H4]]].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros i Hi. rewrite (Hcv g gr c Hg Hin). exact (H4 i Hi).
  - rewrite Hhi. exact Rin.
  - intros o H1 H2 H3. rewrite (bg_byte_reval k r o Hk), (ev_reval _ Hk). apply Rbg; [rewrite <- Hhi; exact H1 | exact H2 | exact H3].
Qed.

Lemma regs_reval_find : forall R k r, IMap.bst R ->
  IMap.forallb (fun k r => PrimInt63.ltb k n && region_vars_below n r) R = true -> IMap.find k R = Some r ->
  ev E' k = ev E k /\ hiZ E' r = hiZ E r /\ PrimInt63.ltb k n = true /\ region_vars_below n r = true.
Proof.
  intros R k r B H Hf. pose proof (proj1 (IMap.forallb_spec _ _ B) H k r Hf) as P. apply andb_prop in P as [P1 P2].
  split; [exact (ev_reval _ P1)|]. split; [exact (hiZ_reval _ P2)|]. auto.
Qed.

Theorem st_ok_reval : forall st ms model,
  0 < to_Z n -> st_vars_below n st = true ->
  st_ok segs OPS E st ms model -> st_ok segs OPS E' st ms model.
Proof.
  intros st ms model Hn Hsv HS.
  unfold st_vars_below in Hsv.
  apply andb_prop in Hsv as [Hsv Hops]. apply andb_prop in Hsv as [Hsv Hfs]. apply andb_prop in Hsv as [Hsv HR].
  apply andb_prop in Hsv as [Hsv Hrv]. apply andb_prop in Hsv as [Hrf Hff].
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops' Hapart Hmf Hcov Hminv].
  assert (Hargs : forall o, In o (s_ops st) -> map (den E') (op_args o) = map (den E) (op_args o)).
  { intros o Ho. apply map_ext_in. intros a Ha. apply den_reval.
    exact (forallb_In _ _ _ a (forallb_In _ _ _ o Hops Ho) Ha). }
  split; try assumption.
  - intros r. rewrite (den_reval _ (rf_allb_get _ _ _ Hrf r)). exact (Hregs r).
  - intros r. rewrite (den_reval _ (rf_allb_get _ _ _ Hff r)). exact (Hfregs r).
  - destruct (s_resv st) as [|a|]; cbn [resv_ok resv_vars_below] in *; [exact Hresv| |exact Hresv].
    rewrite (den_reval _ Hrv). exact Hresv.
  - rewrite <- Hz. apply ev_reval. apply (proj2 (ltb_spec _ _)). change (to_Z 0%uint63) with 0. exact Hn.
  - intros k r Hf. destruct (regs_reval_find _ k r Hbst HR Hf) as (_ & _ & Hk & Hr).
    apply region_ok_reval; [exact Hk | exact Hr | exact (Hreg k r Hf)].
  - intros k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 W a.
    destruct (regs_reval_find _ k1 r1 Hbst HR H1) as (-> & -> & _).
    destruct (regs_reval_find _ k2 r2 Hbst HR H2) as (-> & -> & _).
    exact (Hdisj k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 W a).
  - apply Forall_forall. intros f Hf. apply fact_holds_reval; [exact (forallb_In _ _ _ f Hfs Hf)|].
    exact (proj1 (Forall_forall _ _) Hfacts f Hf).
  - unfold ops_hold in *. apply Forall_forall. intros o Ho. rewrite (Hargs o Ho). exact (proj1 (Forall_forall _ _) Hops' o Ho).
  - unfold ops_apart in *. apply Forall_forall. intros o Ho a Ha. rewrite (Hargs o Ho) in Ha.
    destruct (proj1 (Forall_forall _ _) Hapart o Ho a Ha) as [NB PR]. split; [|exact PR].
    intros (k & r & Hf & Hk & Rg). apply NB. exists k, r. destruct (regs_reval_find _ k r Hbst HR Hf) as (E1 & E2 & _ & _).
    rewrite E1, E2 in Rg. auto.
  -
    apply (cover_transfer segs OPS E E' (s_regs st) (s_regs st) (s_ops st) (s_ops st)); [| | exact Hcov].
    + apply fx_acc_based. intros a (k & r & Hf & Hk & Rg). exists k, r.
      destruct (regs_reval_find _ k r Hbst HR Hf) as (E1 & E2 & _ & _). rewrite E1, E2 in Rg. auto.
    + intros o Ho. unfold insts in *. apply in_map_iff in Ho as (so & <- & Hso). apply in_map_iff. exists so.
      split; [| exact Hso]. rewrite (Hargs so Hso). reflexivity.
Qed.
End Reval.

Section CheckEqs.
Variable C : ctx.
Lemma check_PFail_eq : forall msg st, check segs C (PFail msg) st = (if PrimInt63.eqb msg DEAD && facts_dead (s_facts st) then Some [] else None).
Proof. reflexivity. Qed.
Lemma check_PRun_eq : forall stops k st, check segs C (PRun stops k) st =
  match run segs (c_itab C) stops st with
  | SStop KStopPc st' => check segs C k st'
  | SStop KEcall st' => check segs C k st'
  | SStop (KBranch _ _ _ _) st' => check segs C k st'
  | _ => None
  end.
Proof. reflexivity. Qed.
Lemma check_PCase_eq : forall kT kF st, check segs C (PCase kT kF) st =
  if PrimInt63.ltb (s_pc st) bit62i then
      match IMap.find (s_pc st) (c_itab C) with
      | Some (IBranch c rs1 rs2 off) =>
          let a := getr st rs1 in let b := getr st rs2 in
          match take_branch c a b off true st, take_branch c a b off false st with
          | Some stT, Some stF =>
              match check segs C kT stT, check segs C kF stF with
              | Some o1, Some o2 => Some (o1 ++ o2)
              | _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  else None.
Proof. reflexivity. Qed.
Lemma check_PSplit_eq : forall r n ks st, check segs C (PSplit r n ks) st =
  let v := getr st r in
  match decide_ltu_t (s_facts st) v (VL (wlit n)) with
  | Some true =>
      if Nat.eqb (length ks) (Z.to_nat (to_Z n)) then
        (fix go (ks : list plan) (i : int) : option (list obligation) :=
           match ks with
           | [] => Some []
           | k :: ks' =>
               match check segs C k (addfact (setr st r (VL (wlit i))) (FEq v (VL (wlit i)))), go ks' (PrimInt63.add i 1%uint63) with
               | Some o1, Some o2 => Some (o1 ++ o2)
               | _, _ => None
               end
           end) ks 0%uint63
      else None
  | _ => None
  end.
Proof. reflexivity. Qed.
Lemma check_PSetReg_eq : forall r v k st, check segs C (PSetReg r v k) st =
  match r, decide_eq_t (s_facts st) (getr st r) v with
  | X0, _ => None
  | _, Some true => check segs C k (setr st r v)
  | _, _ => None
  end.
Proof. reflexivity. Qed.
Lemma check_PSubst_eq : forall x u k st, check segs C (PSubst x u k) st =
  if negb (PrimInt63.eqb x 0%uint63)
     && match IMap.find x (s_regs st) with Some _ => false | None => true end
     && match decide_eq_t (s_facts st) (VP x wzero) u with Some true => true | _ => false end
  then
    let f := vsubst x u in
    check segs C k (SS (s_pc st) (rf_map f (s_rf st)) (rf_map f (s_ff st))
                     (match s_resv st with RAddr a => RAddr (f a) | rv => rv end)
                     (IMap.map (region_map f) (s_regs st)) (List.map (fact_map f) (s_facts st))
                     (List.map (op_map f) (s_ops st)) (s_priv st) (s_next st))
  else None.
Proof. reflexivity. Qed.
Lemma check_PName_eq : forall r k st, check segs C (PName r k) st =
  let n := s_next st in
  match r with
  | X0 => None
  | _ =>
      if st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n bit62i then
        check segs C k (SS (s_pc st) (rf_set (s_rf st) r (VP n wzero)) (s_ff st) (s_resv st) (s_regs st)
                        (FEq (VP n wzero) (getr st r) :: s_facts st) (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63))
      else None
  end.
Proof. reflexivity. Qed.
Lemma check_PSetHi_eq : forall rk v k st, check segs C (PSetHi rk v k) st =
  if PrimInt63.eqb rk 0%uint63 then None else
  match IMap.find rk (s_regs st) with
  | Some r =>
      match decide_eq_t (s_facts st) (rg_hi r) v with
      | Some true => check segs C k (setregs st (IMap.add rk (Region (rg_lo r) v (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)))
      | _ => None
      end
  | None => None
  end.
Proof. reflexivity. Qed.
Lemma check_PAssume_eq : forall f k st, check segs C (PAssume f k) st =
  if implied_t (s_facts st) f then check segs C k (addfact st f)
  else
  match check segs C k (addfact st f) with
  | Some o => Some ((s_facts st, f) :: o)
  | None => None
  end.
Proof. reflexivity. Qed.
Lemma check_PCall_eq : forall cid ks st, check segs C (PCall cid ks) st =
  match IMap.find cid (c_contracts C) with
  | Some ct =>
      if PrimInt63.eqb (s_pc st) (c_pc ct) then
        match c_apply ct st with
        | Some sts =>
            (fix go (ks : list plan) (sts : list sstate) : option (list obligation) :=
               match ks, sts with
               | [], [] => Some []
               | k :: ks', st' :: sts' =>
                   if PrimInt63.leb (s_next st) (s_next st') then
                     match check segs C k st', go ks' sts' with
                     | Some o1, Some o2 => Some (o1 ++ o2)
                     | _, _ => None
                     end
                   else None
               | _, _ => None
               end) ks sts
        | None => None
        end
      else None
  | None => None
  end.
Proof. reflexivity. Qed.
Lemma check_PCut_eq : forall tid sg st, check segs C (PCut tid sg) st =
  match IMap.find tid (c_cuts C) with
  | Some T => if entails st (t_st T) (mk_subst sg) then Some [] else None
  | None => None
  end.
Proof. reflexivity. Qed.
Lemma check_PCutDec_eq : forall tid sg st, check segs C (PCutDec tid sg) st =
  match IMap.find tid (c_cuts C) with
  | Some T =>
      let s := mk_subst sg in
      if entails st (t_st T) s then
        match sapply s (t_measure T) with
        | Some m => match decide_ltu_t (s_facts st) m (c_mroot C) with
                    | Some true => Some []
                    | _ => None
                    end
        | None => None
        end
      else None
  | None => None
  end.
Proof. reflexivity. Qed.
Lemma check_PEcall_eq : forall eid sg st, check segs C (PEcall eid sg) st =
  match IMap.find (s_pc st) (c_itab C), IMap.find eid (c_ecalls C) with
  | Some IEcall, Some T => if entails st T (mk_subst sg) then Some [] else None
  | _, _ => None
  end.
Proof. reflexivity. Qed.
Lemma check_PForget_eq : forall k glo ghi kk st, check segs C (PForget k glo ghi kk) st =
  match IMap.find k (s_regs st) with
  | Some r => check segs C kk (setregs st (IMap.add k (Mem.region_forget r glo ghi) (s_regs st)))
  | None => None
  end.
Proof. reflexivity. Qed.
Lemma check_PDropFacts_eq : forall keep k st, check segs C (PDropFacts keep k) st =
  check segs C k (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (firstn keep (s_facts st))
                    (s_ops st) (s_priv st) (s_next st)).
Proof. reflexivity. Qed.
End CheckEqs.

Section CheckSound.
Variables (N : int) (C : ctx) (MP : Model -> Prop) (PB : (int -> list byte) -> Prop) (K : TSet) (E0 : env).
Hypothesis WFC : ctx_wfb C = true.
Hypothesis HIT : itab_ok segs (c_itab C).
Hypothesis HCT : contracts_ok C MP PB.

Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma asteps_MP : forall ms mo ms' mo', asteps segs ms mo ms' mo' -> MP mo -> MP mo'.
Proof.
  intros ms mo ms' mo' H. induction H as [|ms mo ms1 mo1 ms2 mo2 Hsvc Hstep Hms IH]; intros HM; [exact HM|].
  apply IH. unfold Run.mi_account_step in Hstep.
  destruct (step_accesses segs ms) as [report| |]; try discriminate.
  destruct (materialize_model_accesses mo (@accessed_ranges _ report)) as [mo0|] eqn:M; [|discriminate].
  injection Hstep as _ <-. exact (HMPA mo _ mo0 HM M).
Qed.

Definition GOAL (p : plan) : Prop := forall st obls E ms model,
  check segs C p st = Some obls -> obls_hold PB obls ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  eb E = eb E0 -> den E (c_mroot C) = den E0 (c_mroot C) -> vars_below (s_next st) (c_mroot C) = true ->
  plan_stable N p = true -> to_Z N <= to_Z (s_next st) -> stable N E0 E ->
  leaves_ok_st N C p MP K E0 (bv_unsigned (den E0 (c_mroot C))) ->
  realizes segs (mkCfg ms model) K.

Lemma obls_app : forall o1 o2, obls_hold PB (o1 ++ o2) -> obls_hold PB o1 /\ obls_hold PB o2.
Proof. intros o1 o2 H. unfold obls_hold in *. apply Forall_app in H. exact H. Qed.

Lemma goal_PRun : forall stops k, GOAL k -> GOAL (PRun stops k).
Proof.
  intros stops k IH st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PRun_eq in Hc.
  destruct (run segs (c_itab C) stops st) as [s0|why st1] eqn:Hr; [discriminate|].
  pose proof (run_sound segs OPS E st ms model (c_itab C) stops why st1 HIT HS Hr) as (ms1 & mo1 & Hms & HS1).
  pose proof (run_next (c_itab C) stops st why st1 Hr) as Hn.
  assert (R : check segs C k st1 = Some obls -> realizes segs (mkCfg ms model) K).
  { intros Hc'. apply (rz_asteps segs ms model ms1 mo1 K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) Hms).
    apply (IH st1 obls E ms1 mo1 Hc' Ho HS1 (asteps_MP _ _ _ _ Hms HMP) HPB Heb Hm); [rewrite Hn; exact Hv| exact HP | rewrite Hn; exact HN | exact HST |].
    eapply leaves_mono_st; [|exact HL]. intros tid Hu. exact Hu. }
  destruct why; try discriminate Hc; exact (R Hc).
Qed.

Lemma use_IH : forall k p st' obls E ms' model,
  GOAL k ->
  (forall tid, uses_plain_cut k tid = true -> uses_plain_cut p tid = true) ->
  leaves_ok_st N C p MP K E0 (bv_unsigned (den E0 (c_mroot C))) ->
  check segs C k st' = Some obls -> obls_hold PB obls ->
  st_ok segs OPS E st' ms' model -> MP model -> PB (eb E) -> eb E = eb E0 ->
  den E (c_mroot C) = den E0 (c_mroot C) -> vars_below (s_next st') (c_mroot C) = true ->
  plan_stable N k = true -> to_Z N <= to_Z (s_next st') -> stable N E0 E ->
  realizes segs (mkCfg ms' model) K.
Proof.
  intros k p st' obls E ms' model IH Hmono HL Hc Ho HS HMP HPB Heb Hm Hv HP HN HST.
  exact (IH st' obls E ms' model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST (leaves_mono_st N C p k MP K E0 _ Hmono HL)).
Qed.

Lemma goal_PFail : forall msg, GOAL (PFail msg).
Proof.
  intros msg st obls E ms model Hc Ho HS. rewrite check_PFail_eq in Hc.
  destruct (PrimInt63.eqb msg DEAD && facts_dead (s_facts st)) eqn:D; [|discriminate Hc].
  apply andb_prop in D as [_ D]. exfalso. exact (facts_dead_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) D).
Qed.

Lemma goal_PCase : forall kT kF, GOAL kT -> GOAL kF -> GOAL (PCase kT kF).
Proof.
  intros kT kF IHT IHF st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PCase_eq in Hc.
  destruct (PrimInt63.ltb (s_pc st) bit62i) eqn:Hpc; [|discriminate Hc].
  destruct (IMap.find (s_pc st) (c_itab C)) as [fi|] eqn:Hfind; [|discriminate Hc].
  destruct fi; try discriminate Hc. cbv zeta in Hc.
  destruct (take_branch c (getr st rs1) (getr st rs2) off true st) as [stT|] eqn:HT; [|discriminate Hc].
  destruct (take_branch c (getr st rs1) (getr st rs2) off false st) as [stF|] eqn:HF; [|discriminate Hc].
  destruct (check segs C kT stT) as [o1|] eqn:C1; [|discriminate Hc].
  destruct (check segs C kF stF) as [o2|] eqn:C2; [|discriminate Hc].
  injection Hc as <-. destruct (obls_app o1 o2 Ho) as [Ho1 Ho2].
  pose proof (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) as MH.
  destruct (branch_taken c (den E (getr st rs1)) (den E (getr st rs2))) eqn:BT.
  - destruct (take_branch_sound E st ms model (c_itab C) c rs1 rs2 off true stT HIT HS Hpc Hfind BT HT) as (ms' & Hstep & HS').
    apply (rz_astep segs ms model ms' model K MH (so_svc _ _ _ _ _ _ HS) Hstep).
    refine (use_IH kT _ stT o1 E ms' model IHT _ HL C1 Ho1 HS' HMP HPB Heb Hm _ _ _ _).
    + intros tid Hu. cbn [uses_plain_cut]. rewrite Hu. reflexivity.
    + rewrite (take_branch_next _ _ _ _ _ _ _ HT). exact Hv.
    + cbn [plan_stable] in HP. apply andb_prop in HP as [HP1 HP2]. exact HP1.
    + rewrite (take_branch_next _ _ _ _ _ _ _ HT). exact HN.
    + exact HST.
  - destruct (take_branch_sound E st ms model (c_itab C) c rs1 rs2 off false stF HIT HS Hpc Hfind BT HF) as (ms' & Hstep & HS').
    apply (rz_astep segs ms model ms' model K MH (so_svc _ _ _ _ _ _ HS) Hstep).
    refine (use_IH kF _ stF o2 E ms' model IHF _ HL C2 Ho2 HS' HMP HPB Heb Hm _ _ _ _).
    + intros tid Hu. cbn [uses_plain_cut]. rewrite Hu. apply orb_true_r.
    + rewrite (take_branch_next _ _ _ _ _ _ _ HF). exact Hv.
    + cbn [plan_stable] in HP. apply andb_prop in HP as [HP1 HP2]. exact HP2.
    + rewrite (take_branch_next _ _ _ _ _ _ _ HF). exact HN.
    + exact HST.
Qed.

Lemma goal_PSplit : forall r n ks, Forall GOAL ks -> GOAL (PSplit r n ks).
Proof.
  intros r n ks IHs st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PSplit_eq in Hc. cbv zeta in Hc.
  destruct (decide_ltu_t (s_facts st) (getr st r) (VL (wlit n))) as [[|]|] eqn:D; try discriminate Hc.
  destruct (Nat.eqb (length ks) (Z.to_nat (to_Z n))) eqn:Hlen; [|discriminate Hc]. apply Nat.eqb_eq in Hlen.
  match type of Hc with ?g ks 0%uint63 = Some obls => set (go := g) in Hc end.
  assert (GO : forall ks' i os, go ks' i = Some os -> obls_hold PB os -> to_Z i + Z.of_nat (length ks') < two63 ->
            forall j k, nth_error ks' j = Some k ->
            exists i' o, to_Z i' = to_Z i + Z.of_nat j /\
                         check segs C k (addfact (setr st r (VL (wlit i'))) (FEq (getr st r) (VL (wlit i')))) = Some o /\
                         obls_hold PB o).
  { induction ks' as [|k0 ks' IH]; intros i os Hg Hos Hb j k Hj; [destruct j; discriminate Hj|].
    cbn beta iota delta [go] in Hg. fold go in Hg.
    destruct (check segs C k0 _) as [o1|] eqn:C1; [|discriminate Hg].
    destruct (go ks' (PrimInt63.add i 1)) as [o2|] eqn:G2; [|discriminate Hg]. injection Hg as <-.
    destruct (obls_app o1 o2 Hos) as [Ho1 Ho2]. cbn [length] in Hb.
    assert (Hi1 : to_Z (PrimInt63.add i 1) = to_Z i + 1).
    { rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. rewrite wB_two63. pose proof (int_range i). lia. }
    destruct j as [|j].
    - cbn [nth_error] in Hj. injection Hj as <-. exists i, o1. split; [lia|]. split; [exact C1| exact Ho1].
    - cbn [nth_error] in Hj. destruct (IH _ o2 G2 Ho2 ltac:(rewrite Hi1; lia) j k Hj) as (i' & o & Ei & Ck & Hok).
      exists i', o. split; [rewrite Hi1 in Ei; lia|]. split; [exact Ck| exact Hok]. }
  pose proof (decide_ltu_t_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ _ D) as LT.
  apply (proj1 (ltu_iff _ _ true)) in LT. cbn [den] in LT. rewrite wbv_unsigned, wlit_ok in LT.
  pose proof (bv_unsigned_in_range _ (den E (getr st r))) as [R0 _].
  set (jz := bv_unsigned (den E (getr st r))) in *.
  destruct (nth_error ks (Z.to_nat jz)) as [k|] eqn:Hk.
  2:{ apply nth_error_None in Hk. rewrite Hlen in Hk. exfalso. apply Z2Nat.inj_le in Hk; lia. }
  pose proof (int_range n) as Rn.
  destruct (GO ks 0%uint63 obls Hc Ho ltac:(change (to_Z 0%uint63) with 0; rewrite Hlen, Z2Nat.id; lia) _ k Hk)
    as (i' & o & Ei & Ck & Hok).
  change (to_Z 0%uint63) with 0 in Ei. rewrite Z2Nat.id in Ei by lia.
  refine (use_IH k _ _ o E ms model (proj1 (Forall_forall _ _) IHs k (nth_error_In _ _ Hk)) _ HL Ck Hok _ HMP HPB Heb Hm _ _ _ _).
  - intros tid Hu. cbn [uses_plain_cut]. exact (uses_plain_cut_list ks tid k (nth_error_In _ _ Hk) Hu).
  - apply split_child_sound; [exact HS| lia].
  - cbn [s_next addfact]. rewrite s_next_setr. exact Hv.
  - cbn [plan_stable] in HP. fold (plan_stable N) in HP. exact (plan_stable_list N ks k HP (nth_error_In _ _ Hk)).
  - cbn [s_next addfact]. rewrite s_next_setr. exact HN.
  - exact HST.
Qed.

Lemma goal_PSetReg : forall r v k, GOAL k -> GOAL (PSetReg r v k).
Proof.
  intros r v k IH st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PSetReg_eq in Hc.
  assert (H : r <> X0 /\ decide_eq_t (s_facts st) (getr st r) v = Some true /\ check segs C k (setr st r v) = Some obls).
  { destruct r; [discriminate Hc|..]; destruct (decide_eq_t (s_facts st) _ v) as [[|]|]; try discriminate Hc;
    (split; [discriminate| split; [reflexivity| exact Hc]]). }
  clear Hc. destruct H as (Hr & D & Hc).
  pose proof (decide_eq_t_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ _ D) as EQ. apply (proj1 (eqb_iff _ _ true)) in EQ.
  refine (use_IH k _ _ obls E ms model IH _ HL Hc Ho _ HMP HPB Heb Hm _ _ _ _).
  - intros tid Hu. exact Hu.
  - apply setreg_sound; assumption.
  - rewrite s_next_setr. exact Hv.
  - exact HP.
  - rewrite s_next_setr. exact HN.
  - exact HST.
Qed.

Lemma goal_PSubst : forall x u k, GOAL k -> GOAL (PSubst x u k).
Proof.
  intros x u k IH st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PSubst_eq in Hc.
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate Hc] end.
  apply andb_prop in COND as [_ D].
  destruct (decide_eq_t (s_facts st) (VP x wzero) u) as [[|]|] eqn:D'; try discriminate D.
  pose proof (decide_eq_t_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ _ D') as EQ. apply (proj1 (eqb_iff _ _ true)) in EQ.
  cbv zeta in Hc.
  refine (use_IH k _ _ obls E ms model IH _ HL Hc Ho _ HMP HPB Heb Hm _ _ _ _).
  - intros tid Hu. exact Hu.
  - apply psubst_sound; assumption.
  - exact Hv.
  - exact HP.
  - exact HN.
  - exact HST.
Qed.

Lemma goal_PName : forall r k, GOAL k -> GOAL (PName r k).
Proof.
  intros r k IH st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PName_eq in Hc. cbv zeta in Hc.
  assert (H : r <> X0 /\ st_vars_below (s_next st) st = true /\ PrimInt63.ltb 0%uint63 (s_next st) = true /\ PrimInt63.ltb (s_next st) bit62i = true /\
              check segs C k (SS (s_pc st) (rf_set (s_rf st) r (VP (s_next st) wzero)) (s_ff st) (s_resv st) (s_regs st)
                        (FEq (VP (s_next st) wzero) (getr st r) :: s_facts st) (s_ops st) (s_priv st) (PrimInt63.add (s_next st) 1%uint63))
              = Some obls).
  { destruct r; [discriminate Hc|..];
    (destruct (st_vars_below (s_next st) st && PrimInt63.ltb 0%uint63 (s_next st) && PrimInt63.ltb (s_next st) bit62i) eqn:C0; [|discriminate Hc]);
    apply andb_prop in C0 as [C0 C2]; apply andb_prop in C0 as [C1 C3];
    (split; [discriminate| split; [exact C1| split; [exact C3| split; [exact C2| exact Hc]]]]). }
  clear Hc. destruct H as (Hr & SVB & POS & LT & Hc).
  set (n := s_next st) in *.
  set (E' := env_upd E n (den E (getr st r))).
  pose proof (env_upd_ext E n (den E (getr st r))) as EXT.
  assert (HS1 : st_ok segs OPS E' st ms model).
  { apply (st_ok_reval n E E' EXT st ms model); [| exact SVB| exact HS].
    apply ltb_spec in POS. change (to_Z 0%uint63) with 0 in POS. exact POS. }
  refine (use_IH k _ _ obls E' ms model IH _ HL Hc Ho _ HMP _ _ _ _ _ _ _).
  - intros tid Hu. exact Hu.
  -
    assert (Hx : r5_eqb r X0 = false) by (destruct (r5_eqb r X0) eqn:Q; [apply r5_eqb_spec in Q; contradiction| reflexivity]).
    assert (DV : den E' (getr st r) = den E' (VP n wzero)).
    { rewrite (den_env_ext n E E' (getr st r) EXT).
      2:{ unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB; destruct SVB as [SVB ?]).
          pose proof (rf_allb_get _ _ _ SVB r) as G. rewrite sv_vars_below_eq in G. exact G. }
      cbn [den]. subst E'. rewrite env_upd_same. symmetry. apply bv_add_0_r. rewrite wbv_unsigned. reflexivity. }
    pose proof (setreg_sound E' st ms model r (VP n wzero) HS1 Hr DV) as HS2. rewrite (setr_eq st r _ Hx) in HS2.
    pose proof (addfact_sound E' _ ms model (FEq (VP n wzero) (getr st r)) HS2 ltac:(cbn [fact_holds]; symmetry; exact DV)) as HS3.
    destruct HS3 as [Qpc Qx0 Qregs Qfregs Qsvc Qresv Qfcsr Qrom Qz Qbst Qreg Qdisj Qpub Qfacts Qops Qapart Qmf Qcov Qminv].
    constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next addfact] in *; assumption.
  - subst E'. cbn [env_upd eb]. exact HPB.
  - subst E'. cbn [env_upd eb]. exact Heb.
  - rewrite (den_env_ext n E E' (c_mroot C) EXT Hv). exact Hm.
  - cbn [s_next]. apply (vars_below_mono n); [| exact Hv]. rewrite add_spec. change (to_Z 1%uint63) with 1.
    apply ltb_spec in LT. rewrite to_Z_bit62i in LT. rewrite Z.mod_small by (rewrite wB_two63, two63_eq; pose proof (int_range n); lia). lia.
  - exact HP.
  - cbn [s_next]. rewrite add_spec. change (to_Z 1%uint63) with 1.
    apply ltb_spec in LT. rewrite to_Z_bit62i in LT. rewrite Z.mod_small by (rewrite wB_two63, two63_eq; pose proof (int_range n); lia). subst n. lia.
  - exact (stable_ext N E0 E E' n EXT ltac:(subst n; exact HN) HST).
Qed.

Lemma goal_PSetHi : forall rk v k, GOAL k -> GOAL (PSetHi rk v k).
Proof.
  intros rk v k IH st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PSetHi_eq in Hc.
  destruct (PrimInt63.eqb rk 0%uint63) eqn:K0; [discriminate Hc|].
  destruct (IMap.find rk (s_regs st)) as [r|] eqn:Hr; [|discriminate Hc].
  destruct (decide_eq_t (s_facts st) (rg_hi r) v) as [[|]|] eqn:D; try discriminate Hc.
  refine (use_IH k _ _ obls E ms model IH _ HL Hc Ho _ HMP HPB Heb Hm _ _ _ _).
  - intros tid Hu. exact Hu.
  - apply sethi_sound; [exact HS| exact Hr| exact K0|].
    pose proof (decide_eq_t_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ _ D) as X.
    apply (proj1 (eqb_iff _ _ true)) in X. exact X.
  - exact Hv.
  - exact HP.
  - exact HN.
  - exact HST.
Qed.

Lemma goal_PAssume : forall f k, GOAL k -> GOAL (PAssume f k).
Proof.
  intros f k IH st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PAssume_eq in Hc.
  destruct (implied_t (s_facts st) f) eqn:IM.
  { refine (use_IH k _ _ obls E ms model IH _ HL Hc Ho _ HMP HPB Heb Hm _ _ _ _).
    - intros tid Hu. exact Hu.
    - apply addfact_sound; [exact HS|].
      exact (implied_t_sound E (s_facts st) f (so_zero _ _ _ _ _ _ HS) (so_facts _ _ _ _ _ _ HS) IM).
    - exact Hv.
    - exact HP.
    - exact HN.
    - exact HST. }
  destruct (check segs C k (addfact st f)) as [o|] eqn:Ck; [|discriminate Hc]. injection Hc as <-.
  inversion Ho as [|o0 os Ho0 Hos]; subst.
  refine (use_IH k _ _ o E ms model IH _ HL Ck Hos _ HMP HPB Heb Hm _ _ _ _).
  - intros tid Hu. exact Hu.
  - apply addfact_sound; [exact HS|]. apply (Ho0 E HPB (so_zero _ _ _ _ _ _ HS) (so_facts _ _ _ _ _ _ HS)).
  - exact Hv.
  - exact HP.
  - exact HN.
  - exact HST.
Qed.

Lemma goal_PCall : forall cid ks, Forall GOAL ks -> GOAL (PCall cid ks).
Proof.
  intros cid ks IHs st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PCall_eq in Hc.
  destruct (IMap.find cid (c_contracts C)) as [ct|] eqn:Hct; [|discriminate Hc].
  destruct (PrimInt63.eqb (s_pc st) (c_pc ct)) eqn:Hpc; [|discriminate Hc]. apply int_eqb_eq' in Hpc.
  destruct (c_apply ct st) as [sts|] eqn:Happ; [|discriminate Hc].
  match type of Hc with ?g ks sts = Some obls => set (go := g) in Hc end.
  assert (GO : forall ks' sts' os, go ks' sts' = Some os -> obls_hold PB os ->
            forall st', In st' sts' -> exists k o, In k ks' /\ to_Z (s_next st) <= to_Z (s_next st') /\
                                                   check segs C k st' = Some o /\ obls_hold PB o).
  { induction ks' as [|k0 ks' IH]; intros [|s0 sts'] os Hg Hos st' Hin; cbn beta iota delta [go] in Hg; fold go in Hg;
      try discriminate Hg; [destruct Hin|].
    destruct (PrimInt63.leb (s_next st) (s_next s0)) eqn:LE; [|discriminate Hg]. apply leb_spec in LE.
    destruct (check segs C k0 s0) as [o1|] eqn:C1; [|discriminate Hg].
    destruct (go ks' sts') as [o2|] eqn:G2; [|discriminate Hg]. injection Hg as <-.
    destruct (obls_app o1 o2 Hos) as [Ho1 Ho2].
    destruct Hin as [<-|Hin].
    - exists k0, o1. split; [left; reflexivity|]. auto.
    - destruct (IH sts' o2 G2 Ho2 st' Hin) as (k & o & Hk & R). exists k, o. split; [right; exact Hk| exact R]. }
  apply (HCT cid ct Hct st sts Hpc Happ K E ms model HS HMP HPB).
  intros st' Hin E' ms' model' Hext HMP' HS'.
  destruct (GO ks sts obls Hc Ho st' Hin) as (k & o & Hk & LE & Ck & Hok).
  pose proof Hext as [Heb' _].
  refine (use_IH k _ st' o E' ms' model' (proj1 (Forall_forall _ _) IHs k Hk) _ HL Ck Hok HS' HMP' _ _ _ _ _ _ _).
  - intros tid Hu. cbn [uses_plain_cut]. exact (uses_plain_cut_list ks tid k Hk Hu).
  - rewrite Heb'. exact HPB.
  - rewrite Heb'. exact Heb.
  - rewrite (den_env_ext (s_next st) E E' (c_mroot C) Hext Hv). exact Hm.
  - exact (vars_below_mono _ _ _ LE Hv).
  - cbn [plan_stable] in HP. fold (plan_stable N) in HP. exact (plan_stable_list N ks k HP Hk).
  - lia.
  - exact (stable_ext N E0 E E' (s_next st) Hext HN HST).
Qed.

Lemma goal_PCut : forall tid sg, GOAL (PCut tid sg).
Proof.
  intros tid sg st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PCut_eq in Hc.
  destruct (IMap.find tid (c_cuts C)) as [T|] eqn:HT; [|discriminate Hc].
  destruct (entails st (t_st T) (mk_subst sg)) eqn:EN; [|discriminate Hc].
  destruct HL as [HLc _].
  apply (HLc tid T HT (subst_env E (mk_subst sg)) ms model).
  - rewrite subst_env_eb. exact Heb.
  - apply stable_subst; [exact HP | exact HST].
  - exact HMP.
  - exact (entails_sound E st (t_st T) (mk_subst sg) ms model (ctx_wfb_cut C tid T WFC HT) EN HS).
  - left. cbn [uses_plain_cut]. apply Uint63.eqb_refl.
Qed.

Lemma goal_PCutDec : forall tid sg, GOAL (PCutDec tid sg).
Proof.
  intros tid sg st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PCutDec_eq in Hc.
  destruct (IMap.find tid (c_cuts C)) as [T|] eqn:HT; [|discriminate Hc]. cbv zeta in Hc.
  destruct (entails st (t_st T) (mk_subst sg)) eqn:EN; [|discriminate Hc].
  destruct (sapply (mk_subst sg) (t_measure T)) as [m|] eqn:SM; [|discriminate Hc].
  destruct (decide_ltu_t (s_facts st) m (c_mroot C)) as [[|]|] eqn:D; try discriminate Hc.
  destruct HL as [HLc _].
  apply (HLc tid T HT (subst_env E (mk_subst sg)) ms model).
  - rewrite subst_env_eb. exact Heb.
  - apply stable_subst; [exact HP | exact HST].
  - exact HMP.
  - exact (entails_sound E st (t_st T) (mk_subst sg) ms model (ctx_wfb_cut C tid T WFC HT) EN HS).
  - right. pose proof (decide_ltu_t_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ _ D) as LT.
    apply (proj1 (ltu_iff _ _ true)) in LT. rewrite <- Hm, <- (sapply_sound E (mk_subst sg) (t_measure T) m SM). exact LT.
Qed.

Lemma goal_PEcall : forall eid sg, GOAL (PEcall eid sg).
Proof.
  intros eid sg st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PEcall_eq in Hc.
  destruct (IMap.find (s_pc st) (c_itab C)) as [fi|] eqn:Hfi; [|discriminate Hc].
  destruct fi; try discriminate Hc.
  destruct (IMap.find eid (c_ecalls C)) as [T|] eqn:HT; [|discriminate Hc].
  destruct (entails st T (mk_subst sg)) eqn:EN; [|discriminate Hc].
  destruct HL as [_ HLe].
  apply (HLe eid T HT (subst_env E (mk_subst sg)) ms model).
  - rewrite subst_env_eb. exact Heb.
  - apply stable_subst; [exact HP | exact HST].
  - exact HMP.
  - exact (entails_sound E st T (mk_subst sg) ms model (ctx_wfb_ecall C eid T WFC HT) EN HS).
  - rewrite <- (entails_pc st T (mk_subst sg) EN). exact (itab_ecall_at (c_itab C) (s_pc st) HIT Hfi).
Qed.

Lemma goal_PForget : forall k glo ghi kk, GOAL kk -> GOAL (PForget k glo ghi kk).
Proof.
  intros k glo ghi kk IH st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PForget_eq in Hc.
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate Hc].
  refine (use_IH kk _ _ obls E ms model IH _ HL Hc Ho _ HMP HPB Heb Hm _ _ _ _).
  - intros tid Hu. exact Hu.
  - apply forget_sound; assumption.
  - exact Hv.
  - exact HP.
  - exact HN.
  - exact HST.
Qed.

Lemma goal_PDropFacts : forall keep k, GOAL k -> GOAL (PDropFacts keep k).
Proof.
  intros keep k IH st obls E ms model Hc Ho HS HMP HPB Heb Hm Hv HP HN HST HL.
  rewrite check_PDropFacts_eq in Hc.
  refine (use_IH k _ _ obls E ms model IH _ HL Hc Ho _ HMP HPB Heb Hm _ _ _ _).
  - intros tid Hu. exact Hu.
  - apply dropfacts_sound; assumption.
  - exact Hv.
  - exact HP.
  - exact HN.
  - exact HST.
Qed.

Lemma goal_all : forall p, GOAL p.
Proof.
  apply plan_ind2.
  - exact goal_PRun. - exact goal_PCase. - exact goal_PSplit. - exact goal_PSetReg. - exact goal_PSubst. - exact goal_PName.
  - exact goal_PSetHi.
  - exact goal_PAssume. - exact goal_PCall. - exact goal_PCut. - exact goal_PCutDec. - exact goal_PEcall.
  - exact goal_PForget. - exact goal_PDropFacts. - exact goal_PFail.
Qed.

End CheckSound.

Theorem check_sound_stable : forall (N : int) (C : ctx) (MP : Model -> Prop) (PB : (int -> list byte) -> Prop)
                             (p : plan) (st : sstate) (obls : list obligation),
  ctx_wfb C = true ->
  itab_ok segs (c_itab C) ->
  contracts_ok C MP PB ->
  (forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo') ->
  check segs C p st = Some obls ->
  obls_hold PB obls ->
  vars_below (s_next st) (c_mroot C) = true ->
  plan_stable N p = true ->
  to_Z N <= to_Z (s_next st) ->
  forall (K : TSet) E ms model,
    st_ok segs OPS E st ms model ->
    PB (eb E) ->
    MP model ->
    leaves_ok_st N C p MP K E (bv_unsigned (den E (c_mroot C))) ->
    realizes segs (mkCfg ms model) K.
Proof.
  intros N C MP PB p st obls WFC HIT HCT HMPA Hc Ho Hv HP HN K E ms model HS HPB HMP HL.
  exact (goal_all N C MP PB K E WFC HIT HCT HMPA p st obls E ms model Hc Ho HS HMP HPB eq_refl eq_refl Hv HP HN (stable_refl N E) HL).
Qed.

Theorem check_sound : forall (C : ctx) (MP : Model -> Prop) (PB : (int -> list byte) -> Prop)
                             (p : plan) (st : sstate) (obls : list obligation),
  ctx_wfb C = true ->
  itab_ok segs (c_itab C) ->
  contracts_ok C MP PB ->
  (forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo') ->
  check segs C p st = Some obls ->
  obls_hold PB obls ->
  vars_below (s_next st) (c_mroot C) = true ->
  forall (K : TSet) E ms model,
    st_ok segs OPS E st ms model ->
    PB (eb E) ->
    MP model ->
    leaves_ok C p MP K E (bv_unsigned (den E (c_mroot C))) ->
    realizes segs (mkCfg ms model) K.
Proof.
  intros C MP PB p st obls WFC HIT HCT HMPA Hc Ho Hv K E ms model HS HPB HMP HL.
  refine (check_sound_stable 0%uint63 C MP PB p st obls WFC HIT HCT HMPA Hc Ho Hv (plan_stable_0 p) _ K E ms model HS HPB HMP _).
  - pose proof (int_range (s_next st)). change (to_Z 0%uint63) with 0. lia.
  - apply leaves_ok_st_of. exact HL.
Qed.

End WithSegs.
End PlanS.
