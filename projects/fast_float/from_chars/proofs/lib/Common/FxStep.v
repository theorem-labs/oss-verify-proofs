(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxFold FxRgs FxFacts FxImg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Notation "a &&& b" := (if a then b else false) (at level 40, left associativity).
Local Notation "a ||| b" := (if a then true else b) (at level 50, left associativity).

(* [comment removed for export] *)
Inductive isteps (segs : list Segment) : machine_state -> machine_state -> Prop :=
| ist_refl : forall ms, isteps segs ms ms
| ist_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    isteps segs ms' ms'' ->
    isteps segs ms ms''.

Lemma isteps_trans : forall segs a b c, isteps segs a b -> isteps segs b c -> isteps segs a c.
Proof. intros segs a b c H; induction H; intros Hc; [exact Hc | econstructor; eauto]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fpeq (ms ms' : machine_state) : Prop := (forall r, reg_get (ms_fregs ms') r = reg_get (ms_fregs ms) r) /\ ms_fcsr ms' = ms_fcsr ms.
Lemma fpeq_refl : forall ms, fpeq ms ms.
Proof. intros ms. split; [intros r; reflexivity | reflexivity]. Qed.
Lemma fpeq_trans : forall a b c, fpeq a b -> fpeq b c -> fpeq a c.
Proof. intros a b c [H1 H2] [H3 H4]. split; [intros r; rewrite H3; apply H1 | congruence]. Qed.
Definition nofp_xi (x : xi) : bool := match x with XFLd _ _ _ | XFSt _ _ _ | XFInt _ _ | XFOp => false | _ => true end.
Fixpoint tbl_nofp (t : tree xi) : bool :=
  match t with TEmpty => true | TNode l v r => (match v with Some x => nofp_xi x | None => true end && tbl_nofp l && tbl_nofp r)%bool end.
Lemma tbl_nofp_get : forall t p x, tbl_nofp t = true -> tget p t = Some x -> nofp_xi x = true.
Proof.
  induction t as [|l IHl v r IHr]; intros p x H Hp; [destruct p; discriminate Hp|].
  cbn [tbl_nofp] in H. apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hv Hl].
  destruct p as [p|p|]; cbn [tget] in Hp; [exact (IHr p x Hr Hp) | exact (IHl p x Hl Hp) | subst v; exact Hv].
Qed.
Lemma tbl_nofp_lookup : forall t pc, tbl_nofp t = true -> nofp_xi (tlookup t pc) = true.
Proof.
  intros t pc H. unfold tlookup. destruct pc as [|p|p]; [reflexivity| |reflexivity].
  destruct (tget p t) as [x|] eqn:Hp; [exact (tbl_nofp_get t p x H Hp) | reflexivity].
Qed.
Definition fpc (t : tree xi) (ms ms' : machine_state) : Prop := tbl_nofp t = true -> fpeq ms ms'.
Lemma fpc_refl : forall t ms, fpc t ms ms.
Proof. intros t ms _. apply fpeq_refl. Qed.
Lemma fpc_trans : forall t a b c, fpc t a b -> fpc t b c -> fpc t a c.
Proof. intros t a b c H1 H2 Ht. exact (fpeq_trans _ _ _ (H1 Ht) (H2 Ht)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_pow : two64 = 2 ^ 64. Proof. reflexivity. Qed.

Lemma tdiv2_sound : forall E k t t', 0 <= k -> tdiv2 k t = Some t' ->
  exists q, tsumz E t = 2 ^ k * q /\ eqm (tsum E t') q.
Proof.
  intros E k t. induction t as [|[x c] t IH]; intros t' Hk H; cbn [tdiv2] in H.
  - injection H as <-. exists 0. split; [cbn; lia | apply eqm_refl].
  - destruct (Z.eqb (Z.land (sgn64 c) (Z.ones k)) 0) eqn:Hd; [|discriminate].
    destruct (tdiv2 k t) as [r|] eqn:Ht; [|discriminate]. injection H as <-.
    destruct (IH r Hk eq_refl) as (q0 & Hq0 & Heq0).
    apply Z.eqb_eq in Hd. rewrite Z.land_ones in Hd by exact Hk.
    assert (Hv : sgn64 c = 2 ^ k * Z.shiftr (sgn64 c) k).
    { rewrite Z.shiftr_div_pow2 by exact Hk. pose proof (Z.div_mod (sgn64 c) (2 ^ k) ltac:(apply Z.pow_nonzero; lia)) as Hm. lia. }
    exists (Z.shiftr (sgn64 c) k * vz E x + q0). split.
    + cbn [tsumz]. rewrite Hq0. rewrite Hv at 1. lia.
    + cbn [tsum]. apply eqm_add; [|exact Heq0]. apply eqm_mul; [apply eqm_w64 | apply eqm_refl].
Qed.

(* [comment removed for export] *)
Lemma tsplit_sum : forall E k t dt rt, tsplit k t = (dt, rt) ->
  tsumz E t = tsumz E dt + tsumz E rt /\ eqm (tsum E t) (tsum E dt + tsum E rt) /\ tdivb k dt = true.
Proof.
  intros E k t. induction t as [|[x c] t IH]; intros dt rt H; cbn [tsplit] in H.
  - injection H as <- <-. cbn. split; [reflexivity | split; [apply eqm_refl | reflexivity]].
  - destruct (tsplit k t) as [d r] eqn:Ht. destruct (IH d r eq_refl) as (H1 & H2 & H3).
    destruct (Z.eqb (Z.land c (Z.ones k)) 0) eqn:Hc; injection H as <- <-; cbn [tsumz tsum tdivb].
    + split; [lia|]. split; [|rewrite Hc, H3; reflexivity].
      replace (c * vz E x + tsum E d + tsum E r) with (c * vz E x + (tsum E d + tsum E r)) by lia.
      apply eqm_add; [apply eqm_refl | exact H2].
    + split; [lia|]. split; [|exact H3].
      replace (tsum E d + (c * vz E x + tsum E r)) with (c * vz E x + (tsum E d + tsum E r)) by lia.
      apply eqm_add; [apply eqm_refl | exact H2].
Qed.

Lemma tdivb_sgn_mod : forall E k t, 0 <= k <= 64 -> tdivb k t = true -> tsumz E t mod 2 ^ k = 0.
Proof.
  intros E k t Hk. induction t as [|[x c] t IH]; intros H; cbn [tdivb tsumz] in *; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite Z.land_ones in H1 by lia.
  assert (Hc : sgn64 c mod 2 ^ k = 0).
  { unfold sgn64, T63. destruct (Z.ltb c 9223372036854775808); [exact H1|].
    assert (Hp : two64 = 2 ^ (64 - k) * 2 ^ k) by (rewrite two64_pow, <- Z.pow_add_r by lia; f_equal; lia).
    replace (c - two64) with (c + (- 2 ^ (64 - k)) * 2 ^ k) by (rewrite Hp; ring).
    rewrite Z_mod_plus_full. exact H1. }
  rewrite Z.add_mod by (apply Z.pow_nonzero; lia). rewrite IH by exact H2.
  rewrite Z.mul_mod by (apply Z.pow_nonzero; lia). rewrite Hc. cbn. rewrite Z.add_0_r, Z.mod_0_l by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.

Lemma win_sound : forall E fs k l dt rt t, Forall (fact_ok E) fs -> 0 <= k <= 64 -> win fs k l = Some (dt, rt, t) ->
  izl E l = tsumz E dt + izl E (LIN (l_c l) rt) /\ eqm (lz E l) (tsum E dt + lz E (LIN (l_c l) rt)) /\
  2 ^ k * t <= izl E (LIN (l_c l) rt) < 2 ^ k * (t + 1) /\ tdivb k dt = true.
Proof.
  intros E fs k l dt rt t HF Hk H. unfold win in H.
  destruct (tsplit k (l_t l)) as [d r] eqn:Hsp. destruct (tsplit_sum E k _ _ _ Hsp) as (S1 & S2 & S3).
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hiz : izl E l = tsumz E d + izl E (LIN (l_c l) r)) by (unfold izl; cbn [l_c l_t]; rewrite S1; lia).
  assert (Hlz : eqm (lz E l) (tsum E d + lz E (LIN (l_c l) r))).
  { unfold lz; cbn [l_c l_t]. replace (tsum E d + (l_c l + tsum E r)) with (l_c l + (tsum E d + tsum E r)) by lia.
    apply eqm_add; [apply eqm_refl | exact S2]. }
  destruct r as [|y ry].
  - injection H as <- <- <-. split; [exact Hiz|]. split; [exact Hlz|]. split; [|exact S3].
    unfold izl; cbn [l_c l_t tsumz]. rewrite Z.add_0_r, Z.shiftr_div_pow2 by lia.
    pose proof (Z.div_mod (sgn64 (l_c l)) (2 ^ k) ltac:(lia)). pose proof (Z.mod_pos_bound (sgn64 (l_c l)) (2 ^ k) Hpk). nia.
  - set (R := LIN (l_c l) (y :: ry)) in *.
    destruct (nowrap (l_iv fs R)) eqn:Hnw; [|discriminate].
    destruct (irange fs R) as [lo hi] eqn:Hir.
    destruct (Z.eqb (Z.shiftr lo k) (Z.shiftr hi k)) eqn:Heq; [|discriminate]. injection H as <- <- <-.
    split; [exact Hiz|]. split; [exact Hlz|]. split; [|exact S3].
    pose proof (l_iv_sound E fs R HF) as Hiv. unfold nowrap in Hnw. apply andb_prop in Hnw as [N1 N2]. apply Z.leb_le in N1, N2.
    change (LIN (l_c l) (y :: ry)) with R. rewrite <- (u_izl E R) by lia.
    pose proof (irange_sound E fs R HF) as Hr. rewrite Hir in Hr. cbn [fst snd] in Hr.
    apply Z.eqb_eq in Heq. rewrite !Z.shiftr_div_pow2 in Heq by lia. rewrite Z.shiftr_div_pow2 by lia.
    assert (Hlo : lo / 2 ^ k <= bv_unsigned (lden E R) / 2 ^ k) by (apply Z.div_le_mono; lia).
    assert (Hhi : bv_unsigned (lden E R) / 2 ^ k <= hi / 2 ^ k) by (apply Z.div_le_mono; lia).
    assert (Hq : bv_unsigned (lden E R) / 2 ^ k = lo / 2 ^ k) by lia.
    pose proof (Z.div_mod (bv_unsigned (lden E R)) (2 ^ k) ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned (lden E R)) (2 ^ k) Hpk).
    rewrite Hq in *. nia.
Qed.

Lemma srl_shift_sound : forall E fs k a l, Forall (fact_ok E) fs -> 0 <= k <= 63 -> srl_shift fs k a = Some l ->
  bv_unsigned (lden E l) = Z.shiftr (bv_unsigned (lden E a)) k.
Proof.
  intros E fs k [c t0] l HF Hk H. unfold srl_shift in H. cbn [l_t l_c] in H.
  destruct (Z.eqb (Z.shiftr (fst (l_iv fs (LIN c t0))) 64) (Z.shiftr (snd (l_iv fs (LIN c t0))) 64)) eqn:HK; [|discriminate].
  apply Z.eqb_eq in HK.
  destruct (tdiv2 k t0) as [dt'|] eqn:Ht; [|discriminate]. injection H as <-.
  set (K := Z.shiftr (fst (l_iv fs (LIN c t0))) 64) in *.
  pose proof (l_iv_sound E fs (LIN c t0) HF) as Hiv.
  assert (H2 : 0 < two64) by (unfold two64; lia).
  assert (HK1 : K * two64 <= fst (l_iv fs (LIN c t0)) < K * two64 + two64).
  { unfold K. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64) with two64.
    pose proof (Z.div_mod (fst (l_iv fs (LIN c t0))) two64 ltac:(lia)). pose proof (Z.mod_pos_bound (fst (l_iv fs (LIN c t0))) two64 H2). lia. }
  assert (HK2 : K * two64 <= snd (l_iv fs (LIN c t0)) < K * two64 + two64).
  { rewrite HK. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64) with two64.
    pose proof (Z.div_mod (snd (l_iv fs (LIN c t0))) two64 ltac:(lia)). pose proof (Z.mod_pos_bound (snd (l_iv fs (LIN c t0))) two64 H2). lia. }
  assert (Hu : bv_unsigned (lden E (LIN c t0)) = izl E (LIN c t0) - K * two64).
  { rewrite u_lden_mod. pose proof (izl_eqm E (LIN c t0)) as He. unfold eqm in He. rewrite <- He.
    symmetry. apply Z.mod_unique with K; [left; lia | lia]. }
  destruct (tdiv2_sound E k t0 dt' ltac:(lia) Ht) as (q & Hq & Heq).
  assert (Hiz : izl E (LIN c t0) = sgn64 c + tsumz E t0) by reflexivity.
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  set (t' := Z.shiftr (sgn64 c - K * two64) k).
  assert (Hdiv : Z.shiftr (bv_unsigned (lden E (LIN c t0))) k = q + t').
  { rewrite Hu, Hiz, Hq. unfold t'. rewrite !Z.shiftr_div_pow2 by lia.
    replace (sgn64 c + 2 ^ k * q - K * two64) with ((sgn64 c - K * two64) + q * 2 ^ k) by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite Hdiv.
  assert (Hr : 0 <= q + t' < two64).
  { rewrite <- Hdiv. rewrite Z.shiftr_div_pow2 by lia. pose proof (u_range E (LIN c t0)) as Ru. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with (bv_unsigned (lden E (LIN c t0))); [apply Z.div_le_upper_bound; nia | lia]. }
  rewrite u_lden_mod. unfold lz; cbn [l_c l_t].
  rewrite <- (Z.mod_small _ two64 Hr). rewrite (Z.add_comm q t'). apply eqm_add; [apply eqm_w64 | exact Heq].
Qed.

(* [comment removed for export] *)
Fixpoint tsumv (t : list (positive * Z)) (vs : list Z) : Z :=
  match t, vs with (_, c) :: t', v :: vs' => sgn64 c * v + tsumv t' vs' | _, _ => 0 end.
Fixpoint lifts (E : valu) (t : list (positive * Z)) (vs : list Z) : Prop :=
  match t, vs with [], [] => True | (y, _) :: t', v :: vs' => eqm v (vz E y) /\ lifts E t' vs' | _, _ => False end.
Lemma t_riv_lifts : forall E fs t, Forall (fact_ok E) fs -> exists vs, lifts E t vs /\ fst (t_riv fs t) <= tsumv t vs <= snd (t_riv fs t).
Proof.
  intros E fs t HF. induction t as [|[y k] t IH].
  - exists []. split; [exact I | cbn; lia].
  - destruct IH as (vs & HV & HR).
    destruct (rel_iv_sound E fs fs (lvar y) (l_iv fs (lvar y)) HF HF
                (ex_intro _ (izl E (lvar y)) (conj (eqm_trans _ _ _ (izl_eqm E (lvar y)) (eqm_sym _ _ (u_eqm_lz E (lvar y)))) (l_iv_sound E fs (lvar y) HF))))
      as (v & Hv & Hr).
    set (w := rel_iv fs fs (lvar y) (l_iv fs (lvar y))) in *.
    destruct w as [wlo whi] eqn:Hw. cbn [fst snd] in Hr.
    pose proof (iv_scale_sound (sgn64 k) wlo whi v Hr) as Hs.
    exists (v :: vs). split.
    + cbn [lifts]. split; [|exact HV]. rewrite lden_lvar in Hv. unfold vz. exact Hv.
    + cbn [t_riv tsumv]. fold w. rewrite Hw. unfold iv_add. cbn [fst snd]. lia.
Qed.
Lemma lifts_eqm : forall E t vs, lifts E t vs -> eqm (tsumv t vs) (tsum E t).
Proof.
  intros E t. induction t as [|[y c] t IH]; intros [|v vs] H; cbn [lifts tsumv tsum] in *.
  - apply eqm_refl.
  - destruct H.
  - destruct H.
  - destruct H as [H1 H2]. apply eqm_add; [apply eqm_mul; [apply sgn64_eqm | exact H1] | exact (IH vs H2)].
Qed.
Lemma tdiv2_lifts : forall E k t t' vs, 0 <= k -> tdiv2 k t = Some t' -> lifts E t vs ->
  exists q, tsumv t vs = 2 ^ k * q /\ eqm (tsum E t') q.
Proof.
  intros E k t. induction t as [|[x c] t IH]; intros t' vs Hk H HL; cbn [tdiv2] in H.
  - injection H as <-. destruct vs; [|destruct HL]. exists 0. split; [cbn; lia | apply eqm_refl].
  - destruct vs as [|v vs]; [destruct HL|]. destruct HL as [HL1 HL2].
    destruct (Z.eqb (Z.land (sgn64 c) (Z.ones k)) 0) eqn:Hd; [|discriminate].
    destruct (tdiv2 k t) as [r|] eqn:Ht; [|discriminate]. injection H as <-.
    destruct (IH r vs Hk eq_refl HL2) as (q0 & Hq0 & Heq0).
    apply Z.eqb_eq in Hd. rewrite Z.land_ones in Hd by exact Hk.
    assert (Hv : sgn64 c = 2 ^ k * Z.shiftr (sgn64 c) k).
    { rewrite Z.shiftr_div_pow2 by exact Hk. pose proof (Z.div_mod (sgn64 c) (2 ^ k) ltac:(apply Z.pow_nonzero; lia)) as Hm. lia. }
    exists (Z.shiftr (sgn64 c) k * v + q0). split.
    + cbn [tsumv]. rewrite Hq0. rewrite Hv at 1. lia.
    + cbn [tsum]. apply eqm_add; [|exact Heq0]. apply eqm_mul; [apply eqm_w64 | apply eqm_sym; exact HL1].
Qed.
Lemma srl_shift_r_sound : forall E fs k a l, Forall (fact_ok E) fs -> 0 <= k <= 63 -> srl_shift_r fs k a = Some l ->
  bv_unsigned (lden E l) = Z.shiftr (bv_unsigned (lden E a)) k.
Proof.
  intros E fs k [c t0] l HF Hk H. unfold srl_shift_r in H. cbn [l_t l_c] in H. rewrite t_rivQ_eq in H.
  set (iv := iv_add (sgn64 c, sgn64 c) (t_riv fs t0)) in *.
  destruct (Z.eqb (Z.shiftr (fst iv) 64) (Z.shiftr (snd iv) 64)) eqn:HK; [|discriminate].
  apply Z.eqb_eq in HK.
  destruct (tdiv2 k t0) as [dt'|] eqn:Ht; [|discriminate]. injection H as <-.
  set (K := Z.shiftr (fst iv) 64) in *.
  destruct (t_riv_lifts E fs t0 HF) as (vs & HL & HR).
  set (V := sgn64 c + tsumv t0 vs).
  assert (HVi : fst iv <= V <= snd iv) by (unfold iv, iv_add, V; cbn [fst snd]; lia).
  assert (H2 : 0 < two64) by (unfold two64; lia).
  assert (HK1 : K * two64 <= fst iv < K * two64 + two64).
  { unfold K. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64) with two64.
    pose proof (Z.div_mod (fst iv) two64 ltac:(lia)). pose proof (Z.mod_pos_bound (fst iv) two64 H2). lia. }
  assert (HK2 : K * two64 <= snd iv < K * two64 + two64).
  { rewrite HK. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64) with two64.
    pose proof (Z.div_mod (snd iv) two64 ltac:(lia)). pose proof (Z.mod_pos_bound (snd iv) two64 H2). lia. }
  assert (HVe : eqm V (lz E (LIN c t0))).
  { unfold V, lz. cbn [l_c l_t]. apply eqm_add; [apply sgn64_eqm | exact (lifts_eqm E t0 vs HL)]. }
  assert (Hu : bv_unsigned (lden E (LIN c t0)) = V - K * two64).
  { rewrite u_lden_mod. unfold eqm in HVe. rewrite <- HVe.
    symmetry. apply Z.mod_unique with K; [left; lia | lia]. }
  destruct (tdiv2_lifts E k t0 dt' vs ltac:(lia) Ht HL) as (q & Hq & Heq).
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  set (t' := Z.shiftr (sgn64 c - K * two64) k).
  assert (Hdiv : Z.shiftr (bv_unsigned (lden E (LIN c t0))) k = q + t').
  { rewrite Hu. unfold V. rewrite Hq. unfold t'. rewrite !Z.shiftr_div_pow2 by lia.
    replace (sgn64 c + 2 ^ k * q - K * two64) with ((sgn64 c - K * two64) + q * 2 ^ k) by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite Hdiv.
  assert (Hr : 0 <= q + t' < two64).
  { rewrite <- Hdiv. rewrite Z.shiftr_div_pow2 by lia. pose proof (u_range E (LIN c t0)) as Ru. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with (bv_unsigned (lden E (LIN c t0))); [apply Z.div_le_upper_bound; nia | lia]. }
  rewrite u_lden_mod. unfold lz; cbn [l_c l_t].
  rewrite <- (Z.mod_small _ two64 Hr). rewrite (Z.add_comm q t'). apply eqm_add; [apply eqm_w64 | exact Heq].
Qed.
Lemma srl_lin_sound : forall E fs k a l, Forall (fact_ok E) fs -> 0 <= k <= 63 -> srl_lin fs k a = Some l ->
  bv_unsigned (lden E l) = Z.shiftr (bv_unsigned (lden E a)) k.
Proof.
  intros E fs k a l HF Hk H. unfold srl_lin in H.
  destruct (nowrap (l_iv fs a)) eqn:Hnw;
    [|destruct (srl_shift fs k a) as [l0|] eqn:Hs0;
      [injection H as <-; exact (srl_shift_sound E fs k a l0 HF Hk Hs0) | exact (srl_shift_r_sound E fs k a l HF Hk H)]].
  destruct (win fs k a) as [[[dt rt] t]|] eqn:Hw; [|discriminate].
  destruct (tdiv2 k dt) as [dt'|] eqn:Ht; [|discriminate]. injection H as <-.
  destruct (win_sound E fs k a dt rt t HF ltac:(lia) Hw) as (Hiz & _ & Hwin & _).
  pose proof (l_iv_sound E fs a HF) as Hiv. unfold nowrap in Hnw. apply andb_prop in Hnw as [N1 N2].
  apply Z.leb_le in N1, N2. rewrite (u_izl E a) by lia.
  destruct (tdiv2_sound E k dt dt' ltac:(lia) Ht) as (q & Hq & Heq).
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : Z.shiftr (izl E a) k = q + t).
  { rewrite Z.shiftr_div_pow2 by lia. rewrite Hiz, Hq.
    symmetry. apply Z.div_unique with (izl E (LIN (l_c a) rt) - 2 ^ k * t); [lia | nia]. }
  rewrite Hdiv.
  assert (Hr : 0 <= q + t < two64).
  { rewrite <- Hdiv. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    pose proof (Z.pow_le_mono_r 2 0 k ltac:(lia) ltac:(lia)) as Hp. change (2 ^ 0) with 1 in Hp.
    apply Z.le_lt_trans with (izl E a); [apply Z.div_le_upper_bound; nia | unfold M64, two64 in *; lia]. }
  rewrite u_lden_mod. unfold lz; cbn [l_c l_t].
  rewrite <- (Z.mod_small _ two64 Hr). rewrite (Z.add_comm q t). apply eqm_add; [apply eqm_w64 | exact Heq].
Qed.

Lemma tdivb_mod : forall E k t, 0 <= k -> tdivb k t = true -> tsum E t mod 2 ^ k = 0.
Proof.
  intros E k t Hk. induction t as [|[x c] t IH]; intros H; cbn [tdivb tsum] in *; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite Z.land_ones in H1 by exact Hk.
  rewrite Z.add_mod by (apply Z.pow_nonzero; lia). rewrite IH by exact H2.
  rewrite Z.mul_mod by (apply Z.pow_nonzero; lia). rewrite H1. cbn. rewrite Z.add_0_r, Z.mod_0_l by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.

Lemma ldiff_ones_sub : forall x k, 0 <= k -> Z.ldiff x (Z.ones k) = x - x mod 2 ^ k.
Proof.
  intros x k Hk.
  assert (Hd : Z.land (Z.land x (Z.ones k)) (Z.ldiff x (Z.ones k)) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit x n), (Z.testbit (Z.ones k) n); reflexivity. }
  assert (Hs : Z.land x (Z.ones k) + Z.ldiff x (Z.ones k) = x).
  { rewrite Z.add_nocarry_lxor by exact Hd. rewrite Z.lxor_lor by exact Hd. rewrite Z.lor_comm. apply Z.lor_ldiff_and. }
  rewrite Z.land_ones in Hs by exact Hk. lia.
Qed.

Lemma land_himask : forall x k, 0 <= k <= 64 ->
  Z.land x (Z.land (- 2 ^ k) (Z.ones 64)) = x mod 2 ^ 64 - x mod 2 ^ k.
Proof.
  intros x k Hk.
  assert (Hn : - 2 ^ k = Z.lnot (Z.ones k)) by (rewrite Z.ones_equiv; unfold Z.lnot; lia).
  rewrite Hn. rewrite Z.land_comm with (a := Z.lnot (Z.ones k)). rewrite Z.land_assoc.
  rewrite Z.land_ones by lia. rewrite <- Z.ldiff_land. rewrite ldiff_ones_sub by lia.
  rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal; lia.
Qed.

Lemma and_lin_sound : forall E fs m a l, Forall (fact_ok E) fs -> 0 <= m < two64 -> and_lin fs m a = Some l ->
  lden E l = bv_and (lden E a) (Z_to_bv 64 m).
Proof.
  intros E fs m a l HF Hm H. unfold and_lin in H.
  assert (Hua0 : eqm (bv_unsigned (lden E a)) (izl E a)) by (eapply eqm_trans; [apply u_eqm_lz | apply eqm_sym, izl_eqm]).
  destruct (Z.eqb m (Z.ones (ctz64 (m + 1)))) eqn:Hc.
  - set (k := ctz64 (m + 1)) in *. assert (Hk : 0 <= k <= 64) by (destruct (ctz64_spec (m + 1)); lia).
    apply Z.eqb_eq in Hc.
    destruct (win fs k a) as [[[dt rt] t]|] eqn:Hw; [|discriminate]. injection H as <-.
    destruct (win_sound E fs k a dt rt t HF Hk Hw) as (Hiz & _ & Hwin & Hdt).
    assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (Hdiv : (2 ^ k | two64)) by (rewrite two64_pow; apply pow2_divide_le; lia).
    apply bv_eq. rewrite bv_and_unsigned, u_small64 with (z := m) by exact Hm. rewrite Hc, Z.land_ones by lia.
    assert (Hmod : bv_unsigned (lden E a) mod 2 ^ k = izl E (LIN (l_c a) rt) - 2 ^ k * t).
    { unfold eqm in Hua0. rewrite <- (Z.mod_mod_divide (bv_unsigned (lden E a)) two64 (2 ^ k) Hdiv), Hua0,
        (Z.mod_mod_divide _ two64 (2 ^ k) Hdiv).
      rewrite Hiz, Z.add_mod by lia. rewrite (tdivb_sgn_mod E k dt Hk Hdt), Z.add_0_l, Z.mod_mod by lia.
      symmetry. apply Z.mod_unique with t; lia. }
    rewrite Hmod. rewrite u_lden_mod.
    assert (Hr : 0 <= izl E (LIN (l_c a) rt) - 2 ^ k * t < two64).
    { split; [lia|]. apply Z.lt_le_trans with (2 ^ k); [lia|]. rewrite two64_pow. apply Z.pow_le_mono_r; lia. }
    rewrite <- (Z.mod_small _ two64 Hr). unfold lz; cbn [l_c l_t].
    change (eqm (w64 (l_c a - 2 ^ k * t) + tsum E rt) (izl E (LIN (l_c a) rt) - 2 ^ k * t)).
    apply eqm_trans with ((l_c a - 2 ^ k * t) + tsum E rt); [apply eqm_add; [apply eqm_w64 | apply eqm_refl]|].
    unfold izl; cbn [l_c l_t].
    replace (sgn64 (l_c a) + tsumz E rt - 2 ^ k * t) with ((sgn64 (l_c a) - 2 ^ k * t) + tsumz E rt) by lia.
    apply eqm_add; [apply eqm_sub; [apply eqm_sym, sgn64_eqm | apply eqm_refl] | apply eqm_sym, tsumz_eqm].
  - destruct (Z.eqb m (w64 (- 2 ^ ctz64 m))) eqn:Hc2; [|discriminate].
    set (k := ctz64 m) in *. assert (Hk : 0 <= k <= 64) by (destruct (ctz64_spec m); lia). apply Z.eqb_eq in Hc2.
    destruct (win fs k a) as [[[dt rt] t]|] eqn:Hw; [|discriminate]. injection H as <-.
    destruct (win_sound E fs k a dt rt t HF Hk Hw) as (Hiz & _ & Hwin & Hdt).
    assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (Hdiv : (2 ^ k | two64)) by (rewrite two64_pow; apply pow2_divide_le; lia).
    assert (Hm' : m = Z.land (- 2 ^ k) (Z.ones 64)) by (rewrite Hc2; rewrite w64_land; rewrite M64_ones; reflexivity).
    apply bv_eq. rewrite bv_and_unsigned, u_small64 with (z := m) by exact Hm. rewrite Hm', land_himask by exact Hk.
    pose proof (u_range E a) as Ua. change (2 ^ 64) with two64. rewrite Z.mod_small by exact Ua.
    assert (Hmod : bv_unsigned (lden E a) mod 2 ^ k = izl E (LIN (l_c a) rt) - 2 ^ k * t).
    { unfold eqm in Hua0. rewrite <- (Z.mod_mod_divide (bv_unsigned (lden E a)) two64 (2 ^ k) Hdiv), Hua0,
        (Z.mod_mod_divide _ two64 (2 ^ k) Hdiv).
      rewrite Hiz, Z.add_mod by lia. rewrite (tdivb_sgn_mod E k dt Hk Hdt), Z.add_0_l, Z.mod_mod by lia.
      symmetry. apply Z.mod_unique with t; lia. }
    rewrite Hmod. rewrite u_lden_mod.
    assert (Hr : 0 <= bv_unsigned (lden E a) - (izl E (LIN (l_c a) rt) - 2 ^ k * t) < two64).
    { rewrite <- Hmod. pose proof (Z.mod_pos_bound (bv_unsigned (lden E a)) (2 ^ k) Hpk).
      pose proof (Z.mod_le (bv_unsigned (lden E a)) (2 ^ k) ltac:(lia) Hpk). lia. }
    rewrite <- (Z.mod_small _ two64 Hr). unfold lz; cbn [l_c l_t].
    replace (bv_unsigned (lden E a) - (izl E (LIN (l_c a) rt) - 2 ^ k * t))
      with (bv_unsigned (lden E a) - izl E (LIN (l_c a) rt) + 2 ^ k * t) by lia.
    apply eqm_trans with (2 ^ k * t + tsumz E dt); [apply eqm_add; [apply eqm_w64 | apply eqm_sym, tsumz_eqm]|].
    apply eqm_trans with (izl E a - izl E (LIN (l_c a) rt) + 2 ^ k * t); [rewrite Hiz; unfold eqm; f_equal; lia|].
    apply eqm_add; [|apply eqm_refl]. apply eqm_sub; [|apply eqm_refl]. apply eqm_sym. exact Hua0.
Qed.

Lemma land_ctz_mod : forall x m, 0 <= m < two64 -> Z.land x m mod 2 ^ ctz64 m = 0.
Proof.
  intros x m Hm. destruct (ctz64_spec m) as [Hk Hd].
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. rewrite Z.land_ones by lia.
  replace (m mod 2 ^ ctz64 m) with 0; [apply Z.land_0_r|].
  symmetry. apply Z.mod_divide; [apply Z.pow_nonzero; lia | exact Hd].
Qed.

Lemma land_mod_low : forall x m k, 0 <= k -> 0 <= m < 2 ^ k -> Z.land x m = Z.land (x mod 2 ^ k) m.
Proof.
  intros x m k Hk Hm. rewrite <- Z.land_ones by exact Hk. rewrite <- Z.land_assoc.
  replace (Z.land (Z.ones k) m) with m; [reflexivity|]. rewrite Z.land_comm, Z.land_ones by exact Hk. symmetry. apply Z.mod_small. exact Hm.
Qed.

Lemma and_low_sound : forall E fs m a l, Forall (fact_ok E) fs -> 0 <= m < two64 -> and_low fs m a = Some l ->
  lden E l = bv_and (lden E a) (Z_to_bv 64 m).
Proof.
  intros E fs m a l HF Hm H. unfold and_low in H.
  destruct (Z.leb 1 m && Z.leb (Z.log2 m + 1) 64)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2.
  destruct (lowb fs a (Z.log2 m + 1)) as [r|] eqn:Hlb; [|discriminate]. injection H as <-.
  pose proof (lowb_sound E fs a _ r HF Hlb) as Hr.
  assert (Hk : 0 <= Z.log2 m + 1) by (pose proof (Z.log2_nonneg m); lia).
  assert (Hmk : m < 2 ^ (Z.log2 m + 1)) by (apply Z.log2_spec; lia).
  apply bv_eq. rewrite bv_and_unsigned, u_small64 with (z := m) by exact Hm. rewrite lden_lconst, u_Z_to_bv.
  rewrite (land_mod_low (bv_unsigned (lden E a)) m (Z.log2 m + 1) Hk ltac:(lia)), Hr.
  apply Z.mod_small. split; [apply Z.land_nonneg; lia|]. apply Z.le_lt_trans with m; [apply land_le_r; [subst r; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia | lia] | lia].
Qed.

(* [comment removed for export] *)
Lemma and_hi_sound : forall E fs m a l, Forall (fact_ok E) fs -> 0 <= m < two64 -> and_hi fs m a = Some l ->
  lden E l = bv_and (lden E a) (Z_to_bv 64 m).
Proof.
  intros E fs m a l HF Hm H. unfold and_hi in H.
  destruct (Z.eqb m (w64 (- 2 ^ ctz64 m)) && Z.leb 1 (ctz64 m) && Z.leb (ctz64 m) 63)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hk2]. apply andb_prop in Hc as [Hc Hk1]. apply Z.eqb_eq in Hc. apply Z.leb_le in Hk1, Hk2.
  set (k := ctz64 m) in *.
  destruct (lowb fs a k) as [r|] eqn:Hlb; [|discriminate]. injection H as <-.
  pose proof (lowb_sound E fs a k r HF Hlb) as Hr.
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm' : m = Z.land (- 2 ^ k) (Z.ones 64)) by (rewrite Hc; rewrite w64_land; rewrite M64_ones; reflexivity).
  apply bv_eq. rewrite bv_and_unsigned, u_small64 with (z := m) by exact Hm. rewrite Hm', land_himask by lia.
  pose proof (u_range E a) as Ua. change (2 ^ 64) with two64. rewrite Z.mod_small by exact Ua. rewrite Hr.
  rewrite lden_laddc, u_Z_to_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  pose proof (Z.mod_pos_bound (bv_unsigned (lden E a)) (2 ^ k) Hpk) as Hb.
  pose proof (Z.mod_le (bv_unsigned (lden E a)) (2 ^ k) ltac:(lia) Hpk) as Hle. rewrite Hr in Hb, Hle.
  apply Z.mod_small. lia.
Qed.
Lemma and_lowhi_sound : forall E fs m a l, Forall (fact_ok E) fs -> 0 <= m < two64 -> and_lowhi fs m a = Some l ->
  lden E l = bv_and (lden E a) (Z_to_bv 64 m).
Proof.
  intros E fs m a l HF Hm H. unfold and_lowhi in H. destruct (and_low fs m a) as [l'|] eqn:Hl.
  - injection H as <-. exact (and_low_sound E fs m a l' HF Hm Hl).
  - exact (and_hi_sound E fs m a l HF Hm H).
Qed.

(* [comment removed for export] *)
Lemma land_band : forall a k j, 0 < k < j -> j < 64 -> 0 <= a < 2 ^ j -> Z.land a (2 ^ j - 2 ^ k) = Z.land a (two64 - 2 ^ k).
Proof.
  intros a k j Hk Hj Ha.
  assert (E1 : 2 ^ j - 2 ^ k = Z.shiftl (Z.ones (j - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. rewrite Z.mul_pred_l. rewrite <- Z.pow_add_r by lia.
    replace (j - k + k) with j by lia. lia. }
  assert (E2 : two64 - 2 ^ k = Z.shiftl (Z.ones (64 - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. rewrite Z.mul_pred_l. rewrite <- Z.pow_add_r by lia.
    replace (64 - k + k) with 64 by lia. unfold two64. lia. }
  rewrite E1, E2. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_dec i k) as [Hik|Hik].
  - rewrite !Z.shiftl_spec_low by lia. reflexivity.
  - rewrite !Z.shiftl_spec by lia.
    destruct (Z_lt_dec i j) as [Hij|Hij].
    + rewrite !Z.ones_spec_low by lia. reflexivity.
    + assert (Hb : Z.testbit a i = false).
      { destruct (Z.eq_dec a 0) as [->|Hne]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
        assert (Z.log2 a < j) by (apply Z.log2_lt_pow2; lia). lia. }
      rewrite Hb. reflexivity.
Qed.
Lemma and_band_sound : forall E fs m a l, Forall (fact_ok E) fs -> 0 <= m < two64 -> and_band fs m a = Some l ->
  lden E l = bv_and (lden E a) (Z_to_bv 64 m).
Proof.
  intros E fs m a l HF Hm H. unfold and_band in H.
  set (k := ctz64 m) in *. set (j := Z.log2 (m + 2 ^ k)) in *.
  destruct (Z.ltb 0 k &&& Z.ltb k j &&& Z.ltb j 64 &&& Z.eqb m (2 ^ j - 2 ^ k) &&& Z.ltb (snd (irange fs a)) (2 ^ j)) eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc H5]. apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.ltb_lt in H1, H2, H3, H5. apply Z.eqb_eq in H4.
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hkj : 2 ^ k < two64) by (change two64 with (2 ^ 64); apply Z.pow_lt_mono_r; lia).
  assert (Hm' : w64 (- 2 ^ k) = two64 - 2 ^ k).
  { rewrite w64_mod. replace (- 2 ^ k) with ((two64 - 2 ^ k) + (-1) * two64) by lia. rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. lia. }
  assert (Hl : lden E l = bv_and (lden E a) (Z_to_bv 64 (w64 (- 2 ^ k)))).
  { destruct (and_lin fs (w64 (- 2 ^ k)) a) as [l'|] eqn:Hal.
    - injection H as <-. apply (and_lin_sound E fs _ a l' HF); [rewrite Hm'; lia | exact Hal].
    - apply (and_lowhi_sound E fs _ a l HF); [rewrite Hm'; lia | exact H]. }
  rewrite Hl. apply bv_eq. rewrite !bv_and_unsigned, !u_Z_to_bv. rewrite Hm'.
  rewrite (Z.mod_small (two64 - 2 ^ k)) by lia. rewrite (Z.mod_small m) by exact Hm.
  pose proof (irange_sound E fs a HF) as Ra. pose proof (u_range E a) as Ua.
  rewrite H4. symmetry. apply land_band; lia.
Qed.
Lemma and_lin3_sound : forall E fs m a l, Forall (fact_ok E) fs -> 0 <= m < two64 -> and_lin3 fs m a = Some l ->
  lden E l = bv_and (lden E a) (Z_to_bv 64 m).
Proof.
  intros E fs m a l HF Hm H. unfold and_lin3 in H. destruct (and_lin fs m a) as [l'|] eqn:Hal.
  - injection H as <-. exact (and_lin_sound E fs m a l' HF Hm Hal).
  - destruct (and_lowhi fs m a) as [l'|] eqn:Hlh.
    + injection H as <-. exact (and_lowhi_sound E fs m a l' HF Hm Hlh).
    + exact (and_band_sound E fs m a l HF Hm H).
Qed.

Lemma bitop_mod : forall op x y k, 0 <= k -> (op = Z.land \/ op = Z.lor \/ op = Z.lxor) ->
  (op x y) mod 2 ^ k = op (x mod 2 ^ k) (y mod 2 ^ k).
Proof.
  intros op x y k Hk Hop. rewrite <- !Z.land_ones by exact Hk.
  apply Z.bits_inj'. intros n Hn.
  destruct Hop as [-> | [-> | ->]]; rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec;
    destruct (Z.testbit x n), (Z.testbit y n), (Z.testbit (Z.ones k) n); reflexivity.
Qed.

Lemma lowb2_spec : forall fs a b k ra rb, lowb2 fs a b = Some (k, ra, rb) -> lowb fs a k = Some ra /\ lowb fs b k = Some rb.
Proof.
  intros fs a b k ra rb H. unfold lowb2 in H.
  repeat match type of H with
         | context [match lowb fs a ?kk with _ => _ end] => destruct (lowb fs a kk) eqn:?; cbv beta iota in H
         | context [match lowb fs b ?kk with _ => _ end] => destruct (lowb fs b kk) eqn:?; cbv beta iota in H
         end; try discriminate; injection H as <- <- <-; split; assumption.
Qed.

Lemma bits_facts_sound : forall E fs op a b n (E'' : valu), Forall (fact_ok E) fs -> E'' n = alu64 op (lden E a) (lden E b) ->
  Forall (fact_ok E'') (bits_facts fs op a b (lvar n)).
Proof.
  intros E fs op a b n E'' HF Hn. unfold bits_facts.
  destruct (lowb2 fs a b) as [[[k ra] rb]|] eqn:Hl2; [|constructor].
  destruct (lowb2_spec _ _ _ _ _ _ Hl2) as [Ha Hb].
  assert (Hk : 0 <= k) by (unfold lowb in Ha; destruct (Z.leb 0 k && Z.leb k 64)%bool eqn:Hc; [apply andb_prop in Hc as [Hc _]; apply Z.leb_le in Hc; exact Hc | discriminate]).
  pose proof (lowb_sound E fs a k ra HF Ha) as Hra. pose proof (lowb_sound E fs b k rb HF Hb) as Hrb.
  destruct op; try constructor; try constructor; cbn [fact_ok]; rewrite lden_lvar, Hn; cbn [alu64 alu];
    rewrite ?bv_xor_unsigned, ?bv_or_unsigned, ?bv_and_unsigned;
    first [ rewrite (bitop_mod Z.lxor) by (auto || (right; right; reflexivity)) | rewrite (bitop_mod Z.lor) by (auto || (right; left; reflexivity))
          | rewrite (bitop_mod Z.land) by (auto || (left; reflexivity)) ]; rewrite Hra, Hrb; reflexivity.
Qed.

Lemma lxor_m64 : forall x, 0 <= x < two64 -> Z.lxor x M64 = M64 - x.
Proof.
  intros x Hx. assert (Hd : Z.land x (Z.lxor x M64) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0. rewrite M64_ones, Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec i 64) as [Hi64|Hi64].
    - destruct (Z.testbit x i); reflexivity.
    - rewrite (testbit_high64 x i) by (unfold two64 in Hx; change (2 ^ 64) with 18446744073709551616; lia). reflexivity. }
  pose proof (Z.add_nocarry_lxor x (Z.lxor x M64) Hd) as Ha.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Ha. lia.
Qed.
Lemma xor_m64_word : forall w : word, (Z_to_bv 64 M64 - w)%bv = alu64 ALU_XOR w (Z_to_bv 64 M64).
Proof.
  intros w. apply bv_eq. cbn [alu64 alu]. rewrite bv_sub_unsigned, bv_xor_unsigned, !u_Z_to_bv.
  pose proof (bv_unsigned_in_range _ w) as Rw. unfold bv_modulus in Rw. change (2 ^ Z.of_N 64) with two64 in Rw.
  rewrite (Z.mod_small M64) by (unfold M64, two64; lia). rewrite lxor_m64 by exact Rw.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold M64, two64 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma lxor_low_bits : forall X m k, 0 <= X -> 0 <= k -> 0 <= m < 2 ^ k ->
  Z.lxor X m = X - Z.land X (Z.ones k) + Z.lxor (Z.land X (Z.ones k)) m.
Proof.
  intros X m k HX Hk Hm.
  set (r := Z.land X (Z.ones k)). set (y := Z.lxor r m). set (H := X - r).
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hr : r = X mod 2 ^ k) by (unfold r; apply Z.land_ones; lia).
  assert (HH : H = Z.shiftl (Z.shiftr X k) k).
  { unfold H. rewrite Hr, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod X (2 ^ k) ltac:(lia)). lia. }
  assert (Hmb : forall n, k <= n -> Z.testbit m n = false).
  { intros n Hn. rewrite <- (Z.mod_small m (2 ^ k)) by lia. apply Z.mod_pow2_bits_high. lia. }
  assert (Hrb : forall n, 0 <= n -> Z.testbit r n = (Z.testbit X n && Z.ltb n k)%bool).
  { intros n Hn. unfold r. rewrite Z.land_spec, Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec n k); destruct (Z.leb_spec 0 n); try lia; reflexivity. }
  assert (HHb : forall n, 0 <= n -> Z.testbit H n = (Z.testbit X n && negb (Z.ltb n k))%bool).
  { intros n Hn. rewrite HH. destruct (Z.ltb_spec n k) as [Hlt|Hge].
    - rewrite Z.shiftl_spec_low by lia. rewrite andb_false_r. reflexivity.
    - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (n - k + k) with n by lia. rewrite andb_true_r. reflexivity. }
  assert (Hland : Z.land H y = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, HHb by lia. unfold y. rewrite Z.lxor_spec, Hrb by lia.
    destruct (Z.ltb_spec n k) as [Hlt|Hge]; [rewrite andb_false_r; reflexivity|].
    rewrite (Hmb n Hge). cbn. rewrite andb_false_r. cbn. apply andb_false_r. }
  pose proof (Z.add_lor_land H y) as Hal. rewrite Hland, Z.add_0_r in Hal.
  replace (X - r + y) with (H + y) by (unfold H; lia). rewrite <- Hal.
  apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.lor_spec, HHb by lia. unfold y. rewrite Z.lxor_spec, Hrb by lia.
  destruct (Z.ltb_spec n k) as [Hlt|Hge].
  - cbn. rewrite andb_false_r, andb_true_r. reflexivity.
  - rewrite (Hmb n Hge). cbn. rewrite andb_true_r, andb_false_r. cbn. rewrite xorb_false_r, orb_false_r. reflexivity.
Qed.
Lemma lxor_lt_two64 : forall X m, 0 <= X < two64 -> 0 <= m < two64 -> 0 <= Z.lxor X m < two64.
Proof.
  intros X m HX Hm. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor X m) 0) as [Hz|Hz]; [rewrite Hz; unfold two64; lia|].
  assert (Hp : 0 < Z.lxor X m) by (pose proof (proj2 (Z.lxor_nonneg X m)); lia).
  change two64 with (2 ^ 64). apply (proj2 (Z.log2_lt_pow2 (Z.lxor X m) 64 Hp)).
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec X 0) as [->|Hx]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 X 64 ltac:(lia))). change (2 ^ 64) with two64. lia.
  - destruct (Z.eq_dec m 0) as [->|Hx]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 m 64 ltac:(lia))). change (2 ^ 64) with two64. lia.
Qed.
Lemma xor_low_sound : forall E fs m a l, Forall (fact_ok E) fs -> 0 <= m < two64 -> xor_low fs m a = Some l ->
  lden E l = alu64 ALU_XOR (lden E a) (Z_to_bv 64 m).
Proof.
  intros E fs m a l HF Hm H. unfold xor_low in H.
  set (k := Z.log2 m + 1) in *.
  destruct (Z.leb 1 m && Z.leb k 63)%bool eqn:Hc; [|discriminate]. apply andb_prop in Hc as [Hc1 Hc2].
  apply Z.leb_le in Hc1, Hc2.
  destruct (and_lin3 fs (Z.ones k) a) as [la|] eqn:Hal; [|discriminate].
  destruct (is_const la) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
  assert (Hk0 : 0 <= k) by (unfold k; pose proof (Z.log2_nonneg m); lia).
  assert (Hones : 0 <= Z.ones k < two64).
  { rewrite Z.ones_equiv. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (2 ^ k <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). unfold two64. lia. }
  pose proof (and_lin3_sound E fs (Z.ones k) a la HF Hones Hal) as Ha.
  destruct (is_const_sound E la r Hr) as [Hlar Hrr].
  pose proof (u_range E a) as RX. set (X := bv_unsigned (lden E a)) in *.
  assert (Hmk : m < 2 ^ k) by (unfold k; apply Z.log2_lt_pow2; [lia|]; lia).
  assert (Hrv : r = Z.land X (Z.ones k)).
  { assert (Hu : bv_unsigned (lden E la) = Z.land X (Z.ones k)).
    { rewrite Ha, bv_and_unsigned, u_Z_to_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite (Z.mod_small (Z.ones k)) by lia. reflexivity. }
    rewrite Hlar, u_Z_to_bv in Hu. unfold bv_wrap, bv_modulus in Hu. change (2 ^ Z.of_N 64) with two64 in Hu.
    rewrite Z.mod_small in Hu by lia. exact Hu. }
  pose proof (lxor_low_bits X m k (proj1 RX) Hk0 (conj (proj1 Hm) Hmk)) as Hx. rewrite <- Hrv in Hx.
  pose proof (lxor_lt_two64 X m RX Hm) as Hlt.
  cbn [alu64 alu]. apply bv_eq. rewrite bv_xor_unsigned, u_Z_to_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite (Z.mod_small m) by lia. fold X.
  assert (He : eqm (bv_unsigned (lden E (laddc (lsub a la) (Z.lxor r m)))) (X - r + Z.lxor r m)).
  { eapply eqm_trans; [apply u_eqm_lz|]. eapply eqm_trans; [apply lz_laddc|]. apply eqm_add; [|apply eqm_refl].
    eapply eqm_trans; [apply lz_lsub|]. apply eqm_sub.
    - apply eqm_sym. apply u_eqm_lz.
    - apply eqm_sym. replace r with (bv_unsigned (lden E la)) at 1; [apply u_eqm_lz|].
      rewrite Hlar, u_Z_to_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. lia. }
  unfold eqm in He. rewrite (Z.mod_small (bv_unsigned _)) in He by apply u_range.
  rewrite He, <- Hx. apply Z.mod_small. exact Hlt.
Qed.

Lemma ev_alu_lin_sound : forall E fs op a b l, Forall (fact_ok E) fs -> ev_alu_lin fs op a b = Some l ->
  lden E l = alu64 op (lden E a) (lden E b).
Proof.
  intros E fs op a b l HF H. unfold ev_alu_lin in H.
  destruct op; try (destruct (is_const b); destruct (is_const a); discriminate).
  - injection H as <-. apply lden_ladd.
  - injection H as <-. apply lden_lsub.
  - destruct (is_const b) as [y|] eqn:Hb; [|destruct (is_const a); discriminate].
    destruct (is_const_sound E b y Hb) as [Hby Hy]. injection H as <-. rewrite lden_lscale, Hby.
    cbn [alu64 alu]. apply bv_eq. rewrite bv_shiftl_unsigned, bv_and_unsigned, !u_Z_to_bv.
    rewrite (Z.mod_small y) by exact Hy. change (18446744073709551616) with two64 in *.
    rewrite (Z.mod_small 63) by (unfold two64; lia).
    rewrite Z.shiftl_mul_pow2 by (apply Z.land_nonneg; lia).
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite Z.mul_comm. reflexivity.
  - destruct (is_const b) as [y|] eqn:Hb.
    + destruct (Z.eqb y M64) eqn:Hy.
      * apply Z.eqb_eq in Hy. subst y. injection H as <-.
        destruct (is_const_sound E b M64 Hb) as [Hby _]. rewrite Hby, lden_lsub, lden_lconst. apply xor_m64_word.
      * destruct (is_const_sound E b y Hb) as [Hby Hyr]. rewrite Hby. exact (xor_low_sound E fs y a l HF Hyr H).
    + destruct (is_const a) as [x|] eqn:Ha.
      * destruct (Z.eqb x M64) eqn:Hx.
        -- apply Z.eqb_eq in Hx. subst x. injection H as <-.
           destruct (is_const_sound E a M64 Ha) as [Hax _]. rewrite Hax, lden_lsub, lden_lconst, xor_m64_word.
           cbn [alu64 alu]. apply bv_eq. rewrite !bv_xor_unsigned. apply Z.lxor_comm.
        -- destruct (is_const_sound E a x Ha) as [Hax Hxr]. rewrite Hax, (xor_low_sound E fs x b l HF Hxr H).
           cbn [alu64 alu]. apply bv_eq. rewrite !bv_xor_unsigned. apply Z.lxor_comm.
      * destruct (lin_eqb a b) eqn:Hab; [|discriminate]. injection H as <-. apply lin_eqb_eq in Hab. subst b.
        rewrite lden_lconst. cbn [alu64 alu]. apply bv_eq. rewrite bv_xor_unsigned, Z.lxor_nilpotent. reflexivity.
  - destruct (is_const b) as [y|] eqn:Hb; [|destruct (is_const a); discriminate].
    destruct (is_const_sound E b y Hb) as [Hby Hy].
    assert (Hk : 0 <= Z.land y 63 <= 63).
    { split; [apply Z.land_nonneg; lia|]. apply land_le_r; lia. }
    pose proof (srl_lin_sound E fs (Z.land y 63) a l HF Hk H) as Hs.
    rewrite Hby. cbn [alu64 alu]. apply bv_eq. rewrite Hs, bv_shiftr_unsigned, bv_and_unsigned, !u_Z_to_bv.
    rewrite (Z.mod_small y) by exact Hy. rewrite (Z.mod_small 63) by (unfold two64; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Hg : forall x y l0, or_go fs x y = Some l0 -> lden E l0 = bv_or (lden E x) (lden E y)).
    { intros x y l0 Hgo. unfold or_go in Hgo. pose proof (irange_sound E fs y HF) as Ry.
      destruct (Z.leb 0 (fst (irange fs y)) && Z.leb 1 (Z.log2 (snd (irange fs y)) + 1) && Z.leb (Z.log2 (snd (irange fs y)) + 1) 63)%bool eqn:Hk;
        [|discriminate].
      apply andb_prop in Hk as [Hk Hk3]. apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1, Hk2, Hk3.
      set (k := Z.log2 (snd (irange fs y)) + 1) in *.
      destruct (lowb fs x k) as [r0|] eqn:Hlb; [|discriminate]. destruct (Z.eqb r0 0) eqn:Hr0; [|discriminate].
      apply Z.eqb_eq in Hr0. subst r0. injection Hgo as <-.
      pose proof (lowb_sound E fs x k 0 HF Hlb) as Hxl.
      set (X := bv_unsigned (lden E x)) in *. set (Y := bv_unsigned (lden E y)) in *.
      pose proof (u_range E x) as RX. pose proof (u_range E y) as RY. fold X Y in RX, RY.
      assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
      assert (Hyk : Y < 2 ^ k).
      { destruct (Z_lt_le_dec 0 (snd (irange fs y))) as [Hp|Hp].
        - pose proof (Z.log2_spec (snd (irange fs y)) Hp) as [_ Xs]. unfold k. rewrite <- Z.add_1_r in Xs. lia.
        - lia. }
      assert (Hland : Z.land X Y = 0).
      { rewrite <- (Z.mod_small Y (2 ^ k)) by lia. rewrite <- Z.land_ones by lia.
        rewrite (Z.land_comm Y (Z.ones k)), Z.land_assoc, Z.land_ones, Hxl by lia. apply Z.land_0_l. }
      pose proof (Z.add_lor_land X Y) as Hal. rewrite Hland, Z.add_0_r in Hal.
      rewrite lden_ladd. apply bv_eq. rewrite bv_add_unsigned, bv_or_unsigned. fold X Y. rewrite Hal.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small.
      pose proof (Z.div_mod X (2 ^ k) ltac:(lia)) as Hdm. rewrite Hxl, Z.add_0_r in Hdm.
      assert (H64 : two64 = 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; replace (k + (64 - k)) with 64 by lia; reflexivity).
      assert (Hq : X / 2 ^ k < 2 ^ (64 - k)).
      { apply Z.div_lt_upper_bound; [lia|]. rewrite <- H64. unfold M64, two64 in *. lia. }
      assert (Hq0 : 0 <= X / 2 ^ k) by (apply Z.div_pos; lia).
      split; [lia|]. rewrite Hdm, H64. nia. }
    assert (Hol : forall l0, or_lin fs a b = Some l0 -> lden E l0 = alu64 ALU_OR (lden E a) (lden E b)).
    { intros l0 H0. unfold or_lin in H0. destruct (or_go fs a b) as [l'|] eqn:H1.
      + injection H0 as <-. rewrite (Hg a b l' H1). reflexivity.
      + rewrite (Hg b a l0 H0). cbn [alu64 alu]. apply bv_eq. rewrite !bv_or_unsigned. apply Z.lor_comm. }
    (* [comment removed for export] *)
    assert (Hoo : forall m x l0, or_ones fs m x = Some l0 -> lden E l0 = bv_or (lden E x) (Z_to_bv 64 m)).
    { intros m x l0 H0. unfold or_ones in H0.
      destruct (Z.leb 0 m && Z.ltb m two64)%bool eqn:Hm; [|discriminate]. apply andb_prop in Hm as [Hm0 Hm1].
      apply Z.leb_le in Hm0. apply Z.ltb_lt in Hm1.
      destruct (and_lin fs m x) as [la|] eqn:Hal; [|discriminate]. injection H0 as <-.
      pose proof (and_lin_sound E fs m x la HF (conj Hm0 Hm1) Hal) as Ha.
      pose proof (u_range E x) as RX. set (X := bv_unsigned (lden E x)) in *.
      assert (Hla : bv_unsigned (lden E la) = Z.land X m).
      { rewrite Ha, bv_and_unsigned, u_Z_to_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small m) by lia. reflexivity. }
      pose proof (Z.add_lor_land X m) as Hal2.
      assert (Hlor : 0 <= Z.lor X m < two64).
      { split; [apply Z.lor_nonneg; lia|].
        destruct (Z.eq_dec (Z.lor X m) 0) as [Hz|Hz]; [rewrite Hz; unfold two64; lia|].
        assert (Hp : 0 < Z.lor X m) by (pose proof (proj2 (Z.lor_nonneg X m) (conj (proj1 RX) Hm0)); lia).
        change two64 with (2 ^ 64). apply (proj2 (Z.log2_lt_pow2 (Z.lor X m) 64 Hp)). rewrite Z.log2_lor by lia.
        apply Z.max_lub_lt.
        - destruct (Z.eq_dec X 0) as [->|Hx]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 X 64 ltac:(lia))). change (2 ^ 64) with two64. lia.
        - destruct (Z.eq_dec m 0) as [->|Hx]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 m 64 ltac:(lia))). change (2 ^ 64) with two64. lia. }
      apply bv_eq. rewrite bv_or_unsigned, u_Z_to_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite (Z.mod_small m) by lia. fold X.
      assert (He : eqm (bv_unsigned (lden E (laddc (lsub x la) m))) (X - Z.land X m + m)).
      { eapply eqm_trans; [apply u_eqm_lz|]. eapply eqm_trans; [apply lz_laddc|]. apply eqm_add; [|apply eqm_refl].
        eapply eqm_trans; [apply lz_lsub|]. apply eqm_sub.
        - apply eqm_sym. apply u_eqm_lz.
        - apply eqm_sym. rewrite <- Hla. apply u_eqm_lz. }
      unfold eqm in He. rewrite (Z.mod_small (bv_unsigned _)) in He by apply u_range.
      rewrite He. replace (X - Z.land X m + m) with (Z.lor X m) by lia. apply Z.mod_small. exact Hlor. }
    unfold or_lin2 in H.
    destruct (is_const b) as [m|] eqn:Hb.
    + destruct (or_ones fs m a) as [l'|] eqn:H1; [|exact (Hol l H)].
      injection H as <-. destruct (is_const_sound E b m Hb) as [Hbm _]. rewrite (Hoo m a l' H1), Hbm. reflexivity.
    + destruct (is_const a) as [m|] eqn:Ha0; [|exact (Hol l H)].
      destruct (or_ones fs m b) as [l'|] eqn:H1; [|exact (Hol l H)].
      injection H as <-. destruct (is_const_sound E a m Ha0) as [Ham _]. rewrite (Hoo m b l' H1), Ham.
      cbn [alu64 alu]. apply bv_eq. rewrite !bv_or_unsigned. apply Z.lor_comm.
  - destruct (is_const b) as [y|] eqn:Hb.
    + destruct (is_const_sound E b y Hb) as [Hby Hy].
      assert (Hl : lden E l = bv_and (lden E a) (Z_to_bv 64 y)).
      { exact (and_lin3_sound E fs y a l HF Hy H). }
      rewrite Hl, Hby. reflexivity.
    + destruct (is_const a) as [x|] eqn:Ha; [|discriminate].
      destruct (is_const_sound E a x Ha) as [Hax Hx].
      assert (Hl : lden E l = bv_and (lden E b) (Z_to_bv 64 x)).
      { exact (and_lin3_sound E fs x b l HF Hx H). }
      rewrite Hl, Hax. cbn [alu64 alu]. apply bv_eq. rewrite !bv_and_unsigned. apply Z.land_comm.
Qed.

Lemma tn_alu_ok : forall E fs op a b t, Forall (fact_ok E) fs -> tn_alu fs op a b = Some t ->
  tn_ok (bv_unsigned (alu64 op (lden E a) (lden E b))) t.
Proof.
  intros E fs op a b t HF H. unfold tn_alu in H.
  pose proof (tn_of_ok E fs a HF) as Ta. pose proof (tn_of_ok E fs b HF) as Tb. pose proof (u_range E a) as Ua.
  destruct op; try discriminate; cbn [alu64 alu].
  - destruct (is_const b) as [k|] eqn:Hb; [|discriminate]. injection H as <-.
    destruct (is_const_sound E b k Hb) as [Hbk Hk]. rewrite Hbk.
    rewrite bv_shiftl_unsigned, bv_and_unsigned, !u_Z_to_bv. rewrite (Z.mod_small k) by exact Hk.
    rewrite (Z.mod_small 63) by (unfold two64; lia). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite <- Z.land_ones by lia. apply tn_sll_ok; [apply Z.land_nonneg; lia | exact Ta].
  - injection H as <-. rewrite bv_xor_unsigned. apply tn_xor_ok; assumption.
  - destruct (is_const b) as [k|] eqn:Hb; [|discriminate]. injection H as <-.
    destruct (is_const_sound E b k Hb) as [Hbk Hk]. rewrite Hbk.
    rewrite bv_shiftr_unsigned, bv_and_unsigned, !u_Z_to_bv. rewrite (Z.mod_small k) by exact Hk.
    rewrite (Z.mod_small 63) by (unfold two64; lia).
    apply tn_srl_ok; [change (2 ^ 64) with two64; exact Ua | apply Z.land_nonneg; lia | exact Ta].
  - injection H as <-. rewrite bv_or_unsigned. apply tn_or_ok; assumption.
  - injection H as <-. rewrite bv_and_unsigned. apply tn_and_ok; assumption.
Qed.

Lemma ev_alu0_sound : forall E fs op a b l, Forall (fact_ok E) fs -> ev_alu0 fs op a b = Some l ->
  lden E l = alu64 op (lden E a) (lden E b).
Proof.
  intros E fs op a b l HF H. unfold ev_alu0 in H.
  assert (Hgen : (match ev_alu_lin fs op a b with
                  | Some l => Some l
                  | None => match tn_alu fs op a b with Some (m, v) => if Z.eqb m (Z.ones 64) then Some (lconst v) else None | None => None end
                  end) = Some l -> lden E l = alu64 op (lden E a) (lden E b)).
  { intros H'. destruct (ev_alu_lin fs op a b) as [l'|] eqn:Hl.
    - injection H' as <-. exact (ev_alu_lin_sound E fs op a b l' HF Hl).
    - destruct (tn_alu fs op a b) as [[m v]|] eqn:Ht; [|discriminate].
      destruct (Z.eqb_spec m (Z.ones 64)) as [->|_]; [|discriminate]. injection H' as <-.
      pose proof (tn_alu_ok E fs op a b _ HF Ht) as Ht'. unfold tn_ok in Ht'. cbn [fst snd] in Ht'.
      rewrite Z.land_ones in Ht' by lia. pose proof (bv_unsigned_in_range _ (alu64 op (lden E a) (lden E b))) as R.
      unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R. rewrite Z.mod_small in Ht' by exact R.
      rewrite lden_lconst, <- Ht'. apply Z_to_bv_bv_unsigned. }
  assert (Hgen2 : match op with
                  | ALU_SLTU => match ev_br fs BC_LTU a b with Some t => Some (lconst (if t then 1 else 0)) | None => None end
                  | ALU_SLT => match ev_br fs BC_LT a b with Some t => Some (lconst (if t then 1 else 0)) | None => None end
                  | _ => match ev_alu_lin fs op a b with
                         | Some l => Some l
                         | None => match tn_alu fs op a b with Some (m, v) => if Z.eqb m (Z.ones 64) then Some (lconst v) else None | None => None end
                         end
                  end = Some l -> lden E l = alu64 op (lden E a) (lden E b)).
  { intros H'. destruct op; try exact (Hgen H').
    - destruct (ev_br fs BC_LT a b) as [t|] eqn:Hbr; [|discriminate]. injection H' as <-.
      pose proof (ev_br_sound E fs BC_LT a b t HF Hbr) as Ht. cbn [branch_taken] in Ht. cbn [alu64 alu]. rewrite Ht, lden_lconst.
      destruct t; reflexivity.
    - destruct (ev_br fs BC_LTU a b) as [t|] eqn:Hbr; [|discriminate]. injection H' as <-.
      pose proof (ev_br_sound E fs BC_LTU a b t HF Hbr) as Ht. cbn [branch_taken] in Ht. cbn [alu64 alu]. rewrite Ht, lden_lconst.
      destruct t; reflexivity. }
  destruct (is_const a) as [x|] eqn:Ha; destruct (is_const b) as [y|] eqn:Hb; try exact (Hgen2 H).
  injection H as <-. destruct (is_const_sound E a x Ha) as [-> Hx]. destruct (is_const_sound E b y Hb) as [-> Hy].
  unfold lden, lz; cbn [l_c l_t tsum]. rewrite Z.add_0_r, alu_z_ok by assumption. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma land_bandmask : forall x j k, 0 <= k <= j ->
  Z.land x (Z.land (- 2 ^ k) (Z.ones j)) = x mod 2 ^ j - x mod 2 ^ k.
Proof.
  intros x j k Hk.
  assert (Hn : - 2 ^ k = Z.lnot (Z.ones k)) by (rewrite Z.ones_equiv; unfold Z.lnot; lia).
  rewrite Hn. rewrite Z.land_comm with (a := Z.lnot (Z.ones k)). rewrite Z.land_assoc.
  rewrite Z.land_ones by lia. rewrite <- Z.ldiff_land. rewrite ldiff_ones_sub by lia.
  rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ (j - k)). rewrite <- Z.pow_add_r by lia. f_equal; lia.
Qed.
Lemma band_eq : forall j k, 0 <= k <= j -> 2 ^ j - 2 ^ k = Z.land (- 2 ^ k) (Z.ones j).
Proof.
  intros j k Hk. rewrite Z.land_ones by lia.
  assert (H1 : 2 ^ k <= 2 ^ j) by (apply Z.pow_le_mono_r; lia). assert (H2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  apply Z.mod_unique with (q := -1); [left; lia | ring].
Qed.

Lemma and_def_sound : forall E fs (a : lin) m n, Forall (fact_ok E) fs -> 0 <= m < two64 ->
  bv_unsigned (E n) = Z.land (bv_unsigned (lden E a)) m -> Forall (fact_ok E) (and_def fs a m (lvar n)).
Proof.
  intros E fs a m n HF Hm Hu. unfold and_def.
  set (k := ctz64 m) in *. set (j := Z.log2 (m + 2 ^ k)) in *.
  destruct (Z.ltb 0 k &&& Z.leb k 16 &&& (Z.eqb m (w64 (- 2 ^ k)) ||| (Z.ltb k j &&& Z.ltb j 64 &&& Z.eqb m (2 ^ j - 2 ^ k) &&&
            Z.ltb (snd (irange fs a)) (2 ^ j)))) eqn:Hc; [|constructor].
  apply andb_prop in Hc as [Hc Hcase]. apply andb_prop in Hc as [Hk1 Hk2]. apply Z.ltb_lt in Hk1. apply Z.leb_le in Hk2.
  constructor; [|constructor]. cbn [fact_ok].
  pose proof (u_range E a) as Ra. set (X := bv_unsigned (lden E a)) in *.
  assert (Hx : bv_unsigned (E n) = X - X mod 2 ^ k).
  { apply orb_prop in Hcase as [Hm2|Hband].
    - apply Z.eqb_eq in Hm2. rewrite Hu, Hm2. rewrite w64_land. unfold M64. change (2 ^ 64 - 1) with (Z.ones 64). rewrite land_himask by lia.
      rewrite (Z.mod_small X) by (unfold M64, two64 in *; lia). reflexivity.
    - apply andb_prop in Hband as [Hband Hlt]. apply andb_prop in Hband as [Hband Hm2]. apply andb_prop in Hband as [Hkj Hj64].
      apply Z.ltb_lt in Hkj, Hj64, Hlt. apply Z.eqb_eq in Hm2.
      pose proof (irange_sound E fs a HF) as Ia. fold X in Ia.
      rewrite Hu, Hm2, band_eq, land_bandmask by lia. rewrite (Z.mod_small X (2 ^ j)) by lia. reflexivity. }
  rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hx. fold X. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound X (2 ^ k) Hpk) as Hmb.
  replace (X - (X - X mod 2 ^ k)) with (X mod 2 ^ k) by ring. rewrite Z.mod_small by (unfold two64; split; [lia|]; assert (2 ^ k <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia); lia).
  lia.
Qed.

Lemma xor_nz_sound : forall E fs a b n, Forall (fact_ok E) fs -> E n = alu64 ALU_XOR (lden E a) (lden E b) ->
  Forall (fact_ok E) (xor_nz fs a b (lvar n)).
Proof.
  intros E fs a b n HF Hn. unfold xor_nz. destruct (Z.leb 1 (fst (irange fs (lsub a b)))) eqn:H; [|constructor].
  apply Z.leb_le in H. constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hn.
  pose proof (irange_sound E fs (lsub a b) HF) as R. pose proof (u_range E (lvar n)) as Ru. rewrite lden_lvar, Hn in Ru.
  split; [|unfold M64, two64 in *; lia].
  destruct (Z.eq_dec (bv_unsigned (alu64 ALU_XOR (lden E a) (lden E b))) 0) as [Hz|Hz]; [|lia].
  exfalso. cbn [alu64 alu] in Hz. rewrite bv_xor_unsigned in Hz. apply Z.lxor_eq in Hz.
  rewrite lden_lsub, bv_sub_unsigned, Hz, Z.sub_diag in R. cbn [fst snd] in R. unfold bv_wrap in R.
  rewrite Z.mod_0_l in R by (change (bv_modulus 64) with two64; unfold two64; lia). lia.
Qed.

Lemma res_facts_sound : forall E fs op a b n, Forall (fact_ok E) fs -> E n = alu64 op (lden E a) (lden E b) ->
  Forall (fact_ok E) (res_facts fs op a b (lvar n)).
Proof.
  intros E fs op a b n HF Hn. unfold res_facts. apply Forall_app. split.
  2: { destruct (tn_alu fs op a b) as [[m v]|] eqn:Ht; [|constructor]. destruct (Z.eqb m 0); [constructor|].
       constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hn. exact (tn_alu_ok E fs op a b _ HF Ht). }
  destruct op; try (constructor; fail); try (exact (bits_facts_sound E fs _ a b n E HF Hn));
    try (apply Forall_app; split; [exact (xor_nz_sound E fs a b n HF Hn) | exact (bits_facts_sound E fs _ a b n E HF Hn)]).
  - (* [comment removed for export] *) constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hn. cbn [alu64 alu].
    destruct (bv_lts _ _); rewrite u_small64 by (unfold two64; lia); lia.
  - (* [comment removed for export] *) constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hn. cbn [alu64 alu].
    destruct (bv_ltu _ _); rewrite u_small64 by (unfold two64; lia); lia.
  - (* [comment removed for export] *)
    destruct (is_const b) as [kb|] eqn:Hb; [|constructor].
    destruct (is_const_sound E b kb Hb) as [Hbk Hk].
    assert (Hk' : 0 <= Z.land kb 63 <= 63) by (split; [apply Z.land_nonneg; lia | apply land_le_r; lia]).
    assert (Hu : bv_unsigned (E n) = Z.shiftr (bv_unsigned (lden E a)) (Z.land kb 63)).
    { rewrite Hn, Hbk. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, bv_and_unsigned, !u_Z_to_bv. rewrite (Z.mod_small kb) by exact Hk.
      rewrite (Z.mod_small 63) by (unfold two64; lia). reflexivity. }
    set (k := Z.land kb 63) in *.
    pose proof (u_range E a) as Ra. pose proof (irange_sound E fs a HF) as Ia.
    assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    constructor; [|constructor; [| exact (proj2 (Forall_app _ _ _) (conj (srl_div_sound E fs k a n HF Hu) (srl_facts_sound E fs k a n HF Hu)))]]; cbn [fact_ok].
    + rewrite lden_lvar, Hu, !Z.shiftr_div_pow2 by lia. split; apply Z.div_le_mono; lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lscale, lden_lvar, u_Z_to_bv, Hu. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. rewrite Z.shiftr_div_pow2 by lia.
      pose proof (Z.div_mod (bv_unsigned (lden E a)) (2 ^ k) ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound (bv_unsigned (lden E a)) (2 ^ k) Hpk) as Hmb.
      assert (Hq0 : 0 <= bv_unsigned (lden E a) / 2 ^ k) by (apply Z.div_pos; lia).
      rewrite (Z.mod_small (2 ^ k * (bv_unsigned (lden E a) / 2 ^ k))) by (unfold two64 in *; nia).
      rewrite Z.mod_small by (unfold two64 in *; nia). lia.
  - (* [comment removed for export] *)
    assert (Hg : forall m, 0 <= m < two64 -> bv_unsigned (E n) = Z.land (bv_unsigned (lden E a)) (bv_unsigned (lden E b)) ->
               (bv_unsigned (lden E a) = m \/ bv_unsigned (lden E b) = m) ->
               Forall (fact_ok E) [FRange (lvar n) 0 m; FMod (lvar n) (ctz64 m) 0]).
    { intros m Hm Hu Hor. pose proof (u_range E a) as Ra. pose proof (u_range E b) as Rb.
      constructor; [|constructor; [|constructor]]; cbn [fact_ok]; rewrite lden_lvar, Hu.
      - split; [apply Z.land_nonneg; lia|].
        destruct Hor as [Hor|Hor]; rewrite <- Hor; [apply land_le_l | apply land_le_r]; lia.
      - destruct Hor as [Hor|Hor]; rewrite <- Hor; [rewrite Z.land_comm|]; apply land_ctz_mod; rewrite Hor; exact Hm. }
    assert (Hu : bv_unsigned (E n) = Z.land (bv_unsigned (lden E a)) (bv_unsigned (lden E b)))
      by (rewrite Hn; cbn [alu64 alu]; apply bv_and_unsigned).
    apply Forall_app. split; [|exact (bits_facts_sound E fs ALU_AND a b n E HF Hn)].
    destruct (is_const b) as [m|] eqn:Hb.
    + destruct (is_const_sound E b m Hb) as [Hbm Hm]. apply Forall_app. split.
      * apply Hg; [exact Hm | exact Hu | right; rewrite Hbm; apply u_small64; exact Hm].
      * apply and_def_sound; [exact HF | exact Hm|]. rewrite Hu, Hbm, u_small64 by exact Hm. reflexivity.
    + destruct (is_const a) as [m|] eqn:Ha; [|constructor].
      destruct (is_const_sound E a m Ha) as [Ham Hm]. apply Forall_app. split.
      * apply Hg; [exact Hm | exact Hu | left; rewrite Ham; apply u_small64; exact Hm].
      * apply and_def_sound; [exact HF | exact Hm|]. rewrite Hu, Ham, u_small64 by exact Hm. apply Z.land_comm.
Qed.

(* [comment removed for export] *)
Lemma sext_low32_id : forall x : word, (bv_unsigned x < 2147483648 \/ two64 - 2147483648 <= bv_unsigned x) ->
  sext 64 (low32 x) = x.
Proof.
  intros x Hx. apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned. unfold low32. rewrite bv_extract_signed, Z.shiftr_0_r.
  pose proof (bv_unsigned_in_range _ x) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 64) with two64 in Hr.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with two64.
  change (4294967296 `div` 2) with 2147483648. unfold two64 in *.
  destruct Hx as [Hx|Hx].
  - rewrite (Z.mod_small (bv_unsigned x + 2147483648) 4294967296) by lia.
    rewrite Z.mod_small by lia. lia.
  - replace (bv_unsigned x + 2147483648) with ((bv_unsigned x - 18446744071562067968) + 4294967296 * 4294967296) by ring.
    rewrite Z_mod_plus_full. rewrite (Z.mod_small (bv_unsigned x - 18446744071562067968)) by lia.
    replace (bv_unsigned x - 18446744071562067968 - 2147483648) with (bv_unsigned x + (-1) * 18446744073709551616) by ring.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma t_riv_sound : forall E fs t, Forall (fact_ok E) fs -> exists V, eqm V (tsum E t) /\ fst (t_riv fs t) <= V <= snd (t_riv fs t).
Proof.
  intros E fs t HF. induction t as [|[y k] t IH].
  - exists 0. split; [apply eqm_refl | cbn; lia].
  - destruct IH as (V & HV & HR).
    destruct (rel_iv_sound E fs fs (lvar y) (l_iv fs (lvar y)) HF HF
                (ex_intro _ (izl E (lvar y)) (conj (eqm_trans _ _ _ (izl_eqm E (lvar y)) (eqm_sym _ _ (u_eqm_lz E (lvar y)))) (l_iv_sound E fs (lvar y) HF))))
      as (v & Hv & Hr).
    set (w := rel_iv fs fs (lvar y) (l_iv fs (lvar y))) in *.
    destruct w as [wlo whi] eqn:Hw. cbn [fst snd] in Hr.
    pose proof (iv_scale_sound (sgn64 k) wlo whi v Hr) as Hs.
    exists (sgn64 k * v + V). split.
    + cbn [tsum]. apply eqm_add; [|exact HV]. apply eqm_mul; [apply sgn64_eqm|]. rewrite lden_lvar in Hv. unfold vz. exact Hv.
    + cbn [t_riv]. fold w. rewrite Hw. unfold iv_add. cbn [fst snd]. lia.
Qed.
Lemma sext32_1_sound : forall E fs r, Forall (fact_ok E) fs -> sext32_1 fs r = true ->
  bv_unsigned (lden E r) < 2147483648 \/ two64 - 2147483648 <= bv_unsigned (lden E r).
Proof.
  intros E fs r HF H. unfold sext32_1 in H. rewrite t_rivQ_eq in H. destruct (t_riv_sound E fs (l_t r) HF) as (V0 & HV0 & HR0).
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold iv_add in H1, H2. cbn [fst snd] in H1, H2.
  set (V := sgn64 (l_c r) + V0) in *.
  assert (Heq : eqm V (bv_unsigned (lden E r))).
  { eapply eqm_trans; [|apply eqm_sym, u_eqm_lz]. unfold lz, V. apply eqm_add; [apply sgn64_eqm | exact HV0]. }
  pose proof (u_range E r) as Ru. unfold eqm in Heq.
  destruct (Z_le_gt_dec 0 V) as [Hp|Hn].
  - left. rewrite Z.mod_small in Heq by (unfold two64; lia). rewrite (Z.mod_small (bv_unsigned _)) in Heq by exact Ru. lia.
  - right. rewrite (Z.mod_small (bv_unsigned _)) in Heq by exact Ru. rewrite <- Heq.
    replace V with ((V + two64) + (-1) * two64) by ring. rewrite Z_mod_plus_full. rewrite Z.mod_small by (unfold two64 in *; lia). unfold two64 in *. lia.
Qed.

Lemma sext32_ok_sound : forall E fs r, Forall (fact_ok E) fs -> sext32_ok fs r = true ->
  bv_unsigned (lden E r) < 2147483648 \/ two64 - 2147483648 <= bv_unsigned (lden E r).
Proof.
  intros E fs r HF H. unfold sext32_ok in H. apply orb_prop in H. destruct H as [H|H4]; [|exact (sext32_1_sound E fs r HF H4)].
  (* [comment removed for export] *)
  apply orb_prop in H. destruct H as [H|H];
    [|cbv zeta in H; apply orb_prop in H; destruct H as [H|H3];
      [|apply Z.leb_le in H3; pose proof (irange_sound E fs r HF) as Hr; right; lia]].
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (l_iv_sound E fs r HF) as Hiv. rewrite u_lden_mod.
    pose proof (izl_eqm E r) as He. unfold eqm in He. rewrite <- He.
    destruct (Z_le_gt_dec 0 (izl E r)) as [Hp|Hn].
    + left. rewrite Z.mod_small by (unfold two64; lia). lia.
    + right. replace (izl E r) with ((izl E r + two64) + (-1) * two64) by ring.
      rewrite Z_mod_plus_full. rewrite Z.mod_small by (unfold two64 in *; lia). unfold two64 in *. lia.
  - apply Z.ltb_lt in H. pose proof (irange_sound E fs r HF) as Hr. left. lia.
Qed.

Lemma low32_add : forall x y : word, low32 (x + y)%bv = (low32 x + low32 y)%bv.
Proof. intros x y. unfold low32. apply bv_extract_0_bv_add_distr. lia. Qed.

Lemma low32_u : forall x : word, bv_unsigned (low32 x) = bv_unsigned x mod 4294967296.
Proof. intros x. unfold low32. rewrite bv_extract_0_unsigned. reflexivity. Qed.

Lemma mod32_of_mod64 : forall z, (z mod two64) mod 4294967296 = z mod 4294967296.
Proof.
  intros z. unfold two64. rewrite (Z.mod_eq z 18446744073709551616) by lia.
  replace (z - 18446744073709551616 * (z / 18446744073709551616)) with (z + (- (4294967296 * (z / 18446744073709551616))) * 4294967296) by ring.
  apply Z_mod_plus_full.
Qed.

Lemma low32_sub : forall x y : word, low32 (x - y)%bv = (low32 x - low32 y)%bv.
Proof.
  intros x y. apply bv_eq. rewrite bv_sub_unsigned, !low32_u, bv_sub_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with two64. rewrite mod32_of_mod64.
  rewrite Zminus_mod. rewrite (Zminus_mod (bv_unsigned x mod 4294967296)). rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma low32_mul : forall x y : word, low32 (x * y)%bv = (low32 x * low32 y)%bv.
Proof.
  intros x y. apply bv_eq. rewrite bv_mul_unsigned, !low32_u, bv_mul_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with two64. rewrite mod32_of_mod64.
  rewrite Zmult_mod. rewrite (Zmult_mod (bv_unsigned x mod 4294967296)). rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma low32_sll : forall (x : word) (k : Z), 0 <= k < two64 ->
  (low32 x ≪ bv_and (low32 (Z_to_bv 64 k)) (Z_to_bv 32 31))%bv = low32 (Z_to_bv 64 (2 ^ Z.land k 31 * bv_unsigned x)).
Proof.
  intros x k Hk. apply bv_eq. rewrite bv_shiftl_unsigned, bv_and_unsigned, !low32_u, !u_Z_to_bv.
  rewrite (Z.mod_small k two64) by exact Hk. rewrite mod32_of_mod64.
  change (bv_unsigned (Z_to_bv 32 31)) with 31.
  assert (Hl : Z.land (k mod 4294967296) 31 = Z.land k 31).
  { change 31 with (Z.ones 5). rewrite !Z.land_ones by lia. change (2 ^ 5) with 32.
    rewrite (Z.mod_eq k 4294967296) by lia.
    replace (k - 4294967296 * (k / 4294967296)) with (k + (- (134217728 * (k / 4294967296))) * 32) by ring.
    apply Z_mod_plus_full. }
  rewrite Hl. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  assert (Hj : 0 <= Z.land k 31 <= 31).
  { pose proof (Z.land_ones k 5 ltac:(lia)) as Eo. change (Z.ones 5) with 31 in Eo. change (2 ^ 5) with 32 in Eo. rewrite Eo.
    pose proof (Z.mod_pos_bound k 32 ltac:(lia)). lia. }
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Zmult_mod, Z.mod_mod by lia. rewrite <- Zmult_mod. f_equal. ring.
Qed.

Lemma nw32_low32 : forall E r, low32 (lden E (nw32 r)) = low32 (lden E r).
Proof.
  intros E [c t]. apply bv_eq. rewrite !low32_u. unfold nw32, lden, lz. cbn [l_c l_t]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite !mod32_of_mod64.
  rewrite w64_mod. rewrite Z.add_mod, (Z.add_mod c) by lia. f_equal. f_equal.
  rewrite mod32_of_mod64. unfold sx32. destruct (Z.leb 2147483648 (c mod 4294967296)).
  - replace (c mod 4294967296 - 4294967296) with (c mod 4294967296 + (-1) * 4294967296) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
  - apply Z.mod_mod. lia.
Qed.

Lemma lin_w_low32 : forall E op a b r, lin_w op a b = Some r ->
  alu32 op (low32 (lden E a)) (low32 (lden E b)) = low32 (lden E r).
Proof.
  intros E op a b r H. destruct op; cbn [lin_w] in H; try discriminate.
  - injection H as <-. rewrite nw32_low32, lden_ladd. cbn [alu32 alu]. symmetry. apply low32_add.
  - injection H as <-. rewrite nw32_low32, lden_lsub. cbn [alu32 alu]. symmetry. apply low32_sub.
  - destruct (is_const b) as [k|] eqn:Hb; [|discriminate]. injection H as <-.
    rewrite nw32_low32. destruct (is_const_sound E b k Hb) as [Hbk Hk]. rewrite Hbk, lden_lscale. cbn [alu32 alu]. apply low32_sll. exact Hk.
Qed.

Lemma sext_low32_mod : forall (R : word) k, 0 <= k <= 32 -> bv_unsigned (sext 64 (low32 R)) mod 2 ^ k = bv_unsigned R mod 2 ^ k.
Proof.
  intros R k Hk. unfold sext. rewrite bv_sign_extend_unsigned. unfold low32. rewrite bv_extract_signed, Z.shiftr_0_r.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ Z.of_N 32) with (2 ^ 32).
  assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mod_mod_divide by (apply pow2_divide_le; lia).
  set (h := 2 ^ 32 / 2). set (z := bv_unsigned R).
  rewrite (Z.mod_eq (z + h) (2 ^ 32)) by lia.
  replace (z + h - 2 ^ 32 * ((z + h) / 2 ^ 32) - h) with (z + (- ((z + h) / 2 ^ 32) * 2 ^ (32 - k)) * 2 ^ k).
  2: { rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. replace (32 - k + k) with 32 by lia. ring. }
  apply Z_mod_plus_full.
Qed.

(* [comment removed for export] *)
Lemma swrap32_int : forall w z, eqm w z -> - 2147483648 <= z < 2147483648 -> bv_swrap 32 w = z.
Proof.
  intros w z He Hz. unfold eqm in He. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  assert (H32 : w mod 4294967296 = z mod 4294967296).
  { rewrite (Znumtheory.Zmod_div_mod 4294967296 two64 w) by (unfold two64; try lia; exists 4294967296; reflexivity).
    rewrite (Znumtheory.Zmod_div_mod 4294967296 two64 z) by (unfold two64; try lia; exists 4294967296; reflexivity).
    rewrite He. reflexivity. }
  rewrite Zplus_mod, H32, <- Zplus_mod. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land31_low32 : forall kb, bv_unsigned (bv_and (low32 (Z_to_bv 64 kb)) (Z_to_bv 32 31)) = Z.land kb 31.
Proof.
  intros kb. rewrite bv_and_unsigned, low32_unsigned, Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 32 31)) with (Z.ones 5).
  rewrite !Z.land_ones by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
  rewrite <- (Znumtheory.Zmod_div_mod (2 ^ 5) (2 ^ 32) (kb mod 2 ^ 64)) by (try lia; exists (2 ^ 27); reflexivity).
  rewrite <- (Znumtheory.Zmod_div_mod (2 ^ 5) (2 ^ 64) kb) by (try lia; exists (2 ^ 59); reflexivity).
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma sra_w_val : forall (A : word) kb z, eqm (bv_unsigned A) z -> - 2147483648 <= z < 2147483648 ->
  bv_unsigned (sext 64 (alu32 ALU_SRA (low32 A) (low32 (Z_to_bv 64 kb)))) = bv_wrap 64 (bv_swrap 32 (Z.shiftr z (Z.land kb 31))).
Proof.
  intros A kb z He Hz. rewrite sext32_unsigned. f_equal.
  change (alu32 ALU_SRA (low32 A) (low32 (Z_to_bv 64 kb))) with (bv_ashiftr (low32 A) (bv_and (low32 (Z_to_bv 64 kb)) (Z_to_bv 32 31))).
  rewrite bv_ashiftr_unsigned, low32_signed, bv_swrap_wrap'.
  rewrite (swrap32_int (bv_unsigned A) z He Hz). f_equal. f_equal.
  apply land31_low32.
Qed.
Lemma sra_w_facts_sound : forall E fs op a b n (E'' : valu), Forall (fact_ok E) fs ->
  E'' n = sext 64 (alu32 op (low32 (lden E a)) (low32 (lden E b))) -> Forall (fact_ok E'') (sra_w_facts fs op a b (lvar n)).
Proof.
  intros E fs op a b n E'' HF Hn. unfold sra_w_facts. destruct op; try constructor.
  destruct (is_const b) as [kb|] eqn:Hb; [|constructor].
  destruct (Z.leb (-2147483648) (fst (l_iv fs a)) && Z.ltb (snd (l_iv fs a)) 2147483648)%bool eqn:Hw; [|constructor].
  apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.ltb_lt in Hw2.
  constructor; [|constructor]. cbn [fact_ok]. rewrite lden_laddc, lden_lvar, Hn.
  destruct (is_const_sound E b kb Hb) as [Eb _]. rewrite Eb.
  pose proof (l_iv_sound E fs a HF) as Hiv.
  assert (He : eqm (bv_unsigned (lden E a)) (izl E a)).
  { eapply eqm_trans; [apply u_eqm_lz|]. apply eqm_sym. apply izl_eqm. }
  set (z := izl E a) in *. set (k := Z.land kb 31) in *.
  assert (Hk : 0 <= k) by (unfold k; apply Z.land_nonneg; lia).
  rewrite (sra_w_val (lden E a) kb z He ltac:(lia)). fold k.
  set (lo := Z.shiftr (fst (l_iv fs a)) k). set (hi := Z.shiftr (snd (l_iv fs a)) k).
  assert (Hs : lo <= Z.shiftr z k <= hi).
  { unfold lo, hi. rewrite !Z.shiftr_div_pow2 by exact Hk. split; apply Z.div_le_mono; try (apply Z.pow_pos_nonneg; lia); lia. }
  assert (Hs2 : - 2147483648 <= Z.shiftr z k < 2147483648).
  { rewrite Z.shiftr_div_pow2 by exact Hk. assert (Hp : 1 <= 2 ^ k) by (apply (Z.pow_le_mono_r 2 0 k); lia).
    split.
    - apply Z.div_le_lower_bound; [lia|]. assert (2 ^ k * -2147483648 <= -2147483648) by lia. lia.
    - apply Z.div_lt_upper_bound; [lia|]. assert (2147483648 <= 2 ^ k * 2147483648) by lia. lia. }
  rewrite (swrap32_int (Z.shiftr z k) (Z.shiftr z k) (eqm_refl _) Hs2).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small.
  - lia.
  - assert (hi - lo < 2 ^ 64).
    { unfold lo, hi. rewrite !Z.shiftr_div_pow2 by exact Hk. assert (Hp : 1 <= 2 ^ k) by (apply (Z.pow_le_mono_r 2 0 k); lia).
      assert (fst (l_iv fs a) / 2 ^ k >= - 2147483648).
      { apply Z.le_ge. apply Z.div_le_lower_bound; [lia|]. assert (2 ^ k * -2147483648 <= -2147483648) by lia. lia. }
      assert (snd (l_iv fs a) / 2 ^ k < 2147483648).
      { apply Z.div_lt_upper_bound; [lia|]. assert (2147483648 <= 2 ^ k * 2147483648) by lia. lia. }
      lia. }
    lia.
Qed.
Lemma w_facts_sound : forall E fs op a b n (E'' : valu), Forall (fact_ok E) fs ->
  E'' n = sext 64 (alu32 op (low32 (lden E a)) (low32 (lden E b))) -> Forall (fact_ok E'') (w_facts fs op a b (lvar n)).
Proof.
  intros E fs op a b n E'' HF Hn. unfold w_facts. apply Forall_app. split; [|exact (sra_w_facts_sound E fs op a b n E'' HF Hn)].
  destruct (lin_w op a b) as [r|] eqn:Hw; [|constructor].
  destruct (Z.ltb 0 (Z.min 32 (lalign fs r))) eqn:Hk; [|constructor]. apply Z.ltb_lt in Hk.
  constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hn, (lin_w_low32 E op a b r Hw).
  destruct (lalign_sound E fs r HF) as [Hb Hd].
  rewrite sext_low32_mod by lia. apply Z.mod_divide; [apply Z.pow_nonzero; lia|].
  apply Z.divide_trans with (2 ^ lalign fs r); [apply pow2_divide_le; lia | exact Hd].
Qed.

Lemma ev_aluw0_sound : forall E fs op a b l, Forall (fact_ok E) fs -> ev_aluw0 fs op a b = Some l ->
  lden E l = sext 64 (alu32 op (low32 (lden E a)) (low32 (lden E b))).
Proof.
  intros E fs op a b l HF H. unfold ev_aluw0 in H.
  assert (Hsym : match lin_w op a b with Some r => if sext32_ok fs r then Some r else None | None => None end = Some l ->
                 lden E l = sext 64 (alu32 op (low32 (lden E a)) (low32 (lden E b)))).
  { intros H'. destruct (lin_w op a b) as [r|] eqn:Hw; [|discriminate]. destruct (sext32_ok fs r) eqn:Hs; [|discriminate].
    injection H' as <-. rewrite (lin_w_low32 E op a b r Hw). symmetry. apply sext_low32_id. exact (sext32_ok_sound E fs r HF Hs). }
  destruct (is_const a) as [x|] eqn:Ha; destruct (is_const b) as [y|] eqn:Hb; try (exact (Hsym H)).
  injection H as <-. destruct (is_const_sound E a x Ha) as [-> _]. destruct (is_const_sound E b y Hb) as [-> _].
  rewrite lden_lconst. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma land_low_mod : forall (z : Z) k, 0 <= z -> 0 <= k -> Z.land z (Z.ones k) = z mod 2 ^ k.
Proof. intros z k Hz Hk. apply Z.land_ones. exact Hk. Qed.

Lemma sh_amt_alu64 : forall E fs op b x, Forall (fact_ok E) fs -> alu64 op x (lden E (sh_amt fs op 6 b)) = alu64 op x (lden E b).
Proof.
  intros E fs op b x HF. unfold sh_amt. destruct (shift_op op) eqn:Hs; [|reflexivity].
  destruct (is_const b) as [c0|]; [reflexivity|]. destruct (lowb fs b 6) as [c|] eqn:Hl; [|reflexivity].
  pose proof (lowb_sound E fs b 6 c HF Hl) as Hc.
  pose proof (bv_unsigned_in_range _ (lden E b)) as Rb.
  assert (Hc0 : 0 <= c < 64) by (rewrite <- Hc; apply Z.mod_pos_bound; lia).
  assert (Hand : bv_and (lden E (lconst c)) (Z_to_bv 64 63) = bv_and (lden E b) (Z_to_bv 64 63)).
  { apply bv_eq. rewrite !bv_and_unsigned. rewrite lden_lconst. rewrite !Z_to_bv_unsigned.
    change (bv_wrap 64 63) with (Z.ones 6). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small c) by lia. rewrite !Z.land_ones by lia. rewrite Hc. apply Z.mod_small. lia. }
  destruct op; try discriminate; unfold alu64, alu; rewrite Hand; reflexivity.
Qed.
Lemma ev_alu_sound : forall E fs op a b l, Forall (fact_ok E) fs -> ev_alu fs op a b = Some l ->
  lden E l = alu64 op (lden E a) (lden E b).
Proof.
  intros E fs op a b l HF H. unfold ev_alu in H. rewrite (ev_alu0_sound E fs op a _ l HF H). apply sh_amt_alu64. exact HF.
Qed.

Lemma low32_land31 : forall v : word, Z.land (bv_unsigned (low32 v)) (bv_unsigned (Z_to_bv 32 31)) = bv_unsigned v mod 32.
Proof.
  intros v. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r. change (bv_unsigned (Z_to_bv 32 31)) with (Z.ones 5).
  rewrite Z.land_ones by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 5) with 32.
  apply Z.mod_mod_divide. exists (2 ^ 27). reflexivity.
Qed.
Lemma sh_amt_alu32 : forall E fs op b x, Forall (fact_ok E) fs -> alu32 op x (low32 (lden E (sh_amt fs op 5 b))) = alu32 op x (low32 (lden E b)).
Proof.
  intros E fs op b x HF. unfold sh_amt. destruct (shift_op op) eqn:Hs; [|reflexivity].
  destruct (is_const b) as [c0|]; [reflexivity|]. destruct (lowb fs b 5) as [c|] eqn:Hl; [|reflexivity].
  pose proof (lowb_sound E fs b 5 c HF Hl) as Hc. change (2 ^ 5) with 32 in Hc.
  pose proof (bv_unsigned_in_range _ (lden E b)) as Rb.
  assert (Hc0 : 0 <= c < 32) by (rewrite <- Hc; apply Z.mod_pos_bound; lia).
  assert (Hand : bv_and (low32 (lden E (lconst c))) (Z_to_bv 32 31) = bv_and (low32 (lden E b)) (Z_to_bv 32 31)).
  { apply bv_eq. rewrite !bv_and_unsigned. rewrite !low32_land31. rewrite lden_lconst, Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small c) by lia. rewrite Hc. apply Z.mod_small. lia. }
  destruct op; try discriminate; unfold alu32, alu; rewrite Hand; reflexivity.
Qed.
Lemma ev_aluw_sound : forall E fs op a b l, Forall (fact_ok E) fs -> ev_aluw fs op a b = Some l ->
  lden E l = sext 64 (alu32 op (low32 (lden E a)) (low32 (lden E b))).
Proof.
  intros E fs op a b l HF H. unfold ev_aluw in H. rewrite (ev_aluw0_sound E fs op a _ l HF H). f_equal. apply sh_amt_alu32. exact HF.
Qed.


Lemma lscale_mul : forall E y a, 0 <= y < two64 -> lden E (lscale y a) = (lden E a * Z_to_bv 64 y)%bv.
Proof.
  intros E y a Hy. rewrite lden_lscale. apply bv_eq. rewrite bv_mul_unsigned, !u_Z_to_bv. rewrite (Z.mod_small y) by exact Hy.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. rewrite Z.mul_comm. reflexivity.
Qed.

Lemma ev_mul_sound : forall E op a b l, ev_mul op a b = Some l -> lden E l = mul_div op (lden E a) (lden E b).
Proof.
  intros E op a b l H. unfold ev_mul in H.
  destruct (is_const a) as [x|] eqn:Ha; destruct (is_const b) as [y|] eqn:Hb.
  - injection H as <-. destruct (is_const_sound E a x Ha) as [-> _]. destruct (is_const_sound E b y Hb) as [-> _].
    rewrite lden_lconst. apply Z_to_bv_bv_unsigned.
  - destruct op; try discriminate. injection H as <-. destruct (is_const_sound E a x Ha) as [Hax Hx].
    rewrite lscale_mul by exact Hx. rewrite Hax. cbn [mul_div]. apply bv_eq. rewrite !bv_mul_unsigned. rewrite Z.mul_comm. reflexivity.
  - destruct op; try discriminate. injection H as <-. destruct (is_const_sound E b y Hb) as [Hby Hy].
    rewrite lscale_mul by exact Hy. rewrite Hby. reflexivity.
  - discriminate.
Qed.

Lemma ev_mulf_sound : forall E fs op a b l, Forall (fact_ok E) fs -> ev_mulf fs op a b = Some l -> lden E l = mul_div op (lden E a) (lden E b).
Proof.
  intros E fs op a b l HF H. unfold ev_mulf in H.
  assert (Hpow : forall m, (Z.eqb m (2 ^ ctz64 m) && Z.leb (ctz64 m) 63)%bool = true -> 0 <= ctz64 m <= 63 /\ m = 2 ^ ctz64 m).
  { intros m Hm. apply andb_prop in Hm as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. pose proof (ctz64_spec m) as [Hc _]. split; [lia | exact H1]. }
  destruct op; try exact (ev_mul_sound E _ a b l H);
    destruct (is_const b) as [m|] eqn:Hb; try exact (ev_mul_sound E _ a b l H);
    destruct (is_const a) as [x|] eqn:Ha; try exact (ev_mul_sound E _ a b l H).
  - (* [comment removed for export] *)
    destruct (Z.eqb m (2 ^ ctz64 m) && Z.leb (ctz64 m) 63)%bool eqn:Hm; [|discriminate].
    destruct (Hpow m Hm) as [Hk Hmk]. destruct (is_const_sound E b m Hb) as [Hbm Hmr].
    pose proof (srl_lin_sound E fs (ctz64 m) a l HF Hk H) as Hs.
    apply bv_eq. rewrite Hs, Hbm. cbn [mul_div]. rewrite u_Z_to_bv, Z.mod_small by exact Hmr.
    assert (Hm0 : m <> 0) by (rewrite Hmk; apply Z.pow_nonzero; lia). rewrite (proj2 (Z.eqb_neq m 0) Hm0).
    rewrite bv_divu_unsigned, u_Z_to_bv, Z.mod_small by exact Hmr. rewrite Hmk at 2. apply Z.shiftr_div_pow2. lia.
  - (* [comment removed for export] *)
    destruct (Z.eqb m (2 ^ ctz64 m) && Z.leb (ctz64 m) 63)%bool eqn:Hm; [|discriminate].
    destruct (Hpow m Hm) as [Hk Hmk]. destruct (is_const_sound E b m Hb) as [Hbm Hmr].
    destruct (lowb fs a (ctz64 m)) as [r|] eqn:Hlb; [|discriminate]. injection H as <-.
    pose proof (lowb_sound E fs a (ctz64 m) r HF Hlb) as Hr.
    apply bv_eq. rewrite Hbm. cbn [mul_div]. rewrite u_Z_to_bv, Z.mod_small by exact Hmr.
    assert (Hm0 : m <> 0) by (rewrite Hmk; apply Z.pow_nonzero; lia). rewrite (proj2 (Z.eqb_neq m 0) Hm0).
    rewrite bv_modu_unsigned, u_Z_to_bv, (Z.mod_small m two64) by exact Hmr. rewrite lden_lconst, u_Z_to_bv. rewrite <- Hmk in Hr. rewrite Hr.
    apply Z.mod_small. pose proof (Z.mod_pos_bound (bv_unsigned (lden E a)) m ltac:(rewrite Hmk; apply Z.pow_pos_nonneg; lia)) as Hb2.
    rewrite Hr in Hb2. unfold two64 in Hmr |- *. lia.
Qed.

Lemma ev_mulw_sound : forall E fs op a b l, Forall (fact_ok E) fs -> ev_mulw fs op a b = Some l ->
  lden E l = sext 64 (mul_div op (low32 (lden E a)) (low32 (lden E b))).
Proof.
  intros E fs op a b l HF H. unfold ev_mulw in H.
  assert (Hsym : match op with M_MUL => match ev_mul M_MUL a b with Some r => if sext32_ok fs r then Some r else None | None => None end
                             | _ => None end = Some l ->
                 lden E l = sext 64 (mul_div op (low32 (lden E a)) (low32 (lden E b)))).
  { intros H'. destruct op; try discriminate. destruct (ev_mul M_MUL a b) as [r|] eqn:Hw; [|discriminate].
    destruct (sext32_ok fs r) eqn:Hs; [|discriminate]. injection H' as <-.
    pose proof (sext32_ok_sound E fs r HF Hs) as Hr.
    rewrite (ev_mul_sound E M_MUL a b r Hw) in Hr |- *. cbn [mul_div] in Hr |- *. rewrite <- low32_mul. symmetry. apply sext_low32_id. exact Hr. }
  destruct (is_const a) as [x|] eqn:Ha; destruct (is_const b) as [y|] eqn:Hb; try (exact (Hsym H)).
  injection H as <-. destruct (is_const_sound E a x Ha) as [-> _]. destruct (is_const_sound E b y Hb) as [-> _].
  rewrite lden_lconst. apply Z_to_bv_bv_unsigned.
Qed.

Lemma lden_sext_imm : forall E {n} (imm : bv n), (0 < n)%N -> lden E (lconst (bv_unsigned (sext 64 imm))) = sext 64 imm.
Proof. intros. rewrite lden_lconst. apply Z_to_bv_bv_unsigned. Qed.

Lemma lden_const_word : forall E (w : word), lden E (lconst (bv_unsigned w)) = w.
Proof. intros. rewrite lden_lconst. apply Z_to_bv_bv_unsigned. Qed.

Lemma pc_plus4 : forall z, (Z_to_bv 64 z + Z_to_bv 64 4)%bv = Z_to_bv 64 (z + 4).
Proof.
  intros z. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Z.add_mod_idemp_l by lia. rewrite (Z.mod_small 4) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma addr_eq : forall E R regs (rs : reg) (imm : bv 12),
  regs_ok E R regs ->
  lden E (laddc (rget R (rkey rs)) (bv_unsigned (sext 64 imm))) = (getr regs rs + sext 64 imm)%bv.
Proof.
  intros E R regs rs imm HR. rewrite lden_laddc, <- HR. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma get_bytes_z_spec : forall t n o,
  length (get_bytes_z t o n) = n /\
  forall i v, nth_error (get_bytes_z t o n) i = Some v ->
    v = match tget (okey (o + Z.of_nat i)) t with Some v' => v' | None => BK 0 end.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t n. induction n as [|n IH]; intros o; cbn [get_bytes_z].
  - split; [reflexivity|]. intros [|i] v Hv; discriminate.
  - destruct (IH (o + 1)) as [Hlen Hnth]. split; [cbn; lia|].
    intros [|i] v Hv; cbn [nth_error] in Hv.
    + injection Hv as <-. rewrite Z.add_0_r. reflexivity.
    + rewrite (Hnth i v Hv). replace (o + 1 + Z.of_nat i) with (o + Z.of_nat (S i)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma extract_small : forall (w : word) (k : N), (k <= 64)%N -> bv_unsigned w < 2 ^ Z.of_N k -> bv_unsigned (bv_extract 0 k w) = bv_unsigned w.
Proof. LiaFast.lf_pins LiaFast.u0. intros w k Hk Hw. rewrite bv_extract_0_unsigned. apply bv_wrap_small. pose proof (bv_unsigned_in_range _ w). unfold bv_modulus. lia. Qed.
#[using="Type"] Lemma zext_extract_small : forall (w : word) (k : N), (k <= 64)%N -> bv_unsigned w < 2 ^ Z.of_N k -> zext 64 (bv_extract 0 k w) = w.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros w k Hk Hw. apply bv_eq. unfold zext. rewrite bv_zero_extend_unsigned by lia. exact (extract_small w k Hk Hw).
Qed.
#[using="Type"] Lemma sext_extract_small : forall (w : word) (k : N), (1 <= k <= 64)%N -> bv_unsigned w < 2 ^ (Z.of_N k - 1) -> sext 64 (bv_extract 0 k w) = w.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros w k Hk Hw. apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed.
  assert (Hp : 2 ^ (Z.of_N k - 1) <= 2 ^ Z.of_N k) by (apply Z.pow_le_mono_r; lia).
  assert (Hh : bv_half_modulus k = 2 ^ (Z.of_N k - 1)).
  { unfold bv_half_modulus, bv_modulus. replace (Z.of_N k) with (Z.succ (Z.of_N k - 1)) at 1 by lia.
    rewrite Z.pow_succ_r by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  rewrite (extract_small w k) by lia. rewrite bv_swrap_small.
  - apply bv_wrap_small, bv_unsigned_in_range.
  - rewrite Hh. pose proof (bv_unsigned_in_range _ w). pose proof (Z.pow_pos_nonneg 2 (Z.of_N k - 1) ltac:(lia) ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma ld_small_word : forall E fs v sz sg, Forall (fact_ok E) fs -> ld_small fs v sz sg = true ->
  ld_word sz sg (Z_to_le_bytes (nbytes sz) (bv_unsigned (lden E v))) = lden E v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs v sz sg HF Hsm. unfold ld_word, le_bytes_to_word. rewrite bytes_le_to_Z_of_le_bytes by (apply bv_unsigned_in_range).
  pose proof (irange_sound E fs v HF) as Hr. pose proof (bv_unsigned_in_range _ (lden E v)) as Rv. unfold bv_modulus in Rv.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rv.
  destruct sz; cbn [ld_small nbytes] in Hsm |- *.
  - change (2 ^ (8 * Z.of_nat 1)) with 256. destruct sg; apply Z.ltb_lt in Hsm.
    + rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. apply sext_extract_small; [lia | cbn; lia].
    + rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. apply zext_extract_small; [lia | cbn; lia].
  - change (2 ^ (8 * Z.of_nat 2)) with 65536. destruct sg; apply Z.ltb_lt in Hsm.
    + rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. apply sext_extract_small; [lia | cbn; lia].
    + rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. apply zext_extract_small; [lia | cbn; lia].
  - change (2 ^ (8 * Z.of_nat 4)) with 4294967296. destruct sg; apply Z.ltb_lt in Hsm.
    + rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. apply sext_extract_small; [lia | cbn; lia].
    + rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. apply zext_extract_small; [lia | cbn; lia].
  - change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616. rewrite Z.mod_small by exact Rv. rewrite Z_to_bv_bv_unsigned.
    apply bv_eq. rewrite bv_extract_0_unsigned. apply bv_wrap_bv_unsigned.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sext_extract_neg : forall (w : word) (k : N), (1 <= k <= 63)%N -> 2 ^ (Z.of_N k - 1) <= bv_unsigned w < 2 ^ Z.of_N k ->
  sext 64 (bv_extract 0 k w) = Z_to_bv 64 (bv_unsigned w + 18446744073709551616 - 2 ^ Z.of_N k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros w k Hk Hw. apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed.
  assert (Hh : bv_half_modulus k = 2 ^ (Z.of_N k - 1)).
  { unfold bv_half_modulus, bv_modulus. replace (Z.of_N k) with (Z.succ (Z.of_N k - 1)) at 1 by lia.
    rewrite Z.pow_succ_r by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  assert (H2 : 2 ^ Z.of_N k = 2 * 2 ^ (Z.of_N k - 1)).
  { replace (Z.of_N k) with (Z.succ (Z.of_N k - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
  assert (H64 : 2 ^ Z.of_N k <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  rewrite (extract_small w k) by lia. unfold bv_swrap. rewrite Hh. unfold bv_wrap, bv_modulus.
  rewrite <- (Z.mod_unique (bv_unsigned w + 2 ^ (Z.of_N k - 1)) (2 ^ Z.of_N k) 1 (bv_unsigned w + 2 ^ (Z.of_N k - 1) - 2 ^ Z.of_N k)) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite (Z.mod_small (bv_unsigned w + 18446744073709551616 - 2 ^ Z.of_N k)) by lia.
  rewrite <- (Z.mod_unique (bv_unsigned w + 2 ^ (Z.of_N k - 1) - 2 ^ Z.of_N k - 2 ^ (Z.of_N k - 1)) 18446744073709551616 (-1)
                 (bv_unsigned w + 18446744073709551616 - 2 ^ Z.of_N k)) by lia.
  reflexivity.
Qed.
#[using="Type"] Lemma ld_neg_word : forall E fs v sz l, Forall (fact_ok E) fs -> ld_neg fs v sz = Some l ->
  ld_word sz true (Z_to_le_bytes (nbytes sz) (bv_unsigned (lden E v))) = lden E l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs v sz l HF Hn. unfold ld_word, le_bytes_to_word. rewrite bytes_le_to_Z_of_le_bytes by (apply bv_unsigned_in_range).
  pose proof (irange_sound E fs v HF) as Hr. pose proof (bv_unsigned_in_range _ (lden E v)) as Rv. unfold bv_modulus in Rv.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rv.
  unfold ld_neg in Hn. destruct sz; cbn [nbytes] in *; [| | |discriminate].
  - destruct (Z.leb 128 (fst (irange fs v)) && Z.leb (snd (irange fs v)) 255)%bool eqn:Hc; [|discriminate]. injection Hn as <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2. change (2 ^ (8 * Z.of_nat 1)) with 256.
    rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. rewrite (sext_extract_neg (lden E v) 8) by (cbn; lia).
    rewrite lden_ladd, lden_lconst. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616. unfold two64. rewrite Zplus_mod_idemp_r. f_equal. cbn. lia.
  - destruct (Z.leb 32768 (fst (irange fs v)) && Z.leb (snd (irange fs v)) 65535)%bool eqn:Hc; [|discriminate]. injection Hn as <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2. change (2 ^ (8 * Z.of_nat 2)) with 65536.
    rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. rewrite (sext_extract_neg (lden E v) 16) by (cbn; lia).
    rewrite lden_ladd, lden_lconst. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616. unfold two64. rewrite Zplus_mod_idemp_r. f_equal. cbn. lia.
  - destruct (Z.leb 2147483648 (fst (irange fs v)) && Z.leb (snd (irange fs v)) 4294967295)%bool eqn:Hc; [|discriminate]. injection Hn as <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
    rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. rewrite (sext_extract_neg (lden E v) 32) by (cbn; lia).
    rewrite lden_ladd, lden_lconst. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with 18446744073709551616. unfold two64. rewrite Zplus_mod_idemp_r. f_equal. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition mix_tv (E : valu) (b : bval) : Z := match b with BK c => c | BV v _ => bv_unsigned (lden E v) end.
Fixpoint mix_val (E : valu) (bvs : list bval) : Z :=
  match bvs with [] => 0 | b :: r => mix_tv E b + 256 * mix_val E r end.
#[using="Type"] Lemma mix_term_ok : forall E fs b t, Forall (fact_ok E) fs -> mix_term fs b = Some t ->
  bv_unsigned (lden E t) = mix_tv E b /\ 0 <= mix_tv E b < 256 /\ bden E b = Z_to_bv 8 (mix_tv E b).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs b t HF H. destruct b as [c|v j]; cbn [mix_term] in H.
  - destruct (Z.leb 0 c && Z.ltb c 256)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1. cbn [mix_tv bden].
    split; [|split; [lia | reflexivity]]. rewrite lden_lconst, u_Z_to_bv. apply Z.mod_small. unfold two64. lia.
  - destruct j as [|j|j]; try discriminate.
    destruct (Z.leb 0 (fst (irange fs v)) && Z.ltb (snd (irange fs v)) 256)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
    pose proof (irange_sound E fs v HF) as Hr. cbn [mix_tv bden]. split; [reflexivity|]. split; [lia|].
    rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.
#[using="Type"] Lemma mix_lin_ok : forall E fs bvs p l, Forall (fact_ok E) fs -> mix_lin fs bvs p = Some l ->
  eqm (bv_unsigned (lden E l)) (p * mix_val E bvs) /\ 0 <= mix_val E bvs < 256 ^ Z.of_nat (length bvs) /\
  map (bden E) bvs = Z_to_le_bytes (length bvs) (mix_val E bvs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs bvs. induction bvs as [|b r IH]; intros p l HF H; cbn [mix_lin] in H.
  - injection H as <-. cbn [mix_val length map Z_to_le_bytes]. split; [|split; [cbn; lia | reflexivity]].
    rewrite Z.mul_0_r. eapply eqm_trans; [apply u_eqm_lz | apply lz_lconst].
  - destruct (mix_term fs b) as [t|] eqn:Ht; [|discriminate]. destruct (mix_lin fs r (256 * p)) as [l'|] eqn:Hl; [|discriminate].
    injection H as <-. destruct (mix_term_ok E fs b t HF Ht) as (Htv & Hb & Hbd). destruct (IH (256 * p) l' HF Hl) as (Hq & Hv & Hm).
    cbn [mix_val length map Z_to_le_bytes]. split; [|split].
    + eapply eqm_trans; [apply u_eqm_lz|]. eapply eqm_trans; [apply lz_ladd|].
      replace (p * (mix_tv E b + 256 * mix_val E r)) with (p * mix_tv E b + 256 * p * mix_val E r) by ring.
      apply eqm_add.
      * eapply eqm_trans; [apply lz_lscale|]. apply eqm_mul; [apply eqm_refl|]. rewrite <- Htv. apply eqm_sym, u_eqm_lz.
      * eapply eqm_trans; [apply eqm_sym, u_eqm_lz | exact Hq].
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
    + f_equal.
      * rewrite Hbd. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
        rewrite (Z.mul_comm 256 (mix_val E r)), Z.mod_add by lia. reflexivity.
      * rewrite Hm. f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
        rewrite (Z.mul_comm 256 (mix_val E r)), Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
#[using="Type"] Lemma pow256_le : forall n, (n <= 8)%nat -> 256 ^ Z.of_nat n <= two64.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n Hn. change 256 with (2 ^ 8). rewrite <- Z.pow_mul_r by lia. unfold two64. change 18446744073709551616 with (2 ^ 64).
  apply Z.pow_le_mono_r; lia.
Qed.
#[using="Type"] Lemma mix_lin_bytes : forall E fs bvs l, Forall (fact_ok E) fs -> (length bvs <= 8)%nat -> mix_lin fs bvs 1 = Some l ->
  map (bden E) bvs = Z_to_le_bytes (length bvs) (bv_unsigned (lden E l)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs bvs l HF Hlen H. destruct (mix_lin_ok E fs bvs 1 l HF H) as (Hq & Hv & Hm).
  rewrite Hm. f_equal. rewrite Z.mul_1_l in Hq. unfold eqm in Hq. rewrite (Z.mod_small (bv_unsigned _)) in Hq by apply u_range.
  rewrite Hq. symmetry. apply Z.mod_small. pose proof (pow256_le (length bvs) Hlen). lia.
Qed.

#[using="Type"] Lemma ld_bvs_sound : forall E fs bvs bs sz sg l, Forall (fact_ok E) fs -> bs = map (bden E) bvs -> length bvs = nbytes sz ->
  ld_bvs fs bvs sz sg = Some l -> lden E l = ld_word sz sg bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs bvs bs sz sg l HF Hbs Hlen Hl. subst bs. unfold ld_bvs in Hl.
  destruct (all_bk bvs) as [bks|] eqn:Hk.
  - injection Hl as <-. rewrite (all_bk_spec _ _ Hk). rewrite map_map. cbn [bden]. apply lden_const_word.
  - match type of Hl with (match ?o with Some _ => _ | None => _ end) = _ => destruct o as [l0|] eqn:Hold end.
    + injection Hl as <-.
      destruct bvs as [|x bvs']; [discriminate|]. destruct x as [b|v j]; [discriminate|].
      destruct j as [|j|j]; try discriminate.
      destruct (is_bv_of v 0 (BV v 0 :: bvs')) eqn:Hv; [|discriminate].
      pose proof (is_bv_of_spec v _ 0 Hv) as Hsp.
      set (k := nbytes sz) in *.
      assert (Hmap : map (bden E) (BV v 0 :: bvs') = Z_to_le_bytes k (bv_unsigned (lden E v))).
      { apply nth_error_ext. intros i. rewrite nth_error_map.
        destruct (Nat.lt_ge_cases i k) as [Hi|Hi].
        - rewrite nth_Z_to_le_bytes by exact Hi.
          destruct (nth_error (BV v 0 :: bvs') i) as [x|] eqn:Hx.
          + rewrite (Hsp i x Hx). cbn [bden option_map]. repeat f_equal; try lia.
          + apply nth_error_None in Hx. rewrite Hlen in Hx. lia.
        - replace (nth_error (BV v 0 :: bvs') i) with (@None bval) by (symmetry; apply nth_error_None; rewrite Hlen; lia).
          symmetry. apply nth_error_None. rewrite length_Z_to_le_bytes. lia. }
      rewrite Hmap. unfold k. destruct (ld_small fs v sz sg) eqn:Hsm.
      * injection Hold as <-. symmetry. exact (ld_small_word E fs v sz sg HF Hsm).
      * destruct sg; [|discriminate]. symmetry. exact (ld_neg_word E fs v sz l0 HF Hold).
    + (* [comment removed for export] *)
      unfold ld_mix in Hl. destruct (mix_lin fs bvs 1) as [lm|] eqn:Hm; [|discriminate].
      destruct (ld_small fs lm sz sg) eqn:Hsm; [|discriminate]. injection Hl as <-.
      assert (H8 : (length bvs <= 8)%nat) by (rewrite Hlen; destruct sz; cbn; lia).
      rewrite (mix_lin_bytes E fs bvs lm HF H8 Hm), Hlen. symmetry. exact (ld_small_word E fs lm sz sg HF Hsm).
Qed.

#[using="Type"] Lemma ld_rw_sound : forall E fs R m o sz sg bs, Forall (fact_ok E) fs ->
  rg_kind R = RW -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (nbytes sz) <= rsz E R ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (nbytes sz) = Some bs ->
  forall l, (match get_bytes (rg_cont R) o (nbytes sz) with Some bvs => ld_bvs fs bvs sz sg | None => None end) = Some l ->
  lden E l = ld_word sz sg bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs R m o sz sg bs HF Hk0 HR Ho Hn Hrd l Hl.
  destruct HR as (Hsz & Hflat & Hall & Hcont). rewrite Hk0 in Hall.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  destruct (get_bytes (rg_cont R) o (nbytes sz)) as [bvs|] eqn:Hg; [|discriminate].
  destruct (get_bytes_spec _ _ _ _ Hg) as [Hlen Hgn].
  apply (ld_bvs_sound E fs bvs bs sz sg l HF); [|exact Hlen | exact Hl].
  destruct (rdn_from segs m (nbytes sz) (A + o)) as (bs' & Hbs' & Hlen' & Hnth); [lia | lia | |].
  { intros i Hi. replace (A + o + i) with (A + (o + i)) by lia. apply (proj1 (Hall (o + i) ltac:(lia))). }
  rewrite Hrd in Hbs'. injection Hbs' as ->.
  apply nth_error_ext. intros i. rewrite nth_error_map.
  destruct (nth_error bvs i) as [x|] eqn:Hx.
  - pose proof (Hgn i x Hx) as Ht. destruct (Hcont _ _ Ht) as [_ Hrdx].
    rewrite okey_pos in Hrdx by lia.
    destruct (nth_error bs' i) as [b|] eqn:Hb.
    + pose proof (Hnth i b Hb) as Hrb. replace (A + o + Z.of_nat i) with (A + (o + Z.of_nat i)) in Hrb by lia.
      rewrite Hrb in Hrdx. exact Hrdx.
    + apply nth_error_None in Hb. assert (Hi' : (i < length bvs)%nat) by (apply nth_error_Some; rewrite Hx; discriminate). lia.
  - apply nth_error_None in Hx. cbn. apply nth_error_None. lia.
Qed.

#[using="Type"] Lemma ld_rt_sound : forall E fs R m o sz sg bs, Forall (fact_ok E) fs ->
  rg_kind R = RT -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (nbytes sz) <= rsz E R ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (nbytes sz) = Some bs ->
  forall l, (match get_bytes (rg_cont R) o (nbytes sz) with Some bvs => ld_bvs fs bvs sz sg | None => None end) = Some l ->
  lden E l = ld_word sz sg bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs R m o sz sg bs HF Hk0 HR Ho Hn Hrd l Hl.
  destruct HR as (Hsz & Hflat & Hall & Hcont). rewrite Hk0 in Hall.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  destruct (get_bytes (rg_cont R) o (nbytes sz)) as [bvs|] eqn:Hg; [|discriminate].
  destruct (get_bytes_spec _ _ _ _ Hg) as [Hlen Hgn].
  apply (ld_bvs_sound E fs bvs bs sz sg l HF); [|exact Hlen | exact Hl].
  destruct (rdn_from segs m (nbytes sz) (A + o)) as (bs' & Hbs' & Hlen' & Hnth); [lia | lia | |].
  { intros i Hi. replace (A + o + i) with (A + (o + i)) by lia. apply (Hall (o + i) ltac:(lia)). }
  rewrite Hrd in Hbs'. injection Hbs' as ->.
  apply nth_error_ext. intros i. rewrite nth_error_map.
  destruct (nth_error bvs i) as [x|] eqn:Hx.
  - pose proof (Hgn i x Hx) as Ht. destruct (Hcont _ _ Ht) as [_ Hrdx].
    rewrite okey_pos in Hrdx by lia.
    destruct (nth_error bs' i) as [b|] eqn:Hb.
    + pose proof (Hnth i b Hb) as Hrb. replace (A + o + Z.of_nat i) with (A + (o + Z.of_nat i)) in Hrb by lia.
      rewrite Hrb in Hrdx. exact Hrdx.
    + apply nth_error_None in Hb. assert (Hi' : (i < length bvs)%nat) by (apply nth_error_Some; rewrite Hx; discriminate). lia.
  - apply nth_error_None in Hx. cbn. apply nth_error_None. lia.
Qed.

#[using="Type"] Lemma ld_rz_sound : forall E fs R m o sz sg bs, Forall (fact_ok E) fs ->
  rg_kind R = RZ -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (nbytes sz) <= rsz E R ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (nbytes sz) = Some bs ->
  forall l, ld_bvs fs (get_bytes_z (rg_cont R) o (nbytes sz)) sz sg = Some l -> lden E l = ld_word sz sg bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs R m o sz sg bs HF Hk0 HR Ho Hn Hrd l Hl.
  destruct HR as (Hsz & Hflat & Hall & Hcont). rewrite Hk0 in Hall.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  destruct (get_bytes_z_spec (rg_cont R) (nbytes sz) o) as [Hlen Hgn].
  apply (ld_bvs_sound E fs (get_bytes_z (rg_cont R) o (nbytes sz)) bs sz sg l HF); [|exact Hlen | exact Hl].
  destruct (rdn_from segs m (nbytes sz) (A + o)) as (bs' & Hbs' & Hlen' & Hnth); [lia | lia | |].
  { intros i Hi. replace (A + o + i) with (A + (o + i)) by lia. apply (proj1 (proj1 (Hall (o + i) ltac:(lia)))). }
  rewrite Hrd in Hbs'. injection Hbs' as ->.
  apply nth_error_ext. intros i. rewrite nth_error_map.
  destruct (nth_error (get_bytes_z (rg_cont R) o (nbytes sz)) i) as [x|] eqn:Hx.
  - pose proof (Hgn i x Hx) as Hxe.
    assert (Hi' : (i < nbytes sz)%nat) by (rewrite <- Hlen; apply nth_error_Some; rewrite Hx; discriminate).
    destruct (nth_error bs' i) as [b|] eqn:Hb.
    + pose proof (Hnth i b Hb) as Hrb. replace (A + o + Z.of_nat i) with (A + (o + Z.of_nat i)) in Hrb by lia.
      cbn [option_map]. f_equal.
      destruct (tget (okey (o + Z.of_nat i)) (rg_cont R)) as [v|] eqn:Ht.
      * subst x. destruct (Hcont _ _ Ht) as [_ Hrdx]. rewrite okey_pos in Hrdx by lia. rewrite Hrb in Hrdx. injection Hrdx as ->. reflexivity.
      * subst x. pose proof (proj2 (Hall (o + Z.of_nat i) ltac:(lia)) Ht) as Hz. rewrite Hrb in Hz. injection Hz as ->. reflexivity.
    + apply nth_error_None in Hb. lia.
  - apply nth_error_None in Hx. cbn. apply nth_error_None. lia.
Qed.

#[using="Type"] Lemma get_bytes_i_spec : forall img t A n o bvs, get_bytes_i img t A o n = Some bvs ->
  length bvs = n /\ forall i v, nth_error bvs i = Some v ->
    tget (okey (o + Z.of_nat i)) t = Some v \/
    (tget (okey (o + Z.of_nat i)) t = None /\ exists b, v = BK b /\ img_bytes img (A + (o + Z.of_nat i)) 1 = Some [b]).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros img t A n. induction n as [|n IH]; intros o bvs H; cbn [get_bytes_i] in H.
  - injection H as <-. split; [reflexivity|]. intros [|i] v Hv; discriminate.
  - destruct (match tget (okey o) t with Some v => Some v | None => match img_bytes img (A + o) 1 with Some [b] => Some (BK b) | _ => None end end)
      as [v0|] eqn:Hv0; [|discriminate].
    destruct (get_bytes_i img t A (o + 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH (o + 1) r Hr) as [Hlen Hnth]. split; [cbn; lia|].
    intros [|i] v Hv; cbn [nth_error] in Hv.
    + injection Hv as <-. rewrite Z.add_0_r. destruct (tget (okey o) t) as [x|] eqn:Ht; [left; exact Hv0|].
      right. split; [reflexivity|]. destruct (img_bytes img (A + o) 1) as [[|b [|]]|]; try discriminate.
      injection Hv0 as <-. exists b. split; reflexivity.
    + replace (o + Z.of_nat (S i)) with (o + 1 + Z.of_nat i) by lia. exact (Hnth i v Hv).
Qed.

#[using="Type"] Lemma ld_ri_sound : forall E fs img R m o sz sg bs A, Forall (fact_ok E) fs ->
  img_ok segs img -> rg_kind R = RI -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (nbytes sz) <= rsz E R ->
  is_const (rg_base R) = Some A ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (nbytes sz) = Some bs ->
  forall bvs l, get_bytes_i img (rg_cont R) A o (nbytes sz) = Some bvs -> ld_bvs fs bvs sz sg = Some l -> lden E l = ld_word sz sg bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs img R m o sz sg bs A HF Himg Hk0 HR Ho Hn HA Hrd bvs l Hg Hl.
  destruct HR as (Hsz & Hflat & Hall & Hcont). rewrite Hk0 in Hall.
  assert (HAu : bv_unsigned (lden E (rg_base R)) = A) by (apply is_const_u; exact HA).
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  rewrite HAu in *.
  destruct (get_bytes_i_spec img _ A _ _ _ Hg) as [Hlen Hgn].
  apply (ld_bvs_sound E fs bvs bs sz sg l HF); [|exact Hlen | exact Hl].
  destruct (rdn_from segs m (nbytes sz) (A + o)) as (bs' & Hbs' & Hlen' & Hnth); [lia | lia | |].
  { intros i Hi. replace (A + o + i) with (A + (o + i)) by lia. apply (proj1 (proj1 (Hall (o + i) ltac:(lia)))). }
  rewrite Hrd in Hbs'. injection Hbs' as ->.
  apply nth_error_ext. intros i. rewrite nth_error_map.
  destruct (nth_error bvs i) as [x|] eqn:Hx.
  - assert (Hi' : (i < nbytes sz)%nat) by (rewrite <- Hlen; apply nth_error_Some; rewrite Hx; discriminate).
    destruct (nth_error bs' i) as [b|] eqn:Hb.
    + pose proof (Hnth i b Hb) as Hrb. replace (A + o + Z.of_nat i) with (A + (o + Z.of_nat i)) in Hrb by lia.
      cbn [option_map]. f_equal.
      destruct (Hgn i x Hx) as [Ht | (Ht & b0 & -> & Hib)].
      * destruct (Hcont _ _ Ht) as [_ Hrdx]. rewrite okey_pos in Hrdx by lia. rewrite Hrb in Hrdx. injection Hrdx as ->. reflexivity.
      * pose proof (proj2 (Hall (o + Z.of_nat i) ltac:(lia)) Ht) as Hz. rewrite Hrb in Hz.
        destruct (img_bytes_spec segs img 1 (A + (o + Z.of_nat i)) [b0] Himg ltac:(lia) Hib) as [_ Hsp].
        pose proof (Hsp O b0 eq_refl) as Hs. rewrite Z.add_0_r in Hs. rewrite Hs in Hz. injection Hz as ->. reflexivity.
    + apply nth_error_None in Hb. lia.
  - apply nth_error_None in Hx. cbn. apply nth_error_None. lia.
Qed.

#[using="Type"] Lemma ld_ro_sound : forall E img R m o sz bs,
  img_ok segs img -> rg_kind R = RO -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (nbytes sz) <= rsz E R ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (nbytes sz) = Some bs ->
  forall A bks, is_const (rg_base R) = Some A -> img_bytes img (A + o) (nbytes sz) = Some bks ->
  bs = map (Z_to_bv 8) bks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E img R m o sz bs Himg Hk0 HR Ho Hn Hrd A bks HA Hib.
  destruct HR as (Hsz & Hflat & Hall & Hcont). rewrite Hk0 in Hall.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  assert (HAu : bv_unsigned (lden E (rg_base R)) = A) by (apply is_const_u; exact HA).
  rewrite HAu in *.
  destruct (img_bytes_spec segs img (nbytes sz) (A + o) bks Himg ltac:(lia) Hib) as [Hlen Hb].
  destruct (rdn_from segs m (nbytes sz) (A + o)) as (bs' & Hbs' & Hlen' & Hnth); [lia | lia | |].
  { intros i Hi. replace (A + o + i) with (A + (o + i)) by lia. destruct (Hall (o + i) ltac:(lia)) as [Hm Hr].
    unfold rd1. rewrite Hm. exact Hr. }
  rewrite Hrd in Hbs'. injection Hbs' as ->.
  apply nth_error_ext. intros i. rewrite nth_error_map.
  destruct (nth_error bks i) as [v|] eqn:Hv.
  - destruct (nth_error bs' i) as [b|] eqn:Hbb.
    + pose proof (Hnth i b Hbb) as H1. pose proof (Hb i v Hv) as H2.
      destruct (Hall (o + Z.of_nat i) ltac:(pose proof (nth_error_Some bks i) as Hs; assert ((i < length bks)%nat) by (apply Hs; rewrite Hv; discriminate); lia)) as [Hm _].
      replace (A + (o + Z.of_nat i)) with (A + o + Z.of_nat i) in Hm by lia.
      unfold rd1 in H1. rewrite Hm, H2 in H1. cbn. congruence.
    + apply nth_error_None in Hbb. assert ((i < length bks)%nat) by (apply nth_error_Some; rewrite Hv; discriminate). lia.
  - apply nth_error_None in Hv. cbn. apply nth_error_None. lia.
Qed.

#[using="Type"] Lemma ld_value_sound : forall E fs img R m o sz sg bs, Forall (fact_ok E) fs ->
  img_ok segs img -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (nbytes sz) <= rsz E R ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (nbytes sz) = Some bs ->
  forall l, ld_value img fs R o sz sg = Some l -> lden E l = ld_word sz sg bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs img R m o sz sg bs HF Himg HR Ho Hn Hrd l Hl. unfold ld_value in Hl.
  destruct (rg_kind R) eqn:Hk.
  - exact (ld_rw_sound E fs R m o sz sg bs HF Hk HR Ho Hn Hrd l Hl).
  - destruct (is_const (rg_base R)) as [A|] eqn:HA; [|discriminate].
    destruct (img_bytes img (A + o) (nbytes sz)) as [bks|] eqn:Hib; [|discriminate]. injection Hl as <-.
    rewrite (ld_ro_sound E img R m o sz bs Himg Hk HR Ho Hn Hrd A bks HA Hib). apply lden_const_word.
  - exact (ld_rz_sound E fs R m o sz sg bs HF Hk HR Ho Hn Hrd l Hl).
  - destruct (is_const (rg_base R)) as [A|] eqn:HA; [|discriminate].
    destruct (get_bytes_i img (rg_cont R) A o (nbytes sz)) as [bvs|] eqn:Hg; [|discriminate].
    exact (ld_ri_sound E fs img R m o sz sg bs A HF Himg Hk HR Ho Hn HA Hrd bvs l Hg Hl).
  - exact (ld_rt_sound E fs R m o sz sg bs HF Hk HR Ho Hn Hrd l Hl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rg_store_ok : forall E R m o (bvs : list bval) (bs : list byte),
  rg_kind R = RW -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bs) <= rsz E R -> length bvs = length bs ->
  (forall i x, nth_error bvs i = Some x -> nth_error bs i = Some (bden E x)) ->
  rg_ok segs E (write_to_mem m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs)
          (RG (rg_base R) (rg_size R) RW (put_bytes (rg_cont R) o bvs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E R m o bvs bs Hk0 HR Ho Hn Hlen Hb.
  destruct HR as (Hsz & Hflat & Hall & Hcont). rewrite Hk0 in Hall. unfold rg_ok, rsz in *. cbv zeta. cbn [rg_base rg_size rg_cont rg_kind] in *.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  assert (Hwr : forall x, write_to_mem m (Z_to_bv 64 (A + o)) bs x =
             if (Z.leb (A + o) (bv_unsigned x) && Z.ltb (bv_unsigned x) (A + o + Z.of_nat (length bs)))%bool
             then nth_error bs (Z.to_nat (bv_unsigned x - (A + o))) else m x)
    by (intros x; apply write_to_mem_spec; lia).
  split; [exact Hsz|]. split; [exact Hflat|]. split.
  - intros i Hi. cbn [rg_size rg_base rg_cont rg_kind] in Hi |- *. destruct (Hall i Hi) as [H1 H2].
    assert (Hu : bv_unsigned (Z_to_bv 64 (A + i)) = A + i) by (apply u_small64; lia).
    pose proof (Hwr (Z_to_bv 64 (A + i))) as Hw. rewrite Hu in Hw.
    unfold rd1, wview. rewrite Hw.
    destruct (Z.leb (A + o) (A + i) && Z.ltb (A + i) (A + o + Z.of_nat (length bs)))%bool eqn:E1.
    + apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      destruct (nth_error bs (Z.to_nat (A + i - (A + o)))) eqn:Hn'; [split; discriminate|].
      apply nth_error_None in Hn'. lia.
    + split; [exact H1 | exact H2].
  - intros p v Hp. cbn [rg_size rg_base rg_cont] in Hp |- *. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length bvs)))%bool eqn:E1.
    + apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      split; [lia|]. unfold rd1. rewrite Hwr. rewrite u_small64 by (pose proof (Pos2Z.is_pos p); lia).
      replace (Z.leb (A + o) (A + (Zpos p - 1)) && Z.ltb (A + (Zpos p - 1)) (A + o + Z.of_nat (length bs)))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      replace (Z.to_nat (A + (Zpos p - 1) - (A + o))) with (Z.to_nat (Zpos p - 1 - o)) by lia.
      rewrite (Hb _ _ Hp). reflexivity.
    + destruct (Hcont p v Hp) as [Hp1 Hp2]. split; [exact Hp1|].
      unfold rd1. rewrite Hwr. rewrite u_small64 by (pose proof (Pos2Z.is_pos p); lia).
      replace (Z.leb (A + o) (A + (Zpos p - 1)) && Z.ltb (A + (Zpos p - 1)) (A + o + Z.of_nat (length bs)))%bool with false.
      { exact Hp2. }
      symmetry. apply andb_false_iff. apply andb_false_iff in E1. destruct E1 as [E1|E1].
      * apply Z.leb_gt in E1. left. apply Z.leb_gt. lia.
      * apply Z.ltb_ge in E1. right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_havoc_ok : forall E R m o lo hi (bs : list byte),
  rg_kind R = RW -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bs) <= rsz E R -> lo <= o -> o + Z.of_nat (length bs) <= hi ->
  rg_ok segs E (write_to_mem m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs)
          (RG (rg_base R) (rg_size R) RW (havoc_range (rg_cont R) lo hi)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E R m o lo hi bs Hk0 HR Ho Hn Hlo Hhi.
  destruct HR as (Hsz & Hflat & Hall & Hcont). rewrite Hk0 in Hall. unfold rg_ok, rsz in *. cbv zeta. cbn [rg_base rg_size rg_cont rg_kind] in *.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  assert (Hwr : forall x, write_to_mem m (Z_to_bv 64 (A + o)) bs x =
             if (Z.leb (A + o) (bv_unsigned x) && Z.ltb (bv_unsigned x) (A + o + Z.of_nat (length bs)))%bool
             then nth_error bs (Z.to_nat (bv_unsigned x - (A + o))) else m x)
    by (intros x; apply write_to_mem_spec; lia).
  split; [exact Hsz|]. split; [exact Hflat|]. split.
  - intros i Hi. cbn [rg_size rg_base rg_cont rg_kind] in Hi |- *. destruct (Hall i Hi) as [H1 H2].
    assert (Hu : bv_unsigned (Z_to_bv 64 (A + i)) = A + i) by (apply u_small64; lia).
    pose proof (Hwr (Z_to_bv 64 (A + i))) as Hw. rewrite Hu in Hw.
    unfold rd1, wview. rewrite Hw.
    destruct (Z.leb (A + o) (A + i) && Z.ltb (A + i) (A + o + Z.of_nat (length bs)))%bool eqn:E1.
    + apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      destruct (nth_error bs (Z.to_nat (A + i - (A + o)))) eqn:Hn'; [split; discriminate|].
      apply nth_error_None in Hn'. lia.
    + split; [exact H1 | exact H2].
  - intros p v Hp. cbn [rg_size rg_base rg_cont rg_kind] in Hp |- *. unfold havoc_range in Hp. rewrite tget_tfilter in Hp.
    destruct (tget p (rg_cont R)) as [v0|] eqn:Hp0; [|discriminate].
    destruct (negb (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)) eqn:Hout; [|discriminate]. injection Hp as <-.
    destruct (Hcont p v0 Hp0) as [Hp1 Hp2]. split; [exact Hp1|].
    unfold rd1. rewrite Hwr. rewrite u_small64 by (pose proof (Pos2Z.is_pos p); lia).
    replace (Z.leb (A + o) (A + (Zpos p - 1)) && Z.ltb (A + (Zpos p - 1)) (A + o + Z.of_nat (length bs)))%bool with false; [exact Hp2|].
    symmetry. apply negb_true_iff in Hout. apply andb_false_iff in Hout. apply andb_false_iff.
    destruct Hout as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1].
    + left. apply Z.leb_gt. lia.
    + right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma st_bytes_ok : forall E (v : lin) (vw : word) sz,
  lden E v = vw ->
  forall i x, nth_error (st_bytes v (is_const v) 0 (nbytes sz)) i = Some x ->
    nth_error (Z_to_le_bytes (nbytes sz) (st_word sz vw)) i = Some (bden E x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E v vw sz Hv i x Hx.
  destruct (st_bytes_nth _ _ _ _ _ _ Hx) as [Hi Hxe].
  rewrite nth_Z_to_le_bytes by exact Hi. f_equal.
  assert (Hst : st_word sz vw = bv_unsigned vw mod 2 ^ (8 * Z.of_nat (nbytes sz))).
  { destruct sz; cbn [st_word nbytes]; try (unfold low32); rewrite ?bv_extract_unsigned, ?Z.shiftr_0_r; try reflexivity.
    symmetry. apply Z.mod_small. apply bv_unsigned_in_range. }
  rewrite Hst, byte_of_mod by (cbn [Z.of_nat]; lia).
  destruct (is_const v) as [c|] eqn:Hc.
  - subst x. destruct (is_const_sound E v c Hc) as [Hvc Hr]. rewrite Hvc in Hv. subst vw.
    cbn [bden]. rewrite byte_land255, u_small64 by exact Hr. repeat f_equal; try lia.
  - subst x. cbn [bden]. rewrite Hv. repeat f_equal; try lia.
Qed.

#[using="Type"] Lemma find_fbyte_in : forall fs x v j, find_fbyte fs x = Some (v, j) -> exists x', In (FByte x' v j) fs /\ lin_eqb x' x = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs as [|f fs IH]; intros x v j H; cbn [find_fbyte] in H; [discriminate|].
  destruct f as [c a b tk|l lo hi|l k r|l m v'|x' v' j'|xb bsb];
    try (destruct (IH x v j H) as (x0 & Hin & Heq); exists x0; split; [right; exact Hin | exact Heq]).
  destruct (lin_eqb x' x) eqn:Hx.
  - injection H as <- <-. exists x'. split; [left; reflexivity | exact Hx].
  - destruct (IH x v j H) as (x0 & Hin & Heq). exists x0. split; [right; exact Hin | exact Heq].
Qed.

#[using="Type"] Lemma find_fbytes_in : forall fs x bs, find_fbytes fs x = Some bs -> exists x', In (FBytes x' bs) fs /\ lin_eqb x' x = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs as [|f fs IH]; intros x bs H; cbn [find_fbytes] in H; [discriminate|].
  destruct f as [c a b tk|l lo hi|l k r|l m v'|x' v' j'|x' bs'];
    try (destruct (IH x bs H) as (x0 & Hin & Heq); exists x0; split; [right; exact Hin | exact Heq]).
  destruct (lin_eqb x' x) eqn:Hx.
  - injection H as <-. exists x'. split; [left; reflexivity | exact Hx].
  - destruct (IH x bs H) as (x0 & Hin & Heq). exists x0. split; [right; exact Hin | exact Heq].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma length_unmix : forall l n j p, length (unmix l j p n) = n.
Proof. LiaFast.lf_pins LiaFast.u0. intros l n. induction n as [|n IH]; intros j p; cbn [unmix length]; [reflexivity | rewrite IH; reflexivity]. Qed.
#[using="Type"] Lemma st_mix_len : forall fs v w bvs, st_mix fs v w = Some bvs -> length bvs = w.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fs v w bvs H. unfold st_mix in H. destruct (existsb _ (l_t v)); [|discriminate].
  destruct (mix_lin fs (unmix v 0 1 w) 1) as [l|]; [|discriminate]. destruct (lin_eqb l v); [|discriminate].
  injection H as <-. apply length_unmix.
Qed.
#[using="Type"] Lemma st_mix_ok : forall E fs (v : lin) (vw : word) sz bvs, Forall (fact_ok E) fs -> lden E v = vw ->
  st_mix fs v (nbytes sz) = Some bvs ->
  forall i x, nth_error bvs i = Some x -> nth_error (Z_to_le_bytes (nbytes sz) (st_word sz vw)) i = Some (bden E x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs v vw sz bvs HF Hv H i x Hx. pose proof (st_mix_len fs v _ bvs H) as Hlen. unfold st_mix in H.
  destruct (existsb _ (l_t v)); [|discriminate].
  destruct (mix_lin fs (unmix v 0 1 (nbytes sz)) 1) as [l|] eqn:Hm; [|discriminate]. destruct (lin_eqb l v) eqn:Hlv; [|discriminate].
  injection H as H. subst bvs. apply lin_eqb_eq in Hlv. subst l.
  destruct (mix_lin_ok E fs _ 1 v HF Hm) as (Hq & Hb & Hmap). rewrite Hlen in Hb, Hmap.
  assert (H8 : (nbytes sz <= 8)%nat) by (destruct sz; cbn; lia).
  pose proof (pow256_le (nbytes sz) H8) as Hp.
  rewrite Z.mul_1_l in Hq. unfold eqm in Hq. rewrite (Z.mod_small (bv_unsigned _)) in Hq by apply u_range.
  rewrite (Z.mod_small (mix_val _ _)) in Hq by lia.
  assert (Hst : st_word sz vw = bv_unsigned vw mod 2 ^ (8 * Z.of_nat (nbytes sz))).
  { destruct sz; cbn [st_word nbytes]; try (unfold low32); rewrite ?bv_extract_unsigned, ?Z.shiftr_0_r; try reflexivity.
    symmetry. apply Z.mod_small. apply bv_unsigned_in_range. }
  assert (Hpw : 2 ^ (8 * Z.of_nat (nbytes sz)) = 256 ^ Z.of_nat (nbytes sz)) by (change 256 with (2 ^ 8); rewrite <- Z.pow_mul_r by lia; reflexivity).
  rewrite Hst, <- Hv, Hq, Hpw, Z.mod_small by lia. rewrite <- Hmap, nth_error_map, Hx. reflexivity.
Qed.

#[using="Type"] Lemma length_st_vals : forall fs v w, length (st_vals fs v w) = w.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fs v w. unfold st_vals. destruct w as [|[|w]]; destruct (is_const v); try apply length_st_bytes.
  - destruct (find_fbytes fs v) as [bs|]; [|destruct (st_mix fs v 0) as [bvs|] eqn:Hsm; [exact (st_mix_len _ _ _ _ Hsm) | apply length_st_bytes]].
    destruct (Nat.leb 0 (length bs)) eqn:Hl; [|apply length_st_bytes]. reflexivity.
  - destruct (find_fbyte fs v) as [[v' j]|]; [reflexivity | apply length_st_bytes].
  - destruct (find_fbytes fs v) as [bs|]; [|destruct (st_mix fs v (S (S w))) as [bvs|] eqn:Hsm; [exact (st_mix_len _ _ _ _ Hsm) | apply length_st_bytes]].
    destruct (Nat.leb (S (S w)) (length bs)) eqn:Hl; [|apply length_st_bytes].
    apply Nat.leb_le in Hl. rewrite length_map, length_firstn. lia.
Qed.

#[using="Type"] Lemma st_vals_ok : forall E fs (v : lin) (vw : word) sz, Forall (fact_ok E) fs ->
  lden E v = vw ->
  forall i x, nth_error (st_vals fs v (nbytes sz)) i = Some x ->
    nth_error (Z_to_le_bytes (nbytes sz) (st_word sz vw)) i = Some (bden E x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs v vw sz HF Hv i x Hx. unfold st_vals in Hx.
  assert (Hfbs : forall w, (1 < w)%nat -> w = nbytes sz -> nth_error (st_vals fs v w) i = Some x ->
            nth_error (Z_to_le_bytes (nbytes sz) (st_word sz vw)) i = Some (bden E x)).
  { intros w Hw Hwz Hx'. unfold st_vals in Hx'. destruct w as [|[|w']]; [lia|lia|].
    destruct (is_const v) as [c|] eqn:Hc; [apply (st_bytes_ok E v vw sz Hv i x); rewrite Hc, <- Hwz; exact Hx'|].
    destruct (find_fbytes fs v) as [bs|] eqn:Hfb;
      [|destruct (st_mix fs v (S (S w'))) as [bvs|] eqn:Hsm;
        [rewrite Hwz in Hsm; exact (st_mix_ok E fs v vw sz bvs HF Hv Hsm i x Hx')
        |apply (st_bytes_ok E v vw sz Hv i x); rewrite Hc, <- Hwz; exact Hx']].
    destruct (Nat.leb (S (S w')) (length bs)) eqn:Hl; [|apply (st_bytes_ok E v vw sz Hv i x); rewrite Hc, <- Hwz; exact Hx'].
    apply Nat.leb_le in Hl.
    destruct (find_fbytes_in fs v bs Hfb) as (x' & Hin & Heq). apply lin_eqb_eq in Heq. subst x'.
    rewrite Forall_forall in HF. pose proof (HF _ Hin) as Hok. cbn [fact_ok] in Hok.
    rewrite nth_error_map in Hx'. destruct (nth_error (firstn (S (S w')) bs) i) as [[v1 j1]|] eqn:Hn; [|discriminate].
    cbn [option_map] in Hx'. injection Hx' as <-. cbn [fst snd].
    assert (Hi : (i < S (S w'))%nat).
    { assert (X : nth_error (firstn (S (S w')) bs) i <> None) by (rewrite Hn; discriminate).
      apply nth_error_Some in X. rewrite length_firstn in X. lia. }
    rewrite nth_error_firstn in Hn. destruct (Nat.ltb i (S (S w'))) eqn:Hiw; [|discriminate].
    assert (Hib : (i < length bs)%nat) by lia.
    pose proof (Hok i Hib) as Hb. rewrite (nth_error_nth _ _ (lconst 0, 0) Hn) in Hb. cbn [fst snd] in Hb.
    assert (Hsb : forall j n k, (k < n)%nat -> nth_error (st_bytes v None j n) k = Some (BV v (j + Z.of_nat k))).
    { intros j n. revert j. induction n as [|n IH]; intros j k Hk; [lia|]. destruct k as [|k]; cbn [st_bytes nth_error].
      - f_equal. f_equal. lia.
      - rewrite (IH (j + 1) k ltac:(lia)). f_equal. f_equal. lia. }
    pose proof (st_bytes_ok E v vw sz Hv i (BV v (0 + Z.of_nat i)) ltac:(rewrite Hc, <- Hwz; exact (Hsb 0 _ i Hi))) as X.
    rewrite X. f_equal. cbn [bden]. rewrite Z.add_0_l. rewrite <- (byte_land255 (Z.shiftr (bv_unsigned (lden E v)) (8 * Z.of_nat i))).
    rewrite <- (byte_land255 (Z.shiftr (bv_unsigned (lden E v1)) (8 * j1))). f_equal. exact Hb. }
  destruct sz; [| apply (Hfbs 2%nat ltac:(lia) eq_refl Hx)
                | apply (Hfbs 4%nat ltac:(lia) eq_refl Hx)
                | apply (Hfbs 8%nat ltac:(lia) eq_refl Hx)].
  cbn [nbytes] in Hx |- *.
  destruct (is_const v) as [c|] eqn:Hc.
  - apply (st_bytes_ok E v vw SZ1 Hv i x). cbn [nbytes]. rewrite Hc. exact Hx.
  - destruct (find_fbyte fs v) as [[v' j]|] eqn:Hfb.
    + destruct i as [|i]; [|destruct i; discriminate]. cbn [nth_error] in Hx |- *. injection Hx as <-.
      destruct (find_fbyte_in fs v v' j Hfb) as (x' & Hin & Heq). apply lin_eqb_eq in Heq. subst x'.
      rewrite Forall_forall in HF. pose proof (HF _ Hin) as Hok. cbn [fact_ok] in Hok.
      cbn [Z_to_le_bytes st_word bden]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
      rewrite bv_extract_0_unsigned. rewrite <- Hv, Hok. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
      change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
    + apply (st_bytes_ok E v vw SZ1 Hv i x). cbn [nbytes]. rewrite Hc. exact Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ld_word_zext_lt : forall sz bs, bv_unsigned (ld_word sz false bs) < 2 ^ (8 * Z.of_nat (nbytes sz)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [] bs; unfold ld_word, zext; cbn [nbytes]; try rewrite bv_zero_extend_unsigned by lia;
    match goal with |- bv_unsigned ?x < _ => pose proof (bv_unsigned_in_range _ x) as R; unfold bv_modulus in R; cbn in R |- *; lia end.
Qed.

#[using="Type"] Lemma ld_facts0_sound : forall E'' s ms a sz sg bs n,
  sden0 segs E'' s ms ->
  ov_read_bytes segs (ms_mem ms) (lden E'' a) (nbytes sz) = Some bs ->
  E'' n = ld_word sz sg bs ->
  Forall (fact_ok E'') (ld_facts0 (s_facts s) (s_rgs s) a sz sg (lvar n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E'' s ms a sz sg bs n Hd Hbs Hn. pose proof (ld_word_zext_lt sz bs) as Hlt.
  pose proof (bv_unsigned_in_range _ (ld_word sz false bs)) as Hr0. unfold ld_facts0.
  destruct sz; destruct sg; try (constructor; fail); cbn [nbytes Z.of_nat] in Hlt.
  2: { constructor; [cbn [fact_ok]; rewrite lden_lvar, Hn; change (2 ^ (8 * 2)) with 65536 in Hlt; lia | constructor]. }
  2: { constructor; [cbn [fact_ok]; rewrite lden_lvar, Hn; change (2 ^ (8 * 4)) with 4294967296 in Hlt; lia | constructor]. }
  destruct (byte_src (s_facts s) (s_rgs s) a) as [[v j]|] eqn:Hb;
    [|constructor; [cbn [fact_ok]; rewrite lden_lvar, Hn; change (2 ^ (8 * 1)) with 256 in Hlt; lia | constructor]].
  constructor; [|constructor; [cbn [fact_ok]; rewrite lden_lvar, Hn; change (2 ^ (8 * 1)) with 256 in Hlt; lia | constructor]]. cbn [fact_ok]. rewrite lden_lvar, Hn.
  unfold byte_src in Hb. destruct (find_rg (s_facts s) (s_rgs s) a 1 O) as [[[ri R] o]|] eqn:Hfr; [|discriminate].
  assert (Ht : tget (okey o) (rg_cont R) = Some (BV v j)).
  { destruct (rg_kind R); destruct (tget (okey o) (rg_cont R)) as [[b0|v0 j0]|]; try discriminate; injection Hb as <- <-; reflexivity. }
  destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth & Ho). rewrite Nat.sub_0_r in Hnth.
  destruct Hd as (_ & _ & _ & _ & HG & _ & HFs & _).
  destruct (rg_off_sound E'' _ _ _ _ _ (size_lo_sound E'' _ R HFs) Ho) as (Ho0 & Hon & Haddr).
  pose proof (proj1 (Forall_nth' _ _) HG ri R Hnth) as HR. destruct HR as (_ & _ & _ & Hcont).
  destruct (Hcont _ _ Ht) as [_ Hrd]. rewrite okey_pos in Hrd by lia.
  rewrite ov_rdn, Haddr in Hbs. cbn [nbytes rdn] in Hbs. unfold rd1 in Hrd. rewrite Hrd in Hbs. injection Hbs as <-.
  unfold ld_word, le_bytes_to_word. cbn [bytes_le_to_Z bden]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  unfold zext. rewrite bv_zero_extend_unsigned by lia. rewrite bv_extract_0_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256.
  set (z := Z.shiftr (bv_unsigned (lden E'' v)) (8 * j)).
  assert (Hz : 0 <= z mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small (z mod 256) (2 ^ Z.of_N 64)) by (change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma byte_land_mod : forall z1 z2 k i, 0 <= i -> 8 * i + 8 <= k -> z1 mod 2 ^ k = z2 mod 2 ^ k ->
  Z.land (Z.shiftr z1 (8 * i)) 255 = Z.land (Z.shiftr z2 (8 * i)) 255.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z1 z2 k i Hi Hk Hm. apply Z.bits_inj'. intros b Hb. change 255 with (Z.ones 8). rewrite !Z.land_spec.
  destruct (Z_lt_le_dec b 8) as [Hb8|Hb8].
  - rewrite Z.ones_spec_low by lia. rewrite !andb_true_r. rewrite !Z.shiftr_spec by lia.
    rewrite <- (Z.mod_pow2_bits_low z1 k (b + 8 * i)) by lia. rewrite <- (Z.mod_pow2_bits_low z2 k (b + 8 * i)) by lia.
    rewrite Hm. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite !andb_false_r. reflexivity.
Qed.
#[using="Type"] Lemma byte_of_bytes_le : forall bs i, (i < length bs)%nat ->
  Z.land (Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat i)) 255 = bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b bs IH]; intros i Hi; cbn [length] in Hi; [lia|].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
  destruct i as [|i].
  - cbn [nth bytes_le_to_Z]. rewrite Z.mul_0_r, Z.shiftr_0_r. apply Z.bits_inj'. intros k Hk. change 255 with (Z.ones 8).
    rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z_lt_le_dec k 8) as [Hk8|Hk8].
    + rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r _ (k - 8)) by lia. rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      apply (Z_testbit_high 8 (bv_unsigned b) k); lia.
  - cbn [nth bytes_le_to_Z]. rewrite <- (IH i ltac:(lia)). f_equal.
    apply Z.bits_inj'. intros k Hk. rewrite !Z.shiftr_spec by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z_testbit_high 8 (bv_unsigned b) (k + 8 * Z.of_nat (S i))) by lia. cbn [orb].
    f_equal. lia.
Qed.
#[using="Type"] Lemma sext_low : forall (k : N) (x : bv k), (1 <= k <= 64)%N -> bv_unsigned (sext 64 x) mod 2 ^ Z.of_N k = bv_unsigned x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k x Hk. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_wrap, bv_modulus.
  assert (Hpk : 0 < 2 ^ Z.of_N k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hdiv : (2 ^ Z.of_N k | 2 ^ Z.of_N 64)).
  { exists (2 ^ (Z.of_N 64 - Z.of_N k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite Z.mod_mod_divide by assumption.
  unfold bv_signed, bv_swrap, bv_wrap, bv_modulus.
  rewrite Zminus_mod_idemp_l. replace (bv_unsigned x + bv_half_modulus k - bv_half_modulus k) with (bv_unsigned x) by ring.
  apply Z.mod_small. pose proof (bv_unsigned_in_range _ x) as R. unfold bv_modulus in R. exact R.
Qed.
#[using="Type"] Lemma ld_word_low : forall sz sg bs, length bs = nbytes sz ->
  bv_unsigned (ld_word sz sg bs) mod 2 ^ (8 * Z.of_nat (nbytes sz)) = bytes_le_to_Z bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros sz sg bs Hl. pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite Hl in H1.
  unfold ld_word, le_bytes_to_word.
  assert (Hz : forall k : N, (k <= 64)%N -> 8 * Z.of_nat (nbytes sz) = Z.of_N k ->
            bv_unsigned (bv_extract 0 k (Z_to_bv 64 (bytes_le_to_Z bs))) = bytes_le_to_Z bs).
  { intros k Hk Hke. rewrite bv_extract_0_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite (Z.mod_small (bytes_le_to_Z bs) (2 ^ Z.of_N 64)) by (split; [lia|]; eapply Z.lt_le_trans; [exact H1|]; apply Z.pow_le_mono_r; lia).
    apply Z.mod_small. rewrite <- Hke. lia. }
  destruct sz; [destruct sg | destruct sg | destruct sg | ]; cbn [nbytes] in Hz |- *.
  - change (2 ^ (8 * Z.of_nat 1)) with (2 ^ Z.of_N 8). rewrite (sext_low 8) by lia. exact (Hz 8%N ltac:(lia) eq_refl).
  - unfold zext. rewrite bv_zero_extend_unsigned by lia. rewrite (Hz 8%N ltac:(lia) eq_refl). apply Z.mod_small. cbn in H1 |- *. lia.
  - change (2 ^ (8 * Z.of_nat 2)) with (2 ^ Z.of_N 16). rewrite (sext_low 16) by lia. exact (Hz 16%N ltac:(lia) eq_refl).
  - unfold zext. rewrite bv_zero_extend_unsigned by lia. rewrite (Hz 16%N ltac:(lia) eq_refl). apply Z.mod_small. cbn in H1 |- *. lia.
  - change (2 ^ (8 * Z.of_nat 4)) with (2 ^ Z.of_N 32). rewrite (sext_low 32) by lia. exact (Hz 32%N ltac:(lia) eq_refl).
  - unfold zext. rewrite bv_zero_extend_unsigned by lia. rewrite (Hz 32%N ltac:(lia) eq_refl). apply Z.mod_small. cbn in H1 |- *. lia.
  - rewrite (Hz 64%N ltac:(lia) eq_refl). apply Z.mod_small. cbn in H1 |- *. lia.
Qed.
#[using="Type"] Lemma bvs_src_spec : forall c o w bs, bvs_src c o w = Some bs ->
  length bs = w /\ forall i, (i < w)%nat -> tget (okey (o + Z.of_nat i)) c = Some (BV (fst (nth i bs (lconst 0, 0))) (snd (nth i bs (lconst 0, 0)))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c o w. revert o. induction w as [|w IH]; intros o bs H; cbn [bvs_src] in H.
  - injection H as <-. split; [reflexivity | intros i Hi; lia].
  - destruct (tget (okey o) c) as [[b|v j]|] eqn:Ht; try discriminate.
    destruct (bvs_src c (o + 1) w) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH (o + 1) r Hr) as [Hlr Hall]. split; [cbn; lia|].
    intros [|i] Hi; cbn [nth fst snd].
    + rewrite Z.add_0_r. exact Ht.
    + replace (o + Z.of_nat (S i)) with (o + 1 + Z.of_nat i) by lia. exact (Hall i ltac:(lia)).
Qed.
#[using="Type"] Lemma ld_facts_sound : forall E'' s ms a sz sg bs n,
  sden0 segs E'' s ms ->
  ov_read_bytes segs (ms_mem ms) (lden E'' a) (nbytes sz) = Some bs ->
  E'' n = ld_word sz sg bs ->
  Forall (fact_ok E'') (ld_facts (s_facts s) (s_rgs s) a sz sg (lvar n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E'' s ms a sz sg bs n Hd Hbs Hn. unfold ld_facts.
  assert (Hw : forall sz', sz' = sz -> sz' <> SZ1 -> Forall (fact_ok E'')
    (match bytes_src (s_facts s) (s_rgs s) a (nbytes sz') with
     | Some bs0 => fun x => FBytes x bs0 :: ld_facts0 (s_facts s) (s_rgs s) a sz' sg x
     | None => ld_facts0 (s_facts s) (s_rgs s) a sz' sg end (lvar n))).
  { intros sz' -> Hne. destruct (bytes_src (s_facts s) (s_rgs s) a (nbytes sz)) as [bsr|] eqn:Hbr; [|exact (ld_facts0_sound E'' s ms a sz sg bs n Hd Hbs Hn)].
    constructor; [|exact (ld_facts0_sound E'' s ms a sz sg bs n Hd Hbs Hn)].
    unfold bytes_src in Hbr. destruct (find_rg (s_facts s) (s_rgs s) a (Z.of_nat (nbytes sz)) O) as [[[ri R] o]|] eqn:Hfr; [|discriminate].
    assert (Hsrc : bvs_src (rg_cont R) o (nbytes sz) = Some bsr) by (destruct (rg_kind R); first [discriminate | exact Hbr]).
    destruct (bvs_src_spec _ _ _ _ Hsrc) as [Hlb Hall].
    destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth & Ho). rewrite Nat.sub_0_r in Hnth.
    destruct Hd as (_ & _ & _ & _ & HG & _ & HFs & _).
    destruct (rg_off_sound E'' _ _ _ _ _ (size_lo_sound E'' _ R HFs) Ho) as (Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R Hnth) as HR. destruct HR as (_ & HRw & _ & Hcont).
    pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
    rewrite ov_rdn, Haddr in Hbs.
    destruct (rdn_from segs (ms_mem ms) (nbytes sz) (bv_unsigned (lden E'' (rg_base R)) + o) ltac:(lia) ltac:(unfold rsz in *; lia)) as (bs' & Hbs' & Hl' & Hnb).
    { intros i Hi. pose proof (Hall (Z.to_nat i) ltac:(lia)) as Ht. rewrite Z2Nat.id in Ht by lia.
      destruct (Hcont _ _ Ht) as [_ Hrd].
      rewrite okey_pos in Hrd by lia. rewrite Z.add_assoc in Hrd. rewrite Hrd. discriminate. }
    rewrite Hbs' in Hbs. injection Hbs as <-.
    cbn [fact_ok]. intros i Hi. rewrite lden_lvar, Hn. rewrite Hlb in Hi.
    rewrite (byte_land_mod _ (bytes_le_to_Z bs') (8 * Z.of_nat (nbytes sz)) (Z.of_nat i) ltac:(lia) ltac:(lia)).
    2: { rewrite (ld_word_low sz sg bs' Hl'). pose proof (bytes_le_to_Z_nonneg bs'). pose proof (bytes_le_to_Z_bound bs') as X.
         rewrite Hl' in X. symmetry. apply Z.mod_small. lia. }
    rewrite byte_of_bytes_le by lia.
    destruct (Hcont (okey (o + Z.of_nat i)) _ (Hall i Hi)) as [_ Hrd]. rewrite okey_pos in Hrd by lia. rewrite Z.add_assoc in Hrd.
    destruct (nth_error bs' i) as [b|] eqn:Hb; [|exfalso; apply nth_error_None in Hb; lia].
    pose proof (Hnb i b Hb) as Hrb. rewrite Hrd in Hrb. injection Hrb as Hrb.
    rewrite (nth_error_nth _ _ (Z_to_bv 8 0) Hb). rewrite <- Hrb. cbn [bden]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 8) with 256. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. }
  destruct sz; [exact (ld_facts0_sound E'' s ms a SZ1 sg bs n Hd Hbs Hn) | apply Hw; [reflexivity | discriminate]..].
Qed.



(* [comment removed for export] *)
#[using="Type"] Lemma tall_spec : forall {A} (f : A -> bool) t p x, tall f t = true -> tget p t = Some x -> f x = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A f t. induction t as [|l IHl v r IHr]; intros p x H Hp; [rewrite tget_empty in Hp; discriminate|].
  cbn [tall] in H. apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hv Hl].
  destruct p as [p|p|]; cbn [tget] in Hp; [exact (IHr p x Hr Hp) | exact (IHl p x Hl Hp) | subst v; exact Hv].
Qed.
#[using="Type"] Lemma range_zero_spec : forall t lo hi p v, range_zero t lo hi = true -> tget p t = Some v -> lo <= Zpos p - 1 < hi -> v = BK 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t lo hi p v H Hp Hr. unfold range_zero in H.
  assert (Hf : tget p (tfilter (fun p => (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)%bool) t) = Some v).
  { rewrite tget_tfilter, Hp. replace (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)%bool with true; [reflexivity|].
    symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  pose proof (tall_spec _ _ _ _ H Hf) as Hz. destruct v as [b|l j]; cbn in Hz; [|discriminate].
  destruct b as [|b|b]; [reflexivity | discriminate | discriminate].
Qed.

#[using="Type"] Lemma rz_weaken : forall E m R, rg_kind R = RZ \/ rg_kind R = RI -> rg_ok segs E m R -> rg_ok segs E m (RG (rg_base R) (rg_size R) RW (rg_cont R)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R Hk (H1 & H2 & H3 & H4). unfold rg_ok, rsz in *; cbn [rg_base rg_size rg_kind rg_cont] in *.
  split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
  intros i Hi. specialize (H3 i Hi). destruct Hk as [Hk|Hk]; rewrite Hk in H3; exact (proj1 H3).
Qed.

#[using="Type"] Lemma rg_zstore_ok : forall E R m o lo hi (bs : list byte),
  rg_kind R = RZ -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bs) <= rsz E R -> lo <= o -> o + Z.of_nat (length bs) <= hi ->
  (forall i b, nth_error bs i = Some b -> b = Z_to_bv 8 0) -> range_zero (rg_cont R) lo hi = true ->
  rg_ok segs E (write_to_mem m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs)
          (RG (rg_base R) (rg_size R) RZ (havoc_range (rg_cont R) lo hi)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E R m o lo hi bs Hk0 HR Ho Hn Hlo Hhi Hz Hrz.
  pose proof (rg_havoc_ok E (RG (rg_base R) (rg_size R) RW (rg_cont R)) m o lo hi bs eq_refl (rz_weaken E m R (or_introl Hk0) HR) Ho Hn Hlo Hhi) as HW.
  unfold rsz in HW; cbn [rg_base rg_size rg_cont] in HW.
  destruct HW as (W1 & W2 & W3 & W4). destruct HR as (H1 & H2 & H3 & H4). rewrite Hk0 in H3.
  unfold rg_ok, rsz in *; cbn [rg_base rg_size rg_kind rg_cont] in *. split; [exact W1|]. split; [exact W2|]. split; [|exact W4].
  intros i Hi. split; [exact (W3 i Hi)|]. intros Hnt.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  unfold rd1 in *. rewrite write_to_mem_spec by lia. rewrite u_small64 by lia.
  destruct (Z.leb (A + o) (A + i) && Z.ltb (A + i) (A + o + Z.of_nat (length bs)))%bool eqn:E1.
  - apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    destruct (nth_error bs (Z.to_nat (A + i - (A + o)))) as [b|] eqn:Hb.
    + rewrite (Hz _ _ Hb). reflexivity.
    + apply nth_error_None in Hb. lia.
  - destruct (tget (okey i) (rg_cont R)) as [v|] eqn:Ht.
    + unfold havoc_range in Hnt. rewrite tget_tfilter, Ht in Hnt.
      rewrite okey_pos in Hnt by lia.
      destruct (negb (Z.leb lo i && Z.ltb i hi)) eqn:Hin; [discriminate|].
      apply negb_false_iff in Hin. apply andb_prop in Hin as [Hin1 Hin2]. apply Z.leb_le in Hin1. apply Z.ltb_lt in Hin2.
      pose proof (range_zero_spec _ _ _ _ _ Hrz Ht ltac:(rewrite okey_pos by lia; lia)) as ->.
      destruct (H4 _ _ Ht) as [_ Hrd]. rewrite okey_pos in Hrd by lia. exact Hrd.
    + exact (proj2 (H3 i Hi) Ht).
Qed.

#[using="Type"] Lemma rg_store_okz : forall E R m o (bvs : list bval) (bs : list byte),
  rg_kind R = RZ -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bs) <= rsz E R -> length bvs = length bs ->
  (forall i x, nth_error bvs i = Some x -> nth_error bs i = Some (bden E x)) ->
  rg_ok segs E (write_to_mem m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs)
          (RG (rg_base R) (rg_size R) RZ (put_bytes (rg_cont R) o bvs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E R m o bvs bs Hk0 HR Ho Hn Hlen Hb.
  pose proof (rg_store_ok E (RG (rg_base R) (rg_size R) RW (rg_cont R)) m o bvs bs eq_refl (rz_weaken E m R (or_introl Hk0) HR) Ho Hn Hlen Hb) as HW.
  unfold rsz in HW; cbn [rg_base rg_size rg_cont] in HW.
  destruct HW as (W1 & W2 & W3 & W4). destruct HR as (H1 & H2 & H3 & H4). rewrite Hk0 in H3.
  unfold rg_ok, rsz in *; cbn [rg_base rg_size rg_kind rg_cont] in *. split; [exact W1|]. split; [exact W2|]. split; [|exact W4].
  intros i Hi. split; [exact (W3 i Hi)|]. intros Hnt.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  assert (Hout : ~ (o <= i < o + Z.of_nat (length bvs))).
  { intros Hin. rewrite put_bytes_spec in Hnt by exact Ho. rewrite okey_pos in Hnt by lia.
    replace (Z.leb o i && Z.ltb i (o + Z.of_nat (length bvs)))%bool with true in Hnt
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    destruct (nth_error bvs (Z.to_nat (i - o))) eqn:He; [discriminate|]. apply nth_error_None in He. lia. }
  assert (Hold : tget (okey i) (rg_cont R) = None).
  { rewrite put_bytes_spec in Hnt by exact Ho. rewrite okey_pos in Hnt by lia.
    replace (Z.leb o i && Z.ltb i (o + Z.of_nat (length bvs)))%bool with false in Hnt
      by (symmetry; apply andb_false_iff; destruct (Z_lt_ge_dec i o); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
    exact Hnt. }
  pose proof (proj2 (H3 i Hi) Hold) as Hz.
  unfold rd1 in *. rewrite write_to_mem_spec by lia. rewrite u_small64 by lia.
  replace (Z.leb (A + o) (A + i) && Z.ltb (A + i) (A + o + Z.of_nat (length bs)))%bool with false; [exact Hz|].
  symmetry. apply andb_false_iff. destruct (Z_lt_ge_dec i o); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_store_okz_z : forall E R m o (bvs : list bval) (bs : list byte),
  rg_kind R = RZ -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bs) <= rsz E R -> length bvs = length bs ->
  (forall i x, nth_error bvs i = Some x -> nth_error bs i = Some (bden E x)) ->
  rg_ok segs E (write_to_mem m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs)
          (RG (rg_base R) (rg_size R) RZ (put_bytes_z (rg_cont R) o bvs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E R m o bvs bs Hk0 HR Ho Hn Hlen Hb.
  pose proof (rg_store_okz E R m o bvs bs Hk0 HR Ho Hn Hlen Hb) as HZ.
  destruct HZ as (Z1 & Z2 & Z3 & Z4). unfold rg_ok, rsz in *; cbn [rg_base rg_size rg_kind rg_cont] in *.
  split; [exact Z1|]. split; [exact Z2|]. split.
  - intros i Hi. split; [exact (proj1 (Z3 i Hi))|]. intros Hnt.
    rewrite put_bytes_z_spec in Hnt by exact Ho. rewrite okey_pos in Hnt by lia.
    destruct (Z.leb o i && Z.ltb i (o + Z.of_nat (length bvs)))%bool eqn:Hin.
    + destruct (nth_error bvs (Z.to_nat (i - o))) as [v|] eqn:Hv.
      * destruct v as [[|b0|b0]|l j]; cbn [is_bk0] in Hnt; try discriminate.
        pose proof (Z4 (okey i) (BK 0)) as X. rewrite put_bytes_spec in X by exact Ho. rewrite okey_pos in X by lia.
        rewrite Hin, Hv in X. destruct (X eq_refl) as [_ X2]. rewrite X2. reflexivity.
      * apply nth_error_None in Hv. apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
    + apply (proj2 (Z3 i Hi)). rewrite put_bytes_spec by exact Ho. rewrite okey_pos by lia. rewrite Hin. exact Hnt.
  - intros p v Hp. rewrite put_bytes_z_spec in Hp by exact Ho. apply Z4. rewrite put_bytes_spec by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length bvs)))%bool; [|exact Hp].
    destruct (nth_error bvs (Z.to_nat (Zpos p - 1 - o))) as [x|]; [|discriminate].
    destruct (is_bk0 x); [discriminate | exact Hp].
Qed.

#[using="Type"] Lemma rg_store_oki : forall E R m o (bvs : list bval) (bs : list byte),
  rg_kind R = RI -> rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bs) <= rsz E R -> length bvs = length bs ->
  (forall i x, nth_error bvs i = Some x -> nth_error bs i = Some (bden E x)) ->
  rg_ok segs E (write_to_mem m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) bs)
          (RG (rg_base R) (rg_size R) RI (put_bytes (rg_cont R) o bvs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E R m o bvs bs Hk0 HR Ho Hn Hlen Hb.
  pose proof (rg_store_ok E (RG (rg_base R) (rg_size R) RW (rg_cont R)) m o bvs bs eq_refl (rz_weaken E m R (or_intror Hk0) HR) Ho Hn Hlen Hb) as HW.
  unfold rsz in HW; cbn [rg_base rg_size rg_cont] in HW.
  destruct HW as (W1 & W2 & W3 & W4). destruct HR as (H1 & H2 & H3 & H4). rewrite Hk0 in H3.
  unfold rg_ok, rsz in *; cbn [rg_base rg_size rg_kind rg_cont] in *. split; [exact W1|]. split; [exact W2|]. split; [|exact W4].
  intros i Hi. split; [exact (W3 i Hi)|]. intros Hnt.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  assert (Hout : ~ (o <= i < o + Z.of_nat (length bvs))).
  { intros Hin. rewrite put_bytes_spec in Hnt by exact Ho. rewrite okey_pos in Hnt by lia.
    replace (Z.leb o i && Z.ltb i (o + Z.of_nat (length bvs)))%bool with true in Hnt
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    destruct (nth_error bvs (Z.to_nat (i - o))) eqn:He; [discriminate|]. apply nth_error_None in He. lia. }
  assert (Hold : tget (okey i) (rg_cont R) = None).
  { rewrite put_bytes_spec in Hnt by exact Ho. rewrite okey_pos in Hnt by lia.
    replace (Z.leb o i && Z.ltb i (o + Z.of_nat (length bvs)))%bool with false in Hnt
      by (symmetry; apply andb_false_iff; destruct (Z_lt_ge_dec i o); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
    exact Hnt. }
  pose proof (proj2 (H3 i Hi) Hold) as Hz.
  unfold rd1 in *. rewrite write_to_mem_spec by lia. rewrite u_small64 by lia.
  replace (Z.leb (A + o) (A + i) && Z.ltb (A + i) (A + o + Z.of_nat (length bs)))%bool with false; [exact Hz|].
  symmetry. apply andb_false_iff. destruct (Z_lt_ge_dec i o); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma load_at_sound : forall E img fs rgs a sz sg r m,
  img_ok segs img -> Forall (rg_ok segs E m) rgs -> Forall (fact_ok E) fs -> load_at img fs rgs a sz sg = Some r ->
  exists bs, ov_read_bytes segs m (lden E a) (nbytes sz) = Some bs /\ (forall l, r = Some l -> lden E l = ld_word sz sg bs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E img fs rgs a sz sg r m Himg HG HF H. unfold load_at in H.
  destruct (find_rg fs rgs a (Z.of_nat (nbytes sz)) O) as [[[ri R0] o]|] eqn:Hfr.
  - injection H as <-.
    destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_off_sound E _ _ _ _ _ (size_lo_sound E fs R0 HF) Ho) as (Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as HR0.
    pose proof HR0 as HR00. destruct HR00 as (Hsz & Hflat & Hall & Hcont).
    pose proof (u_range E (rg_base R0)) as RA.
    destruct (rdn_from segs m (nbytes sz) (bv_unsigned (lden E (rg_base R0)) + o)) as (bs & Hbs & Hlen & Hnth).
    { lia. } { lia. }
    { intros i0 Hi0. replace (bv_unsigned (lden E (rg_base R0)) + o + i0) with (bv_unsigned (lden E (rg_base R0)) + (o + i0)) by lia.
      specialize (Hall (o + i0) ltac:(lia)). destruct (rg_kind R0);
      [ exact (proj1 Hall) | unfold rd1; rewrite (proj1 Hall); exact (proj2 Hall) | exact (proj1 (proj1 Hall)) | exact (proj1 (proj1 Hall)) | exact Hall ]. }
    exists bs. split; [rewrite ov_rdn, Haddr; exact Hbs|].
    intros l Hl. exact (ld_value_sound E fs img R0 m o sz sg bs HF Himg HR0 Ho0 Hon Hbs l Hl).
  - destruct (find_rg_sym fs rgs a (Z.of_nat (nbytes sz)) O) as [[[ri R0] [lo hi]]|] eqn:Hfs; [|discriminate].
    injection H as <-.
    destruct (find_rg_sym_spec _ _ _ _ _ _ _ _ _ Hfs) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_off_any_sound E _ _ _ _ _ _ HF Ho) as (o & Holh & Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as HR0.
    destruct HR0 as (Hsz & Hflat & Hall & Hcont).
    pose proof (u_range E (rg_base R0)) as RA.
    destruct (rdn_from segs m (nbytes sz) (bv_unsigned (lden E (rg_base R0)) + o)) as (bs & Hbs & Hlen & Hnth).
    { lia. } { lia. }
    { intros i0 Hi0. replace (bv_unsigned (lden E (rg_base R0)) + o + i0) with (bv_unsigned (lden E (rg_base R0)) + (o + i0)) by lia.
      specialize (Hall (o + i0) ltac:(lia)). destruct (rg_kind R0);
      [ exact (proj1 Hall) | unfold rd1; rewrite (proj1 Hall); exact (proj2 Hall) | exact (proj1 (proj1 Hall)) | exact (proj1 (proj1 Hall)) | exact Hall ]. }
    exists bs. split; [rewrite ov_rdn, Haddr; exact Hbs|].
    intros l Hl. unfold sym_ld in Hl.
    assert (HR0' : rg_ok segs E m R0) by exact (proj1 (Forall_nth' _ _) HG ri R0 Hnth0).
    destruct (is_rz (rg_kind R0) &&& range_zero (rg_cont R0) lo (hi + Z.of_nat (nbytes sz))) eqn:Hz.
    { apply andb_prop in Hz as [Hk Hz]. destruct (rg_kind R0) eqn:Hk0; try discriminate.
      assert (Hlo0 : 0 <= lo) by exact (rg_off_any_lo _ _ _ _ _ _ Ho).
      assert (Hgz : forall o', lo <= o' <= hi -> get_bytes_z (rg_cont R0) o' (nbytes sz) = repeat (BK 0) (nbytes sz)).
      { intros o' Ho'. assert (Hgen : forall n o0, lo <= o0 -> o0 + Z.of_nat n <= hi + Z.of_nat (nbytes sz) ->
                                   get_bytes_z (rg_cont R0) o0 n = repeat (BK 0) n).
        { induction n as [|n IHn]; intros o0 Ho1 Ho2; [reflexivity|]. cbn [get_bytes_z repeat].
          rewrite (IHn (o0 + 1)) by lia. f_equal.
          destruct (tget (okey o0) (rg_cont R0)) as [v|] eqn:Ht0; [|reflexivity].
          unfold range_zero in Hz. assert (Htf : tget (okey o0) (tfilter (fun p => (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) (hi + Z.of_nat (nbytes sz)))%bool) (rg_cont R0)) = Some v).
          { rewrite tget_tfilter, Ht0. rewrite okey_pos by lia. replace (o0 + 1 - 1) with o0 by lia.
            assert (E1 : Z.leb lo o0 = true) by (apply Z.leb_le; lia). assert (E2 : Z.ltb o0 (hi + Z.of_nat (nbytes sz)) = true) by (apply Z.ltb_lt; lia).
            rewrite E1, E2. reflexivity. }
          pose proof (tall_spec _ _ _ _ Hz Htf) as Hb. destruct v as [[|b|b]|l0 j]; cbn in Hb; try discriminate. reflexivity. }
        apply Hgen; lia. }
      assert (Hlv : ld_value img fs R0 o sz sg = Some l).
      { unfold ld_value in Hl |- *. rewrite Hk0 in Hl |- *. rewrite (Hgz o ltac:(lia)). rewrite (Hgz lo ltac:(lia)) in Hl. exact Hl. }
      exact (ld_value_sound E fs img R0 m o sz sg bs HF Himg HR0' Ho0 Hon Hbs _ Hlv). }
    destruct (Z.leb (hi - lo) 512); [|discriminate].
    destruct (ld_value img fs R0 lo sz sg) as [[c [|]]|] eqn:Hlo; try discriminate.
    destruct (uni_ld img fs R0 lo (Z.to_nat (hi - lo + 1)) sz sg c) eqn:Hu; [|discriminate]. injection Hl as <-.
    assert (Hall' : forall n o', uni_ld img fs R0 lo n sz sg c = true -> lo <= o' < lo + Z.of_nat n -> ld_value img fs R0 o' sz sg = Some (LIN c [])).
    { intros n. generalize lo. induction n as [|n IH]; intros lo0 o' Hun Ho'; [lia|].
      cbn [uni_ld] in Hun. destruct (ld_value img fs R0 lo0 sz sg) as [[c' [|]]|] eqn:Hl0; try discriminate.
      apply andb_prop in Hun as [Hc Hun]. apply Z.eqb_eq in Hc. subst c'.
      destruct (Z.eq_dec o' lo0) as [->|Hne]; [exact Hl0|]. apply (IH (lo0 + 1)); [exact Hun | lia]. }
    pose proof (Hall' _ o Hu ltac:(lia)) as Hlv.
    exact (ld_value_sound E fs img R0 m o sz sg bs HF Himg HR0' Ho0 Hon Hbs _ Hlv).
Qed.

#[using="Type"] Lemma store_at_sound : forall E fs rgs a w bvs rgs' m bs,
  Forall (rg_ok segs E m) rgs -> rgs_disj E rgs -> Forall (fact_ok E) fs -> store_at fs rgs a w bvs = Some rgs' ->
  length bs = w -> length bvs = w -> (forall i x, nth_error bvs i = Some x -> nth_error bs i = Some (bden E x)) ->
  store_ok segs m (lden E a) w = true /\ Forall (rg_ok segs E (write_to_mem m (lden E a) bs)) rgs' /\ rgs_disj E rgs'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs rgs a w bvs rgs' m bs HG HD HF H Hlb Hlv Hbv. unfold store_at in H.
  destruct (find_rg fs rgs a (Z.of_nat w) O) as [[[ri R0] o]|] eqn:Hfr.
  - destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_off_sound E _ _ _ _ _ (size_lo_sound E fs R0 HF) Ho) as (Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as HR0.
    pose proof (u_range E (rg_base R0)) as RA.
    assert (HW : forall i0, 0 <= i0 < rsz E R0 -> wview segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R0)) + i0)) <> None).
    { intros i0 Hi0. destruct HR0 as (_ & _ & Hall & _). specialize (Hall i0 Hi0).
      destruct (rg_kind R0) eqn:Hk0; [exact (proj2 Hall) | discriminate | exact (proj2 (proj1 Hall)) | exact (proj2 (proj1 Hall)) | discriminate]. }
    assert (Hflat : bv_unsigned (lden E (rg_base R0)) + rsz E R0 <= two64) by exact (proj1 (proj2 HR0)).
    destruct (rg_kind R0) eqn:Hk0; [ | discriminate | | | discriminate ]; injection H as <-;
    (rewrite Haddr; split; [|split];
    [ apply store_ok_from; [lia | lia |]; intros i0 Hi0;
      replace (bv_unsigned (lden E (rg_base R0)) + o + i0) with (bv_unsigned (lden E (rg_base R0)) + (o + i0)) by lia;
      apply (HW (o + i0) ltac:(lia))
    | apply Forall_nth'; intros j Rj Hj; destruct (Nat.eq_dec j ri) as [->|Hne];
      [ rewrite (nth_upd_same _ _ _ _ Hnth0) in Hj; injection Hj as <-;
        first [ apply rg_store_ok; [exact Hk0 | exact HR0 | exact Ho0 | rewrite Hlb; exact Hon | congruence | exact Hbv]
              | apply rg_store_okz; [exact Hk0 | exact HR0 | exact Ho0 | rewrite Hlb; exact Hon | congruence | exact Hbv]
              | apply rg_store_oki; [exact Hk0 | exact HR0 | exact Ho0 | rewrite Hlb; exact Hon | congruence | exact Hbv] ]
      | rewrite nth_upd_other in Hj by lia;
        eapply (rgs_frame_write segs E m rgs ri R0 o); [exact HG | exact HD | exact Hnth0 | exact Ho0
                                                       | rewrite Hlb; exact Hon | exact Hne | exact Hj] ]
    | eapply rgs_disj_upd; [exact Hnth0 | reflexivity | reflexivity | exact HD] ]).
  - destruct (find_rg_sym fs rgs a (Z.of_nat w) O) as [[[ri R0] [lo hi]]|] eqn:Hfs; [|discriminate].
    destruct (find_rg_sym_spec _ _ _ _ _ _ _ _ _ Hfs) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_off_any_sound E _ _ _ _ _ _ HF Ho) as (o & Holh & Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as HR0.
    pose proof (u_range E (rg_base R0)) as RA.
    assert (HRW : rg_kind R0 = RW \/ rg_kind R0 = RZ \/ rg_kind R0 = RI -> rg_ok segs E m (RG (rg_base R0) (rg_size R0) RW (rg_cont R0))).
    { intros [Hk|Hk]; [destruct R0 as [b0 s0 k0 c0]; cbn in Hk; subst k0; exact HR0 | exact (rz_weaken E m R0 Hk HR0)]. }
    assert (Hcase : rg_kind R0 = RW \/ rg_kind R0 = RZ \/ rg_kind R0 = RI)
      by (destruct (rg_kind R0); [left; reflexivity | discriminate | right; left; reflexivity | right; right; reflexivity | discriminate]).
    assert (Hzst : rg_kind R0 = RZ -> (forallb is_bk0 bvs && range_zero (rg_cont R0) lo (hi + Z.of_nat w))%bool = true ->
                   store_ok segs m (lden E a) w = true /\
                   Forall (rg_ok segs E (write_to_mem m (lden E a) bs)) (upd_nth rgs ri (RG (rg_base R0) (rg_size R0) RZ (havoc_range (rg_cont R0) lo (hi + Z.of_nat w)))) /\
                   rgs_disj E (upd_nth rgs ri (RG (rg_base R0) (rg_size R0) RZ (havoc_range (rg_cont R0) lo (hi + Z.of_nat w))))).
    { intros Hk Hzz. apply andb_prop in Hzz as [Hzb Hrz].
      pose proof (HRW Hcase) as HR0'; pose proof HR0' as HR00; destruct HR00 as (Hsz & Hflat & Hall & Hcont); unfold rsz in Hsz, Hflat, Hall, Hon; cbn [rg_kind rg_base rg_size] in Hsz, Hflat, Hall.
      rewrite Haddr; split; [|split].
      - apply store_ok_from; [lia | lia |]; intros i0 Hi0.
        replace (bv_unsigned (lden E (rg_base R0)) + o + i0) with (bv_unsigned (lden E (rg_base R0)) + (o + i0)) by lia.
        apply (proj2 (Hall (o + i0) ltac:(unfold rsz in *; cbn [rg_size] in *; lia))).
      - apply Forall_nth'; intros j Rj Hj; destruct (Nat.eq_dec j ri) as [->|Hne].
        + rewrite (nth_upd_same _ _ _ _ Hnth0) in Hj; injection Hj as <-.
          apply (rg_zstore_ok E R0); [exact Hk | exact HR0 | exact Ho0 | rewrite Hlb; exact Hon | lia | rewrite Hlb; lia | | exact Hrz].
          intros i b Hb. rewrite forallb_forall in Hzb.
          assert (Hi : (i < length bvs)%nat) by (rewrite Hlv, <- Hlb; apply nth_error_Some; rewrite Hb; discriminate).
          destruct (nth_error bvs i) as [x|] eqn:Hx; [|apply nth_error_None in Hx; lia].
          pose proof (Hzb x (nth_error_In _ _ Hx)) as Hx0. rewrite (Hbv i x Hx) in Hb. injection Hb as <-.
          destruct x as [[|b0|b0]|l j']; cbn in Hx0; try discriminate. reflexivity.
        + rewrite nth_upd_other in Hj by lia.
          eapply (rgs_frame_write segs E m rgs ri R0 o); [exact HG | exact HD | exact Hnth0 | exact Ho0 | rewrite Hlb; exact Hon | exact Hne | exact Hj].
      - eapply rgs_disj_upd; [exact Hnth0 | reflexivity | reflexivity | exact HD]. }
    destruct (rg_kind R0) eqn:Hk0; [ | discriminate | | | discriminate ];
    [ | destruct (forallb is_bk0 bvs && range_zero (rg_cont R0) lo (hi + Z.of_nat w))%bool eqn:Hzz; [injection H as <-; exact (Hzst eq_refl eq_refl)|] | ];
    injection H as <-;
    (pose proof (HRW Hcase) as HR0'; pose proof HR0' as HR00; destruct HR00 as (Hsz & Hflat & Hall & Hcont); unfold rsz in Hsz, Hflat, Hall, Hon; cbn [rg_kind rg_base rg_size] in Hsz, Hflat, Hall;
    rewrite Haddr; split; [|split];
    [ apply store_ok_from; [lia | lia |]; intros i0 Hi0;
      replace (bv_unsigned (lden E (rg_base R0)) + o + i0) with (bv_unsigned (lden E (rg_base R0)) + (o + i0)) by lia;
      apply (proj2 (Hall (o + i0) ltac:(unfold rsz in *; cbn [rg_size] in *; lia)))
    | apply Forall_nth'; intros j Rj Hj; destruct (Nat.eq_dec j ri) as [->|Hne];
      [ rewrite (nth_upd_same _ _ _ _ Hnth0) in Hj; injection Hj as <-;
        apply (rg_havoc_ok E (RG (rg_base R0) (rg_size R0) RW (rg_cont R0))); [reflexivity | exact HR0' | exact Ho0 | rewrite Hlb; exact Hon | lia | rewrite Hlb; lia]
      | rewrite nth_upd_other in Hj by lia;
        eapply (rgs_frame_write segs E m rgs ri R0 o); [exact HG | exact HD | exact Hnth0 | exact Ho0
                                                       | rewrite Hlb; exact Hon | exact Hne | exact Hj] ]
    | eapply rgs_disj_upd; [exact Hnth0 | reflexivity | reflexivity | exact HD] ]).
Qed.

(* [comment removed for export] *)
Definition shape (rgs : list region) : list (lin * lin) := List.map (fun R => (rg_base R, rg_size R)) rgs.
Definition outside (E : valu) (rgs : list region) (x : word) : Prop :=
  Forall (fun R => bv_unsigned x < bv_unsigned (lden E (rg_base R)) \/ bv_unsigned (lden E (rg_base R)) + rsz E R <= bv_unsigned x) rgs.

#[using="Type"] Lemma shape_upd : forall rgs i R R0, nth_error rgs i = Some R0 -> rg_base R = rg_base R0 -> rg_size R = rg_size R0 ->
  shape (upd_nth rgs i R) = shape rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction rgs as [|x rs IH]; intros [|i] R R0 H Hb Hs; cbn in *; try discriminate.
  - injection H as <-. rewrite Hb, Hs. reflexivity.
  - f_equal. eapply IH; eassumption.
Qed.

#[using="Type"] Lemma store_at_shape : forall fs rgs a w bvs rgs', store_at fs rgs a w bvs = Some rgs' -> shape rgs' = shape rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fs rgs a w bvs rgs' H. unfold store_at in H.
  destruct (find_rg fs rgs a (Z.of_nat w) O) as [[[ri R0] o]|] eqn:Hfr.
  - destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth0 & _). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_kind R0); try discriminate; injection H as <-; apply (shape_upd _ _ _ R0 Hnth0); reflexivity.
  - destruct (find_rg_sym fs rgs a (Z.of_nat w) O) as [[[ri R0] [lo hi]]|] eqn:Hfs; [|discriminate].
    destruct (find_rg_sym_spec _ _ _ _ _ _ _ _ _ Hfs) as (_ & Hnth0 & _). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_kind R0); try discriminate; try (destruct (forallb is_bk0 bvs && range_zero (rg_cont R0) lo (hi + Z.of_nat w))%bool);
      injection H as <-; apply (shape_upd _ _ _ R0 Hnth0); reflexivity.
Qed.

#[using="Type"] Lemma write_outside : forall m A o w bs x, 0 <= A -> 0 <= o -> A + o + Z.of_nat w <= two64 -> length bs = w ->
  (bv_unsigned x < A \/ A + o + Z.of_nat w <= bv_unsigned x \/ bv_unsigned x < A + o) ->
  write_to_mem m (Z_to_bv 64 (A + o)) bs x = m x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A o w bs x HA Ho Hw Hl Hx. rewrite write_to_mem_spec by lia.
  replace (Z.leb (A + o) (bv_unsigned x) && Z.ltb (bv_unsigned x) (A + o + Z.of_nat (length bs)))%bool with false; [reflexivity|].
  symmetry. apply andb_false_iff. rewrite Hl. destruct Hx as [Hx|[Hx|Hx]]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
Qed.

#[using="Type"] Lemma store_at_frame : forall E fs rgs a w bvs rgs' m bs, Forall (rg_ok segs E m) rgs -> Forall (fact_ok E) fs ->
  store_at fs rgs a w bvs = Some rgs' -> length bs = w ->
  forall x, outside E rgs x -> write_to_mem m (lden E a) bs x = m x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs rgs a w bvs rgs' m bs HG HF H Hl x Hx. unfold store_at in H.
  destruct (find_rg fs rgs a (Z.of_nat w) O) as [[[ri R0] o]|] eqn:Hfr.
  - destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_off_sound E _ _ _ _ _ (size_lo_sound E fs R0 HF) Ho) as (Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as (_ & Hflat & _).
    pose proof (proj1 (Forall_nth' _ _) Hx ri R0 Hnth0) as Hout. cbv beta in Hout. pose proof (u_range E (rg_base R0)) as RA.
    rewrite Haddr. apply (write_outside m _ o w bs x); [lia | lia | lia | exact Hl | lia].
  - destruct (find_rg_sym fs rgs a (Z.of_nat w) O) as [[[ri R0] [lo hi]]|] eqn:Hfs; [|discriminate].
    destruct (find_rg_sym_spec _ _ _ _ _ _ _ _ _ Hfs) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_off_any_sound E _ _ _ _ _ _ HF Ho) as (o & Holh & Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as (_ & Hflat & _).
    pose proof (proj1 (Forall_nth' _ _) Hx ri R0 Hnth0) as Hout. cbv beta in Hout. pose proof (u_range E (rg_base R0)) as RA.
    rewrite Haddr. apply (write_outside m _ o w bs x); [lia | lia | lia | exact Hl | lia].
Qed.

(* [comment removed for export] *)
Definition is_rt (k : rkind) : bool := match k with RT => true | _ => false end.
Definition rtm (rgs : list region) : list bool := List.map (fun R => is_rt (rg_kind R)) rgs.
Definition in_rg (E : valu) (R : region) (x : word) : Prop :=
  bv_unsigned (lden E (rg_base R)) <= bv_unsigned x < bv_unsigned (lden E (rg_base R)) + rsz E R.
(* [comment removed for export] *)
Definition fr_pt (E : valu) (rgs : list region) (x : word) : Prop :=
  outside E rgs x \/ Exists (fun R => is_rt (rg_kind R) = true /\ in_rg E R x) rgs.

#[using="Type"] Lemma outside_shape_s : forall E rgs rgs' x, shape rgs' = shape rgs -> outside E rgs x -> outside E rgs' x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rgs. induction rgs as [|R rs IH]; intros [|R' rs'] x Hs H; cbn in *; try discriminate; [constructor|].
  injection Hs as Hb Hsz Hrs. inversion H; subst. constructor; [unfold rsz in *; rewrite Hb, Hsz; assumption | exact (IH rs' x Hrs H3)].
Qed.
#[using="Type"] Lemma rt_in_shape : forall E rgs rgs' x, shape rgs' = shape rgs -> rtm rgs' = rtm rgs ->
  Exists (fun R => is_rt (rg_kind R) = true /\ in_rg E R x) rgs -> Exists (fun R => is_rt (rg_kind R) = true /\ in_rg E R x) rgs'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rgs. induction rgs as [|R rs IH]; intros [|R' rs'] x Hs Hm H; cbn [shape rtm List.map] in Hs, Hm; try discriminate.
  - inversion H.
  - injection Hs as Hb Hsz Hrs. injection Hm as Hk Hrm. inversion H as [? ? [Hr Hin] | ? ? He]; subst.
    + apply Exists_cons_hd. split; [rewrite Hk; exact Hr | unfold in_rg, rsz in *; rewrite Hb, Hsz; exact Hin].
    + apply Exists_cons_tl. exact (IH rs' x Hrs Hrm He).
Qed.
#[using="Type"] Lemma fr_pt_shape : forall E rgs rgs' x, shape rgs' = shape rgs -> rtm rgs' = rtm rgs -> fr_pt E rgs x -> fr_pt E rgs' x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rgs rgs' x Hs Hm [H|H]; [left; exact (outside_shape_s E rgs rgs' x Hs H) | right; exact (rt_in_shape E rgs rgs' x Hs Hm H)].
Qed.

#[using="Type"] Lemma rtm_upd : forall rgs i R R0, nth_error rgs i = Some R0 -> is_rt (rg_kind R) = is_rt (rg_kind R0) -> rtm (upd_nth rgs i R) = rtm rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction rgs as [|x rs IH]; intros [|i] R R0 H Hk; cbn in *; try discriminate.
  - injection H as <-. rewrite Hk. reflexivity.
  - f_equal. eapply IH; eassumption.
Qed.

#[using="Type"] Lemma store_at_rtm : forall fs rgs a w bvs rgs', store_at fs rgs a w bvs = Some rgs' -> rtm rgs' = rtm rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fs rgs a w bvs rgs' H. unfold store_at in H.
  destruct (find_rg fs rgs a (Z.of_nat w) O) as [[[ri R0] o]|] eqn:Hfr.
  - destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth0 & _). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_kind R0) eqn:Hk; try discriminate; injection H as <-; apply (rtm_upd _ _ _ R0 Hnth0); rewrite Hk; reflexivity.
  - destruct (find_rg_sym fs rgs a (Z.of_nat w) O) as [[[ri R0] [lo hi]]|] eqn:Hfs; [|discriminate].
    destruct (find_rg_sym_spec _ _ _ _ _ _ _ _ _ Hfs) as (_ & Hnth0 & _). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_kind R0) eqn:Hk; try discriminate; try (destruct (forallb is_bk0 bvs && range_zero (rg_cont R0) lo (hi + Z.of_nat w))%bool);
      injection H as <-; apply (rtm_upd _ _ _ R0 Hnth0); rewrite Hk; reflexivity.
Qed.

#[using="Type"] Lemma store_at_frame_fr : forall E fs rgs a w bvs rgs' m bs, Forall (rg_ok segs E m) rgs -> rgs_disj E rgs -> Forall (fact_ok E) fs ->
  store_at fs rgs a w bvs = Some rgs' -> length bs = w ->
  forall x, fr_pt E rgs x -> write_to_mem m (lden E a) bs x = m x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs rgs a w bvs rgs' m bs HG HD HF H Hl x [Hx|Hx]; [exact (store_at_frame E fs rgs a w bvs rgs' m bs HG HF H Hl x Hx)|].
  apply Exists_exists in Hx as (Rj & HRj & Hrt & Hin). apply In_nth_error in HRj as [j Hj].
  unfold store_at in H.
  destruct (find_rg fs rgs a (Z.of_nat w) O) as [[[ri R0] o]|] eqn:Hfr.
  - destruct (find_rg_spec _ _ _ _ _ _ _ _ Hfr) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_off_sound E _ _ _ _ _ (size_lo_sound E fs R0 HF) Ho) as (Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as (_ & Hflat & _).
    pose proof (u_range E (rg_base R0)) as RA.
    assert (Hne : ri <> j).
    { intros ->. rewrite Hnth0 in Hj. injection Hj as <-. destruct (rg_kind R0); cbn in Hrt; try discriminate. }
    pose proof (rgs_disj_nth E rgs ri j R0 Rj HD Hne Hnth0 Hj) as Hdj. unfold rg_disj, in_rg in *.
    rewrite Haddr. apply (write_outside m _ o w bs x); [lia | lia | lia | exact Hl | lia].
  - destruct (find_rg_sym fs rgs a (Z.of_nat w) O) as [[[ri R0] [lo hi]]|] eqn:Hfs; [|discriminate].
    destruct (find_rg_sym_spec _ _ _ _ _ _ _ _ _ Hfs) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
    destruct (rg_off_any_sound E _ _ _ _ _ _ HF Ho) as (o & Holh & Ho0 & Hon & Haddr).
    pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as (_ & Hflat & _).
    pose proof (u_range E (rg_base R0)) as RA.
    assert (Hne : ri <> j).
    { intros ->. rewrite Hnth0 in Hj. injection Hj as <-. destruct (rg_kind R0); cbn in Hrt; try discriminate. }
    pose proof (rgs_disj_nth E rgs ri j R0 Rj HD Hne Hnth0 Hj) as Hdj. unfold rg_disj, in_rg in *.
    rewrite Haddr. apply (write_outside m _ o w bs x); [lia | lia | lia | exact Hl | lia].
Qed.

#[using="Type"] Lemma s_rgs_set_res : forall s rd r fs npc, s_rgs (set_res s rd r fs npc) = s_rgs s.
Proof. LiaFast.lf_pins LiaFast.u0. intros s rd [l|] fs npc; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma off_ne : forall E a b d, lin_off a b = Some d -> d <> 0 -> bv_unsigned (lden E a) <> bv_unsigned (lden E b).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E a b d H Hd Heq. destruct (lin_off_sound E a b d H) as [Hs Hr].
  assert (Hab : lden E a = lden E b) by (apply bv_eq; exact Heq).
  rewrite lden_lsub, Hab in Hs.
  assert (Hu : bv_unsigned (bv_sub (lden E b) (lden E b)) = 0) by (rewrite bv_sub_unsigned, Z.sub_diag; reflexivity).
  rewrite Hs, u_small64 in Hu by exact Hr. exact (Hd Hu).
Qed.

#[using="Type"] Lemma inval_sound : forall E r rv a, rsv_ok E r rv -> rsv_ok E (inval r a) (ival (lden E a) rv).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E r rv a H. destruct r as [|l|]; cbn [rsv_ok inval] in *.
  - subst rv. reflexivity.
  - subst rv. unfold ival. destruct (lin_off l a) as [d|] eqn:Hd; [|exact I].
    destruct (Z.eqb_spec d 0) as [->|Hne].
    + rewrite (lden_eq_of_off0 E l a Hd), Z.eqb_refl. reflexivity.
    + cbn [rsv_ok]. destruct (Z.eqb_spec (bv_unsigned (lden E l)) (bv_unsigned (lden E a))) as [Heq|_]; [|reflexivity].
      exfalso. exact (off_ne E l a d Hd Hne Heq).
  - exact I.
Qed.

#[using="Type"] Lemma sc_ok_sound : forall E r rv a b, rsv_ok E r rv -> sc_ok r a = Some b ->
  (b = true -> exists r0, rv = Some r0 /\ bv_unsigned r0 = bv_unsigned (lden E a)) /\
  (b = false -> match rv with Some r0 => Z.eqb (bv_unsigned r0) (bv_unsigned (lden E a)) = false | None => True end).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E r rv a b H Hs. destruct r as [|l|]; cbn [rsv_ok sc_ok] in *.
  - injection Hs as <-. subst rv. split; [discriminate | intros _; exact I].
  - subst rv. destruct (lin_off l a) as [d|] eqn:Hd; [|discriminate]. injection Hs as <-.
    split.
    + intros Hb. apply Z.eqb_eq in Hb. subst d. exists (lden E l). split; [reflexivity|].
      rewrite (lden_eq_of_off0 E l a Hd). reflexivity.
    + intros Hb. apply Z.eqb_neq in Hb. apply Z.eqb_neq. exact (off_ne E l a d Hd Hb).
  - discriminate.
Qed.

#[using="Type"] Lemma amo_al_sound : forall E fs wd a, Forall (fact_ok E) fs -> amo_al fs wd a = true -> amo_aligned wd (lden E a) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs wd a HF H. unfold amo_al in H. apply Z.leb_le in H. destruct (lalign_sound E fs a HF) as [Hb Hd].
  unfold amo_aligned. apply Z.eqb_eq. apply Z.mod_divide; [destruct wd; cbn; lia|].
  apply Z.divide_trans with (2 ^ lalign fs a); [|exact Hd].
  replace (amo_bytes wd) with (2 ^ amo_lg wd) by (destruct wd; reflexivity).
  apply pow2_divide_le. destruct wd; cbn [amo_lg] in *; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma low32_zext : forall x : bv 32, low32 (zext 64 x) = x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x. apply bv_eq. unfold low32, zext. rewrite bv_extract_unsigned, bv_zero_extend_unsigned by lia.
  rewrite Z.shiftr_0_r. apply bv_wrap_small. apply (bv_unsigned_in_range _ x).
Qed.

#[using="Type"] Lemma amo_st_word : forall E op wd ov src, (op = AMO_ADD \/ op = AMO_SWAP) ->
  st_word (amo_sz wd) (lden E (amo_new op ov src)) = st_word (amo_sz wd) (amo_word op wd (lden E ov) (lden E src)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E op wd ov src Hop. destruct Hop as [-> | ->]; destruct wd; cbn [amo_new amo_sz amo_word amo_val st_word].
  - rewrite lden_ladd, low32_zext. unfold low32.
    rewrite !bv_extract_unsigned, !bv_add_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
    rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity).
    rewrite Z.add_mod by lia. reflexivity.
  - rewrite lden_ladd. reflexivity.
  - rewrite low32_zext. reflexivity.
  - reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma res_sound_gen : forall E s ms (rd : reg) r fs npc (v : word) fr' fc' rsym rv',
  sden segs E s ms ->
  (forall E', agree (s_next s) E E' -> regs_ok E' (s_regs s) (ms_regs ms) -> forall l, r = Some l -> lden E' l = v) ->
  (forall E'', agree (s_next s) E E'' -> E'' (s_next s) = v -> Forall (fact_ok E'') (fs (lvar (s_next s)))) ->
  frm_zero fc' ->
  (forall E'', agree (s_next s) E E'' -> rsv_ok E'' rsym rv') ->
  exists E', agree (s_next s) E E' /\ (s_next s <= s_next (with_resv (set_res s (rkey rd) r fs npc) rsym))%positive /\
    sden segs E' (with_resv (set_res s (rkey rd) r fs npc) rsym)
      (mks fr' fc' (rupd (ms_regs ms) rd v) (Z_to_bv 64 npc) rv' (ms_mem ms) (ms_rom ms)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms rd r fs npc v fr' fc' rsym rv' Hden Hval Hfs Hfrm Hrv.
  destruct r as [l|].
  - exists E. split; [apply agree_refl|]. split; [cbn; lia|].
    intros E'' Ha. destruct (Hden E'' Ha) as (_ & _ & _ & HR & HG & HD & HF & _).
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv set_res with_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact (Hrv E'' Ha)|].
    split; [apply regs_ok_upd; [exact HR | apply (Hval E'' Ha HR l eq_refl)]|].
    split; [exact HG|]. split; [exact HD|]. split; [exact HF | exact Hfrm].
  - exists (upd E (s_next s) v). split; [apply agree_upd|]. split; [cbn; lia|].
    intros E'' Ha. cbn [s_next set_res with_resv] in Ha.
    assert (Ha0 : agree (s_next s) E E'').
    { intros x Hx. rewrite <- (Ha x ltac:(lia)). unfold upd. destruct (Pos.eqb_spec x (s_next s)); [lia | reflexivity]. }
    assert (Hv : E'' (s_next s) = v) by (rewrite <- (Ha (s_next s) ltac:(lia)); unfold upd; rewrite Pos.eqb_refl; reflexivity).
    destruct (Hden E'' Ha0) as (_ & _ & _ & HR & HG & HD & HF & _).
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv set_res with_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact (Hrv E'' Ha0)|].
    split; [apply regs_ok_upd; [exact HR | rewrite lden_lvar; exact Hv]|].
    split; [exact HG|]. split; [exact HD|]. split; [apply Forall_app; split; [exact (Hfs E'' Ha0 Hv) | exact HF] | exact Hfrm].
Qed.

#[using="Type"] Lemma with_resv_same : forall s rd r fs npc, with_resv (set_res s rd r fs npc) (s_resv s) = set_res s rd r fs npc.
Proof. LiaFast.lf_pins LiaFast.u0. intros s rd [l|] fs npc; reflexivity. Qed.

#[using="Type"] Lemma res_sound : forall E s ms (rd : reg) r fs npc (v : word) fr' fc',
  sden segs E s ms ->
  (forall E', agree (s_next s) E E' -> regs_ok E' (s_regs s) (ms_regs ms) -> forall l, r = Some l -> lden E' l = v) ->
  (forall E'', agree (s_next s) E E'' -> E'' (s_next s) = v -> Forall (fact_ok E'') (fs (lvar (s_next s)))) ->
  frm_zero fc' ->
  exists E', agree (s_next s) E E' /\ (s_next s <= s_next (set_res s (rkey rd) r fs npc))%positive /\
    sden segs E' (set_res s (rkey rd) r fs npc) (mks fr' fc' (rupd (ms_regs ms) rd v) (Z_to_bv 64 npc) (ms_resv ms) (ms_mem ms) (ms_rom ms)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms rd r fs npc v fr' fc' Hden Hval Hfs Hfrm.
  destruct (res_sound_gen E s ms rd r fs npc v fr' fc' (s_resv s) (ms_resv ms) Hden Hval Hfs Hfrm) as (E' & Ha & Hn & Hs).
  - intros E'' Ha''. exact (proj1 (proj2 (proj2 (Hden E'' Ha'')))).
  - rewrite with_resv_same in Hn, Hs. exists E'. split; [exact Ha | split; [exact Hn | exact Hs]].
Qed.

#[using="Type"] Lemma pc_sound : forall E s ms npc fr' fc', sden segs E s ms -> frm_zero fc' ->
  sden segs E (with_pc s npc) (mks fr' fc' (ms_regs ms) (Z_to_bv 64 npc) (ms_resv ms) (ms_mem ms) (ms_rom ms)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms npc fr' fc' Hden Hfrm E'' Ha. destruct (Hden E'' Ha) as (_ & _ & Hrv & HR & HG & HD & HF & _).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv with_pc mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
  repeat split; assumption.
Qed.

#[using="Type"] Lemma mem_sound : forall E E1 s ms a w bvs rgs' bs R' nx rsym regs' rv' npc,
  sden segs E s ms -> agree (s_next s) E E1 -> (s_next s <= nx)%positive ->
  store_at (s_facts s) (s_rgs s) a w bvs = Some rgs' ->
  (forall E'', agree (s_next s) E E'' -> lden E'' a = lden E a) ->
  length bs = w -> length bvs = w ->
  (forall E'', agree nx E1 E'' -> forall i x, nth_error bvs i = Some x -> nth_error bs i = Some (bden E'' x)) ->
  (forall E'', agree nx E1 E'' -> regs_ok E'' R' regs') ->
  (forall E'', agree nx E1 E'' -> rsv_ok E'' rsym rv') ->
  store_ok segs (ms_mem ms) (lden E a) w = true /\
  sden segs E1 (SST npc R' rgs' (s_facts s) nx rsym)
       (mks (ms_fregs ms) (ms_fcsr ms) regs' (Z_to_bv 64 npc) rv' (write_to_mem (ms_mem ms) (lden E a) bs) (ms_rom ms)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E E1 s ms a w bvs rgs' bs R' nx rsym regs' rv' npc Hden Ha1 Hnx Hsa Haddr Hlb Hlv Hbv HR' Hrv.
  assert (Hag : forall E'', agree nx E1 E'' -> agree (s_next s) E E'').
  { intros E'' H x Hx. rewrite (Ha1 x Hx). apply H. lia. }
  split.
  - destruct (Hden E (agree_refl _ _)) as (_ & _ & _ & _ & HG & HD & HF & _).
    pose proof (Hbv E1 (agree_refl _ _)) as Hb1.
    (* [comment removed for export] *)
    destruct (Hden E1 Ha1) as (_ & _ & _ & _ & HG1 & HD1 & HF1 & _).
    rewrite <- (Haddr E1 Ha1).
    exact (proj1 (store_at_sound E1 _ _ _ _ _ _ _ bs HG1 HD1 HF1 Hsa Hlb Hlv Hb1)).
  - intros E'' Ha''. pose proof (Hag E'' Ha'') as Ha0.
    destruct (Hden E'' Ha0) as (_ & _ & _ & _ & HG & HD & HF & Hfrm).
    destruct (store_at_sound E'' _ _ _ _ _ _ _ bs HG HD HF Hsa Hlb Hlv (Hbv E'' Ha'')) as (_ & HG' & HD').
    rewrite (Haddr E'' Ha0) in HG'.
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact (Hrv E'' Ha'')|].
    split; [exact (HR' E'' Ha'')|]. split; [exact HG'|]. split; [exact HD'|]. split; [exact HF | exact Hfrm].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac xl_clean Hxl :=
  cbn [xlate] in Hxl; unfold fcvt_x in Hxl;
  repeat match type of Hxl with
         | context [match ?x with _ => _ end] => destruct x eqn:?
         end; try discriminate Hxl.
Ltac xl_fin := repeat eexists; repeat split; first [reflexivity | assumption | discriminate | (left; reflexivity) | (right; reflexivity)].

#[using="Type"] Lemma xl_aluI : forall pc i op rd rs imm, xlate pc i = XAluI op rd rs imm ->
  (exists rd' rs' (im : bv 12), i = OpImm op rd' rs' im /\ rd = rkey rd' /\ rs = rkey rs' /\ imm = bv_unsigned (sext 64 im)) \/
  (exists rd' rs' (sh : bv 6), i = ShiftImm op rd' rs' sh /\ rd = rkey rd' /\ rs = rkey rs' /\ imm = bv_unsigned (zext 64 sh)).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i op rd rs imm H. destruct i; xl_clean H; injection H as <- <- <- <-; [left | right]; xl_fin. Qed.
#[using="Type"] Lemma xl_alu : forall pc i op rd rs1 rs2, xlate pc i = XAlu op rd rs1 rs2 ->
  exists rd' a b, i = Op op rd' a b /\ rd = rkey rd' /\ rs1 = rkey a /\ rs2 = rkey b.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i op rd rs1 rs2 H. destruct i; xl_clean H; injection H as <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_aluIW : forall pc i op rd rs imm, xlate pc i = XAluIW op rd rs imm ->
  (exists rd' rs' (im : bv 12), i = OpImm32 rd' rs' im /\ op = ALU_ADD /\ rd = rkey rd' /\ rs = rkey rs' /\ imm = bv_unsigned (sext 32 im)) \/
  (exists rd' rs' (sh : bv 5), i = ShiftImm32 op rd' rs' sh /\ rd = rkey rd' /\ rs = rkey rs' /\ imm = bv_unsigned (zext 32 sh)).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i op rd rs imm H. destruct i; xl_clean H; injection H as <- <- <- <-; [left | right]; xl_fin. Qed.
#[using="Type"] Lemma xl_aluW : forall pc i op rd rs1 rs2, xlate pc i = XAluW op rd rs1 rs2 ->
  exists rd' a b, i = Op32 op rd' a b /\ rd = rkey rd' /\ rs1 = rkey a /\ rs2 = rkey b.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i op rd rs1 rs2 H. destruct i; xl_clean H; injection H as <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_mul : forall pc i op rd rs1 rs2, xlate pc i = XMul op rd rs1 rs2 ->
  exists rd' a b, i = Mul op rd' a b /\ rd = rkey rd' /\ rs1 = rkey a /\ rs2 = rkey b.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i op rd rs1 rs2 H. destruct i; xl_clean H; injection H as <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_mulw : forall pc i op rd rs1 rs2, xlate pc i = XMulW op rd rs1 rs2 ->
  exists rd' a b, i = Mul32 op rd' a b /\ rd = rkey rd' /\ rs1 = rkey a /\ rs2 = rkey b.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i op rd rs1 rs2 H. destruct i; xl_clean H; injection H as <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_li : forall pc i rd v, xlate pc i = XLi rd v ->
  (exists rd' im, i = Lui rd' im /\ rd = rkey rd' /\ v = bv_unsigned (sext 64 (bv_concat 32 im (Z_to_bv 12 0)))) \/
  (exists rd' im, i = Auipc rd' im /\ rd = rkey rd' /\ v = bv_unsigned (Z_to_bv 64 pc + sext 64 (bv_concat 32 im (Z_to_bv 12 0)))%bv).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i rd v H. destruct i; xl_clean H; injection H as <- <-; [left | right]; xl_fin. Qed.
#[using="Type"] Lemma xl_jal : forall pc i rd tgt link, xlate pc i = XJal rd tgt link ->
  exists rd' im, i = Jal rd' im /\ rd = rkey rd' /\ tgt = bv_unsigned (Z_to_bv 64 pc + sext 64 im)%bv /\
                 link = bv_unsigned (Z_to_bv 64 pc + Z_to_bv 64 4)%bv.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i rd tgt link H. destruct i; xl_clean H; injection H as <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_jalr : forall pc i rd rs imm link, xlate pc i = XJalr rd rs imm link ->
  exists rd' rs' im, i = Jalr rd' rs' im /\ rd = rkey rd' /\ rs = rkey rs' /\ imm = bv_unsigned (sext 64 im) /\
                     link = bv_unsigned (Z_to_bv 64 pc + Z_to_bv 64 4)%bv.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i rd rs imm link H. destruct i; xl_clean H; injection H as <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_br : forall pc i c rs1 rs2 tgt, xlate pc i = XBr c rs1 rs2 tgt ->
  exists a b im, i = Branch c a b im /\ rs1 = rkey a /\ rs2 = rkey b /\ tgt = bv_unsigned (Z_to_bv 64 pc + sext 64 im)%bv.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i c rs1 rs2 tgt H. destruct i; xl_clean H; injection H as <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_ld : forall pc i sz sg rd rs imm, xlate pc i = XLd sz sg rd rs imm ->
  exists rd' rs' im, i = Load sz sg rd' rs' im /\ rd = rkey rd' /\ rs = rkey rs' /\ imm = bv_unsigned (sext 64 im).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i sz sg rd rs imm H. destruct i; xl_clean H; injection H as <- <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_st : forall pc i sz rs1 rs2 imm, xlate pc i = XSt sz rs1 rs2 imm ->
  exists a b im, i = Store sz a b im /\ rs1 = rkey a /\ rs2 = rkey b /\ imm = bv_unsigned (sext 64 im).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i sz rs1 rs2 imm H. destruct i; xl_clean H; injection H as <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_fence : forall pc i, xlate pc i = XFence -> match i with Fence _ _ _ _ _ | FenceI _ _ _ => True | _ => False end.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i H. destruct i; xl_clean H; exact I. Qed.
#[using="Type"] Lemma xl_lr : forall pc i wd rd rs, xlate pc i = XLr wd rd rs ->
  exists aq rl rd' rs', i = Lr wd aq rl rd' rs' /\ rd = rkey rd' /\ rs = rkey rs'.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i wd rd rs H. destruct i; xl_clean H; injection H as <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_sc : forall pc i wd rd rs1 rs2, xlate pc i = XSc wd rd rs1 rs2 ->
  exists aq rl rd' a b, i = Sc wd aq rl rd' a b /\ rd = rkey rd' /\ rs1 = rkey a /\ rs2 = rkey b.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i wd rd rs1 rs2 H. destruct i; xl_clean H; injection H as <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_amo : forall pc i op wd rd rs1 rs2, xlate pc i = XAmo op wd rd rs1 rs2 ->
  exists aq rl rd' a b, i = Amo op wd aq rl rd' a b /\ rd = rkey rd' /\ rs1 = rkey a /\ rs2 = rkey b /\
                        (op = AMO_ADD \/ op = AMO_SWAP).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i op wd rd rs1 rs2 H. destruct i; xl_clean H; injection H as <- <- <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_fld : forall pc i fmt rs imm, xlate pc i = XFLd fmt rs imm ->
  exists rd' rs' im, i = FLoad fmt rd' rs' im /\ rs = rkey rs' /\ imm = bv_unsigned (sext 64 im).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i fmt rs imm H. destruct i; xl_clean H; injection H as <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_fst : forall pc i fmt rs imm, xlate pc i = XFSt fmt rs imm ->
  exists rs' b im, i = FStore fmt rs' b im /\ rs = rkey rs' /\ imm = bv_unsigned (sext 64 im).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i fmt rs imm H. destruct i; xl_clean H; injection H as <- <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_fint : forall pc i rd cmp, xlate pc i = XFInt rd cmp ->
  exists rdr, rd = rkey rdr /\
    (match i with
     | Fmv FMV_X_F _ rd' _ => rd' = rdr
     | Fcmp _ _ rd' _ _ => rd' = rdr
     | Fcvt dst src rd' _ rm => rd' = rdr /\ dst <> FC_S /\ dst <> FC_D /\ (src = FC_S \/ src = FC_D) /\
                               (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool = true
     | _ => False end) /\ (cmp = true -> match i with Fcmp _ _ _ _ _ => True | _ => False end).
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i rd cmp H. destruct i; xl_clean H; injection H as <- <-; xl_fin. Qed.
#[using="Type"] Lemma xl_fop : forall pc i, xlate pc i = XFOp ->
  match i with
  | Fmv FMV_F_X _ _ _ | Fsgnj _ _ _ _ _ => True
  | Fari _ _ _ _ _ rm => (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool = true
  | Fcvt dst _ _ _ rm => (dst = FC_S \/ dst = FC_D) /\ (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool = true
  | _ => False end.
Proof. LiaFast.lf_pins LiaFast.u0. intros pc i H. destruct i; xl_clean H; xl_fin. Qed.

#[using="Type"] Lemma alu_step_inv : forall s rd fs op a b npc s' FS,
  (match ev_alu fs op a b with
   | None => match split_req fs op a b with
             | Some (l, c) => if lclosed (s_next s) l then SSplit l c else SOk (set_res s rd None FS npc)
             | None => SOk (set_res s rd None FS npc)
             end
   | r => SOk (set_res s rd r FS npc)
   end) = SOk s' -> s' = set_res s rd (ev_alu fs op a b) FS npc.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s rd fs op a b npc s' FS H. destruct (ev_alu fs op a b) as [l0|]; [injection H as <-; reflexivity|].
  destruct (split_req fs op a b) as [[l c]|]; [destruct (lclosed (s_next s) l); [discriminate | injection H as <-; reflexivity] | injection H as <-; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac res_tac E s ms rd npc v fr fc :=
  lazymatch goal with |- context [set_res _ _ ?r ?fs _] =>
    edestruct (res_sound E s ms rd r fs npc v fr fc) as (E' & Ha & Hn & Hs')
  end.
Ltac res_tac2 E s ms rd r fs npc v fr fc :=
  edestruct (res_sound E s ms rd r fs npc v fr fc) as (E' & Ha & Hn & Hs').
(* [comment removed for export] *)
#[using="Type"] Lemma signed_small : forall (w : bv 64), bv_unsigned w < 9223372036854775808 -> bv_signed w = bv_unsigned w.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros w Hw. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 64) with 9223372036854775808. change (bv_modulus 64) with 18446744073709551616.
  pose proof (bv_unsigned_in_range _ w) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 64) with 18446744073709551616 in X.
  rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma win_minmax_spec : forall img fs R n o acc mn mx, win_minmax img fs R o n acc = Some (mn, mx) ->
  mn <= fst acc /\ snd acc <= mx /\
  forall j, o <= j < o + Z.of_nat n -> exists c, ld_value img fs R j SZ1 false = Some (LIN c []) /\ 0 <= c <= 255 /\ mn <= c <= mx.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros img fs R n. induction n as [|n IH]; intros o acc mn mx H; cbn [win_minmax] in H.
  - injection H as Hacc. subst acc. cbn [fst snd]. split; [lia|]. split; [lia|]. intros j Hj. lia.
  - destruct (ld_value img fs R o SZ1 false) as [[c l]|] eqn:Hv; [|discriminate]. destruct l as [|? ?]; [|discriminate].
    destruct (Z.leb 0 c && Z.leb c 255)%bool eqn:Hc; [|discriminate]. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2.
    destruct (IH (o + 1) _ _ _ H) as (H1 & H2 & H3). cbn [fst snd] in H1, H2.
    split; [lia|]. split; [lia|]. intros j Hj.
    destruct (Z.eq_dec j o) as [->|Hne]; [exists c; split; [exact Hv | split; lia]|].
    apply H3. lia.
Qed.
#[using="Type"] Lemma e3_facts_sound : forall E'' img s ms a sz sg bs n,
  img_ok segs img -> sden0 segs E'' s ms ->
  ov_read_bytes segs (ms_mem ms) (lden E'' a) (nbytes sz) = Some bs ->
  E'' n = ld_word sz sg bs ->
  Forall (fact_ok E'') (e3_facts img (s_facts s) (s_rgs s) a sz sg (lvar n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E'' img s ms a sz sg bs n Himg Hd Hbs Hn. unfold e3_facts.
  destruct sz; destruct sg; try constructor.
  destruct (e3_range img (s_facts s) (s_rgs s) a) as [[mn mx]|] eqn:He; [|constructor].
  constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hn.
  unfold e3_range in He. destruct (find_rg (s_facts s) (s_rgs s) a 1 O) as [[[ri0 R00] o00]|] eqn:Hfr; [discriminate|].
  destruct (find_rg_sym (s_facts s) (s_rgs s) a 1 O) as [[[ri R0] [lo hi]]|] eqn:Hfs; [|discriminate].
  destruct (Z.leb (hi - lo) 511) eqn:Hw; [|discriminate].
  destruct (win_minmax_spec _ _ _ _ _ _ _ _ He) as (_ & _ & Hall).
  destruct Hd as (_ & _ & _ & _ & HG & _ & HF & _).
  destruct (find_rg_sym_spec _ _ _ _ _ _ _ _ _ Hfs) as (_ & Hnth0 & Ho). rewrite Nat.sub_0_r in Hnth0.
  destruct (rg_off_any_sound E'' _ _ _ _ _ _ HF Ho) as (o & Holh & Ho0 & Hon & Haddr).
  pose proof (proj1 (Forall_nth' _ _) HG ri R0 Hnth0) as HR0.
  destruct (Hall o ltac:(rewrite Z2Nat.id by lia; lia)) as (c & Hv & Hc255 & Hmm).
  rewrite ov_rdn, Haddr in Hbs.
  pose proof (ld_value_sound E'' (s_facts s) img R0 (ms_mem ms) o SZ1 false bs HF Himg HR0 Ho0 Hon Hbs (LIN c []) Hv) as Hl.
  rewrite <- Hl. unfold lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac fp_tac := let Hnf := fresh "Hnf" in intros Hnf; first [split; [intros ?r; reflexivity | reflexivity] | cbn in Hnf; discriminate Hnf].
Ltac fin_fr := split; [intros ?x ?Hxo; reflexivity | cbn [s_rgs with_pc with_resv]; rewrite ?s_rgs_set_res; split; [reflexivity | split; [reflexivity | fp_tac]]].
Ltac fin_st Hsvc Ha Hn Hs' := split; [exact Hsvc | split; [exact Ha | split; [exact Hn | split; [first [exact Hs' | rewrite ?pc_plus4; exact Hs' | rewrite ?pc_plus4 in Hs'; exact Hs'] | fin_fr]]]].

#[using="Type"] Theorem fx_step_frp : forall t img s s' E ms,
  tbl_ok segs t -> img_ok segs img -> fx_step t img s = SOk s' -> sden segs E s ms ->
  exists ms' E', RiscvSemantics.step segs ms = MachineOk ms' /\ ms_svc_pending ms = None /\
                 agree (s_next s) E E' /\ (s_next s <= s_next s')%positive /\ sden segs E' s' ms' /\
                 (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs s') = shape (s_rgs s) /\
                 rtm (s_rgs s') = rtm (s_rgs s) /\ (nofp_xi (tlookup t (s_pc s)) = true -> fpeq ms ms').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s s' E ms Ht Himg Hstep Hden.
  pose proof (sden_0 _ _ _ _ Hden) as Hd0.
  destruct Hd0 as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  pose proof (mks_eta ms Hsvc) as Hms. rewrite Hpc in Hms.
  unfold fx_step in Hstep.
  destruct (tlookup t (s_pc s)) as [op rd rs imm | op rd rs1 rs2 | op rd rs imm | op rd rs1 rs2 | op rd rs1 rs2 | op rd rs1 rs2
                                   | rd v | rd tgt link | rd rs imm link | c rs1 rs2 tgt | sz sg rd rs imm | sz rs1 rs2 imm |
                                   | wd rd rs | wd rd rs1 rs2 | op wd rd rs1 rs2 | fmt rs imm | fmt rs1 imm | rd cmp | | | ] eqn:Hx;
    try discriminate Hstep;
  (destruct (Ht (s_pc s) _ Hx ltac:(discriminate) ltac:(discriminate)) as (w & i & Hfetch & Hecall & Hdecode & Hxl));
  (assert (Hst0 : RiscvSemantics.step segs ms = RiscvSemantics.step segs (mks (ms_fregs ms) (ms_fcsr ms) (ms_regs ms) (Z_to_bv 64 (s_pc s)) (ms_resv ms) (ms_mem ms) (ms_rom ms)))
     by (f_equal; exact Hms)); rewrite Hst0; clear Hst0 Hms.
  (* [comment removed for export] *)
  - apply alu_step_inv in Hstep. subst s'.
    destruct (xl_aluI _ _ _ _ _ _ Hxl) as [(rd' & rs' & im & -> & -> & -> & ->) | (rd' & rs' & im & -> & -> & -> & ->)].
    + res_tac E s ms rd' (s_pc s + 4) (alu64 op (getr (ms_regs ms) rs') (sext 64 im)) (ms_fregs ms) (ms_fcsr ms);
         [exact Hden | | | exact Hfrm |].
      * intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _).
        rewrite (ev_alu_sound E' _ _ _ _ _ HF' Hl), <- (HR' rs'). f_equal. apply lden_sext_imm; lia.
      * intros E'' Ha'' Hv. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _ & _ & HF'' & _).
        apply (res_facts_sound E''); [exact HF''|]. rewrite Hv, (HR'' rs'), lden_sext_imm by lia. reflexivity.
      * eexists _, E'. split; [eapply g_opimm; eassumption|]. fin_st Hsvc Ha Hn Hs'.
    + res_tac E s ms rd' (s_pc s + 4) (alu64 op (getr (ms_regs ms) rs') (zext 64 im)) (ms_fregs ms) (ms_fcsr ms);
         [exact Hden | | | exact Hfrm |].
      * intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _).
        rewrite (ev_alu_sound E' _ _ _ _ _ HF' Hl), <- (HR' rs'). f_equal. apply lden_const_word.
      * intros E'' Ha'' Hv. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _ & _ & HF'' & _).
        apply (res_facts_sound E''); [exact HF''|]. rewrite Hv, (HR'' rs'), lden_const_word. reflexivity.
      * eexists _, E'. split; [eapply g_shiftimm; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - apply alu_step_inv in Hstep. subst s'. destruct (xl_alu _ _ _ _ _ _ Hxl) as (rd' & a & b & -> & -> & -> & ->).
    res_tac E s ms rd' (s_pc s + 4) (alu64 op (getr (ms_regs ms) a) (getr (ms_regs ms) b)) (ms_fregs ms) (ms_fcsr ms);
       [exact Hden | | | exact Hfrm |].
    + intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _).
      rewrite (ev_alu_sound E' _ _ _ _ _ HF' Hl), <- (HR' a), <- (HR' b). reflexivity.
    + intros E'' Ha'' Hv. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _ & _ & HF'' & _).
      apply (res_facts_sound E''); [exact HF''|]. rewrite Hv, (HR'' a), (HR'' b). reflexivity.
    + eexists _, E'. split; [eapply g_op; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - injection Hstep as <-.
    destruct (xl_aluIW _ _ _ _ _ _ Hxl) as [(rd' & rs' & im & -> & -> & -> & -> & ->) | (rd' & rs' & im & -> & -> & -> & ->)].
    + res_tac E s ms rd' (s_pc s + 4) (sext 64 (alu32 ALU_ADD (low32 (getr (ms_regs ms) rs')) (sext 32 im))) (ms_fregs ms) (ms_fcsr ms);
         [exact Hden | | | exact Hfrm |].
      * intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _). rewrite (ev_aluw_sound E' _ _ _ _ _ HF' Hl), <- (HR' rs'). f_equal. f_equal.
        rewrite lden_lconst. apply bv_eq. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r, u_Z_to_bv.
        pose proof (bv_unsigned_in_range _ (sext 32 im)) as Rr. unfold bv_modulus in Rr.
        rewrite Z.mod_small by (unfold two64; change (2 ^ Z.of_N 32) with 4294967296 in Rr; lia).
        apply bv_wrap_small. exact Rr.
      * intros E'' Ha'' Hv. apply (w_facts_sound E (s_facts s)); [exact HF|]. rewrite Hv, (HR rs'). f_equal. f_equal. symmetry.
        rewrite lden_lconst. apply bv_eq. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r, u_Z_to_bv.
        pose proof (bv_unsigned_in_range _ (sext 32 im)) as Rr. unfold bv_modulus in Rr.
        rewrite Z.mod_small by (unfold two64; change (2 ^ Z.of_N 32) with 4294967296 in Rr; lia).
        apply bv_wrap_small. exact Rr.
      * eexists _, E'. split; [eapply g_opimm32; eassumption|]. fin_st Hsvc Ha Hn Hs'.
    + res_tac E s ms rd' (s_pc s + 4) (sext 64 (alu32 op (low32 (getr (ms_regs ms) rs')) (zext 32 im))) (ms_fregs ms) (ms_fcsr ms);
         [exact Hden | | | exact Hfrm |].
      * intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _). rewrite (ev_aluw_sound E' _ _ _ _ _ HF' Hl), <- (HR' rs'). f_equal. f_equal.
        rewrite lden_lconst. apply bv_eq. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r, u_Z_to_bv.
        pose proof (bv_unsigned_in_range _ (zext 32 im)) as Rr. unfold bv_modulus in Rr.
        rewrite Z.mod_small by (unfold two64; change (2 ^ Z.of_N 32) with 4294967296 in Rr; lia).
        apply bv_wrap_small. exact Rr.
      * intros E'' Ha'' Hv. apply (w_facts_sound E (s_facts s)); [exact HF|]. rewrite Hv, (HR rs'). f_equal. f_equal. symmetry.
        rewrite lden_lconst. apply bv_eq. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r, u_Z_to_bv.
        pose proof (bv_unsigned_in_range _ (zext 32 im)) as Rr. unfold bv_modulus in Rr.
        rewrite Z.mod_small by (unfold two64; change (2 ^ Z.of_N 32) with 4294967296 in Rr; lia).
        apply bv_wrap_small. exact Rr.
      * eexists _, E'. split; [eapply g_shiftimm32; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - injection Hstep as <-. destruct (xl_aluW _ _ _ _ _ _ Hxl) as (rd' & a & b & -> & -> & -> & ->).
    res_tac E s ms rd' (s_pc s + 4) (sext 64 (alu32 op (low32 (getr (ms_regs ms) a)) (low32 (getr (ms_regs ms) b)))) (ms_fregs ms) (ms_fcsr ms);
       [exact Hden | | | exact Hfrm |].
    + intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _). rewrite (ev_aluw_sound E' _ _ _ _ _ HF' Hl), <- (HR' a), <- (HR' b). reflexivity.
    + intros E'' Ha'' Hv. apply (w_facts_sound E (s_facts s)); [exact HF|]. rewrite Hv, (HR a), (HR b). reflexivity.
    + eexists _, E'. split; [eapply g_op32; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - injection Hstep as <-. destruct (xl_mul _ _ _ _ _ _ Hxl) as (rd' & a & b & -> & -> & -> & ->).
    res_tac E s ms rd' (s_pc s + 4) (mul_div op (getr (ms_regs ms) a) (getr (ms_regs ms) b)) (ms_fregs ms) (ms_fcsr ms);
       [exact Hden | | | exact Hfrm |].
    + intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _). rewrite (ev_mulf_sound E' _ _ _ _ _ HF' Hl), <- (HR' a), <- (HR' b). reflexivity.
    + intros E'' Ha'' Hv. unfold mul_facts. destruct op; try (solve [constructor]).
      * (* [comment removed for export] *)
        cbv zeta. destruct (Z.ltb (snd (irange (s_facts s) (rget (s_regs s) (rkey a)))) 9223372036854775808 &&
                            Z.ltb (snd (irange (s_facts s) (rget (s_regs s) (rkey b)))) 9223372036854775808)%bool eqn:Hsm; [|constructor].
        apply andb_prop in Hsm as [Hsa Hsb]. apply Z.ltb_lt in Hsa, Hsb.
        apply Forall_cons; [|constructor]. cbn [fact_ok].
        rewrite lden_lvar, Hv. cbn [mul_div]. unfold bv_mulhss.
        pose proof (irange_sound E (s_facts s) (rget (s_regs s) (rkey a)) HF) as Ra0.
        pose proof (irange_sound E (s_facts s) (rget (s_regs s) (rkey b)) HF) as Rb0.
        rewrite <- (HR a) in Ra0. rewrite <- (HR b) in Rb0.
        rewrite (signed_small (getr (ms_regs ms) a)) by lia. rewrite (signed_small (getr (ms_regs ms) b)) by lia. clear Ra0 Rb0.
        pose proof (irange_sound E (s_facts s) (rget (s_regs s) (rkey a)) HF) as Ra.
        pose proof (irange_sound E (s_facts s) (rget (s_regs s) (rkey b)) HF) as Rb.
        rewrite <- (HR a) in Ra. rewrite <- (HR b) in Rb.
        set (ua := bv_unsigned (getr (ms_regs ms) a)) in *. set (ub := bv_unsigned (getr (ms_regs ms) b)) in *.
        pose proof (bv_unsigned_in_range _ (getr (ms_regs ms) a)) as X1. pose proof (bv_unsigned_in_range _ (getr (ms_regs ms) b)) as X2.
        unfold bv_modulus in X1, X2. change (2 ^ Z.of_N 64) with two64 in X1, X2. fold ua ub in X1, X2.
        assert (Hp : 0 <= ua * ub) by nia.
        assert (Hq : Z.shiftr (ua * ub) 64 < two64).
        { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. unfold two64 in *. nia. }
        rewrite Z_to_bv_unsigned. change (Z.of_N 64) with 64. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite Z.mod_small by (split; [apply Z.shiftr_nonneg; exact Hp | exact Hq]).
        split; [apply Z.shiftr_nonneg; exact Hp|]. rewrite !Z.shiftr_div_pow2 by lia.
        apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia|]. apply Z.mul_le_mono_nonneg; lia.
      * cbn [fact_ok]. apply Forall_cons; [|constructor]. cbn [fact_ok].
        rewrite lden_lvar, Hv. cbn [mul_div]. unfold bv_mulhuu.
        pose proof (irange_sound E (s_facts s) (rget (s_regs s) (rkey a)) HF) as Ra.
        pose proof (irange_sound E (s_facts s) (rget (s_regs s) (rkey b)) HF) as Rb.
        rewrite <- (HR a) in Ra. rewrite <- (HR b) in Rb.
        set (ua := bv_unsigned (getr (ms_regs ms) a)) in *. set (ub := bv_unsigned (getr (ms_regs ms) b)) in *.
        pose proof (bv_unsigned_in_range _ (getr (ms_regs ms) a)) as X1. pose proof (bv_unsigned_in_range _ (getr (ms_regs ms) b)) as X2.
        unfold bv_modulus in X1, X2. change (2 ^ Z.of_N 64) with two64 in X1, X2. fold ua ub in X1, X2.
        assert (Hp : 0 <= ua * ub) by nia.
        assert (Hq : Z.shiftr (ua * ub) 64 < two64).
        { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. unfold two64 in *. nia. }
        rewrite Z_to_bv_unsigned. change (Z.of_N 64) with 64. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite Z.mod_small by (split; [apply Z.shiftr_nonneg; exact Hp | exact Hq]).
        split; [apply Z.shiftr_nonneg; exact Hp|]. rewrite !Z.shiftr_div_pow2 by lia.
        apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia|]. apply Z.mul_le_mono_nonneg; lia.
    + eexists _, E'. split; [eapply g_mul; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - injection Hstep as <-. destruct (xl_mulw _ _ _ _ _ _ Hxl) as (rd' & a & b & -> & -> & -> & ->).
    res_tac E s ms rd' (s_pc s + 4) (sext 64 (mul_div op (low32 (getr (ms_regs ms) a)) (low32 (getr (ms_regs ms) b)))) (ms_fregs ms) (ms_fcsr ms);
       [exact Hden | | intros; constructor | exact Hfrm |].
    + intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & _ & _ & HF' & _). rewrite (ev_mulw_sound E' _ _ _ _ _ HF' Hl), <- (HR' a), <- (HR' b). reflexivity.
    + eexists _, E'. split; [eapply g_mul32; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - injection Hstep as <-. destruct (xl_li _ _ _ _ Hxl) as [(rd' & im & -> & -> & ->) | (rd' & im & -> & -> & ->)].
    + res_tac2 E s ms rd' (Some (lconst (bv_unsigned (sext 64 (bv_concat 32 im (Z_to_bv 12 0)))))) nofacts (s_pc s + 4) (sext 64 (bv_concat 32 im (Z_to_bv 12 0))) (ms_fregs ms) (ms_fcsr ms);
         [exact Hden | | intros; constructor | exact Hfrm |].
      * intros E' Ha' HR' l Hl. injection Hl as <-. apply lden_const_word.
      * eexists _, E'. split; [eapply g_lui; eassumption|]. fin_st Hsvc Ha Hn Hs'.
    + res_tac2 E s ms rd' (Some (lconst (bv_unsigned (Z_to_bv 64 (s_pc s) + sext 64 (bv_concat 32 im (Z_to_bv 12 0)))%bv))) nofacts (s_pc s + 4) (Z_to_bv 64 (s_pc s) + sext 64 (bv_concat 32 im (Z_to_bv 12 0)))%bv (ms_fregs ms) (ms_fcsr ms);
         [exact Hden | | intros; constructor | exact Hfrm |].
      * intros E' Ha' HR' l Hl. injection Hl as <-. apply lden_const_word.
      * eexists _, E'. split; [eapply g_auipc; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - injection Hstep as <-. destruct (xl_jal _ _ _ _ _ Hxl) as (rd' & im & -> & -> & -> & ->).
    res_tac2 E s ms rd' (Some (lconst (bv_unsigned (Z_to_bv 64 (s_pc s) + Z_to_bv 64 4)%bv))) nofacts (bv_unsigned (Z_to_bv 64 (s_pc s) + sext 64 im)%bv) (Z_to_bv 64 (s_pc s) + Z_to_bv 64 4)%bv (ms_fregs ms) (ms_fcsr ms);
       [exact Hden | | intros; constructor | exact Hfrm |].
    + intros E' Ha' HR' l Hl. injection Hl as <-. apply lden_const_word.
    + eexists _, E'. split; [eapply g_jal; eassumption|]. rewrite Z_to_bv_bv_unsigned in Hs'. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - destruct (xl_jalr _ _ _ _ _ _ Hxl) as (rd' & rs' & im & -> & -> & -> & -> & ->).
    destruct (is_const (rget (s_regs s) (rkey rs'))) as [x|] eqn:Hcx; [|discriminate]. injection Hstep as <-.
    pose proof (is_const_sound E _ _ Hcx) as [Hxv _]. rewrite <- (HR rs') in Hxv.
    res_tac2 E s ms rd' (Some (lconst (bv_unsigned (Z_to_bv 64 (s_pc s) + Z_to_bv 64 4)%bv))) nofacts (bv_unsigned (bv_and (Z_to_bv 64 x + Z_to_bv 64 (bv_unsigned (sext 64 im)))%bv (bv_not w1)))
                 (Z_to_bv 64 (s_pc s) + Z_to_bv 64 4)%bv (ms_fregs ms) (ms_fcsr ms);
       [exact Hden | | intros; constructor | exact Hfrm |].
    + intros E' Ha' HR' l Hl. injection Hl as <-. apply lden_const_word.
    + eexists _, E'. split; [eapply g_jalr; eassumption|].
      replace (bv_and (getr (ms_regs ms) rs' + sext 64 im)%bv (bv_not w1))
        with (Z_to_bv 64 (bv_unsigned (bv_and (Z_to_bv 64 x + Z_to_bv 64 (bv_unsigned (sext 64 im)))%bv (bv_not w1))))
        by (rewrite !Z_to_bv_bv_unsigned, Hxv; reflexivity).
      fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - destruct (xl_br _ _ _ _ _ _ Hxl) as (a & b & im & -> & -> & -> & ->).
    destruct (ev_br (s_facts s) c (rget (s_regs s) (rkey a)) (rget (s_regs s) (rkey b))) as [tk|] eqn:Hbr; [|discriminate].
    pose proof (ev_br_sound E _ _ _ _ _ HF Hbr) as Htk. rewrite <- (HR a), <- (HR b) in Htk.
    assert (Hs1 : s' = with_pc s (if tk then bv_unsigned (Z_to_bv 64 (s_pc s) + sext 64 im)%bv else s_pc s + 4))
      by (destruct tk; injection Hstep as <-; reflexivity).
    subst s'. eexists _, E. split; [erewrite g_branch by eassumption; rewrite Htk; reflexivity|].
    split; [exact Hsvc|]. split; [apply agree_refl|]. split; [cbn; lia|].
    replace (if tk then (Z_to_bv 64 (s_pc s) + sext 64 im)%bv else (Z_to_bv 64 (s_pc s) + Z_to_bv 64 4)%bv)
      with (Z_to_bv 64 (if tk then bv_unsigned (Z_to_bv 64 (s_pc s) + sext 64 im)%bv else s_pc s + 4))
      by (destruct tk; [apply Z_to_bv_bv_unsigned | symmetry; apply pc_plus4]).
    split; [apply pc_sound; [exact Hden | exact Hfrm] | fin_fr].
  (* [comment removed for export] *)
  - destruct (xl_ld _ _ _ _ _ _ _ Hxl) as (rd' & rs' & im & -> & -> & -> & ->).
    destruct (load_at img (s_facts s) (s_rgs s) (laddc (rget (s_regs s) (rkey rs')) (bv_unsigned (sext 64 im))) sz sg) as [r|] eqn:Hld;
      [|discriminate]. injection Hstep as <-.
    destruct (load_at_sound E img _ _ _ _ _ r (ms_mem ms) Himg HG HF Hld) as (bs & Hbs & Hval).
    rewrite (addr_eq E _ _ rs' im HR) in Hbs.
    edestruct (res_sound E s ms rd' r (fun x => e3_facts img (s_facts s) (s_rgs s) (laddc (rget (s_regs s) (rkey rs')) (bv_unsigned (sext 64 im))) sz sg x ++
                                             ld_facts (s_facts s) (s_rgs s) (laddc (rget (s_regs s) (rkey rs')) (bv_unsigned (sext 64 im))) sz sg x) (s_pc s + 4) (ld_word sz sg bs) (ms_fregs ms) (ms_fcsr ms))
      as (E' & Ha & Hn & Hs'); [exact Hden | | | exact Hfrm |].
    + intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & HG' & _ & HF' & _).
      destruct (load_at_sound E' img _ _ _ _ _ r (ms_mem ms) Himg HG' HF' Hld) as (bs' & Hbs' & Hval').
      rewrite (addr_eq E' _ _ rs' im HR'), Hbs in Hbs'. injection Hbs' as <-. exact (Hval' l Hl).
    + intros E'' Ha'' Hv. pose proof (Hden E'' Ha'') as Hd''. apply Forall_app. split.
      * apply (e3_facts_sound E'' img s ms _ sz sg bs (s_next s) Himg Hd''); [|exact Hv].
        destruct Hd'' as (_ & _ & _ & HR'' & _). rewrite (addr_eq E'' _ _ rs' im HR''). exact Hbs.
      * apply (ld_facts_sound E'' s ms _ sz sg bs (s_next s) Hd''); [|exact Hv].
        destruct Hd'' as (_ & _ & _ & HR'' & _). rewrite (addr_eq E'' _ _ rs' im HR''). exact Hbs.
    + eexists _, E'. split; [eapply g_load; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - destruct (xl_st _ _ _ _ _ _ Hxl) as (ra & rb & im & -> & -> & -> & ->).
    set (a := laddc (rget (s_regs s) (rkey ra)) (bv_unsigned (sext 64 im))) in *.
    set (v := rget (s_regs s) (rkey rb)) in *.
    destruct (store_at (s_facts s) (s_rgs s) a (nbytes sz) (st_vals (s_facts s) v (nbytes sz))) as [rgs'|] eqn:Hsa; [|discriminate].
    injection Hstep as <-.
    assert (Hadr : forall E'', agree (s_next s) E E'' -> lden E'' a = lden E a).
    { intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _). unfold a.
      rewrite (addr_eq E'' _ _ ra im HR''), (addr_eq E _ _ ra im HR). reflexivity. }
    edestruct (mem_sound E E s ms a (nbytes sz) (st_vals (s_facts s) v (nbytes sz)) rgs' (Z_to_le_bytes (nbytes sz) (st_word sz (getr (ms_regs ms) rb)))
                 (s_regs s) (s_next s) (inval (s_resv s) a) (ms_regs ms) (ival (lden E a) (ms_resv ms)) (s_pc s + 4))
      as [Hok Hs']; [exact Hden | apply agree_refl | lia | exact Hsa | exact Hadr | apply length_Z_to_le_bytes | apply length_st_vals | | | |].
    + intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _ & _ & HF'' & _). apply st_vals_ok; [exact HF''|]. unfold v. rewrite <- (HR'' rb). reflexivity.
    + intros E'' Ha''. exact (proj1 (proj2 (proj2 (proj2 (Hden E'' Ha''))))).
    + intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & Hrv'' & _). rewrite <- (Hadr E'' Ha''). apply inval_sound. exact Hrv''.
    + unfold a in Hok, Hs'. rewrite (addr_eq E _ _ ra im HR) in Hok, Hs'.
      eexists _, E. split; [eapply g_store; eassumption|].
      split; [exact Hsvc | split; [apply agree_refl | split; [cbn; lia | split; [rewrite ?pc_plus4; exact Hs' | split]]]].
      * intros x Hxo. cbn [ms_mem mks]. rewrite <- (addr_eq E _ _ ra im HR).
        exact (store_at_frame_fr E _ _ _ _ _ _ (ms_mem ms) _ HG HD HF Hsa (length_Z_to_le_bytes _ _) x Hxo).
      * split; [exact (store_at_shape _ _ _ _ _ _ Hsa) | split; [exact (store_at_rtm _ _ _ _ _ _ Hsa) | fp_tac]].
  (* [comment removed for export] *)
  - injection Hstep as <-. pose proof (xl_fence _ _ Hxl) as Hi.
    eexists _, E. split; [eapply g_fence; [eassumption | eassumption | eassumption | exact Hi]|].
    split; [exact Hsvc|]. split; [apply agree_refl|]. split; [cbn; lia|]. rewrite pc_plus4. split; [apply pc_sound; [exact Hden | exact Hfrm] | fin_fr].
  (* [comment removed for export] *)
  - destruct (xl_lr _ _ _ _ _ Hxl) as (aq & rl & rd' & rs' & -> & -> & ->).
    destruct (amo_al (s_facts s) wd (rget (s_regs s) (rkey rs'))) eqn:Hal; [|discriminate].
    destruct (load_at img (s_facts s) (s_rgs s) (rget (s_regs s) (rkey rs')) (amo_sz wd) (amo_sg wd)) as [r|] eqn:Hld; [|discriminate].
    injection Hstep as <-.
    pose proof (amo_al_sound E _ _ _ HF Hal) as Hal'. rewrite <- (HR rs') in Hal'.
    destruct (load_at_sound E img _ _ _ _ _ r (ms_mem ms) Himg HG HF Hld) as (bs & Hbs & Hval). rewrite <- (HR rs') in Hbs.
    edestruct (res_sound_gen E s ms rd' r nofacts (s_pc s + 4) (ld_word (amo_sz wd) (amo_sg wd) bs) (ms_fregs ms) (ms_fcsr ms)
                 (RAt (rget (s_regs s) (rkey rs'))) (Some (getr (ms_regs ms) rs')))
      as (E' & Ha & Hn & Hs'); [exact Hden | | intros; constructor | exact Hfrm | |].
    + intros E' Ha' HR' l Hl. destruct (Hden E' Ha') as (_ & _ & _ & _ & HG' & _ & HF' & _).
      destruct (load_at_sound E' img _ _ _ _ _ r (ms_mem ms) Himg HG' HF' Hld) as (bs' & Hbs' & Hval').
      rewrite <- (HR' rs'), Hbs in Hbs'. injection Hbs' as <-. exact (Hval' l Hl).
    + intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _). cbn [rsv_ok]. rewrite (HR'' rs'). reflexivity.
    + eexists _, E'. split; [eapply g_lr; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - destruct (xl_sc _ _ _ _ _ _ Hxl) as (aq & rl & rd' & ra & rb & -> & -> & -> & ->).
    destruct (amo_al (s_facts s) wd (rget (s_regs s) (rkey ra))) eqn:Hal; [|discriminate].
    pose proof (amo_al_sound E _ _ _ HF Hal) as Hal'. rewrite <- (HR ra) in Hal'.
    destruct (sc_ok (s_resv s) (rget (s_regs s) (rkey ra))) as [[|]|] eqn:Hsc; [| |discriminate].
    + destruct (sc_ok_sound E _ _ _ _ Hrsv Hsc) as [Hsc1 _]. destruct (Hsc1 eq_refl) as (r0 & Hr0 & Hr0u).
      rewrite <- (HR ra) in Hr0u.
      set (a := rget (s_regs s) (rkey ra)) in *. set (v := rget (s_regs s) (rkey rb)) in *.
      destruct (store_at (s_facts s) (s_rgs s) a (nbytes (amo_sz wd)) (st_bytes v (is_const v) 0 (nbytes (amo_sz wd)))) as [rgs'|] eqn:Hsa;
        [|discriminate]. injection Hstep as <-.
      assert (Hadr : forall E'', agree (s_next s) E E'' -> lden E'' a = lden E a).
      { intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _). unfold a. rewrite <- (HR'' ra), <- (HR ra). reflexivity. }
      edestruct (mem_sound E E s ms a (nbytes (amo_sz wd)) (st_bytes v (is_const v) 0 (nbytes (amo_sz wd))) rgs' (Z_to_le_bytes (nbytes (amo_sz wd)) (st_word (amo_sz wd) (getr (ms_regs ms) rb)))
                   (rset (s_regs s) (rkey rd') lc0) (s_next s) RNone (rupd (ms_regs ms) rd' (Z_to_bv 64 0)) None (s_pc s + 4))
        as [Hok Hs']; [exact Hden | apply agree_refl | lia | exact Hsa | exact Hadr | apply length_Z_to_le_bytes | apply length_st_bytes | | | |].
      * intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _). apply st_bytes_ok. unfold v. rewrite <- (HR'' rb). reflexivity.
      * intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _). unfold rupd. apply regs_ok_upd; [exact HR'' | reflexivity].
      * intros E'' _. reflexivity.
      * unfold a in Hok, Hs'. rewrite <- (HR ra) in Hok, Hs'.
        eexists _, E. split; [eapply g_sc_ok; eassumption|].
        split; [exact Hsvc | split; [apply agree_refl | split; [cbn; lia | split; [rewrite ?pc_plus4; exact Hs' | split]]]].
        -- intros x Hxo. cbn [ms_mem mks]. rewrite (HR ra).
           exact (store_at_frame_fr E _ _ _ _ _ _ (ms_mem ms) _ HG HD HF Hsa (length_Z_to_le_bytes _ _) x Hxo).
        -- split; [exact (store_at_shape _ _ _ _ _ _ Hsa) | split; [exact (store_at_rtm _ _ _ _ _ _ Hsa) | fp_tac]].
    + destruct (sc_ok_sound E _ _ _ _ Hrsv Hsc) as [_ Hsc2]. pose proof (Hsc2 eq_refl) as Hfl. rewrite <- (HR ra) in Hfl.
      injection Hstep as <-.
      edestruct (res_sound_gen E s ms rd' (Some (lconst 1)) nofacts (s_pc s + 4) (Z_to_bv 64 1) (ms_fregs ms) (ms_fcsr ms) RNone None)
        as (E' & Ha & Hn & Hs'); [exact Hden | | intros; constructor | exact Hfrm | intros; reflexivity |].
      * intros E' Ha' HR' l Hl. injection Hl as <-. apply lden_lconst.
      * eexists _, E'. split; [eapply g_sc_fail; eassumption|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - destruct (xl_amo _ _ _ _ _ _ _ Hxl) as (aq & rl & rd' & ra & rb & -> & -> & -> & -> & Hop).
    destruct (amo_al (s_facts s) wd (rget (s_regs s) (rkey ra))) eqn:Hal; [|discriminate].
    pose proof (amo_al_sound E _ _ _ HF Hal) as Hal'. rewrite <- (HR ra) in Hal'.
    set (a := rget (s_regs s) (rkey ra)) in *. set (src := rget (s_regs s) (rkey rb)) in *.
    destruct (load_at img (s_facts s) (s_rgs s) a (amo_sz wd) (amo_sg wd)) as [r|] eqn:Hld; [|discriminate].
    destruct (load_at_sound E img _ _ _ _ _ r (ms_mem ms) Himg HG HF Hld) as (bs & Hbs & Hval).
    set (old := ld_word (amo_sz wd) (amo_sg wd) bs) in *.
    set (ov := match r with Some l => l | None => lvar (s_next s) end) in *.
    set (nx := match r with Some _ => s_next s | None => Pos.succ (s_next s) end) in *.
    set (E1 := match r with Some _ => E | None => upd E (s_next s) old end).
    assert (Ha1 : agree (s_next s) E E1) by (unfold E1; destruct r; [apply agree_refl | apply agree_upd]).
    assert (Hnx : (s_next s <= nx)%positive) by (unfold nx; destruct r; lia).
    assert (Hov : forall E'', agree nx E1 E'' -> lden E'' ov = old).
    { intros E'' Ha''. unfold ov, nx, E1 in *. destruct r as [l|].
      - destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & HG'' & _ & HF'' & _).
        destruct (load_at_sound E'' img _ _ _ _ _ (Some l) (ms_mem ms) Himg HG'' HF'' Hld) as (bs' & Hbs' & Hval').
        assert (Ha0 : lden E'' a = lden E a) by (unfold a; rewrite <- (HR'' ra), <- (HR ra); reflexivity).
        rewrite Ha0, Hbs in Hbs'. injection Hbs' as <-. exact (Hval' l eq_refl).
      - rewrite lden_lvar. rewrite <- (Ha'' (s_next s) ltac:(lia)). unfold upd. rewrite Pos.eqb_refl. reflexivity. }
    assert (Hag : forall E'', agree nx E1 E'' -> agree (s_next s) E E'').
    { intros E'' H0 x0 Hx0. rewrite (Ha1 x0 Hx0). apply H0. lia. }
    set (nv := amo_new op ov src) in *.
    destruct (store_at (s_facts s) (s_rgs s) a (nbytes (amo_sz wd)) (st_bytes nv (is_const nv) 0 (nbytes (amo_sz wd)))) as [rgs'|] eqn:Hsa;
      [|discriminate]. injection Hstep as <-.
    assert (Hadr : forall E'', agree (s_next s) E E'' -> lden E'' a = lden E a).
    { intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _). unfold a. rewrite <- (HR'' ra), <- (HR ra). reflexivity. }
    edestruct (mem_sound E E1 s ms a (nbytes (amo_sz wd)) (st_bytes nv (is_const nv) 0 (nbytes (amo_sz wd))) rgs'
                 (Z_to_le_bytes (nbytes (amo_sz wd)) (st_word (amo_sz wd) (amo_word op wd old (getr (ms_regs ms) rb))))
                 (rset (s_regs s) (rkey rd') ov) nx (inval (s_resv s) a) (rupd (ms_regs ms) rd' old) (ival (lden E a) (ms_resv ms)) (s_pc s + 4))
      as [Hok Hs']; [exact Hden | exact Ha1 | exact Hnx | exact Hsa | exact Hadr | apply length_Z_to_le_bytes | apply length_st_bytes | | | |].
    + intros E'' Ha''. destruct (Hden E'' (Hag E'' Ha'')) as (_ & _ & _ & HR'' & _).
      intros j x Hj. rewrite <- (Hov E'' Ha''). rewrite (HR'' rb). fold src. rewrite <- (amo_st_word E'' op wd ov src Hop).
      exact (st_bytes_ok E'' nv (lden E'' nv) (amo_sz wd) eq_refl j x Hj).
    + intros E'' Ha''. destruct (Hden E'' (Hag E'' Ha'')) as (_ & _ & _ & HR'' & _). unfold rupd. apply regs_ok_upd; [exact HR'' | exact (Hov E'' Ha'')].
    + intros E'' Ha''. destruct (Hden E'' (Hag E'' Ha'')) as (_ & _ & Hrv'' & _). rewrite <- (Hadr E'' (Hag E'' Ha'')). apply inval_sound. exact Hrv''.
    + unfold a in Hok, Hs', Hbs. rewrite <- (HR ra) in Hok, Hs', Hbs.
      eexists _, E1. split; [eapply g_amo; eassumption|].
      split; [exact Hsvc | split; [exact Ha1 | split; [cbn; exact Hnx | split; [rewrite ?pc_plus4; exact Hs' | split]]]].
      * intros x Hxo. cbn [ms_mem mks]. rewrite (HR ra).
        exact (store_at_frame_fr E _ _ _ _ _ _ (ms_mem ms) _ HG HD HF Hsa (length_Z_to_le_bytes _ _) x Hxo).
      * split; [exact (store_at_shape _ _ _ _ _ _ Hsa) | split; [exact (store_at_rtm _ _ _ _ _ _ Hsa) | fp_tac]].
  (* [comment removed for export] *)
  - destruct (xl_fld _ _ _ _ _ Hxl) as (rd' & rs' & im & -> & -> & ->).
    destruct (load_at img (s_facts s) (s_rgs s) (laddc (rget (s_regs s) (rkey rs')) (bv_unsigned (sext 64 im))) (fsz fmt) false) as [r|] eqn:Hld;
      [|discriminate]. injection Hstep as <-.
    destruct (load_at_sound E img _ _ _ _ _ r (ms_mem ms) Himg HG HF Hld) as (bs & Hbs & _).
    rewrite (addr_eq E _ _ rs' im HR) in Hbs.
    destruct (g_fload segs (ms_fregs ms) (ms_fcsr ms) (ms_regs ms) (Z_to_bv 64 (s_pc s)) (ms_resv ms) (ms_mem ms) (ms_rom ms) w Hfetch Hecall
                fmt rd' rs' im bs Hdecode Hbs) as [fr' Hgl].
    eexists _, E. split; [rewrite Hgl, pc_plus4; reflexivity|].
    split; [exact Hsvc|]. split; [apply agree_refl|]. split; [cbn; lia|]. split; [apply pc_sound; [exact Hden | exact Hfrm] | fin_fr].
  (* [comment removed for export] *)
  - destruct (xl_fst _ _ _ _ _ Hxl) as (ra & rb & im & -> & -> & ->).
    set (a := laddc (rget (s_regs s) (rkey ra)) (bv_unsigned (sext 64 im))) in *.
    destruct (store_at (s_facts s) (s_rgs s) a (nbytes (fsz fmt)) (st_bytes (lvar (s_next s)) None 0 (nbytes (fsz fmt)))) as [rgs'|] eqn:Hsa;
      [|discriminate]. injection Hstep as <-.
    set (fv := reg_get (ms_fregs ms) rb).
    set (E1 := upd E (s_next s) fv).
    assert (Hag : forall E'', agree (Pos.succ (s_next s)) E1 E'' -> agree (s_next s) E E'').
    { intros E'' H0 x0 Hx0. rewrite (agree_upd (s_next s) E fv x0 Hx0). apply H0. lia. }
    assert (Hadr : forall E'', agree (s_next s) E E'' -> lden E'' a = lden E a).
    { intros E'' Ha''. destruct (Hden E'' Ha'') as (_ & _ & _ & HR'' & _). unfold a.
      rewrite (addr_eq E'' _ _ ra im HR''), (addr_eq E _ _ ra im HR). reflexivity. }
    edestruct (mem_sound E E1 s ms a (nbytes (fsz fmt)) (st_bytes (lvar (s_next s)) None 0 (nbytes (fsz fmt))) rgs' (Z_to_le_bytes (nbytes (fsz fmt)) (fst_word fmt fv))
                 (s_regs s) (Pos.succ (s_next s)) (inval (s_resv s) a) (ms_regs ms) (ival (lden E a) (ms_resv ms)) (s_pc s + 4))
      as [Hok Hs']; [exact Hden | apply agree_upd | lia | exact Hsa | exact Hadr | apply length_Z_to_le_bytes | apply length_st_bytes | | | |].
    + intros E'' Ha''. intros j x Hj.
      assert (Hfv : lden E'' (lvar (s_next s)) = fv).
      { rewrite lden_lvar, <- (Ha'' (s_next s) ltac:(lia)). unfold E1, upd. rewrite Pos.eqb_refl. reflexivity. }
      replace (fst_word fmt fv) with (st_word (fsz fmt) fv) by (destruct fmt; reflexivity).
      exact (st_bytes_ok E'' (lvar (s_next s)) fv (fsz fmt) Hfv j x Hj).
    + intros E'' Ha''. exact (proj1 (proj2 (proj2 (proj2 (Hden E'' (Hag E'' Ha'')))))).
    + intros E'' Ha''. destruct (Hden E'' (Hag E'' Ha'')) as (_ & _ & Hrv'' & _). rewrite <- (Hadr E'' (Hag E'' Ha'')). apply inval_sound. exact Hrv''.
    + unfold a in Hok, Hs'. rewrite (addr_eq E _ _ ra im HR) in Hok, Hs'.
      eexists _, E1. split; [eapply g_fstore; eassumption|].
      split; [exact Hsvc | split; [apply agree_upd | split; [cbn; lia | split; [rewrite ?pc_plus4; exact Hs' | split]]]].
      * intros x Hxo. cbn [ms_mem mks]. rewrite <- (addr_eq E _ _ ra im HR).
        exact (store_at_frame_fr E _ _ _ _ _ _ (ms_mem ms) _ HG HD HF Hsa (length_Z_to_le_bytes _ _) x Hxo).
      * split; [exact (store_at_shape _ _ _ _ _ _ Hsa) | split; [exact (store_at_rtm _ _ _ _ _ _ Hsa) | fp_tac]].
  (* [comment removed for export] *)
  - destruct (xl_fint _ _ _ _ Hxl) as (rdr & -> & Hi & Hcmp). injection Hstep as <-.
    destruct (g_fint segs (ms_fregs ms) (ms_fcsr ms) (ms_regs ms) (Z_to_bv 64 (s_pc s)) (ms_resv ms) (ms_mem ms) (ms_rom ms) w Hfetch Hecall
                i rdr Hdecode Hfrm Hi) as (v & fc' & Hfrm' & Hv01 & Hgl).
    edestruct (res_sound E s ms rdr None (if cmp then bit_facts else nofacts) (s_pc s + 4) v (ms_fregs ms) fc')
      as (E' & Ha & Hn & Hs'); [exact Hden | intros; discriminate | | exact Hfrm' |].
    + intros E'' Ha'' Hv. destruct cmp; [|constructor]. specialize (Hcmp eq_refl).
      destruct i; try contradiction. constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hv.
      destruct Hv01 as [-> | ->]; rewrite u_small64 by (unfold two64; lia); lia.
    + eexists _, E'. split; [rewrite Hgl, pc_plus4; reflexivity|]. fin_st Hsvc Ha Hn Hs'.
  (* [comment removed for export] *)
  - pose proof (xl_fop _ _ Hxl) as Hi. injection Hstep as <-.
    destruct (g_fop segs (ms_fregs ms) (ms_fcsr ms) (ms_regs ms) (Z_to_bv 64 (s_pc s)) (ms_resv ms) (ms_mem ms) (ms_rom ms) w Hfetch Hecall
                i Hdecode Hfrm Hi) as (fr' & fc' & Hfrm' & Hgl).
    eexists _, E. split; [rewrite Hgl, pc_plus4; reflexivity|].
    split; [exact Hsvc|]. split; [apply agree_refl|]. split; [cbn; lia|]. split; [apply pc_sound; [exact Hden | exact Hfrm'] | fin_fr].
Qed.

#[using="Type"] Theorem fx_step_fr : forall t img s s' E ms,
  tbl_ok segs t -> img_ok segs img -> fx_step t img s = SOk s' -> sden segs E s ms ->
  exists ms' E', RiscvSemantics.step segs ms = MachineOk ms' /\ ms_svc_pending ms = None /\
                 agree (s_next s) E E' /\ (s_next s <= s_next s')%positive /\ sden segs E' s' ms' /\
                 (forall x, fr_pt E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs s') = shape (s_rgs s) /\
                 rtm (s_rgs s') = rtm (s_rgs s).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s s' E ms Ht Himg Hs Hd.
  destruct (fx_step_frp t img s s' E ms Ht Himg Hs Hd) as (ms' & E' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
  exists ms', E'. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fx_step_fpc : forall t img s s' E ms ms',
  tbl_ok segs t -> img_ok segs img -> fx_step t img s = SOk s' -> sden segs E s ms -> RiscvSemantics.step segs ms = MachineOk ms' ->
  fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s s' E ms ms' Ht Himg Hs Hd Hst Hnf.
  destruct (fx_step_frp t img s s' E ms Ht Himg Hs Hd) as (ms1 & E1 & H1 & _ & _ & _ & _ & _ & _ & _ & Hfp).
  rewrite Hst in H1. injection H1 as <-. exact (Hfp (tbl_nofp_lookup t (s_pc s) Hnf)).
Qed.

#[using="Type"] Theorem fx_step_sound : forall t img s s' E ms,
  tbl_ok segs t -> img_ok segs img -> fx_step t img s = SOk s' -> sden segs E s ms ->
  exists ms' E', RiscvSemantics.step segs ms = MachineOk ms' /\ ms_svc_pending ms = None /\
                 agree (s_next s) E E' /\ (s_next s <= s_next s')%positive /\ sden segs E' s' ms' /\
                 (forall x, outside E (s_rgs s) x -> ms_mem ms' x = ms_mem ms x) /\ shape (s_rgs s') = shape (s_rgs s).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img s s' E ms Ht Himg Hs Hd.
  destruct (fx_step_fr t img s s' E ms Ht Himg Hs Hd) as (ms' & E' & H1 & H2 & H3 & H4 & H5 & Hfr & Hsh & _).
  exists ms', E'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [intros x Hx; exact (Hfr x (or_introl Hx)) | exact Hsh].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem fx_run_sound_fp : forall t img fuel stops s E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms ->
  exists ms' E', isteps segs ms ms' /\ agree (s_next s) E E' /\ sden segs E' (fx_run t img fuel stops s) ms' /\ fpc t ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel. induction fuel as [|f IH]; intros stops s E ms Ht Himg Hden; cbn [fx_run].
  - exists ms, E. split; [constructor|]. split; [apply agree_refl | split; [exact Hden | apply fpc_refl]].
  - destruct (fx_step t img s) as [s'| c a b tgt | l c |] eqn:Hs.
    + destruct (fx_step_sound t img s s' E ms Ht Himg Hs Hden) as (ms1 & E1 & Hst & Hsvc & Ha1 & Hn1 & Hd1 & _ & _).
      pose proof (fx_step_fpc t img s s' E ms ms1 Ht Himg Hs Hden Hst) as Hfp1.
      destruct (existsb (Z.eqb (s_pc s')) stops).
      * exists ms1, E1. split; [econstructor; [exact Hsvc | exact Hst | constructor]|]. split; [exact Ha1 | split; [exact Hd1 | exact Hfp1]].
      * destruct (IH stops s' E1 ms1 Ht Himg Hd1) as (ms2 & E2 & Hst2 & Ha2 & Hd2 & Hfp2).
        exists ms2, E2. split; [econstructor; [exact Hsvc | exact Hst | exact Hst2]|]. split; [|split; [exact Hd2 | exact (fpc_trans _ _ _ _ Hfp1 Hfp2)]].
        intros x Hx. rewrite (Ha1 x Hx). apply Ha2. lia.
    + exists ms, E. split; [constructor|]. split; [apply agree_refl | split; [exact Hden | apply fpc_refl]].
    + exists ms, E. split; [constructor|]. split; [apply agree_refl | split; [exact Hden | apply fpc_refl]].
    + exists ms, E. split; [constructor|]. split; [apply agree_refl | split; [exact Hden | apply fpc_refl]].
Qed.
#[using="Type"] Theorem fx_run_sound : forall t img fuel stops s E ms,
  tbl_ok segs t -> img_ok segs img -> sden segs E s ms ->
  exists ms' E', isteps segs ms ms' /\ agree (s_next s) E E' /\ sden segs E' (fx_run t img fuel stops s) ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops s E ms Ht Himg Hd. destruct (fx_run_sound_fp t img fuel stops s E ms Ht Himg Hd) as (ms' & E' & H1 & H2 & H3 & _).
  exists ms', E'. exact (conj H1 (conj H2 H3)).
Qed.

End WithSegs.
