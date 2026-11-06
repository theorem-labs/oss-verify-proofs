(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Znumtheory Zpow_facts.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgMont BgExp BgInv BgSpecs BgFrame BgLibSpec BgShiftSpec BgAddSpec
  BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect BgSqrSpec BgModSpec BgMontCorrect BgNumTheory BgMontSpec BgRecpSpec BgInvSpec BgMontSpec2
  BgCtxSpec BgExpLoops BgExpSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section ExpWord.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation BMu := (BM (M:=btree ptr) (ptr:=ptr)) (only parsing).

Local Ltac nlia := unfold ndiff, live, ROne, RMontN, RMontRR, RMontNi, RTmod, NFIX, RPool in *; lia.

Lemma mulw_no_ovf : forall w v, 1 <= w < BW -> 1 <= v < BW -> (mulw w v / v =? w) = (w * v <? BW).
Proof.
  intros w v Hw Hv. unfold mulw. destruct (Z.ltb_spec (w * v) BW) as [Hlt|Hge].
  - rewrite Z.mod_small by (split; [apply Z.mul_nonneg_nonneg; lia|exact Hlt]). rewrite Z.div_mul by lia. apply Z.eqb_refl.
  - apply Z.eqb_neq. intros E.
    pose proof (Z.mod_pos_bound (w * v) BW ltac:(unfold BW; lia)) as Hb.
    pose proof (Z.div_mod (w * v) BW ltac:(unfold BW; lia)) as Hd.
    assert (Hq : 1 <= w * v / BW) by (apply Z.div_le_lower_bound; lia).
    assert (Hle : (w * v) mod BW <= w * v - BW).
    { assert (BW * 1 <= BW * (w * v / BW)) by (apply Z.mul_le_mono_nonneg_l; unfold BW in *; lia). lia. }
    pose proof (Z.mul_div_le ((w * v) mod BW) v ltac:(lia)) as Hm. rewrite E in Hm.
    assert (v * w <= w * v - BW) by lia. assert (BW <= 0) by lia. unfold BW in *. lia.
Qed.

Section MontWord.
Variables (M : Z) (nl : nat) (rm : bnref) (m : BN) (u0 : nat).

Let q0 : bnref := RPool u0.
Let q1 : bnref := RPool (S u0).

Hypothesis Hm : bg_okv m /\ bn_norm m /\ bn_top m = nl /\ (1 <= nl <= 64)%nat /\ bn_mag m = M /\ Z.odd M = true /\ (rm < 5)%nat.

Definition RepW (x : Z) (b : BN) : Prop :=
  bn_canon b /\ (bn_top b <= nl)%nat /\ bn_neg b = false /\ 0 <= bn_mag b < M /\ bn_mag b = (x * Bp nl) mod M.

Definition roles (r t : bnref) : Prop := (r = q0 /\ t = q1) \/ (r = q1 /\ t = q0).

Definition mw_ctx (s : ST) : Prop := mont_ok s M nl /\ getbn rm s = m /\ (u0 + 2 <= gx_used (st_ctx s))%nat.

Definition mw_val (s : ST) (r : bnref) (w : Z) (r1 : bool) (V : Z) : Prop :=
  1 <= w < BW /\ exists X, (r1 = true -> X = 1) /\ (r1 = false -> RepW X (getbn r s)) /\ (X * w) mod M = V mod M.

Lemma M_facts : 1 <= M < Bp nl.
Proof.
  destruct Hm as (Ok & Nm & Tm & Hnl & Mm & Od & _). rewrite <- Mm, <- Tm. split; [|apply okv_mag_lt; exact Ok].
  pose proof (norm_mag_pos m Ok Nm ltac:(lia)). lia.
Qed.

Lemma roles_facts : forall r t, roles r t ->
  (NFIX + u0 <= r)%nat /\ (r < NFIX + u0 + 2)%nat /\ (NFIX + u0 <= t)%nat /\ (t < NFIX + u0 + 2)%nat /\ r <> t /\
  (forall x, In x [q0; q1] <-> x = r \/ x = t).
Proof.
  intros r t [[-> ->]|[-> ->]]; unfold q0, q1, RPool; (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]);
    intros x; cbn; (split; [intros [H|[H|[]]]; subst x; auto | intros [H|H]; subst x; auto]).
Qed.

Lemma mw_ctx_keeps : forall s s' o, mw_ctx s -> keeps (gx_used (st_ctx s)) o s s' -> (forall x, In x o -> (NFIX + u0 <= x)%nat) -> mw_ctx s'.
Proof.
  intros s s' o (A & B & C) K Ho. destruct Hm as (_ & _ & _ & _ & _ & _ & Hrm). unfold mw_ctx.
  split; [apply (mont_ok_keeps _ o s s' M nl K); [intros H|intros H| exact A]; apply Ho in H; unfold RMontN, RMontRR, NFIX in H; lia|].
  split; [rewrite (keeps_get _ _ _ _ rm K); [exact B|unfold NFIX; lia|intros H; apply Ho in H; unfold NFIX in H; lia]|].
  rewrite (keeps_used _ _ _ _ K). exact C.
Qed.

Lemma mw_flush_spec : forall r t w (r1 : bool) X F s,
  mw_ctx s -> roles r t -> 1 <= w < BW -> (r1 = true -> X = 1) -> (r1 = false -> RepW X (getbn r s)) ->
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + 4 <= BG_POOL)%nat ->
  hoare F s (mw_flush ops r t w r1 rm) (fun rt s' => let '(r', t') := rt in
     keeps (gx_used (st_ctx s)) [q0; q1] s s' /\ mw_ctx s' /\ roles r' t' /\ RepW (X * w) (getbn r' s')).
Proof.
  intros r t w r1 X F s HC HR Hw HX1 HX0 Hd Hp. apply hoare_wf. intros Hs.
  pose proof HC as (MO & Erm & Hu). destruct Hm as (Okm & Nm & Tm & Hnl & Mm & Od & Hrm). pose proof M_facts as [HM1 HMR].
  pose proof (roles_facts r t HR) as (R1 & R2 & R3 & R4 & R5 & R6).
  assert (Vr : (r < length (st_bns s))%nat) by (apply live_valid; [exact Hs|nlia]).
  assert (Vt : (t < length (st_bns s))%nat) by (apply live_valid; [exact Hs|nlia]).
  assert (NrOne : r <> ROne) by nlia.
  assert (RRf : bn_top (getbn RMontRR s) = nl /\ bn_neg (getbn RMontRR s) = false /\ bn_mag (getbn RMontRR s) = (Bp nl * Bp nl) mod M).
  { unfold mont_ok in MO. cbv zeta in MO. destruct MO as (_ & _ & _ & _ & _ & _ & _ & _ & E). exact E. }
  destruct RRf as (Trr & Nrr & Mrr).
  unfold mw_flush. destruct r1.
  -
    specialize (HX1 eq_refl). subst X. unfold mw_to_mont_word.
    eapply hoare_bind with (R := fun _ s2 => keeps (gx_used (st_ctx s)) [r] s s2 /\ mont_ok s2 M nl /\
                                         mont_res_canon M nl (w * ((Bp nl * Bp nl) mod M)) (getbn r s2)).
    { eapply hoare_bind; [apply BN_set_word_spec; [exact Vr|exact NrOne|split; lia]|].
    intros [] s1 Hs1 (b1 & -> & M1 & C1 & N1 & T1).
    assert (K1 : keeps (gx_used (st_ctx s)) [r] s (setbn r b1 s)) by apply keeps_setbn.
    assert (MO1 : mont_ok (setbn r b1 s) M nl).
    { apply (mont_ok_keeps _ [r] s _ M nl K1); [| |exact MO]; intros [E|[]]; nlia. }
    unfold BN_to_montgomery.
    eapply hoare_mono.
    { apply (BN_mod_mul_montgomery_spec r r RMontRR _ _ M nl MO1). unfold mul_mont_pre, live. rewrite st_ctx_setbn.
      rewrite getbn_setbn_same by exact Vr. rewrite getbn_setbn_other by nlia. rewrite Trr, Nrr, Mrr, N1, M1.
      split; [lia|]. split; [lia|]. split; [nlia|]. split; [exact NrOne|]. split; [nlia|].
      split; [nlia|]. split; [exact Hd|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [reflexivity|]. split; [reflexivity|].
      pose proof (Z.mod_pos_bound (Bp nl * Bp nl) M ltac:(lia)) as Hb.
      assert (E1 : Bp nl = BW * Bp (nl - 1)) by (replace nl with (S (nl - 1)) at 1 by lia; rewrite Bp_S; reflexivity).
      pose proof (Bp_pos (nl - 1)).
      assert (w * ((Bp nl * Bp nl) mod M) <= w * M) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (w * M < BW * M) by (apply (proj1 (Z.mul_lt_mono_pos_r M _ _ ltac:(lia))); lia).
      assert (BW * M <= Bp nl * M) by (apply Z.mul_le_mono_nonneg_r; [lia|]; rewrite E1; assert (BW * 1 <= BW * Bp (nl - 1)) by (apply Z.mul_le_mono_nonneg_l; unfold BW; lia); lia).
      lia. }
    intros [] s2 Hs2 (K2 & MO2 & MC2). rewrite st_ctx_setbn in K2. rewrite getbn_setbn_same, getbn_setbn_other in MC2 by (first [exact Vr|nlia]).
    rewrite M1, Mrr in MC2. split; [|split; [exact MO2|exact MC2]].
    eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|exact K2]]. intros x Hx _. cbn in Hx |- *. tauto. }
    intros [] s2 Hs2 (K02r & MO2 & MC2). destruct MC2 as (C2 & T2 & N2 & B2 & V2).
    apply hoare_ret.
    assert (K02 : keeps (gx_used (st_ctx s)) [q0; q1] s s2).
    { eapply keeps_weaken; [apply Nat.le_refl| |exact K02r]. intros x Hx _. apply R6. destruct Hx as [<-|[]]. left. reflexivity. }
    split; [exact K02|]. split; [apply (mw_ctx_keeps s s2 _ HC K02); intros x Hx; apply R6 in Hx; lia|]. split; [exact HR|].
    unfold RepW. split; [exact C2|]. split; [exact T2|]. split; [exact N2|]. split; [exact B2|].
    rewrite <- (Z.mod_small _ M B2). rewrite Z.mul_1_l. apply (bn_to_mont_value M nl w); [lia|exact Od|exact V2].
  -
    specialize (HX0 eq_refl). destruct HX0 as (Cx & Tx & Nx & Bx & Mx). unfold mw_mod_mul_word.
    eapply hoare_bind; [apply BN_mul_word_spec; [exact Vr|exact NrOne|lia|destruct Cx as [H _]; exact H|unfold BG_DMAX; lia]|].
    intros [] s1 Hs1 (b1 & -> & M1 & Nb1 & Ng1 & T1). specialize (Ng1 Nx).
    assert (K1 : keeps (gx_used (st_ctx s)) [r] s (setbn r b1 s)) by apply keeps_setbn.
    unfold BN_mod. eapply hoare_bind.
    { apply BN_div_spec. unfold div_pre, live. rewrite st_ctx_setbn, getbn_setbn_same, !getbn_setbn_other by (first [exact Vr | nlia]).
      rewrite Erm, Tm.
      split; [nlia|]. split; [nlia|]. split; [intros d Hd'; discriminate|].
      split; [intros x [= <-]; split; [nlia|]; split; [nlia|]; split; [nlia|discriminate]|].
      split; [unfold BG_DEPTH in *; lia|]. split; [lia|]. split; [exact Nm|]. split; [lia|]. unfold BG_DMAX. lia. }
    intros [] s2 Hs2 (K2 & _ & Dr). cbn [opt_refs app] in K2. rewrite st_ctx_setbn in K2.
    specialize (Dr t eq_refl). cbv zeta in Dr. rewrite getbn_setbn_same, getbn_setbn_other in Dr by (first [exact Vr | nlia]).
    rewrite Erm, Mm, Tm, M1, Ng1 in Dr. destruct Dr as (C2 & M2 & N2 & T2). cbn [andb] in N2.
    apply hoare_ret.
    assert (K02 : keeps (gx_used (st_ctx s)) [q0; q1] s s2).
    { eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|exact K2]]. intros x Hx _. apply R6.
      cbn in Hx. destruct Hx as [<-|[<-|[]]]; [left|right]; reflexivity. }
    split; [exact K02|]. split; [apply (mw_ctx_keeps s s2 _ HC K02); intros x Hx; apply R6 in Hx; lia|].
    split; [destruct HR as [[-> ->]|[-> ->]]; [right|left]; split; reflexivity|].
    pose proof (Z.mod_pos_bound (bn_mag (getbn r s) * w) M ltac:(lia)) as Hb.
    unfold RepW. split; [exact C2|]. split; [lia|]. split; [exact N2|]. split; [lia|].
    rewrite M2, Mx. rewrite Z.mul_mod_idemp_l by lia. f_equal. ring.
Qed.

Lemma exp_bit_step : forall P c, 0 <= P -> 0 <= c ->
  P / 2 ^ c = 2 * (P / 2 ^ (c + 1)) + Z.b2z (Z.testbit P c).
Proof.
  intros P c HP Hc. rewrite Z.testbit_spec' by lia. pose proof (exp_window_step P c 0 HP ltac:(lia)) as E.
  rewrite Z.sub_0_r, Z.add_0_l, Z.pow_1_r in E. unfold bits_val in E. rewrite Z.pow_1_r in E. lia.
Qed.

Lemma pow_bit_step : forall a e (b : bool), 0 <= e -> 1 <= a ->
  a ^ (2 * e + Z.b2z b) = a ^ e * a ^ e * (if b then a else 1).
Proof.
  intros a e b He Ha. rewrite Z.pow_add_r by (destruct b; cbn [Z.b2z]; lia). replace (2 * e) with (e + e) by lia. rewrite Z.pow_add_r by lia.
  destruct b; cbn [Z.b2z]; [rewrite Z.pow_1_r|rewrite Z.pow_0_r]; reflexivity.
Qed.

Lemma sq_mod : forall x V, 0 < M -> x mod M = V mod M -> (x * x) mod M = (V * V) mod M.
Proof. intros x V HM E. rewrite <- (mod_mod_mul x x), <- (mod_mod_mul V V) by lia. rewrite E. reflexivity. Qed.

Lemma mul_mod_r : forall x V a, 0 < M -> x mod M = V mod M -> (x * a) mod M = (V * a) mod M.
Proof. intros x V a HM E. rewrite <- (Z.mul_mod_idemp_l x), <- (Z.mul_mod_idemp_l V) by lia. rewrite E. reflexivity. Qed.

Definition mw_sq (s : ST) (r : bnref) (w : Z) (r1 : bool) (V : Z) : Prop :=
  1 <= w < BW /\ exists X, (r1 = true -> X = 1) /\ (r1 = false -> RepW X (getbn r s)) /\ (X * X * w) mod M = (V * V) mod M.

Lemma mw_loop_spec : forall cnt a rp r t w (r1 : bool) F s P,
  mw_ctx s -> (rp < 5)%nat -> P = bn_mag (getbn rp s) -> 0 <= P -> 1 <= a < BW ->
  (length (gx_frames (st_ctx s)) + 2 <= BG_DEPTH)%nat -> (gx_used (st_ctx s) + 4 <= BG_POOL)%nat ->
  roles r t -> mw_val s r w r1 (a ^ (P / 2 ^ Z.of_nat cnt)) ->
  hoare F s (mw_loop ops cnt a rp rm (r, t, w, r1)) (fun st' s' => let '(r', t', w', r1') := st' in
     keeps (gx_used (st_ctx s)) [q0; q1] s s' /\ mw_ctx s' /\ roles r' t' /\ mw_val s' r' w' r1' (a ^ P)).
Proof.
  induction cnt as [|c IH]; intros a rp r t w r1 F s P HC Hrp EP HP0 Ha Hd Hp HR HV.
  - cbn [mw_loop]. apply hoare_ret. rewrite Z.pow_0_r, Z.div_1_r in HV. split; [apply keeps_refl|]. split; [exact HC|]. split; [exact HR|exact HV].
  - cbn [mw_loop]. apply hoare_wf. intros Hs. pose proof M_facts as [HM1 HMR]. destruct Hm as (Okm & Nm & Tm & Hnl & Mm & Od & Hrm).
    set (u := gx_used (st_ctx s)) in *.
    set (e := P / 2 ^ (Z.of_nat c + 1)). set (V := a ^ e) in *.
    assert (He : 0 <= e) by (unfold e; apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]).
    rewrite Nat2Z.inj_succ, <- Z.add_1_r in HV. fold e V in HV. destruct HV as (Hw & X & HX1 & HX0 & EQ).
    pose proof (roles_facts r t HR) as (R1 & R2 & R3 & R4 & R5 & R6).

    rewrite (mulw_no_ovf w w Hw Hw).
    eapply hoare_bind with (R := fun rt s1 => let '(r', t') := rt in
       keeps u [q0; q1] s s1 /\ mw_ctx s1 /\ roles r' t' /\
       mw_sq s1 r' (if negb (w * w <? BW) then 1 else mulw w w) (if negb (w * w <? BW) then false else r1) V).
    { destruct (Z.ltb_spec (w * w) BW) as [Hlt|Hge]; cbn [negb].
      - apply hoare_ret. split; [apply keeps_refl|]. split; [exact HC|]. split; [exact HR|].
        unfold mw_sq, mulw. rewrite Z.mod_small by (split; [apply Z.mul_nonneg_nonneg; lia|exact Hlt]).
        split; [split; [apply Z.le_trans with (m := 1 * 1); [lia|apply Z.mul_le_mono_nonneg; lia]|exact Hlt]|].
        exists X. split; [exact HX1|]. split; [exact HX0|]. replace (X * X * (w * w)) with ((X * w) * (X * w)) by ring. apply sq_mod; [lia|exact EQ].
      - eapply hoare_mono; [apply (mw_flush_spec r t w r1 X F s); assumption|].
        intros [r' t'] s1 _ (K1 & C1 & HR1 & RX1). split; [exact K1|]. split; [exact C1|]. split; [exact HR1|].
        unfold mw_sq. split; [unfold BW; lia|]. exists (X * w). split; [intros E; discriminate E|]. split; [intros _; exact RX1|].
        rewrite Z.mul_1_r. apply sq_mod; [lia|exact EQ]. }
    intros [ra ta] s1 Hs1 (K1 & C1 & HR1 & SQ1).
    set (r1a := if negb (w * w <? BW) then false else r1) in *. set (wa := if negb (w * w <? BW) then 1 else mulw w w) in *.
    cbv beta iota. fold r1a wa.
    pose proof (keeps_used _ _ _ _ K1) as U1. pose proof (keeps_frames _ _ _ _ K1) as F1. fold u in U1.
    pose proof (roles_facts ra ta HR1) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    destruct SQ1 as (Hwa & Xa & XA1 & XA0 & EQa). pose proof C1 as (MO1 & Erm1 & Hu1).

    eapply hoare_bind with (R := fun _ s2 => keeps u [q0; q1] s s2 /\ mw_ctx s2 /\ mw_val s2 ra wa r1a (V * V)).
    { destruct r1a.
      - apply hoare_ret. split; [exact K1|]. split; [exact C1|]. split; [exact Hwa|]. exists 1. specialize (XA1 eq_refl). subst Xa.
        split; [reflexivity|]. split; [intros E; discriminate E|]. exact EQa.
      - specialize (XA0 eq_refl). destruct XA0 as (Cx & Tx & Nx & Bx & Mx).
        assert (Vra : (ra < length (st_bns s1))%nat) by (apply live_valid; [exact Hs1|nlia]).
        eapply hoare_mono.
        { apply (BN_mod_mul_montgomery_spec ra ra ra _ s1 M nl MO1). unfold mul_mont_pre, live. rewrite Nx.
          split; [nlia|]. split; [nlia|]. split; [nlia|]. split; [nlia|]. split; [nlia|]. split; [nlia|].
          split; [rewrite F1; exact Hd|]. split; [rewrite U1; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
          assert (bn_mag (getbn ra s1) * bn_mag (getbn ra s1) <= bn_mag (getbn ra s1) * M) by (apply Z.mul_le_mono_nonneg_l; lia).
          assert (bn_mag (getbn ra s1) * M < Bp nl * M) by (apply (proj1 (Z.mul_lt_mono_pos_r M _ _ ltac:(lia))); lia). lia. }
        intros [] s2 _ (K2 & MO2 & (C2 & T2 & N2 & B2 & V2)). rewrite U1 in K2.
        assert (K02 : keeps u [q0; q1] s s2).
        { eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|exact K2]]. intros x Hx _. cbn in Hx.
          destruct Hx as [Hx|[Hx|[Hx|[]]]]; [left; exact Hx|right; left; exact Hx|]. apply Q6. left. symmetry. exact Hx. }
        split; [exact K02|]. split; [apply (mw_ctx_keeps s1 s2 [ra] C1); [rewrite U1; exact K2|intros x [<-|[]]; lia]|].
        split; [exact Hwa|]. exists (Xa * Xa). split; [intros E; discriminate E|]. split; [intros _|exact EQa].
        unfold RepW. split; [exact C2|]. split; [exact T2|]. split; [exact N2|]. split; [exact B2|].
        apply (mont_rep_mul M nl Xa Xa (bn_mag (getbn ra s1)) (bn_mag (getbn ra s1))); try assumption; lia. }
    intros [] s2 Hs2 (K2 & C2 & MV2).
    pose proof (keeps_used _ _ _ _ K2) as U2. pose proof (keeps_frames _ _ _ _ K2) as F2. fold u in U2.

    apply hoare_bind_get.
    assert (Erp : getbn rp s2 = getbn rp s) by (apply (keeps_get _ _ _ _ rp K2); [nlia|intros Hx; apply R6 in Hx; nlia]).
    rewrite Erp, (is_bit_set_pure_spec (getbn rp s)) by (first [apply (st_wf_okv rp s Hs); apply live_valid; [exact Hs|nlia] | lia]). rewrite <- EP.
    pose proof (exp_bit_step P (Z.of_nat c) HP0 ltac:(lia)) as Estep. fold e in Estep.
    assert (EV : a ^ (P / 2 ^ Z.of_nat c) = V * V * (if Z.testbit P (Z.of_nat c) then a else 1)).
    { rewrite Estep. unfold V. apply pow_bit_step; lia. }
    destruct MV2 as (Hwa2 & Xb & XB1 & XB0 & EQb). pose proof C2 as (MO2 & Erm2 & Hu2).
    destruct (Z.testbit P (Z.of_nat c)) eqn:Eb.
    +
      rewrite (mulw_no_ovf wa a Hwa2 Ha).
      eapply hoare_bind with (R := fun rt s3 => let '(r3, t3) := rt in
         keeps u [q0; q1] s s3 /\ mw_ctx s3 /\ roles r3 t3 /\
         mw_val s3 r3 (if negb (wa * a <? BW) then a else mulw wa a) (if negb (wa * a <? BW) then false else r1a) (V * V * a)).
      { destruct (Z.ltb_spec (wa * a) BW) as [Hlt|Hge]; cbn [negb].
        - apply hoare_ret. split; [exact K2|]. split; [exact C2|]. split; [exact HR1|].
          unfold mw_val, mulw. rewrite Z.mod_small by (split; [apply Z.mul_nonneg_nonneg; lia|exact Hlt]).
          split; [split; [apply Z.le_trans with (m := 1 * 1); [lia|apply Z.mul_le_mono_nonneg; lia]|exact Hlt]|].
          exists Xb. split; [exact XB1|]. split; [exact XB0|]. rewrite Z.mul_assoc. apply mul_mod_r; [lia|exact EQb].
        - eapply hoare_mono; [apply (mw_flush_spec ra ta wa r1a Xb F s2); try assumption; [rewrite F2; exact Hd|rewrite U2; lia]|].
          intros [r3 t3] s3 _ (K3 & C3 & HR3 & RX3). rewrite U2 in K3.
          split; [|split; [exact C3|split; [exact HR3|]]].
          { eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K2|exact K3]]. intros x Hx _. cbn in Hx |- *. tauto. }
          unfold mw_val. split; [exact Ha|]. exists (Xb * wa). split; [intros E; discriminate E|]. split; [intros _; exact RX3|].
          apply mul_mod_r; [lia|exact EQb]. }
      intros [r3 t3] s3 Hs3 (K3 & C3 & HR3 & MV3). cbv beta iota.
      pose proof (keeps_used _ _ _ _ K3) as U3. pose proof (keeps_frames _ _ _ _ K3) as F3. fold u in U3.
      eapply hoare_mono.
      { apply (IH a rp r3 t3 _ _ F s3 P C3 Hrp); try assumption.
        - rewrite (keeps_get _ _ _ _ rp K3); [exact EP|nlia|intros Hx; apply R6 in Hx; nlia].
        - rewrite F3. exact Hd.
        - rewrite U3. exact Hp.
        - rewrite EV. exact MV3. }
      intros [[[r4 t4] w4] r14] s4 _ (K4 & C4 & HR4 & MV4). rewrite U3 in K4.
      split; [|split; [exact C4|split; [exact HR4|exact MV4]]].
      eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K3|exact K4]]. intros x Hx _. cbn in Hx |- *. tauto.
    +
      eapply hoare_mono.
      { apply (IH a rp ra ta _ _ F s2 P C2 Hrp); try assumption.
        - rewrite Erp. exact EP.
        - rewrite F2. exact Hd.
        - rewrite U2. exact Hp.
        - rewrite EV, Z.mul_1_r. split; [exact Hwa2|]. exists Xb. auto. }
      intros [[[r4 t4] w4] r14] s4 _ (K4 & C4 & HR4 & MV4). rewrite U2 in K4.
      split; [|split; [exact C4|split; [exact HR4|exact MV4]]].
      eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K2|exact K4]]. intros x Hx _. cbn in Hx |- *. tauto.
Qed.

End MontWord.

Definition modexpw_pre (rr rp rm : bnref) (s : ST) : Prop :=
  live rr s /\ live rp s /\ live rm s /\ ndiff rr ROne /\ ndiff rr rm /\ (rr < 5 /\ rp < 5 /\ rm < 5)%nat /\
  (length (gx_frames (st_ctx s)) + 4 <= BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 14 <= BG_POOL)%nat /\
  bn_norm (getbn rm s) /\ (1 <= bn_top (getbn rm s) <= 64)%nat /\
  bn_norm (getbn rp s) /\ (bn_top (getbn rp s) <= 64)%nat.

Lemma mod_small_limb_modulus : forall (m : BN), bg_okv m -> bn_top m = 1%nat -> nth 0 (bn_buf m) 0 = bn_mag m.
Proof.
  intros m [Hl Ht] E. unfold bn_mag. rewrite E. unfold bn_dmax in Ht. destruct (bn_buf m) as [|x l]; cbn in *; [lia|]. lia.
Qed.

Lemma BN_mod_exp_mont_word_spec : forall rr (a : Z) rp rm F s,
  modexpw_pre rr rp rm s -> mont_pristine s -> getbn RTmod s = bn_nil 0 ->
  Z.odd (bn_mag (getbn rm s)) = true -> 0 <= a < BW -> (length F < BG_NF)%nat ->
  hoare F s (BN_mod_exp_mont_word ops rr a rp rm) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     exp_post a (bn_mag (getbn rp s)) (bn_mag (getbn rm s)) (getbn rr s') /\
     (bn_top (getbn rr s') <= bn_top (getbn rm s))%nat /\ mont_pristine s' /\ getbn RTmod s' = bn_nil 0).
Proof.
  intros rr a rp rm F s (Lr & Lp & Lm & Nr1 & Nrm & (R1 & R2 & R3) & Hdepth & Hpool & Nm & Tm & Np & Tp) Hpr ET Hodd Ha HF.
  apply hoare_wf. intros Hs. unfold BN_mod_exp_mont_word. set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid rr s Hs Lr) as Vr. pose proof (live_valid rp s Hs Lp) as Vp. pose proof (live_valid rm s Hs Lm) as Vm.
  unfold live in Lr, Lp, Lm. fold u in Lr, Lp, Lm.
  set (p := getbn rp s) in *. set (m := getbn rm s) in *.
  pose proof (st_wf_okv rm s Hs Vm) as Okm. pose proof (st_wf_okv rp s Hs Vp) as Okp. fold p in Okp. fold m in Okm.
  pose proof (norm_mag_pos _ Okm Nm ltac:(lia)) as HM. set (M := bn_mag m) in *. set (P := bn_mag p) in *. set (nl := bn_top m) in *.
  assert (HL : (NFIX <= length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; lia).
  assert (HMR : M < Bp nl) by (apply okv_mag_lt; exact Okm).
  pose proof Hpr as (PrRR & PrN & PrNi & Pri & Pn0).
  eapply hoare_bind; [apply any_consttime_spec; intros q [<-|[<-|[]]]; assumption|]. intros ct s0 _ (-> & ->).
  apply hoare_bind_get. fold m. rewrite (is_odd_pure_spec m Okm). fold M. rewrite Hodd. cbn [negb].

  set (a' := if (bn_top m =? 1)%nat then a mod nth 0 (bn_buf m) 0 else a).
  assert (Ha' : 0 <= a' < BW /\ a' mod M = a mod M /\ (a' = 0 -> a mod M = 0) /\ (a' <> 0 -> 2 <= M)).
  { unfold a'. destruct (Nat.eqb_spec (bn_top m) 1) as [E1|E1].
    - rewrite (mod_small_limb_modulus m Okm E1). fold M. pose proof (Z.mod_pos_bound a M HM) as Hb.
      assert (M < BW) by (unfold nl in HMR; rewrite E1 in HMR; change (Bp 1) with (BW * 1) in HMR; lia).
      split; [lia|]. split; [apply Z.mod_mod; lia|]. split; [intros E; exact E|]. intros E. lia.
    - split; [exact Ha|]. split; [reflexivity|]. split; [intros ->; reflexivity|]. intros _.
      pose proof (okv_mag_ge m Okm Nm ltac:(lia)) as Hge. fold M in Hge. pose proof (Bp_pos (bn_top m - 2)) as HB.
      replace (bn_top m - 1)%nat with (S (bn_top m - 2)) in Hge by lia. rewrite Bp_S in Hge. unfold BW in Hge. lia. }
  destruct Ha' as (Ba' & Ema' & Za' & NZa').
  eapply hoare_bind; [apply BN_num_bits_spec; exact Vp|]. intros bits s0 _ (-> & ->). fold p.
  pose proof (num_bits_pure_spec p Okp Np) as (B0 & B1 & B2 & B3). fold P in B1, B2.
  pose proof (okv_mag_nonneg p Okp) as HP0. fold P in HP0.
  destruct (Z.eqb_spec (num_bits_pure p) 0) as [Ez|Ez].
  {
    assert (P = 0) as EP by (destruct (Z.eq_dec P 0) as [|Hne]; [assumption|]; specialize (B2 ltac:(lia)); rewrite Ez in B2;
      change (2 ^ (0 - 1)) with 0 in B2; change (2 ^ 0) with 1 in B2; lia).
    rewrite EP. eapply hoare_mono; [apply (exp_bits0_spec rr rm F s a); [unfold live; lia|exact Vm|exact Nr1|exact Nrm|exact Nm|fold m; lia]|].
    intros [] s' _ (K & E & T). split; [exact K|]. split; [exact E|]. split; [lia|].
    unfold mont_pristine. destruct K as [[_ Sl] (S1 & S2 & S3 & S4)]. rewrite S1, S2.
    rewrite !Sl by (first [unfold RMontRR, RMontN, RMontNi, RTmod, NFIX; lia|intros [E'|[]]; unfold RMontRR, RMontN, RMontNi, RTmod in E'; lia]).
    split; [exact Hpr|exact ET]. }
  set (bits := num_bits_pure p) in *.
  assert (HP1 : 1 <= P) by (destruct (Z.eq_dec P 0) as [E0|]; [exfalso; apply Ez; apply B1; exact E0|lia]).
  specialize (B2 ltac:(lia)).
  destruct (Z.eqb_spec a' 0) as [Za|Za].
  {
    eapply hoare_mono; [apply BN_zero_spec; [exact Vr|exact Nr1]|].
    intros [] s' _ (b' & -> & T' & N'). rewrite getbn_setbn_same by exact Vr. split; [apply keeps_setbn|].
    split.
    { unfold exp_post. rewrite (bn_mag_top0 b' T'). split; [split; [left; exact T'|intros _; exact N']|]. split; [exact N'|].
      rewrite <- (pow_mod_base a P M) by lia. rewrite (Za' Za), Z.pow_0_l by lia. reflexivity. }
    split; [lia|]. unfold mont_pristine. rewrite !getbn_setbn_other by (unfold RMontRR, RMontN, RMontNi, RTmod; lia). cbn. split; [exact Hpr|exact ET]. }
  specialize (NZa' Za).

  eapply hoare_bind; [apply BN_CTX_start_spec; unfold BG_DEPTH in *; lia|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  pose proof (inner_bns_eq u s s0 Eb0 Sc0) as I0.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
  intros r s1 Hs1 (Er & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Er, Eu1.
  pose proof (inner_get u r s0 s1 Len1 Sc1 Oth1 ltac:(rewrite Er; unfold RPool; lia)) as I1.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu1; unfold BG_POOL in *; lia|].
  intros t s2 Hs2 (Et & Eu2 & Ef2 & Sc2 & Len2 & Oth2 & _). rewrite Eu1 in Et, Eu2.
  pose proof (inner_get u t s1 s2 Len2 Sc2 Oth2 ltac:(rewrite Et; unfold RPool; lia)) as I2.
  pose proof (inner_trans _ _ _ _ _ _ (inner_trans _ _ _ _ _ _ I0 I1) I2) as I02. cbn [app] in I02.
  assert (G2 : forall z, (z < NFIX + u)%nat -> getbn z s2 = getbn z s) by (intros z Hz; apply (inner_get_slot _ _ _ _ z I02 Hz); intros []).
  pose proof I02 as (L2 & Sc02 & _).
  assert (Ef2' : gx_frames (st_ctx s2) = gx_frames (st_ctx s) ++ [u]) by (rewrite Ef2, Ef1; exact Ef0).

  eapply hoareG_bind.
  { apply BN_MONT_CTX_new_spec; [exact HF|]. unfold mont_pristine. rewrite !G2 by (unfold RMontRR, RMontN, RMontNi, NFIX; lia).
    destruct Sc02 as (S1 & S2 & _). rewrite S1, S2. exact Hpr. }
  intros pm s2' _ ->. cbv beta.

  eapply hoareG_bind.
  { apply BN_MONT_CTX_set_spec. unfold montset_pre, live. rewrite Eu2, Ef2', length_app, !G2 by (unfold RTmod, NFIX; lia). cbn [length]. fold m M nl.
    split; [lia|]. split; [unfold ndiff, RMontN; lia|]. split; [unfold ndiff, RMontRR; lia|]. split; [unfold ndiff, RTmod; lia|].
    split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [exact ET|]. cbv zeta. split; [exact Nm|]. split; [lia|exact Hodd]. }
  intros [] s4 Hs4 (KM4 & Ri4 & MO4). rewrite (G2 rm Lm) in Ri4, MO4. fold m M nl in Ri4, MO4. rewrite Eu2 in KM4.
  destruct KM4 as [[(L4 & U4 & F4) Sl4] [Rb4 Rs4]]. rewrite Eu2 in U4. rewrite Ef2' in F4.
  assert (G4 : forall z, (z < NFIX + S (S u))%nat -> z <> RMontN -> z <> RMontRR -> getbn z s4 = getbn z s2).
  { intros z Hz Hz1 Hz2. apply Sl4; [exact Hz|]. intros [E|[E|[]]]; [apply Hz1|apply Hz2]; rewrite E; reflexivity. }
  assert (G4s : forall z, (z < NFIX + u)%nat -> z <> RMontN -> z <> RMontRR -> getbn z s4 = getbn z s).
  { intros z Hz Hz1 Hz2. rewrite G4 by (lia || assumption). apply G2. exact Hz. }

  assert (KM : bg_okv m /\ bn_norm m /\ bn_top m = nl /\ (1 <= nl <= 64)%nat /\ bn_mag m = M /\ Z.odd M = true /\ (rm < 5)%nat).
  { split; [exact Okm|]. split; [exact Nm|]. split; [reflexivity|]. split; [exact Tm|]. split; [reflexivity|]. split; [exact Hodd|exact R3]. }
  assert (C4 : mw_ctx M nl rm m u s4).
  { unfold mw_ctx. split; [exact MO4|]. split; [apply G4s; [lia|unfold RMontN; lia|unfold RMontRR; lia]|]. rewrite U4. lia. }
  eapply hoareG_bind.
  { apply (mw_loop_spec M nl rm m u KM (Z.to_nat (bits - 1)) a' rp r t a' true _ s4 P C4 R2).
    - rewrite G4s by (first [lia|unfold RMontN, RMontRR; lia]). reflexivity.
    - exact HP0.
    - lia.
    - rewrite F4, length_app. cbn [length]. unfold BG_DEPTH in *. lia.
    - rewrite U4. unfold BG_POOL in *. lia.
    - left. rewrite Er, Et. split; reflexivity.
    - unfold mw_val. split; [lia|]. exists 1. split; [reflexivity|]. split; [intros E; discriminate E|].
      rewrite Z2Nat.id by lia. replace (P / 2 ^ (bits - 1)) with 1; [rewrite Z.pow_1_r, Z.mul_1_l; reflexivity|].
      assert (2 ^ bits = 2 * 2 ^ (bits - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      apply Z.div_unique with (r := P - 2 ^ (bits - 1)); [left|]; lia. }
  intros [[[r5 t5] w5] r15] s5 Hs5 (K5 & C5 & HR5 & MV5). cbv beta iota. rewrite U4 in K5.
  destruct MV5 as (Hw5 & X5 & HX51 & HX50 & EQ5). pose proof C5 as (MO5 & Erm5 & Hu5).
  pose proof (keeps_used _ _ _ _ K5) as U5. pose proof (keeps_frames _ _ _ _ K5) as F5. rewrite U4 in U5. rewrite F4 in F5.
  assert (EaP : (a' ^ P) mod M = (a ^ P) mod M) by (rewrite <- (pow_mod_base a' P M), Ema', pow_mod_base by lia; reflexivity).

  eapply hoareG_bind with (R := fun rt s6 => let '(r6, t6) := rt in
     keeps (S (S u)) [RPool u; RPool (S u)] s4 s6 /\ mw_ctx M nl rm m u s6 /\ roles u r6 t6 /\
     exists X6, ((if w5 =? 1 then r15 else false) = true -> X6 = 1) /\ ((if w5 =? 1 then r15 else false) = false -> RepW M nl X6 (getbn r6 s6)) /\
                X6 mod M = (a ^ P) mod M).
  { destruct (Z.eqb_spec w5 1) as [Ew|Ew].
    - apply hoare_ret. split; [exact K5|]. split; [exact C5|]. split; [exact HR5|]. exists X5. split; [exact HX51|]. split; [exact HX50|].
      rewrite <- EaP, <- EQ5, Ew, Z.mul_1_r. reflexivity.
    - eapply hoare_mono; [apply (mw_flush_spec M nl rm m u KM r5 t5 w5 r15 X5 _ s5 C5 HR5 Hw5 HX51 HX50); [rewrite F5, length_app; cbn [length]; unfold BG_DEPTH in *; lia|rewrite U5; unfold BG_POOL in *; lia]|].
      intros [r6 t6] s6 _ (K6 & C6 & HR6 & RX6). rewrite U5 in K6.
      split; [|split; [exact C6|split; [exact HR6|]]].
      { eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K5|exact K6]]. intros x Hx _. cbn in Hx |- *. tauto. }
      exists (X5 * w5). split; [intros E; discriminate E|]. split; [intros _; exact RX6|]. rewrite <- EaP. exact EQ5. }
  intros [r6 t6] s6 Hs6 (K6 & C6 & HR6 & X6 & HX61 & HX60 & EQ6). cbv beta iota.
  pose proof C6 as (MO6 & Erm6 & Hu6). pose proof (keeps_used _ _ _ _ K6) as U6. pose proof (keeps_frames _ _ _ _ K6) as F6. rewrite U4 in U6. rewrite F4 in F6.
  pose proof (roles_facts M nl rm m u KM r6 t6 HR6) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  assert (Vr6 : (rr < length (st_bns s6))%nat) by (apply live_valid; [exact Hs6|unfold live; rewrite U6; lia]).

  eapply hoareG_bind with (R := fun _ s7 => keeps (S (S u)) [RPool u; RPool (S u); rr] s4 s7 /\ mont_ok s7 M nl /\
                                        exp_post a P M (getbn rr s7) /\ (bn_top (getbn rr s7) <= nl)%nat).
  { destruct (if w5 =? 1 then r15 else false).
    - specialize (HX61 eq_refl). subst X6. rewrite Z.mod_1_l in EQ6 by lia.
      eapply hoare_mono; [apply BN_one_spec; [exact Vr6|exact Nr1]|].
      intros [] s7 _ (b7 & -> & M7 & C7 & N7 & T7). rewrite getbn_setbn_same by exact Vr6.
      split; [|split; [|split; [|lia]]].
      + eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K6|rewrite <- U6; apply keeps_setbn]]. intros x Hx _. cbn in Hx |- *. tauto.
      + apply (mont_ok_keeps (S (S u)) [rr] s6 _ M nl); [rewrite <- U6; apply keeps_setbn| | |exact MO6]; unfold RMontN, RMontRR; intros [E|[]]; lia.
      + unfold exp_post. split; [exact C7|]. split; [exact N7|]. rewrite M7. exact EQ6.
    - specialize (HX60 eq_refl). destruct HX60 as (Cx & Tx & Nx & Bx & Mx).
      eapply hoare_mono.
      { apply (BN_from_montgomery_spec rr r6 _ s6 M nl MO6). unfold from_mont_top_pre, live. rewrite U6, F6, length_app, Nx. cbn [length].
        split; [lia|]. split; [nlia|]. split; [exact Nr1|]. split; [unfold ndiff, RMontN; lia|]. split; [unfold ndiff, RMontRR; lia|].
        split; [unfold BG_DEPTH in *; lia|]. split; [unfold BG_POOL in *; lia|]. split; [lia|]. split; [reflexivity|].
        pose proof (Bp_pos nl). assert (M * 1 <= M * Bp nl) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
      intros [] s7 _ (K7 & MO7 & (C7 & T7 & N7 & B7 & V7)). rewrite U6 in K7. rewrite Mx in V7.
      split; [|split; [exact MO7|split; [|exact T7]]].
      + eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K6|exact K7]]. intros x Hx _. cbn in Hx |- *. tauto.
      + unfold exp_post. split; [exact C7|]. split; [exact N7|]. rewrite <- (Z.mod_small _ M B7), <- EQ6.
        apply (mont_cancel (Bp nl) M); [lia|rewrite Bp_pow2; apply gcd_pow2_odd; [lia|exact Hodd]|]. rewrite V7. apply Z.mod_mod. lia. }
  intros [] s7 Hs7 (K7 & MO7 & X7 & T7).
  pose proof (keeps_used _ _ _ _ K7) as U7. pose proof (keeps_frames _ _ _ _ K7) as F7. rewrite U4 in U7. rewrite F4 in F7.
  assert (G7 : forall z, (z < NFIX + u)%nat -> z <> rr -> z <> RMontN -> z <> RMontRR -> getbn z s7 = getbn z s).
  { intros z Hz Hz0 Hz1 Hz2. rewrite (keeps_get _ _ _ _ z K7); [apply G4s; assumption|lia|].
    unfold RPool. intros [E|[E|[E|[]]]]; [lia|lia|apply Hz0; rewrite E; reflexivity]. }

  eapply hoareG_bind.
  { apply BN_MONT_CTX_free_spec. rewrite (G7 RMontNi) by (unfold RMontNi, RMontN, RMontRR, NFIX; lia). exact PrNi. }
  intros [] s8 _ ->.
  eapply hoare_mono; [apply (BN_CTX_end_spec F _ (gx_frames (st_ctx s)) u); cbn; exact F7|].
  intros [] s9 _ (Eb9 & Sc9 & Eu9 & Ef9).
  assert (E9 : forall z, getbn z s9 = getbn z (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) s7))).
  { intros z. unfold getbn at 1. rewrite Eb9. reflexivity. }
  destruct Sc9 as (S1 & S2 & S3 & S4). cbn in S1, S2, S3, S4.
  destruct K7 as [[(L7 & _) _] (Y1 & Y2 & Y3 & Y4)].
  assert (VN7 : (RMontN < length (st_bns s7))%nat) by (apply live_valid; [exact Hs7|unfold live, RMontN, NFIX; lia]).
  assert (VRR7 : (RMontRR < length (st_bns s7))%nat) by (apply live_valid; [exact Hs7|unfold live, RMontRR, NFIX; lia]).
  split; [|split; [|split; [|split]]].
  - split; [split; [split|]|].
    + rewrite Eb9. cbn. rewrite !list_set_length. lia.
    + rewrite Eu9, Ef9. split; reflexivity.
    + intros q Hq Hn. rewrite E9. destruct (Nat.eq_dec q RMontN) as [->|Hq1]; [|destruct (Nat.eq_dec q RMontRR) as [->|Hq2]].
      * rewrite getbn_setbn_same by (rewrite length_setbn; exact VN7). symmetry. exact PrN.
      * rewrite getbn_setbn_other by (unfold RMontN, RMontRR; lia). rewrite getbn_setbn_same by exact VRR7. symmetry. exact PrRR.
      * rewrite !getbn_setbn_other by (first [exact (not_eq_sym Hq1) | exact (not_eq_sym Hq2) | congruence]).
        apply G7; [exact Hq|intros ->; apply Hn; left; reflexivity|exact Hq1|exact Hq2].
    + unfold scal_same. rewrite S1, S2, S3, S4. cbn. rewrite Y3, Y4, Rb4, Rs4.
      destruct Sc02 as (_ & _ & S03a & S03b). rewrite S03a, S03b, Pri, Pn0. repeat split; reflexivity.
  - rewrite E9, !getbn_setbn_other by (unfold RMontN, RMontRR; lia). exact X7.
  - rewrite E9, !getbn_setbn_other by (unfold RMontN, RMontRR; lia). exact T7.
  - unfold mont_pristine. rewrite !E9. cbn [st_ri st_n0 set_mont].
    rewrite getbn_setbn_other by (unfold RMontN, RMontRR; lia). rewrite getbn_setbn_same by exact VRR7.
    rewrite getbn_setbn_same by (rewrite length_setbn; exact VN7).
    rewrite !getbn_setbn_other by (unfold RMontN, RMontRR, RMontNi; lia). rewrite (G7 RMontNi) by (unfold RMontNi, RMontN, RMontRR, NFIX; lia).
    rewrite S1, S2. cbn. repeat split; try reflexivity. exact PrNi.
  - rewrite E9, !getbn_setbn_other by (unfold RMontN, RMontRR, RTmod; lia).
    rewrite (G7 RTmod) by (unfold RTmod, RMontN, RMontRR, NFIX; lia). exact ET.
Qed.

Lemma modexp_pre_weaken : forall rr ra rp rm (s : ST) Dn Pn Dn' Pn', modexp_pre rr ra rp rm s Dn Pn -> (Dn' <= Dn)%nat -> (Pn' <= Pn)%nat ->
  modexp_pre rr ra rp rm s Dn' Pn'.
Proof.
  intros rr ra rp rm s Dn Pn Dn' Pn' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) H1 H2. unfold modexp_pre.
  repeat (split; [assumption|]). split; [lia|]. split; [lia|]. exact A10.
Qed.

Definition exp_pristine (s : ST) : Prop := mont_pristine s /\ recp_pristine s /\ getbn RTmod s = bn_nil 0.

Lemma BN_mod_exp_spec : forall rr ra rp rm F s,
  modexp_pre rr ra rp rm s 5 42 -> refs5 rr ra rp rm -> exp_pristine s -> bn_norm (getbn ra s) -> (length F < BG_NF)%nat ->
  hoare F s (BN_mod_exp ops rr ra rp rm) (fun _ s' =>
     keeps (gx_used (st_ctx s)) [rr] s s' /\
     exp_post (bn_val (getbn ra s)) (bn_mag (getbn rp s)) (bn_mag (getbn rm s)) (getbn rr s') /\
     (bn_top (getbn rr s') <= bn_top (getbn rm s))%nat /\ exp_pristine s').
Proof.
  intros rr ra rp rm F s Hpre Hrefs (PrM & PrR & ET) Na HF. pose proof Hpre as (Lr & La & Lp & Lm & Nr1 & Nrm & Nrp & Hdepth & Hpool & Nm & Tm & Np & Tp & Ta).
  pose proof Hrefs as (R1 & R2 & R3 & R4).
  apply hoare_wf. intros Hs. unfold BN_mod_exp. set (u := gx_used (st_ctx s)) in *.
  pose proof (live_valid rr s Hs Lr) as Vr. pose proof (live_valid ra s Hs La) as Va. pose proof (live_valid rp s Hs Lp) as Vp. pose proof (live_valid rm s Hs Lm) as Vm.
  pose proof (st_wf_okv rm s Hs Vm) as Okm. pose proof (st_wf_okv ra s Hs Va) as Oka.

  assert (PR : forall s', keeps u [rr] s s' -> mont_pristine s' /\ getbn RTmod s' = bn_nil 0 -> recp_pristine s').
  { intros s' [[_ Sl] (S1 & S2 & S3 & S4)] _. unfold recp_pristine in *. unfold live in Lr. rewrite S3, S4.
    rewrite !Sl by (first [unfold RRecpN, RRecpNr, NFIX; lia | unfold RRecpN, RRecpNr; intros [E|[]]; lia]). exact PrR. }
  assert (PM : forall s', keeps u [rr] s s' -> recp_pristine s' -> mont_pristine s' /\ getbn RTmod s' = bn_nil 0).
  { intros s' [[_ Sl] (S1 & S2 & S3 & S4)] _. unfold mont_pristine in *. unfold live in Lr. rewrite S1, S2.
    rewrite !Sl by (first [unfold RMontRR, RMontN, RMontNi, RTmod, NFIX; lia | unfold RMontRR, RMontN, RMontNi, RTmod; intros [E|[]]; lia]).
    split; [exact PrM|exact ET]. }
  apply hoare_bind_get. rewrite (is_odd_pure_spec _ Okm). destruct (Z.odd (bn_mag (getbn rm s))) eqn:Hodd.
  - apply hoare_bind_get.
    eapply hoare_bind; [apply any_consttime_spec; intros q [<-|[<-|[<-|[]]]]; assumption|]. intros ct s0 _ (-> & ->).
    destruct ((bn_top (getbn ra s) =? 1)%nat && negb (bn_neg (getbn ra s)) && negb false) eqn:Ec.
    +
      rewrite andb_true_r in Ec. apply andb_prop in Ec. destruct Ec as [Et En]. apply Nat.eqb_eq in Et. apply negb_true_iff in En.
      pose proof (mod_small_limb_modulus (getbn ra s) Oka Et) as Ea.
      assert (Hw : 0 <= nth 0 (bn_buf (getbn ra s)) 0 < BW) by (apply (limbs_nth _ 0%nat); destruct Oka as [Hl _]; exact Hl).
      eapply hoare_mono.
      { apply BN_mod_exp_mont_word_spec; try assumption. unfold modexpw_pre. repeat (split; [assumption|]). split; [lia|].
        split; [lia|]. split; [lia|]. repeat (split; [assumption|]). exact Tp. }
      intros [] s' _ (K & X & T & PM' & ET'). rewrite Ea in X. unfold bn_val. rewrite En.
      split; [exact K|]. split; [exact X|]. split; [exact T|]. split; [exact PM'|]. split; [apply (PR s' K); split; assumption|exact ET'].
    + eapply hoare_mono.
      { apply BN_mod_exp_mont_spec; try assumption. eapply modexp_pre_weaken; [exact Hpre|lia|lia]. }
      intros [] s' _ (K & X & T & PM' & ET').
      split; [exact K|]. split; [exact X|]. split; [exact T|]. split; [exact PM'|]. split; [apply (PR s' K); split; assumption|exact ET'].
  - eapply hoare_mono.
    { apply BN_mod_exp_recp_spec; try assumption. }
    intros [] s' _ (K & X & T & PR'). destruct (PM s' K PR') as [PM' ET'].
    split; [exact K|]. split; [exact X|]. split; [exact T|]. split; [exact PM'|]. split; [exact PR'|exact ET'].
Qed.

End ExpWord.
