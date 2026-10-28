(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BMState BLFrame BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DiagStmt.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma bytes_at_mid : forall m a bs i k,
  bytes_at asegs m a bs -> (i + k <= length bs)%nat ->
  bytes_at asegs m (a + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m a bs i k B Hik.
  rewrite <- (firstn_skipn i bs) in B. apply bytes_at_app in B. destruct B as [_ B].
  rewrite length_firstn, Nat.min_l in B by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

Lemma rin_ivs_none_fa : forall X a, Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) X -> ~ rin_ivs X a.
Proof.
  induction X as [|iv X IH]; intros a F; cbn; [tauto|]. inversion F as [|? ? F1 F2]; subst.
  intros [K|K]; [lia| exact (IH a F2 K)].
Qed.

Section SrcX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma rin_ivs_mono_mid : forall X A B a, rin_ivs (X ++ B) a -> rin_ivs (X ++ A ++ B) a.
  Proof.
    intros X A B a K. apply rin_ivs_app in K. apply rin_ivs_app. destruct K as [K|K]; [left; exact K|].
    right. apply rin_ivs_app. right. exact K.
  Qed.
  Lemma rin_ivs_mono_end : forall X A B a, rin_ivs (X ++ A) a -> rin_ivs (X ++ A ++ B) a.
  Proof.
    intros X A B a K. apply rin_ivs_app in K. apply rin_ivs_app. destruct K as [K|K]; [left; exact K|].
    right. apply rin_ivs_app. left. exact K.
  Qed.

  Lemma srcx_keep_now : forall LBk LF spz X m p n (s : as_St H) (LB : list block),
    srcx_keep H LBk LF spz X m p n -> ACONST m -> mem_inv asegs m ->
    as_RHEAP H s LB m -> (forall b, In b LBk -> In b LB) ->
    exists bs, length bs = Z.to_nat n /\ bytes_at asegs m p bs /\ accessible m p n /\ shvis m p (p + n).
  Proof.
    intros LBk LF spz X m p n s LB (bs & L & K) AC MI RH INC. exists bs. split; [exact L|].
    apply (K m [] s LB); [exact AC | exact MI | apply Forall_nil | apply xpres_refl | exact RH | exact INC].
  Qed.

  Lemma srcx_keep_fwd : forall LBk LF spz X XS0 m m1 p n,
    srcx_keep H LBk LF spz X m p n -> Forall (fs_scratch H LF) XS0 -> xpres H LBk spz (X ++ XS0) m m1 ->
    srcx_keep H LBk LF spz X m1 p n.
  Proof.
    intros LBk LF spz X XS0 m m1 p n (bs & L & K) FX0 XP0. exists bs. split; [exact L|].
    intros m' XS s' LB' AC MI FX XP RH INC. apply (K m' (XS0 ++ XS) s' LB'); [exact AC | exact MI | apply Forall_app; split; assumption | | exact RH | exact INC].
    eapply xpres_trans.
    - eapply xpres_weaken; [exact XP0 | apply Z.le_refl | intros b Hb; exact Hb | intros a Ha; apply rin_ivs_mono_end; exact Ha].
    - eapply xpres_weaken; [exact XP | apply Z.le_refl | intros b Hb; exact Hb | intros a Ha; apply rin_ivs_mono_mid; exact Ha].
  Qed.

  Lemma srcx_keep_fwd0 : forall LBk LF spz X m m1 p n,
    srcx_keep H LBk LF spz X m p n -> xpres H LBk spz X m m1 -> srcx_keep H LBk LF spz X m1 p n.
  Proof.
    intros LBk LF spz X m m1 p n K XP. eapply (srcx_keep_fwd LBk LF spz X [] m m1 p n K); [apply Forall_nil|].
    rewrite app_nil_r. exact XP.
  Qed.

  Lemma srcx_keep_sp : forall LBk LF spz spz' X m p n,
    srcx_keep H LBk LF spz X m p n -> spz' <= spz -> srcx_keep H LBk LF spz' X m p n.
  Proof.
    intros LBk LF spz spz' X m p n (bs & L & K) LE. exists bs. split; [exact L|].
    intros m' XS s' LB' AC MI FX XP RH INC. apply (K m' XS s' LB'); [exact AC | exact MI | exact FX | | exact RH | exact INC].
    eapply xpres_weaken; [exact XP | exact LE | intros b Hb; exact Hb | intros a Ha; exact Ha].
  Qed.

  Lemma srcx_keep_sub : forall LBk LF spz X m p n i k,
    srcx_keep H LBk LF spz X m p n -> 0 <= i -> 0 <= k -> i + k <= n -> srcx_keep H LBk LF spz X m (p + i) k.
  Proof.
    intros LBk LF spz X m p n i k (bs & L & K) Hi Hk Hik.
    exists (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)). split.
    { rewrite length_firstn, length_skipn, L. lia. }
    intros m' XS s' LB' AC MI FX XP RH INC. destruct (K m' XS s' LB' AC MI FX XP RH INC) as (B & A & V).
    pose proof (bytes_at_bound _ _ _ _ B) as [P0 _].
    split; [|split].
    - replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia. apply bytes_at_mid; [exact B | rewrite L; lia].
    - eapply accessible_sub; [exact A | lia | lia | lia].
    - destruct (Z.eq_dec n 0) as [N0|N0].
      + assert (i = 0) by lia. assert (k = 0) by lia. subst i k. rewrite !Z.add_0_r in *. rewrite N0, Z.add_0_r in V. exact V.
      + eapply shvis_sub; [exact V | lia | lia | lia | lia | lia].
  Qed.

  Lemma srcx_keep_blk : forall LBk LF spz X m p n pid A k bs (m0 : mem),
    In (pid, A, k) LBk -> A <= p -> p + n <= A + k -> 0 <= n ->
    length bs = Z.to_nat n -> bytes_at asegs m p bs -> accessible m p n ->
    as_RFS H LF m0 ->
    Forall (fun iv : Z * Z => A + k <= fst iv \/ snd iv <= A) X ->
    Forall (fun iv : Z * Z => sh A + nsh k <= fst iv \/ snd iv <= sh A) X ->
    srcx_keep H LBk LF spz X m p n.
  Proof.
    intros LBk LF spz X m p n pid A k bs m0 Hin HA Hpn Hn L BA ACC RFS0 FXA FXS.
    exists bs. split; [exact L|]. intros m' XS s' LB' AC MI FX XP RH INC.
    pose proof (INC _ Hin) as INb.
    pose proof (ah_blocks H HH _ _ _ _ RH INb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    pose proof (fsobj_block H HH s' LB' m' LF pid A k RH INb) as FO.
    assert (SX : Forall (fun iv : Z * Z => A + k <= fst iv \/ snd iv <= A) XS).
    { eapply Forall_impl; [| exact FX]. intros iv Hiv.
      exact (fsobj_scratch H HH LF A k m0 iv RFS0 FO ltac:(lia) Rn ltac:(unfold AAPP_HI; lia) RAPP Hiv). }
    assert (SXs : Forall (fun iv : Z * Z => sh A + nsh k <= fst iv \/ snd iv <= sh A) XS).
    { eapply Forall_impl; [| exact FX]. intros iv Hiv.
      exact (fsobj_scratch_sh H HH LF A k m0 iv RFS0 FO ltac:(lia) Rn ltac:(unfold AAPP_HI; lia) Hiv). }
    assert (A8 : A mod 8 = 0) by (clear - R16; Z.div_mod_to_equations; lia).
    split; [| split].
    - eapply xpres_bytes_at; [exact XP | exact BA |]. rewrite L, Z2Nat.id by exact Hn. split.
      + eapply (aclient_range_block H); [exact Hin | exact HA | exact Hpn].
      + apply Forall_app. split; (eapply Forall_impl; [| first [exact FXA | exact SX]]); intros iv Hiv; cbn beta in *; lia.
    - destruct ACC as (P0 & P1 & PX). split; [exact P0|]. split; [exact P1|]. intros x Hx.
      destruct (PX x Hx) as (v & V1 & V2 & V3). exists v. split; [exact V1|]. split; [| exact V3].
      assert (SR : sh A <= sh x < sh A + nsh k) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
      assert (SB : 0 <= sh x < 2 ^ 64) by (unfold sh; rewrite ASHADOW_BASE_val; unfold AAPP_HI in *; Z.div_mod_to_equations; lia).
      assert (XC : xclient H LBk spz (X ++ XS) (sh x)).
      { split.
        - right; right; right; left. exists (pid, A, k). split; [exact Hin | cbn [blk_addr blk_size fst snd]; exact SR].
        - apply rin_ivs_none_fa. apply Forall_app. split; (eapply Forall_impl; [| first [exact FXS | exact SXs]]); intros iv Hiv; cbn beta in *; lia. }
      unfold mrd in *. rewrite (proj1 (XP (sh x) SB XC)). exact V2.
    - pose proof (ah_blk_shvis H HH s' LB' m' pid A k RH INb) as SV.
      destruct (Z.eq_dec n 0) as [N0|N0].
      + eapply shvis_sub; [exact SV | lia | exact HA | lia | lia | lia].
      + eapply shvis_sub; [exact SV | lia | exact HA | exact Hpn | lia | lia].
  Qed.

  Lemma srcx_apart : forall LBk LF spz X m p n m1 XS a (s1 : as_St H) (LB1 : list block) (wlo whi : Z),
    srcx_keep H LBk LF spz X m p n ->
    ACONST m1 -> mem_inv asegs m1 -> Forall (fs_scratch H LF) XS -> xpres H LBk spz (X ++ XS) m m1 ->
    as_RHEAP H s1 LB1 m1 -> (forall b, In b LBk -> In b LB1) ->
    wlo <= a < whi -> aclient_write_ok H LB1 (wlo, whi) ->
    0 <= a < 2 ^ 64 -> wview asegs m1 (wa a) <> None -> ~ aconst_addr a ->
    (aclient_addr H LBk spz a -> rin_ivs (X ++ XS) a) ->
    ~ (p <= a < p + n).
  Proof.
    intros LBk LF spz X m p n m1 XS a s1 LB1 wlo whi (bs & L & K) AC MI FX XP RH1 INC1 HW CW Ha WV NC CL IN.
    destruct (K m1 XS s1 LB1 AC MI FX XP RH1 INC1) as (B1 & _ & _).
    destruct B1 as (P0 & P1 & RD1).
    assert (Hi : (Z.to_nat (a - p) < length bs)%nat) by (rewrite L; lia).
    pose proof (RD1 _ Hi) as R1. replace (p + Z.of_nat (Z.to_nat (a - p))) with a in R1 by lia.
    destruct (nth_error bs (Z.to_nat (a - p))) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
    set (b' := Z_to_bv 8 (bv_unsigned b + 1)).
    assert (NE : b' <> b).
    { intros E. pose proof (f_equal bv_unsigned E) as E2. subst b'. rewrite Z_to_bv_unsigned in E2.
      rewrite bv_wrap8_mod in E2.
      pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with (2 ^ 8) in R.
      destruct (Z.eq_dec (bv_unsigned b) 255) as [E255|E255].
      - rewrite E255 in E2. cbn in E2. lia.
      - rewrite Z.mod_small in E2 by lia. lia. }
    set (m2 := fun x : word => if (bv_unsigned x =? a)%Z then Some b' else m1 x).
    assert (M2a : m2 (wa a) = Some b') by (subst m2; cbn beta; rewrite wa_unsigned, Z.eqb_refl by lia; reflexivity).
    assert (M2o : forall x : word, bv_unsigned x <> a -> m2 x = m1 x).
    { intros x Hx. subst m2; cbn beta. destruct (Z.eqb_spec (bv_unsigned x) a) as [E|E]; [lia | reflexivity]. }
    assert (M2z : forall z, 0 <= z < 2 ^ 64 -> z <> a -> m2 (wa z) = m1 (wa z)).
    { intros z Hz Hza. apply M2o. rewrite wa_unsigned by lia. exact Hza. }
    assert (WV2 : forall x : word, wview asegs m1 x <> None -> wview asegs m2 x <> None).
    { intros x Wx. unfold wview in *. destruct (Z.eqb_spec (bv_unsigned x) a) as [E|E].
      - replace x with (wa a) by (apply bv_eq; rewrite wa_unsigned by lia; symmetry; exact E). rewrite M2a. discriminate.
      - rewrite (M2o x E). exact Wx. }
    assert (RD2 : forall x : word, bv_unsigned x <> a -> mrd asegs m2 x = mrd asegs m1 x).
    { intros x Hx. unfold mrd. rewrite (M2o x Hx). reflexivity. }
    assert (AC2 : ACONST m2).
    { eapply ACONST_ext; [exact AC | | |].
      - intros z Hz Hc. apply M2z; [exact Hz|]. intros ->. exact (NC Hc).
      - intros z Hz Wz. apply WV2. exact Wz.
      - intros z Hz. destruct (Z.eq_dec z a) as [->|Hza].
        + exists b'. unfold mrd. rewrite M2a. reflexivity.
        + assert (Hz' : 0 <= z < 2 ^ 64) by (unfold sh, AIMG_LO, AIMG_TOP in Hz; rewrite ASHADOW_BASE_val in Hz; lia).
          rewrite RD2 by (rewrite wa_unsigned by lia; exact Hza).
          destruct AC as (_ & _ & (_ & _ & SS)). exact (proj2 (SS z Hz)). }
    assert (MI2 : mem_inv asegs m2).
    { intros x bx Hx. destruct (Z.eqb_spec (bv_unsigned x) a) as [E|E].
      - assert (Ex : x = wa a) by (apply bv_eq; rewrite wa_unsigned by lia; exact E). rewrite Ex.
        destruct (m1 (wa a)) as [b1|] eqn:M1a.
        + exact (MI _ _ M1a).
        + apply (wview_not_ro asegs m1); [exact WV | exact M1a].
      - rewrite (M2o x E) in Hx. exact (MI _ _ Hx). }
    assert (XP2 : xpres H LBk spz (X ++ XS) m m2).
    { intros z Hz [Cz Xz]. destruct (XP z Hz (conj Cz Xz)) as [E1 W1].
      assert (Hza : z <> a) by (intros ->; exact (Xz (CL Cz))).
      split; [rewrite (M2z z Hz Hza); exact E1 | intros W0; apply WV2; apply W1; exact W0]. }
    assert (RH2 : as_RHEAP H s1 LB1 m2).
    { eapply (ah_RHEAP_frame H HH s1 LB1 m1 m2 [(wlo, whi)]); [exact RH1 | | intros x Wx; exact (WV2 x Wx) | apply Forall_cons; [exact CW | apply Forall_nil]].
      intros x Ox. cbn [outside] in Ox. apply M2o. intros E. apply (proj1 Ox). rewrite E. exact HW. }
    destruct (K m2 XS s1 LB1 AC2 MI2 FX XP2 RH2 INC1) as ((_ & _ & RD3) & _ & _).
    pose proof (RD3 _ Hi) as R3. replace (p + Z.of_nat (Z.to_nat (a - p))) with a in R3 by lia.
    rewrite NB in R3. unfold mrd in R3. rewrite M2a in R3. apply NE. congruence.
  Qed.
End SrcX.
