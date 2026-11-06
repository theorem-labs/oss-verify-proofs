(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun As0_code_93368_94368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DDmul L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ARedP L5ARed L5AMul10K L5AMulMP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AMULMK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AMULMP. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?G |- ?G => exact H end.
Local Ltac sc := first [ asm | rk | gmem | arith_goal; first [asm | blia] ].
Local Notation U := L5AMULK.U.
Local Notation UR := L5AMULK.UR.
Local Notation U_to := L5AMULK.U_to.
Local Notation mfacts := L5AMULK.mfacts.

Definition HEAD : Z := 0x93e28.
Definition RZRET : Z := 0x93dc4.
Definition REDRET : Z := 0x93edc.
Definition RET : Z := 0x93f00.
Definition HV (y : Z) : Z := y / L5DDM.K.
Definition LV (y : Z) : Z := y mod L5DDM.K.
Lemma HV_rng y : 0 <= y < 2 ^ 64 -> 0 <= HV y <= 4294967295. Proof. intros Hy. pose proof (L5DDM.hv_rng y Hy) as H. unfold HV, L5DDM.K in *. lia. Qed.
Lemma LV_rng y : 0 <= LV y <= 4294967295. Proof. pose proof (L5DDM.lv_rng y) as H. unfold LV, L5DDM.K in *. lia. Qed.
Lemma y_halves y : 0 <= y -> HV y * L5DDM.K + LV y = y. Proof. intros. unfold HV, LV. symmetry. apply L5DDM.y_split. lia. Qed.

Definition KSL : list nat := [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition at_mhead (R : bvmap 5 word) (sp o d y : Z) (len J : nat) (c X : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 5) = Z_to_bv 64 c /\ getr R (reg 8) = Z_to_bv 64 o /\
  getr R (reg 10) = Z_to_bv 64 (d + 8 * Z.of_nat J - 8) /\ getr R (reg 11) = Z_to_bv 64 d /\ getr R (reg 12) = Z_to_bv 64 (HV y) /\
  getr R (reg 13) = Z_to_bv 64 (d + 8 * Z.of_nat J) /\ getr R (reg 14) = Z_to_bv 64 4294967295 /\ getr R (reg 15) = Z_to_bv 64 (LV y) /\
  getr R (reg 16) = Z_to_bv 64 (Z.of_nat J + d / 8 + 2147450880 - 1) /\
  getr R (reg 17) = Z_to_bv 64 (Z.of_nat len - Z.of_nat J + 1) /\ getr R (reg 18) = Z_to_bv 64 2147450880 /\ getr R (reg 19) = Z_to_bv 64 (Z.of_nat len) /\
  getr R (reg 20) = Z_to_bv 64 X /\ getr R (reg 21) = Z_to_bv 64 (o / 8 + 2147450880).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mloop (k : nat) : forall fx R M (sp o d cap y : Z) (len J : nat) (ws : list Z),
  mfacts M sp o d cap -> (1 <= J)%nat -> (J <= len)%nat -> k = (len - J + 1)%nat -> Z.of_nat len + 1 <= cap ->
  length ws = len -> words_ok ws -> 0 <= y < 2 ^ 64 ->
  (forall i, (i < J - 1)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (nth_w (mulw_words ws y) i)) ->
  (forall i, (J - 1 <= i <= len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (nth_w (ws ++ [0]) i)) ->
  at_mhead R sp o d y len J (mulw_c ws y 0 (J - 1)) (nth_w ws (J - 1)) ->
  exists fx' R' M',
    msteps RSEGS (st fx R HEAD M) (st fx' R' L5ARED.REDUCE M')
    /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 1) = Z_to_bv 64 REDRET
    /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) (nth_w (mulw_words ws y) i))
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * (Z.of_nat len + 1)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros fx R M sp o d cap y len J ws MFM J1 JL Hk CAP WL WO Hy LOW HIGH AT. { exfalso. clear - Hk J1 JL. lia. }
  pose proof MFM as [[SPR A16] W64 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ].
  destruct AT as (A2 & A5 & A8 & A10 & A11 & A12 & A13 & A14 & A15 & A16r & A17 & A18 & A19 & A20 & A21).
  set (X := nth_w ws (J - 1)) in *. set (c := mulw_c ws y 0 (J - 1)) in *.
  assert (RX : 0 <= X < 2 ^ 64) by (subst X; apply words_ok_nth; exact WO).
  assert (Rc : 0 <= c < 2 ^ 64) by (subst c; apply mulw_c_bound; [exact WO | exact Hy | clear; lia]).
  pose proof (HV_rng y Hy) as Hhv. pose proof (LV_rng y) as Hlv.
  assert (WO0 : words_ok (ws ++ [0])). { apply words_ok_app. exact WO. constructor. clear; lia. constructor. }
  set (X' := nth_w (ws ++ [0]) J).
  assert (RX' : 0 <= X' < 2 ^ 64) by (subst X'; apply words_ok_nth; exact WO0).
  assert (CJ : L5.u64_at RSEGS M (d + 8 * Z.of_nat J) X'). { subst X'. apply HIGH. clear - JL; lia. }
  assert (STEP : X * (HV y * L5DDM.K + LV y) + c = nth_w ws (J - 1) * y + mulw_c ws y 0 (J - 1)). { rewrite y_halves by (clear - Hy; lia). reflexivity. }
  assert (STW : (X * (HV y * L5DDM.K + LV y) + c) mod 2 ^ 64 = nth_w (mulw_words ws y) (J - 1)).
  { rewrite STEP. unfold mulw_words. rewrite mulw_loop_nth by (rewrite WL; clear - J1 JL; lia). reflexivity. }
  assert (STC : (X * (HV y * L5DDM.K + LV y) + c) / 2 ^ 64 = mulw_c ws y 0 J).
  { rewrite STEP. rewrite <- (mulw_c_S ws y 0 (J - 1)) by (rewrite WL; clear - J1 JL; lia). f_equal. clear - J1; lia. }
  assert (HhvK : 0 <= HV y < L5DDM.K) by (unfold L5DDM.K; clear - Hhv; lia). assert (HlvK : 0 <= LV y < L5DDM.K) by (unfold L5DDM.K; clear - Hlv; lia).
  (* [comment removed for export] *)
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - FRO; lia). assert (FRDp : sp - 64 + 64 <= d \/ d + 8 * cap <= sp - 64) by (clear - FRD; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia).
  assert (HVJ : 1 <= Z.of_nat J <= 134217728) by (clear - J1 JL CAP CAPR; lia). assert (HVCJ : 1 <= cap - Z.of_nat J <= 134217728) by (clear - JL CAP CAPR J1; lia).
  assert (HVL : 1 <= Z.of_nat len <= 134217728) by (clear - J1 JL CAP CAPR; lia).
  assert (HVc : 0 <= c <= 18446744073709551615) by (clear - Rc; lia). assert (HVX : 0 <= X <= 18446744073709551615) by (clear - RX; lia).
  destruct k as [|k'].
  - (* [comment removed for export] *)
    assert (EJ : J = len) by (clear - Hk J1 JL; lia). subst J.
    assert (HV52 : 1 <= Z.of_nat len - Z.of_nat len + 1 <= 1) by (clear; lia). assert (HV3440 : 0 <= Z.of_nat len - Z.of_nat len <= 0) by (clear; lia).
    assert (HVCL : 1 <= cap - Z.of_nat len <= 134217728) by exact HVCJ.
    pose proof (vmmL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 36%nat => d | 37%nat => cap | 38%nat => X | 39%nat => X'
                  | 40%nat => Z.of_nat len | 41%nat => c | 43%nat => U R 1 | 52%nat => Z.of_nat len - Z.of_nat len + 1 | 54%nat => HV y | 55%nat => LV y | 56%nat => U R 9 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & lFR & lFZ & (lMS & lKS & lR1 & lR5 & lR6 & lR7 & lR9 & lR10 & lR11 & lR13 & lR16 & lR17 & lR20 & lR28 & lR29 & lR30 & lR31 & lCTOP & lCLIMB)).
    match type of lCLIMB with L5.u64_at _ _ _ ?e => assert (LOE : e = (X * (HV y * L5DDM.K + LV y) + c) mod 2 ^ 64) by exact (L5DDM.lo_eq X (HV y) (LV y) c RX HhvK HlvK); rewrite LOE in lCLIMB end.
    match type of lCTOP with L5.u64_at _ _ _ ?e => assert (HIE : e = (X * (HV y * L5DDM.K + LV y) + c) / 2 ^ 64) by exact (L5DDM.hi_eq X (HV y) (LV y) c RX HhvK HlvK Rc); rewrite HIE in lCTOP end.
    rewrite STW in lCLIMB. rewrite STC in lCTOP.
    exists fx1, R1, M1. split. exact lMS.
    split. { intros x Hx. apply lKS. revert Hx; apply (L5K.incl_b _ KS_vmmL); vm_compute; reflexivity. }
    split. exact lR10. split. exact lR1.
    split. { intros i Hi. destruct (Nat.eq_dec i len) as [->|NE].
      { unfold mulw_words. rewrite <- WL at 2. rewrite mulw_loop_last. rewrite WL. replace (d + 8 * Z.of_nat len) with (8 * Z.of_nat len + d) by (clear; lia). exact lCTOP. }
      destruct (Nat.eq_dec i (len - 1)) as [->|NE2].
      { replace (d + 8 * Z.of_nat (len - 1)) with (d + 8 * Z.of_nat len - 8) by (clear - J1; lia). exact lCLIMB. }
      eapply L5C.u64_at_agree. 4:{ apply LOW. clear - Hi NE NE2; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia.
      intros j Hj. apply lFZ. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi NE NE2 J1; lia. }
    split. { intros i Hi Hn. apply lFZ. exact Hi. clear - Hn J1; lia. } exact MG1.
  - (* [comment removed for export] *)
    assert (JL2 : (J < len)%nat) by (clear - Hk J1 JL; lia).
    assert (HV52 : 2 <= Z.of_nat len - Z.of_nat J + 1 <= 134217728) by (clear - JL2 HVL J1; lia).
    pose proof (vmmI_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 36%nat => d | 37%nat => cap | 38%nat => X | 39%nat => X'
                  | 40%nat => Z.of_nat J | 41%nat => c | 43%nat => U R 1 | 52%nat => Z.of_nat len - Z.of_nat J + 1 | 54%nat => HV y | 55%nat => LV y | 56%nat => U R 9 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & iFR & iFZ & (iMS & iKS & iR5 & iR6 & iR7 & iR9 & iR10 & iR13 & iR16 & iR17 & iR20 & iR28 & iR29 & iR30 & iR31 & iCLIMB)).
    match type of iCLIMB with L5.u64_at _ _ _ ?e => assert (LOE : e = (X * (HV y * L5DDM.K + LV y) + c) mod 2 ^ 64) by exact (L5DDM.lo_eq X (HV y) (LV y) c RX HhvK HlvK); rewrite LOE in iCLIMB end.
    match type of iR5 with _ = ?e => assert (HIE : e = (X * (HV y * L5DDM.K + LV y) + c) / 2 ^ 64) by exact (L5DDM.hi_eq X (HV y) (LV y) c RX HhvK HlvK Rc); rewrite HIE in iR5 end.
    rewrite STW in iCLIMB. rewrite STC in iR5.
    assert (MF1 : mfacts M1 sp o d cap). { eapply L5AMULK.mfacts_keep. exact MFM. exact MG1. intros i Hi Hd _ _. apply iFZ. exact Hi. clear - Hd J1 JL CAP; lia. }
    assert (XN : X' = nth_w ws J). { subst X'. unfold nth_w. rewrite app_nth1 by (rewrite WL; exact JL2). reflexivity. }
    destruct (IH fx1 R1 M1 sp o d cap y len (Datatypes.S J) ws MF1 ltac:(clear; lia) ltac:(clear - JL2; lia) ltac:(clear - Hk JL2 J1; lia) CAP WL WO Hy) as (fx' & R' & M' & MS & K & R10' & R1' & LIMBS & FR' & GR').
    + intros i Hi. destruct (Nat.eq_dec i (J - 1)) as [->|NE].
      { replace (d + 8 * Z.of_nat (J - 1)) with (d + 8 * Z.of_nat J - 8) by (clear - J1; lia). exact iCLIMB. }
      eapply L5C.u64_at_agree. 4:{ apply LOW. clear - Hi NE; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi JL; lia.
      intros j Hj. apply iFZ. clear - Hj DR CAPR CAP Hi JL; lia. clear - Hj Hi NE J1; lia.
    + intros i Hi. eapply L5C.u64_at_agree. 4:{ apply HIGH. clear - Hi; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia.
      intros j Hj. apply iFZ. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi J1; lia.
    + unfold at_mhead. replace (Datatypes.S J - 1)%nat with J by (clear; lia). rewrite <- XN.
      assert (KK : forall x, In x [2; 8; 11; 12; 14; 15; 18; 19; 21]%nat -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. apply iKS. revert Hx; apply (L5K.incl_b _ KS_vmmI); vm_compute; reflexivity. }
      repeat split.
      * rewrite (KK 2%nat) by inl; exact A2. * rewrite <- iR5. symmetry. apply Z_to_bv_bv_unsigned. * rewrite (KK 8%nat) by inl; exact A8.
      * rewrite iR10. f_equal. clear; lia. * rewrite (KK 11%nat) by inl; exact A11. * rewrite (KK 12%nat) by inl; exact A12.
      * rewrite iR13. f_equal. clear; lia. * rewrite (KK 14%nat) by inl; exact A14. * rewrite (KK 15%nat) by inl; exact A15.
      * rewrite iR16. f_equal. clear; lia. * rewrite iR17. f_equal. clear; lia. * rewrite (KK 18%nat) by inl; exact A18. * rewrite (KK 19%nat) by inl; exact A19.
      * exact iR20. * rewrite (KK 21%nat) by inl; exact A21.
    + exists fx', R', M'. split. { eapply msteps_trans. exact iMS. exact MS. }
      split. { intros x Hx. rewrite (K x Hx). apply iKS. revert Hx; apply (L5K.incl_b _ KS_vmmI); vm_compute; reflexivity. }
      split. exact R10'. split. exact R1'. split. exact LIMBS.
      split. { intros i Hi Hn. rewrite (FR' i Hi Hn). apply iFZ. exact Hi. clear - Hn J1 JL; lia. }
      eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSC : list nat := [3; 4; 22; 23; 24; 25; 26; 27]%nat.
Definition KSP : list nat := [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition st_after (sto : L5.bstore) (wl : list Z) : L5.bstore :=
  match sto with
  | L5.BInl _ _ => L5.BInl (nth_w wl 0) (nth_w wl 1)
  | L5.BDyn c q => L5.BDyn c q
  end.

Theorem mulm_core fx R M (sp o r y fb : Z) (len : nat) (sto : L5.bstore) (wsR : list Z) (v8 v9 v18 v19 v20 v21 : Z) :
  let b := L5.BO fb (Datatypes.S len) sto in let d := L5.bo_data o b in let cap := L5.bo_cap b in let ws := firstn len wsR in
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 y -> 0 <= y < 2 ^ 64 -> getr R (reg 18) = Z_to_bv 64 SB ->
  getr R (reg 19) = Z_to_bv 64 (Z.of_nat len) -> (1 <= len)%nat -> getr R (reg 20) = Z_to_bv 64 (nth 0 wsR 0) ->
  getr R (reg 21) = Z_to_bv 64 (o / 8 + SB) ->
  L5.u64_at RSEGS M (sp - 8) r -> L5.ra_ok r ->
  L5.u64_at RSEGS M (sp - 16) v8 -> L5.u64_at RSEGS M (sp - 24) v9 -> L5.u64_at RSEGS M (sp - 32) v18 -> L5.u64_at RSEGS M (sp - 40) v19 ->
  L5.u64_at RSEGS M (sp - 48) v20 -> L5.u64_at RSEGS M (sp - 56) v21 ->
  0 <= v8 < 2 ^ 64 -> 0 <= v9 < 2 ^ 64 -> 0 <= v18 < 2 ^ 64 -> 0 <= v19 < 2 ^ 64 -> 0 <= v20 < 2 ^ 64 -> 0 <= v21 < 2 ^ 64 ->
  mfacts M sp o d cap -> L5.writable RSEGS M (sp - 80) 16 ->
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b wsR -> nth len wsR 0 = 0 -> Z.of_nat len + 1 <= cap ->
  match sto with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end ->
  exists fx' R' M',
    msteps RSEGS (st fx R RZRET M) (st fx' R' r M')
    /\ (forall x, In x KSC -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 o
    /\ getr R' (reg 8) = Z_to_bv 64 v8 /\ getr R' (reg 9) = Z_to_bv 64 v9 /\ getr R' (reg 18) = Z_to_bv 64 v18 /\ getr R' (reg 19) = Z_to_bv 64 v19
    /\ getr R' (reg 20) = Z_to_bv 64 v20 /\ getr R' (reg 21) = Z_to_bv 64 v21
    /\ (let wl := mulw_words ws y in let n' := L5W.rlen wl in
        L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land fb 253 else fb) n' (st_after sto wl)) /\ L5.limbs_at RSEGS M' d wl)
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (o <= a < o + 16) -> ~ (sp - 80 <= a < sp - 64) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.
Proof.
  cbn zeta. intros G2 G8 G9 Hy G18 G19 Lpos G20 G21 C8 RA C16 C24 C32 C40 C48 C56 R8 R9 R18 R19 R20 R21 MFM W80 OB OL TOP0 CAP ODYN.
  pose proof MFM as [[SPR A16] W64 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ].
  unfold L5.bo_data, L5.bo_cap in *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  set (d := match sto with L5.BInl _ _ => o + 16 | L5.BDyn _ q => q end) in *.
  set (cap := match sto with L5.BInl _ _ => 2 | L5.BDyn c _ => c end) in *.
  pose proof OB as (O0 & Ffb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Ffb, O8, OST. destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  set (ws := firstn len wsR) in *.
  assert (WOR : words_ok wsR) by exact Rws.
  assert (WL : length ws = len). { subst ws. rewrite length_firstn, Lws. clear; lia. }
  assert (WO : words_ok ws). { subst ws. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) WOR w). eapply L5AMULK.in_firstn. exact Hw. }
  assert (WS : L5.limbs_at RSEGS M d wsR).
  { subst d. destruct sto as [w0 w1|c q]. 2: exact LAT. destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). rewrite LAT. intros i Hi. rewrite length_firstn in Hi. cbn [length Nat.min] in Hi.
    destruct i as [|[|i]]. { cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by (clear; lia). exact O16. }
    { destruct len as [|ly]. exfalso; clear - Hi; lia. cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by (clear; lia). exact O24. }
    exfalso. destruct len as [|[|ly]]; cbn in Hi; clear - Hi Hl2; lia. }
  assert (NTH : forall i, (i <= len)%nat -> nth i wsR 0 = nth_w (ws ++ [0]) i).
  { intros i Hi. unfold nth_w. destruct (Nat.eq_dec i len) as [->|NE].
    - rewrite app_nth2 by (rewrite WL; clear; lia). rewrite WL, Nat.sub_diag. cbn [nth]. exact TOP0.
    - rewrite app_nth1 by (rewrite WL; clear - Hi NE; lia). subst ws. rewrite <- (firstn_skipn len wsR) at 1. rewrite app_nth1. reflexivity. rewrite length_firstn, Lws. clear - Hi NE; lia. }
  assert (LIMBS : forall i, (i <= len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (nth_w (ws ++ [0]) i)). { intros i Hi. rewrite <- NTH by exact Hi. apply WS. rewrite Lws. clear - Hi; lia. }
  assert (EX0 : nth 0 wsR 0 = nth_w ws 0). { rewrite (NTH 0%nat ltac:(clear; lia)). unfold nth_w. rewrite app_nth1 by (rewrite WL; exact Lpos). reflexivity. }
  assert (RX0 : 0 <= nth 0 wsR 0 < 2 ^ 64). { rewrite EX0. apply words_ok_nth. exact WO. }
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - FRO; lia). assert (FRDp : sp - 64 + 64 <= d \/ d + 8 * cap <= sp - 64) by (clear - FRD; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia). assert (HVF : 0 <= fb <= 255) by (clear - Ffb; lia).
  assert (HVL1 : 1 <= Z.of_nat len <= 134217728) by (clear - Lpos CAP CAPR; lia). assert (HVCL : 1 <= cap - Z.of_nat len <= 134217728) by (clear - CAP CAPR Lpos; lia).
  assert (HVY : 0 <= y <= 18446744073709551615) by (clear - Hy; lia).
  set (x0 := nth 0 wsR 0) in *.
  set (wl := mulw_words ws y).
  assert (WLL : length wl = Datatypes.S len) by (subst wl; rewrite mulw_words_length, WL; reflexivity).
  assert (WLO : words_ok wl) by (subst wl; apply mulw_words_ok; [exact WO | exact Hy]).
  (* [comment removed for export] *)
  assert (PART1 : exists fx1 R1 M1, msteps RSEGS (st fx R RZRET M) (st fx1 R1 L5ARED.REDUCE M1)
      /\ (forall x, In x KSP -> getr R1 (reg x) = getr R (reg x)) /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 1) = Z_to_bv 64 REDRET
      /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat i) (nth_w wl i))
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ mem_grows M M1).
  { assert (RUN : exists fx1 R1 M1, mem_grows M M1 /\ (forall a : word, M1 a = M a)
               /\ msteps RSEGS (st fx R 0x93dc4 M) (st fx1 R1 0x93e28 M1) /\ (forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
               /\ getr R1 (reg 5) = Z_to_bv 64 0 /\ getr R1 (reg 10) = Z_to_bv 64 d /\ getr R1 (reg 11) = Z_to_bv 64 d /\ getr R1 (reg 12) = Z_to_bv 64 (HV y) /\ getr R1 (reg 13) = Z_to_bv 64 (d + 8)
               /\ getr R1 (reg 14) = Z_to_bv 64 4294967295 /\ getr R1 (reg 15) = Z_to_bv 64 (LV y) /\ getr R1 (reg 16) = Z_to_bv 64 (d / 8 + 2147450880) /\ getr R1 (reg 17) = Z_to_bv 64 (Z.of_nat len)).
    { assert (LVE : (4294967296 * y) mod 2 ^ 64 / 4294967296 = LV y) by (exact (L5DDM.lv_eq y Hy)).
      subst d cap. destruct sto as [w0 w1|c q].
      + destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). assert (HVL2 : 1 <= Z.of_nat len <= 2) by (clear - Lpos Hl2; lia).
        pose proof (vmmBi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 42%nat => x0 | 43%nat => U R 1 | 51%nat => U R 10 | 53%nat => y | _ => 0 end)) as P. cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx1 & R1 & M1 & MG1 & bFR & bFZ & (bMS & bKS & bR5 & bR10 & bR11 & bR12 & bR13 & bR14 & bR15 & bR16 & bR17)).
        exists fx1, R1, M1. split. exact MG1. split. exact bFR. split. exact bMS.
        split. { intros x Hx. apply bKS. revert Hx; apply (L5K.incl_b _ KS_vmmBi); vm_compute; reflexivity. }
        rewrite LVE in bR15.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        repeat split; try assumption; try (rewrite <- bR15; symmetry; apply Z_to_bv_bv_unsigned); (first [rewrite bR10 | rewrite bR11 | rewrite bR12 | rewrite bR13 | rewrite bR16 | rewrite bR17]; f_equal; unfold HV, L5DDM.K; clear - O8a; lia).
      + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
        assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia). assert (HVC : 0 <= c < 2 ^ 64) by (clear - Hcap; lia).
        pose proof (vmmBd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => c | 42%nat => x0 | 43%nat => U R 1 | 51%nat => U R 10 | 53%nat => y | _ => 0 end)) as P. cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx1 & R1 & M1 & MG1 & bFR & bFZ & (bMS & bKS & bR5 & bR10 & bR11 & bR12 & bR13 & bR14 & bR15 & bR16 & bR17)).
        exists fx1, R1, M1. split. exact MG1. split. exact bFR. split. exact bMS.
        split. { intros x Hx. apply bKS. revert Hx; apply (L5K.incl_b _ KS_vmmBd); vm_compute; reflexivity. }
        rewrite LVE in bR15.
        repeat split; try assumption; try (rewrite <- bR15; symmetry; apply Z_to_bv_bv_unsigned); (first [rewrite bR10 | rewrite bR11 | rewrite bR12 | rewrite bR13 | rewrite bR16 | rewrite bR17]; f_equal; unfold HV, L5DDM.K; clear - Q8; lia). }
    destruct RUN as (fx1 & R1 & M1 & MG1 & FR1 & MS1 & K1 & B5 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17).
    assert (EM1 : M1 = M). { apply functional_extensionality. exact FR1. } subst M1.
    destruct (mloop len fx1 R1 M sp o d cap y len 1 ws MFM ltac:(clear; lia) Lpos ltac:(clear - Lpos; lia) CAP WL WO Hy) as (fx2 & R2 & M2 & MS2 & K2 & R2_10 & R2_1 & LIMBS2 & FR2 & GR2).
    { intros i Hi. exfalso. clear - Hi. lia. }
    { intros i Hi. apply LIMBS. clear - Hi; lia. }
    { unfold at_mhead. replace (1 - 1)%nat with 0%nat by reflexivity. rewrite mulw_c_0. rewrite <- EX0. change (Z.of_nat 1) with 1.
      repeat split; try (first [assumption | rewrite (K1 _) by inl; assumption]).
      all: first [rewrite B10 | rewrite B13 | rewrite B16 | rewrite B17]; f_equal; clear; lia. }
    exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. exact MS2. }
    split. { intros x Hx. rewrite (K2 x). apply K1. revert Hx; apply (L5K.incl_b KSP); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSP); vm_compute; reflexivity. }
    split. exact R2_10. split. exact R2_1. split. exact LIMBS2. split. exact FR2. exact GR2. }
  destruct PART1 as (fx1 & R1 & M1 & MS1 & K1 & R1_10 & R1_1 & LIMBS1 & FR1 & GR1).

  assert (MF1 : mfacts M1 sp o d cap). { eapply L5AMULK.mfacts_keep. exact MFM. exact GR1. intros i Hi Hd _ _. apply FR1. exact Hi. clear - Hd CAP CAPR; lia. }
  pose proof MF1 as [_ W64a [IMGC1 [CSB1 CUAR1]] _ OZ1 OW1 _ DW1 DZ1].
  assert (W80a : L5.writable RSEGS M1 (sp - 64 - 16) 16). { replace (sp - 64 - 16) with (sp - 80) by (clear; lia). eapply L5.writable_grows. exact GR1. exact W80. }
  assert (HDR1 : forall a v, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR1. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb OD CAP; lia. }
  assert (FB1 : L5.u8_at RSEGS M1 o fb). { eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FR1. clear - Hj OR; lia. clear - Hj OD CAP; lia. }
  set (b1 := L5.BO fb (Datatypes.S len) (st_after sto wl)).
  assert (OB1 : L5.big_at RSEGS M1 o b1 /\ L5C.obj_limbs RSEGS M1 b1 wl).
  { subst b1 d cap. unfold L5.big_at, L5C.obj_limbs, st_after. cbn [L5.bo_fb L5.bo_len L5.bo_st]. destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). assert (EL1 : len = 1%nat) by (clear - Hl2 Lpos; lia). split.
      + split. exact FB1. split. exact Ffb. split. { apply HDR1. clear; lia. clear; lia. exact O8. } split. exact B0.
        split. { replace (o + 16) with (o + 16 + 8 * Z.of_nat 0) by (clear; lia). apply LIMBS1. clear; lia. }
        split. { replace (o + 24) with (o + 16 + 8 * Z.of_nat 1) by (clear; lia). apply LIMBS1. clear - EL1; lia. }
        split. exact Hl2. split. apply words_ok_nth; exact WLO. apply words_ok_nth; exact WLO.
      + split. exact WLL. split. exact WLO.
        assert (E2 : forall l : list Z, length l = 2%nat -> l = firstn 2 [nth_w l 0; nth_w l 1]). { intros l Hl. destruct l as [|a [|b0 [|c0 l]]]; cbn in Hl; try discriminate. reflexivity. }
        rewrite EL1. apply E2. rewrite WLL, EL1. reflexivity.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). split.
      + split. exact FB1. split. exact Ffb. split. { apply HDR1. clear; lia. clear; lia. exact O8. } split. exact B1.
        assert (HDR2 : forall a v, o + 16 <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
        { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR1. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb ODYN CAP; lia. }
        split. { apply HDR2. clear; lia. clear; lia. exact O16. } split. { apply HDR2. clear; lia. clear; lia. exact O24. }
        split. exact Hlc. split. exact Hcap. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH.
      + split. exact WLL. split. exact WLO. intros i Hi. rewrite WLL in Hi. apply LIMBS1. clear - Hi; lia. }
  destruct OB1 as [OB1 OL1].
  assert (RAred : L5.ra_ok REDRET). { split. unfold REDRET; clear; lia. reflexivity. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A16' : (sp - 64) mod 16 = 0) by (clear - A16; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (G2' : getr R1 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (K1 2%nat) by inl; exact G2).
  destruct (L5ARED.reduce_run fx1 R1 M1 o (sp - 64) REDRET b1 wl R1_10 R1_1 RAred G2' ltac:(clear - SPR; lia) A16' W80a IMGC1 CSB1 CUAR1
              ltac:(clear - OR; lia) O8a OBIG ltac:(clear - FRO; lia) OZ1 OW1 OB1 OL1)
    as (fx2 & R2 & M2 & MS2 & OB2 & K2 & R2_2 & R2_10 & FR2 & GR2).
  { subst b1 d cap. unfold L5.bo_data, L5.bo_cap, st_after. cbn [L5.bo_st]. destruct sto as [w0 w1|c q]; cbn iota.
    all: split; [exact DBIG|]. all: split; [clear - FRD; lia|]. all: split; [exact OD|]. all: split; [exact DW1|]. all: split; [exact DZ1|]. all: clear - CAPR; lia. }
  cbn zeta in OB2. replace (L5.bo_fb b1) with fb in OB2 by reflexivity. replace (L5.bo_st b1) with (st_after sto wl) in OB2 by reflexivity.
  assert (MF2 : mfacts M2 sp o d cap). { eapply L5AMULK.mfacts_keep. exact MF1. exact GR2. intros i Hi _ Ho Hs. apply FR2. exact Hi. exact Ho. clear - Hs; lia. }
  pose proof MF2 as [_ W64b [IMGC2 [CSB2 CUAR2]] _ _ _ _ _ _].
  assert (XF : forall a v, sp - 64 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. rewrite FR2. apply FR1.
    clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb FRD CAP; lia. clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb FRO; lia. clear - Hj Ha Hb; lia. }
  assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
  (* [comment removed for export] *)
  pose proof (vmmE_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => o | 43%nat => U R2 1 | 44%nat => r | 45%nat => v8 | 46%nat => v9 | 47%nat => v18 | 48%nat => v19 | 49%nat => v20 | 50%nat => v21 | _ => 0 end)) as P.
  cbn beta iota in P.
  assert (G8' : getr R2 (reg 8) = Z_to_bv 64 o). { rewrite (K2 8%nat) by inl. rewrite (K1 8%nat) by inl. exact G8. }
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc]) ]).
  destruct P as (fx3 & R3 & M3 & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21)).
  assert (EM3 : M3 = M2). { apply functional_extensionality. exact eFR. } subst M3.
  pose proof (ret_to fx3 R3 M2 0x93f00 W_93f00 r F_93f00 eq_refl D_93f00 eR1 (proj1 RA) (proj2 RA)) as RETs.
  exists fx3, R3, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact eMS. exact RETs. }
  split. { intros x Hx. rewrite (eKS x). rewrite (K2 x). apply K1. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity.
           revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. }
  split. exact eR2. split. exact eR10. split. exact eR8. split. exact eR9. split. exact eR18. split. exact eR19. split. exact eR20. split. exact eR21.
  split. { split. exact OB2. intros i Hi. rewrite WLL in Hi. eapply L5C.u64_at_agree. 4:{ apply LIMBS1. clear - Hi; lia. }
           2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia. intros j Hj. apply FR2. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi CAP OD; lia. clear - Hj Hi CAP FRD; lia. }
  split. { intros a Ha Hd Ho Hs. rewrite FR2. apply FR1. exact Ha. exact Hd. exact Ha. exact Ho. clear - Hs; lia. }
  eapply mem_grows_trans. exact GR1. exact GR2.
Qed.

End SCFG_1.
End L5AMULMK.
