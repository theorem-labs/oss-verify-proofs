(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun Bo0_code_8f368_90368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DDmul L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BRedP L5BRed L5BLeafK L5BMul10P.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AMULK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AMULP. Import L5W.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?G |- ?G => exact H end.
Local Ltac sc := first [ asm | rk | gmem | arith_goal; first [asm | blia] ].
Local Notation U := L5BLK.U.
Local Notation UR := L5BLK.UR.
Local Notation U_to := L5BLK.U_to.
Definition mfacts := L5BLK.mfacts 128 104 1.
Lemma mfacts_keep M M' sp o d cap :
  mfacts M sp o d cap -> mem_grows M M' ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * cap) -> ~ (o <= i < o + 16) -> ~ (sp - 128 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> mfacts M' sp o d cap.
Proof. apply L5BLK.mfacts_keep; clear; lia. Qed.

Definition MUL10 : Z := 0x8f3b0.
Definition HEAD : Z := 0x8f4d0.
Definition RZRET : Z := 0x8f474.
Definition REDRET : Z := 0x8f5a4.
Definition RET : Z := 0x8f5d8.
(* [comment removed for export] *)
Section it.
  Variables X c : Z.
  Hypothesis HX : 0 <= X < 2 ^ 64.
  Hypothesis Hc : 0 <= c < 2 ^ 64.
  Let hiA := X / 4294967296.
  Let loA := X mod 4294967296.
  Lemma lo_norm : (4294967296 * X) mod 2 ^ 64 / 4294967296 = loA.
  Proof using HX. exact (L5DDM.lv_eq X HX). Qed.
  Lemma hiA_rng : 0 <= hiA < 4294967296.
  Proof using HX. subst hiA. split. apply Z.div_pos; [clear - HX|clear]; Lia.lia. apply Z.div_lt_upper_bound. clear; Lia.lia. clear - HX. Lia.lia. Qed.
  Lemma loA_rng : 0 <= loA < 4294967296.
  Proof using. subst loA. apply Z.mod_pos_bound. clear; Lia.lia. Qed.
  Lemma X_split : X = hiA * 4294967296 + loA.
  Proof using. subst hiA loA. rewrite (Z.mul_comm _ 4294967296). apply Z.div_mod. clear; Lia.lia. Qed.
  Lemma T1_eq : (42949672960 * hiA) mod 2 ^ 64 = 4294967296 * ((10 * hiA) mod 4294967296).
  Proof using HX. replace (42949672960 * hiA) with (4294967296 * (10 * hiA)) by (clear; Lia.lia). change (2 ^ 64) with (4294967296 * 4294967296).
    rewrite Z.mul_mod_distr_l by (clear; Lia.lia). reflexivity. Qed.
  Lemma lo10_eq :
    (c + ((42949672960 * (X / 4294967296)) mod 2 ^ 64 + (10 * ((4294967296 * X) mod 2 ^ 64 / 4294967296)) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64 = (X * 10 + c) mod 2 ^ 64.
  Proof using HX.
    rewrite lo_norm. fold hiA. rewrite <- (Z.add_mod (42949672960 * hiA) (10 * loA)) by (clear; Lia.lia). rewrite Z.add_mod_idemp_r by (clear; Lia.lia).
    pose proof X_split as XS. f_equal. clearbody hiA loA. clear - XS. Lia.lia.
  Qed.
  Lemma hi10_eq :
    let T1 := (42949672960 * (X / 4294967296)) mod 2 ^ 64 in
    let P3 := (10 * ((4294967296 * X) mod 2 ^ 64 / 4294967296)) mod 2 ^ 64 in
    let LF := (T1 + P3) mod 2 ^ 64 in
    ((if (c + LF) mod 2 ^ 64 <? LF then 1 else 0) + ((if LF <? T1 then 1 else 0) + ((10 * (X / 4294967296)) mod 2 ^ 64) / 4294967296) mod 2 ^ 64) mod 2 ^ 64
    = (X * 10 + c) / 2 ^ 64.
  Proof using HX Hc.
    cbv zeta. rewrite lo_norm. fold hiA. pose proof hiA_rng as RA. pose proof loA_rng as RL. rewrite T1_eq.
    rewrite (Z.mod_small (10 * loA)) by (clear - RL; Lia.lia). rewrite (Z.mod_small (10 * hiA) (2 ^ 64)) by (clear - RA; Lia.lia).
    pose proof (Z.div_mod (10 * hiA) 4294967296 ltac:(clear; Lia.lia)) as EH. pose proof (Z.mod_pos_bound (10 * hiA) 4294967296 ltac:(clear; Lia.lia)) as RM.
    set (m := (10 * hiA) mod 4294967296) in *. set (q := (10 * hiA) / 4294967296) in *.
    assert (Rq : 0 <= q <= 9). { subst q. split. apply Z.div_pos; [clear - RA|clear]; Lia.lia. apply Z.lt_succ_r. apply Z.div_lt_upper_bound. clear; Lia.lia. clear - RA; Lia.lia. }
    set (T1 := 4294967296 * m). set (P3 := 10 * loA).
    assert (RT : 0 <= T1 + P3 < 2 ^ 64 + 2 ^ 64) by (subst T1 P3; clear - RM RL; Lia.lia).
    set (LF := (T1 + P3) mod 2 ^ 64).
    assert (B2 : (if LF <? T1 then 1 else 0) = (T1 + P3) / 2 ^ 64 /\ 0 <= LF < 2 ^ 64 /\ T1 + P3 = 2 ^ 64 * ((T1 + P3) / 2 ^ 64) + LF).
    { subst LF. destruct (Z_lt_le_dec (T1 + P3) (2 ^ 64)).
      - rewrite Z.mod_small, Z.div_small by (clear - RT l; Lia.lia). destruct (Z.ltb_spec (T1 + P3) T1); subst T1 P3; clear - RM RL l H; Lia.lia.
      - rewrite <- (Z_mod_plus_full (T1 + P3) (-1)). rewrite Z.mod_small by (clear - RT l; Lia.lia).
        replace ((T1 + P3) / 2 ^ 64) with 1. destruct (Z.ltb_spec (T1 + P3 + -1 * 2 ^ 64) T1); subst T1 P3; clear - RM RL l H; Lia.lia.
        apply (Z.div_unique_pos _ _ 1 (T1 + P3 - 2 ^ 64)); clear - RT l; Lia.lia. }
    destruct B2 as (B2 & RLF & E2). rewrite B2. set (q2 := (T1 + P3) / 2 ^ 64) in *.
    assert (Rq2 : 0 <= q2 <= 1). { subst q2. split. apply Z.div_pos; clear - RT; Lia.lia. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; clear - RT; Lia.lia. }
    assert (B1 : (if (c + LF) mod 2 ^ 64 <? LF then 1 else 0) = (c + LF) / 2 ^ 64 /\ 0 <= (c + LF) / 2 ^ 64 <= 1).
    { destruct (Z_lt_le_dec (c + LF) (2 ^ 64)).
      - rewrite Z.mod_small, Z.div_small by (clear - Hc RLF l; Lia.lia). destruct (Z.ltb_spec (c + LF) LF); clear - Hc RLF l H; Lia.lia.
      - rewrite <- (Z_mod_plus_full (c + LF) (-1)). rewrite Z.mod_small by (clear - Hc RLF l; Lia.lia).
        replace ((c + LF) / 2 ^ 64) with 1. destruct (Z.ltb_spec (c + LF + -1 * 2 ^ 64) LF); clear - Hc RLF l H; Lia.lia.
        apply (Z.div_unique_pos _ _ 1 (c + LF - 2 ^ 64)); clear - Hc RLF l; Lia.lia. }
    destruct B1 as (B1 & Rq1). rewrite B1. set (q1 := (c + LF) / 2 ^ 64) in *.
    pose proof (Z.div_mod (c + LF) (2 ^ 64) ltac:(clear; Lia.lia)) as E1. fold q1 in E1.
    pose proof (Z.mod_pos_bound (c + LF) (2 ^ 64) ltac:(clear; Lia.lia)) as RS.
    rewrite (Z.mod_small (q2 + q)) by (clear - Rq Rq2; Lia.lia). rewrite (Z.mod_small (q1 + _)) by (clear - Rq Rq1 Rq2; Lia.lia).
    apply (Z.div_unique_pos _ _ _ ((c + LF) mod 2 ^ 64)). exact RS.
    pose proof X_split as XS. subst T1 P3. clearbody hiA loA. clear - XS E1 E2 EH. Lia.lia.
  Qed.
End it.

Definition KSL : list nat := [2; 3; 4; 8; 9; 18; 20; 26; 27]%nat.

(* [comment removed for export] *)
Definition at_mhead (R : bvmap 5 word) (M : word -> option byte) (sp o d : Z) (len J : nat) (c X : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 112) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 (Z.of_nat len) /\ getr R (reg 18) = Z_to_bv 64 10 /\
  getr R (reg 19) = Z_to_bv 64 (Z.of_nat J - 1) /\ getr R (reg 20) = Z_to_bv 64 2147450880 /\ getr R (reg 21) = Z_to_bv 64 X /\ getr R (reg 22) = Z_to_bv 64 c /\
  L5.u64_at RSEGS M (sp - 104) d /\ L5.u64_at RSEGS M (sp - 96) (Z.of_nat len + 1).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mloop (k : nat) : forall fx R M (sp o d cap : Z) (len J : nat) (ws : list Z),
  mfacts M sp o d cap -> (1 <= J)%nat -> (J <= len)%nat -> k = (len - J + 1)%nat -> Z.of_nat len + 1 <= cap ->
  length ws = len -> words_ok ws ->
  (forall i, (i < J - 1)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (nth_w (mulw_words ws 10) i)) ->
  (forall i, (J - 1 <= i <= len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (nth_w (ws ++ [0]) i)) ->
  at_mhead R M sp o d len J (mulw_c ws 10 0 (J - 1)) (nth_w ws (J - 1)) ->
  exists fx' R' M',
    msteps RSEGS (st fx R HEAD M) (st fx' R' L5ARED.REDUCE M')
    /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 8) = Z_to_bv 64 o /\ getr R' (reg 1) = Z_to_bv 64 REDRET
    /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) (nth_w (mulw_words ws 10) i))
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * (Z.of_nat len + 1)) -> ~ (sp - 120 <= i < sp - 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros fx R M sp o d cap len J ws MFM J1 JL Hk CAP WL WO LOW HIGH AT. { exfalso. clear - Hk J1 JL. lia. }
  pose proof MFM as [[SPR A16] W128 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ VZ].
  destruct AT as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & VD & VN).
  set (X := nth_w ws (J - 1)) in *. set (c := mulw_c ws 10 0 (J - 1)) in *.
  assert (RX : 0 <= X < 2 ^ 64) by (subst X; apply words_ok_nth; exact WO).
  assert (Rc : 0 <= c < 2 ^ 64) by (subst c; apply mulw_c_bound; [exact WO | clear; lia | clear; lia]).
  assert (WO0 : words_ok (ws ++ [0])). { apply words_ok_app. exact WO. constructor. clear; lia. constructor. }
  set (X' := nth_w (ws ++ [0]) J).
  assert (RX' : 0 <= X' < 2 ^ 64) by (subst X'; apply words_ok_nth; exact WO0).
  assert (CJ : L5.u64_at RSEGS M (d + 8 * (Z.of_nat J - 1) + 8) X'). { subst X'. replace (d + 8 * (Z.of_nat J - 1) + 8) with (d + 8 * Z.of_nat J) by (clear; lia). apply HIGH. clear - JL; lia. }
  assert (STW : (X * 10 + c) mod 2 ^ 64 = nth_w (mulw_words ws 10) (J - 1)).
  { unfold mulw_words. rewrite mulw_loop_nth by (rewrite WL; clear - J1 JL; lia). reflexivity. }
  assert (STC : (X * 10 + c) / 2 ^ 64 = mulw_c ws 10 0 J).
  { change ((nth_w ws (J - 1) * 10 + mulw_c ws 10 0 (J - 1)) / 2 ^ 64 = mulw_c ws 10 0 J). rewrite <- (mulw_c_S ws 10 0 (J - 1)) by (rewrite WL; clear - J1 JL; lia). f_equal. clear - J1; lia. }
  (* [comment removed for export] *)
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 128 + 128 <= o \/ o + 32 <= sp - 128) by (clear - FRO; lia). assert (FRDp : sp - 128 + 128 <= d \/ d + 8 * cap <= sp - 128) by (clear - FRD; lia).
  assert (DIMGp : 65536 + 6438912 <= d \/ d + 8 * cap <= 65536) by (clear - DIMG; lia).
  assert (HV2 : 140735332487296 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia).
  assert (HVI : 0 <= Z.of_nat J - 1 <= 134217727) by (clear - J1 JL CAP CAPR; lia). assert (HVCI : 2 <= cap - (Z.of_nat J - 1) <= 134217728) by (clear - JL CAP CAPR J1; lia).
  assert (HVL : 1 <= Z.of_nat len <= 134217728) by (clear - J1 JL CAP CAPR; lia).
  assert (HVc : 0 <= c <= 18446744073709551615) by (clear - Rc; lia). assert (HVX : 0 <= X <= 18446744073709551615) by (clear - RX; lia).
  assert (HVX' : 0 <= X' <= 18446744073709551615) by (clear - RX'; lia).
  assert (VZp : L5KA.zeros_at M ((sp - 104) / 8 + 2147450880) 1) by exact VZ.
  destruct k as [|k'].
  - (* [comment removed for export] *)
    assert (EJ : J = len) by (clear - Hk J1 JL; lia). subst J.
    assert (HV3440 : 1 <= Z.of_nat len - (Z.of_nat len - 1) <= 1) by (clear; lia).
    assert (HVCL : 1 <= cap - Z.of_nat len <= 134217728) by (clear - CAP CAPR HVL; lia).
    pose proof (amL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 36%nat => d | 37%nat => cap | 38%nat => X | 39%nat => X'
                  | 40%nat => Z.of_nat len - 1 | 41%nat => c | 43%nat => U R 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & lFR & lFZ & (lMS & lKS & lR1 & lR10 & lR11 & lR12 & lR13 & lR14 & lR19 & lR21 & lR22 & lR23 & lR24 & lR25 & lCTOP & lCRA & lCLIMB)).
    match type of lCLIMB with L5.u64_at _ _ _ ?e => assert (LOE : e = (X * 10 + c) mod 2 ^ 64) by exact (lo10_eq X c RX); rewrite LOE in lCLIMB end.
    match type of lCTOP with L5.u64_at _ _ _ ?e => assert (HIE : e = (X * 10 + c) / 2 ^ 64) by exact (hi10_eq X c RX Rc); rewrite HIE in lCTOP end.
    rewrite STW in lCLIMB. rewrite STC in lCTOP.
    exists fx1, R1, M1. split. exact lMS.
    split. { intros x Hx. apply lKS. revert Hx; apply (L5K.incl_b _ KS_amL); vm_compute; reflexivity. }
    split. exact lR10. split. { rewrite (lKS 8%nat). exact A8. apply (L5K.in_b 8%nat KS_amL); vm_compute; reflexivity. } split. exact lR1.
    split. { intros i Hi. destruct (Nat.eq_dec i len) as [->|NE].
      { unfold mulw_words. rewrite <- WL at 2. rewrite mulw_loop_last. rewrite WL. replace (d + 8 * Z.of_nat len) with (8 * Z.of_nat len + d) by (clear; lia). exact lCTOP. }
      destruct (Nat.eq_dec i (len - 1)) as [->|NE2].
      { replace (d + 8 * Z.of_nat (len - 1)) with (d + 8 * (Z.of_nat len - 1)) by (clear - J1; lia). exact lCLIMB. }
      eapply L5C.u64_at_agree. 4:{ apply LOW. clear - Hi NE NE2; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia.
      intros j Hj. apply lFZ. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi NE NE2 J1; lia. clear - Hj Hi CAP FRD SPR; lia. }
    split. { intros i Hi Hn Hs. apply lFZ. exact Hi. clear - Hn J1; lia. clear - Hs; lia. } exact MG1.
  - (* [comment removed for export] *)
    assert (JL2 : (J < len)%nat) by (clear - Hk J1 JL; lia).
    assert (HV3440 : 2 <= Z.of_nat len - (Z.of_nat J - 1) <= 134217728) by (clear - JL2 HVL J1; lia).
    pose proof (amI_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 36%nat => d | 37%nat => cap | 38%nat => X | 39%nat => X'
                  | 40%nat => Z.of_nat J - 1 | 41%nat => c | 43%nat => U R 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & iFR & iFZ & (iMS & iKS & iR1 & iR10 & iR11 & iR12 & iR13 & iR14 & iR19 & iR21 & iR22 & iR23 & iR24 & iR25 & iCRA & iCLIMB)).
    match type of iCLIMB with L5.u64_at _ _ _ ?e => assert (LOE : e = (X * 10 + c) mod 2 ^ 64) by exact (lo10_eq X c RX); rewrite LOE in iCLIMB end.
    match type of iR22 with _ = ?e => assert (HIE : e = (X * 10 + c) / 2 ^ 64) by exact (hi10_eq X c RX Rc); rewrite HIE in iR22 end.
    rewrite STW in iCLIMB. rewrite STC in iR22.
    assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep. exact MFM. exact MG1. intros i Hi Hd _ Hs. apply iFZ. exact Hi. clear - Hd J1 JL CAP; lia. clear - Hs; lia. }
    assert (XN : X' = nth_w ws J). { subst X'. unfold nth_w. rewrite app_nth1 by (rewrite WL; exact JL2). reflexivity. }
    assert (KEEP : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= d + 8 * (Z.of_nat J - 1) \/ d + 8 * (Z.of_nat J - 1) + 8 <= a) -> (a + 8 <= sp - 120 \/ sp - 112 <= a) ->
                   L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb Hd Hs Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: exact Ha. 2: exact Hb. intros j Hj. apply iFZ. clear - Hj Ha Hb; lia. clear - Hj Hd; lia. clear - Hj Hs; lia. }
    destruct (IH fx1 R1 M1 sp o d cap len (Datatypes.S J) ws MF1 ltac:(clear; lia) ltac:(clear - JL2; lia) ltac:(clear - Hk JL2 J1; lia) CAP WL WO) as (fx' & R' & M' & MS & K & R10' & R8' & R1' & LIMBS & FR' & GR').
    + intros i Hi. destruct (Nat.eq_dec i (J - 1)) as [->|NE].
      { replace (d + 8 * Z.of_nat (J - 1)) with (d + 8 * (Z.of_nat J - 1)) by (clear - J1; lia). exact iCLIMB. }
      apply KEEP. clear - DR; lia. clear - DR CAPR CAP Hi JL; lia. clear - Hi NE J1; lia. clear - Hi JL CAP FRD SPR; lia. apply LOW. clear - Hi NE; lia.
    + intros i Hi. apply KEEP. clear - DR; lia. clear - DR CAPR CAP Hi; lia. clear - Hi J1; lia. clear - Hi CAP FRD SPR; lia. apply HIGH. clear - Hi; lia.
    + unfold at_mhead. replace (Datatypes.S J - 1)%nat with J by (clear; lia). rewrite <- XN.
      assert (KK : forall x, In x [2; 8; 9; 18; 20]%nat -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. apply iKS. revert Hx; apply (L5K.incl_b _ KS_amI); vm_compute; reflexivity. }
      repeat split.
      * rewrite (KK 2%nat) by inl; exact A2. * rewrite (KK 8%nat) by inl; exact A8. * rewrite (KK 9%nat) by inl; exact A9. * rewrite (KK 18%nat) by inl; exact A18.
      * rewrite iR19. f_equal. clear; lia.
      * rewrite (KK 20%nat) by inl; exact A20. * exact iR21.
      * rewrite <- iR22. symmetry. apply Z_to_bv_bv_unsigned.
      * apply KEEP. clear - SPR; lia. clear - SPR; lia. clear - FRD CAP JL J1 SPR; lia. clear; lia. exact VD.
      * apply KEEP. clear - SPR; lia. clear - SPR; lia. clear - FRD CAP JL J1 SPR; lia. clear; lia. exact VN.
    + exists fx', R', M'. split. { eapply msteps_trans. exact iMS. exact MS. }
      split. { intros x Hx. rewrite (K x Hx). apply iKS. revert Hx; apply (L5K.incl_b _ KS_amI); vm_compute; reflexivity. }
      split. exact R10'. split. exact R8'. split. exact R1'. split. exact LIMBS.
      split. { intros i Hi Hn Hs. rewrite (FR' i Hi Hn Hs). apply iFZ. exact Hi. clear - Hn J1 JL; lia. clear - Hs; lia. }
      eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KSC : list nat := [3; 4; 26; 27]%nat.
Definition KSP : list nat := [2; 3; 4; 26; 27]%nat.

(* [comment removed for export] *)
Definition st_after (sto : L5.bstore) (len : nat) (wl : list Z) : L5.bstore :=
  match sto with
  | L5.BInl _ v1 => L5.BInl (nth_w wl 0) (if Nat.eqb len 0 then v1 else nth_w wl 1)
  | L5.BDyn c q => L5.BDyn c q
  end.

Lemma saved_back M M2 sp (FRs : forall a, 0 <= a < 2 ^ 64 -> sp - 88 <= a < sp -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) :
  140735332487296 <= sp <= 140737488355328 ->
  forall a v, sp - 88 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v.
Proof.
  intros SPR a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia.
  intros j Hj. apply FRs. clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb; lia.
Qed.

(* [comment removed for export] *)
Lemma mul10_tail fx1 R1 M1 (sp o r : Z) (b1 : L5.bigobj) (wl : list Z) (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : Z) :
  let d := L5.bo_data o b1 in let cap := L5.bo_cap b1 in
  getr R1 (reg 2) = Z_to_bv 64 (sp - 112) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 10) = Z_to_bv 64 o -> getr R1 (reg 1) = Z_to_bv 64 REDRET ->
  L5.u64_at RSEGS M1 (sp - 8) r -> L5.ra_ok r ->
  L5.u64_at RSEGS M1 (sp - 16) v8 -> L5.u64_at RSEGS M1 (sp - 24) v9 -> L5.u64_at RSEGS M1 (sp - 32) v18 -> L5.u64_at RSEGS M1 (sp - 40) v19 -> L5.u64_at RSEGS M1 (sp - 48) v20 -> L5.u64_at RSEGS M1 (sp - 56) v21 -> L5.u64_at RSEGS M1 (sp - 64) v22 -> L5.u64_at RSEGS M1 (sp - 72) v23 -> L5.u64_at RSEGS M1 (sp - 80) v24 -> L5.u64_at RSEGS M1 (sp - 88) v25 ->
  0 <= v8 < 2 ^ 64 -> 0 <= v9 < 2 ^ 64 -> 0 <= v18 < 2 ^ 64 -> 0 <= v19 < 2 ^ 64 -> 0 <= v20 < 2 ^ 64 -> 0 <= v21 < 2 ^ 64 -> 0 <= v22 < 2 ^ 64 -> 0 <= v23 < 2 ^ 64 -> 0 <= v24 < 2 ^ 64 -> 0 <= v25 < 2 ^ 64 ->
  mfacts M1 sp o d cap ->
  L5.big_at RSEGS M1 o b1 -> L5C.obj_limbs RSEGS M1 b1 wl ->
  exists fx' R' M',
    msteps RSEGS (st fx1 R1 L5ARED.REDUCE M1) (st fx' R' r M')
    /\ (forall x, In x KSC -> getr R' (reg x) = getr R1 (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 o
    /\ getr R' (reg 8) = Z_to_bv 64 v8 /\ getr R' (reg 9) = Z_to_bv 64 v9 /\ getr R' (reg 18) = Z_to_bv 64 v18 /\ getr R' (reg 19) = Z_to_bv 64 v19 /\ getr R' (reg 20) = Z_to_bv 64 v20 /\ getr R' (reg 21) = Z_to_bv 64 v21 /\ getr R' (reg 22) = Z_to_bv 64 v22 /\ getr R' (reg 23) = Z_to_bv 64 v23 /\ getr R' (reg 24) = Z_to_bv 64 v24 /\ getr R' (reg 25) = Z_to_bv 64 v25
    /\ (let n' := L5W.rlen wl in L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land (L5.bo_fb b1) 253 else L5.bo_fb b1) n' (L5.bo_st b1)))
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 16) -> ~ (sp - 128 <= a < sp - 112) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))
    /\ mem_grows M1 M'.
Proof.
  cbn zeta. intros G2 G8 R1_10 R1_1 C8 RA C16 C24 C32 C40 C48 C56 C64 C72 C80 C88 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 MF1 OB1 OL1.
  pose proof MF1 as [[SPR A16] W128a [IMGC1 [CSB1 CUAR1]] (OR & O8a & OBIG & FRO) OZ1 OW1 (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW1 DZ1 VZ1].
  assert (W16a : L5.writable RSEGS M1 (sp - 112 - 16) 16). { eapply L5.writable_sub. exact W128a. clear; lia. clear; lia. }
  assert (RAred : L5.ra_ok REDRET). { split. unfold REDRET; clear; lia. reflexivity. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A16' : (sp - 112) mod 16 = 0) by (clear - A16; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct (L5ARED.reduce_run fx1 R1 M1 o (sp - 112) REDRET b1 wl R1_10 R1_1 RAred G2 ltac:(clear - SPR; lia) A16' W16a IMGC1 CSB1 CUAR1
              ltac:(clear - OR; lia) O8a OBIG ltac:(clear - FRO; lia) OZ1 OW1 OB1 OL1)
    as (fx2 & R2 & M2 & MS2 & OB2 & K2 & R2_2 & R2_10 & FR2 & GR2).
  { split; [exact DBIG|]. split; [clear - FRD; lia|]. split; [exact OD|]. split; [exact DW1|]. split; [exact DZ1|]. clear - CAPR; lia. }
  cbn zeta in OB2.
  assert (XF : forall a v, sp - 88 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v).
  { apply saved_back. 2: clear - SPR; lia. intros a Ha Hs. apply FR2. exact Ha. clear - Hs FRO; lia. clear - Hs; lia. }
  assert (MF2 : mfacts M2 sp o (L5.bo_data o b1) (L5.bo_cap b1)). { eapply mfacts_keep. exact MF1. exact GR2. intros i Hi _ Ho Hs. apply FR2. exact Hi. exact Ho. clear - Hs; lia. }
  pose proof MF2 as [_ W128b [IMGC2 [CSB2 CUAR2]] _ _ _ _ _ _ _].
  assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
  assert (ALS : aligned sp 16) by exact A16. assert (HV2 : 140735332487296 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVO : 0 <= o < 2 ^ 64) by (clear - OR; lia).
  pose proof (amE_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => o | 43%nat => U R2 1 | 44%nat => r | 45%nat => v8 | 46%nat => v9 | 47%nat => v18 | 48%nat => v19 | 49%nat => v20 | 50%nat => v21 | 51%nat => v22 | 52%nat => v23 | 53%nat => v24 | 54%nat => v25 | _ => 0 end)) as P.
  cbn beta iota in P.
  assert (G8' : getr R2 (reg 8) = Z_to_bv 64 o). { rewrite (K2 8%nat) by inl. exact G8. }
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc]) ]).
  destruct P as (fx3 & R3 & M3 & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25)).
  assert (EM3 : M3 = M2). { apply functional_extensionality. exact eFR. } subst M3.
  pose proof (ret_to fx3 R3 M2 0x8f5d8 W_8f5d8 r F_8f5d8 eq_refl D_8f5d8 eR1 (proj1 RA) (proj2 RA)) as RETs.
  exists fx3, R3, M2. split. { eapply msteps_trans. exact MS2. eapply msteps_trans. exact eMS. exact RETs. }
  split. { intros x Hx. rewrite (eKS x). apply K2. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. }
  split. exact eR2. split. exact eR10. split. exact eR8. split. exact eR9. split. exact eR18. split. exact eR19. split. exact eR20. split. exact eR21. split. exact eR22. split. exact eR23. split. exact eR24. split. exact eR25.
  split. exact OB2. split. { intros a Ha Ho Hs. apply FR2. exact Ha. exact Ho. clear - Hs; lia. } exact GR2.
Qed.

Theorem mul10_core fx R M (sp o r x0 fb : Z) (len : nat) (sto : L5.bstore) (wsR : list Z) (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : Z) :
  let b := L5.BO fb (Datatypes.S len) sto in let d := L5.bo_data o b in let cap := L5.bo_cap b in let ws := firstn len wsR in
  getr R (reg 2) = Z_to_bv 64 (sp - 112) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 (Z.of_nat len) -> getr R (reg 18) = Z_to_bv 64 10 -> getr R (reg 19) = Z_to_bv 64 (o + 8) ->
  getr R (reg 20) = Z_to_bv 64 SB -> getr R (reg 21) = Z_to_bv 64 x0 -> 0 <= x0 < 2 ^ 64 -> ((1 <= len)%nat -> x0 = nth 0 wsR 0) ->
  getr R (reg 22) = Z_to_bv 64 (o / 8 + SB) -> getr R (reg 23) = Z_to_bv 64 ((o + 8) / 8 + SB) ->
  L5.u64_at RSEGS M (sp - 8) r -> L5.ra_ok r ->
  L5.u64_at RSEGS M (sp - 16) v8 -> L5.u64_at RSEGS M (sp - 24) v9 -> L5.u64_at RSEGS M (sp - 32) v18 -> L5.u64_at RSEGS M (sp - 40) v19 -> L5.u64_at RSEGS M (sp - 48) v20 -> L5.u64_at RSEGS M (sp - 56) v21 -> L5.u64_at RSEGS M (sp - 64) v22 -> L5.u64_at RSEGS M (sp - 72) v23 -> L5.u64_at RSEGS M (sp - 80) v24 -> L5.u64_at RSEGS M (sp - 88) v25 ->
  0 <= v8 < 2 ^ 64 -> 0 <= v9 < 2 ^ 64 -> 0 <= v18 < 2 ^ 64 -> 0 <= v19 < 2 ^ 64 -> 0 <= v20 < 2 ^ 64 -> 0 <= v21 < 2 ^ 64 -> 0 <= v22 < 2 ^ 64 -> 0 <= v23 < 2 ^ 64 -> 0 <= v24 < 2 ^ 64 -> 0 <= v25 < 2 ^ 64 ->
  mfacts M sp o d cap ->
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b wsR -> nth len wsR 0 = 0 -> Z.of_nat len + 1 <= cap ->
  match sto with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end ->
  exists fx' R' M',
    msteps RSEGS (st fx R RZRET M) (st fx' R' r M')
    /\ (forall x, In x KSC -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 o
    /\ getr R' (reg 8) = Z_to_bv 64 v8 /\ getr R' (reg 9) = Z_to_bv 64 v9 /\ getr R' (reg 18) = Z_to_bv 64 v18 /\ getr R' (reg 19) = Z_to_bv 64 v19 /\ getr R' (reg 20) = Z_to_bv 64 v20 /\ getr R' (reg 21) = Z_to_bv 64 v21 /\ getr R' (reg 22) = Z_to_bv 64 v22 /\ getr R' (reg 23) = Z_to_bv 64 v23 /\ getr R' (reg 24) = Z_to_bv 64 v24 /\ getr R' (reg 25) = Z_to_bv 64 v25
    /\ (let wl := mulw_words ws 10 in let n' := L5W.rlen wl in
        L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land fb 253 else fb) n' (st_after sto len wl)) /\ L5.limbs_at RSEGS M' d wl)
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (o <= a < o + 16) -> ~ (sp - 128 <= a < sp - 88) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.
Proof.
  cbn zeta. intros G2 G8 G9 G18 G19 G20 G21 Rx0 X0 G22 G23 C8 RA C16 C24 C32 C40 C48 C56 C64 C72 C80 C88 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 MFM OB OL TOP0 CAP ODYN.
  pose proof MFM as [[SPR A16] W128 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ VZ].
  unfold L5.bo_data, L5.bo_cap in *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  set (d := match sto with L5.BInl _ _ => o + 16 | L5.BDyn _ q => q end) in *.
  set (cap := match sto with L5.BInl _ _ => 2 | L5.BDyn c _ => c end) in *.
  pose proof OB as (O0 & Ffb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Ffb, O8, OST. destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  set (ws := firstn len wsR) in *.
  assert (WOR : words_ok wsR) by exact Rws.
  assert (WL : length ws = len). { subst ws. rewrite length_firstn, Lws. clear; lia. }
  assert (WO : words_ok ws). { subst ws. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) WOR w). eapply L5BLK.in_firstn. exact Hw. }
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
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 128 + 128 <= o \/ o + 32 <= sp - 128) by (clear - FRO; lia). assert (FRDp : sp - 128 + 128 <= d \/ d + 8 * cap <= sp - 128) by (clear - FRD; lia).
  assert (DIMGp : 65536 + 6438912 <= d \/ d + 8 * cap <= 65536) by (clear - DIMG; lia).
  assert (HV2 : 140735332487296 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia). assert (HVF : 0 <= fb <= 255) by (clear - Ffb; lia).
  assert (HVCL : 1 <= cap - Z.of_nat len <= 134217728) by (clear - CAP CAPR; lia).
  assert (HVX0 : 0 <= x0 < 2 ^ 64) by exact Rx0.
  assert (VZp : L5KA.zeros_at M ((sp - 104) / 8 + 2147450880) 1) by exact VZ.
  assert (O8s : L5.u64_at RSEGS M (o + 8) (Z.of_nat len + 1)). { replace (Z.of_nat len + 1) with (Z.of_nat (Datatypes.S len)) by (clear; lia). exact O8. }
  set (wl := mulw_words ws 10).
  assert (WLL : length wl = Datatypes.S len) by (subst wl; rewrite mulw_words_length, WL; reflexivity).
  assert (WLO : words_ok wl) by (subst wl; apply mulw_words_ok; [exact WO | clear; lia]).
  (* [comment removed for export] *)
  assert (PART1 : exists fx1 R1 M1, msteps RSEGS (st fx R RZRET M) (st fx1 R1 L5ARED.REDUCE M1)
      /\ (forall x, In x KSP -> getr R1 (reg x) = getr R (reg x)) /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 1) = Z_to_bv 64 REDRET
      /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat i) (nth_w wl i))
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (sp - 120 <= a < sp - 88) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ mem_grows M M1).
  { destruct (Nat.eq_dec len 0) as [L0|Lnz].
    - (* [comment removed for export] *)
      assert (HVL0 : 0 <= Z.of_nat len <= 0) by (clear - L0; lia).
      assert (RUN : exists fx1 R1 M1, mem_grows M M1 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8) -> ~ (sp - 120 <= a < sp - 88) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
                 /\ msteps RSEGS (st fx R RZRET M) (st fx1 R1 L5ARED.REDUCE M1) /\ (forall x, In x [2; 3; 4; 8; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
                 /\ getr R1 (reg 1) = Z_to_bv 64 REDRET /\ getr R1 (reg 10) = Z_to_bv 64 o /\ L5.u64_at RSEGS M1 d 0).
      { subst d cap. destruct sto as [w0 w1|c q].
        + destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1).
          pose proof (amZi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 42%nat => x0 | 43%nat => U R 1 | 58%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
          feed P ltac:(first [apply UR | apply U_to | sc]).
          destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR1 & zR10 & zR11 & zR12 & zR13 & zR14 & zR22 & zQ0 & zCRA & zVN & zVD)).
          exists fx1, R1, M1. split. exact MG1. split. { intros a Ha Hn Hs. apply zFZ. exact Ha. clear - Hs; lia. clear - Hn; lia. clear - Hs; lia. } split. exact zMS.
          split. { intros x Hx. apply zKS. revert Hx; apply (L5K.incl_b _ KS_amZi); vm_compute; reflexivity. } split. exact zR1. split. exact zR10. exact zQ0.
        + destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
          assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia). assert (HVC : 0 <= c < 2 ^ 64) by (clear - Hcap; lia).
          pose proof (amZd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => c | 42%nat => x0 | 43%nat => U R 1 | 58%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
          feed P ltac:(first [apply UR | apply U_to | sc]).
          destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR1 & zR10 & zR11 & zR12 & zR13 & zR14 & zR22 & zQ0 & zCRA & zVN & zVD)).
          exists fx1, R1, M1. split. exact MG1. split. { intros a Ha Hn Hs. apply zFZ. exact Ha. clear - Hs; lia. clear - Hn; lia. clear - Hs; lia. } split. exact zMS.
          split. { intros x Hx. apply zKS. revert Hx; apply (L5K.incl_b _ KS_amZd); vm_compute; reflexivity. } split. exact zR1. split. exact zR10. exact zQ0. }
      destruct RUN as (fx1 & R1 & M1 & MG1 & FR1 & MS1 & K1 & Z1 & Z10 & ZQ).
      exists fx1, R1, M1. split. exact MS1.
      split. { intros x Hx. apply K1. revert Hx; apply (L5K.incl_b KSP); vm_compute; reflexivity. }
      split. exact Z10. split. { rewrite (K1 8%nat) by inl. exact G8. } split. exact Z1.
      split. { intros i Hi. replace i with 0%nat by (clear - Hi L0; lia). replace (d + 8 * Z.of_nat 0) with d by (clear; lia).
               replace (nth_w wl 0) with 0. exact ZQ. subst wl ws. rewrite L0. reflexivity. }
      split. { intros a Ha Hn Hs. apply FR1. exact Ha. clear - Hn L0; lia. exact Hs. } exact MG1.
    - (* [comment removed for export] *)
      assert (Lpos : (1 <= len)%nat) by (clear - Lnz; lia).
      assert (EX0 : x0 = nth_w ws 0). { rewrite (X0 Lpos). rewrite (NTH 0%nat ltac:(clear; lia)). unfold nth_w. rewrite app_nth1 by (rewrite WL; exact Lpos). reflexivity. }
      assert (HVL1 : 1 <= Z.of_nat len <= 134217728) by (clear - Lpos CAP CAPR; lia).
      assert (RUN : exists fx1 R1 M1, mem_grows M M1 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 104 <= a < sp - 88) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
                 /\ msteps RSEGS (st fx R RZRET M) (st fx1 R1 HEAD M1) /\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
                 /\ getr R1 (reg 19) = Z_to_bv 64 0 /\ getr R1 (reg 22) = Z_to_bv 64 0
                 /\ L5.u64_at RSEGS M1 (sp - 96) (Z.of_nat len + 1) /\ L5.u64_at RSEGS M1 (sp - 104) d).
      { subst d cap. destruct sto as [w0 w1|c q].
        + destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). assert (HVL2 : 1 <= Z.of_nat len <= 2) by (clear - Lpos Hl2; lia).
          pose proof (amBi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 42%nat => x0 | 43%nat => U R 1 | 58%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
          feed P ltac:(first [apply UR | apply U_to | sc]).
          destruct P as (fx1 & R1 & M1 & MG1 & bFR & bFZ & (bMS & bKS & bR10 & bR11 & bR19 & bR22 & bVN & bVD)).
          exists fx1, R1, M1. split. exact MG1. split. { intros a Ha Hn. apply bFZ. exact Ha. clear - Hn; lia. } split. exact bMS.
          split. { intros x Hx. apply bKS. revert Hx; apply (L5K.incl_b _ KS_amBi); vm_compute; reflexivity. }
          split. exact bR19. split. exact bR22. split. exact bVN. exact bVD.
        + destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
          assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia). assert (HVC : 0 <= c < 2 ^ 64) by (clear - Hcap; lia).
          assert (HVLC : 1 <= c - Z.of_nat len <= 134217728) by (clear - HVCL; lia).
          pose proof (amBd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => c | 42%nat => x0 | 43%nat => U R 1 | 58%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
          feed P ltac:(first [apply UR | apply U_to | sc]).
          destruct P as (fx1 & R1 & M1 & MG1 & bFR & bFZ & (bMS & bKS & bR10 & bR11 & bR19 & bR22 & bVN & bVD)).
          exists fx1, R1, M1. split. exact MG1. split. { intros a Ha Hn. apply bFZ. exact Ha. clear - Hn; lia. } split. exact bMS.
          split. { intros x Hx. apply bKS. revert Hx; apply (L5K.incl_b _ KS_amBd); vm_compute; reflexivity. }
          split. exact bR19. split. exact bR22. split. exact bVN. exact bVD. }
      destruct RUN as (fx1 & R1 & M1 & MG1 & FR1 & MS1 & K1 & B19 & B22 & BVN & BVD).
      assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep. exact MFM. exact MG1. intros a Ha _ _ Hs. apply FR1. exact Ha. clear - Hs; lia. }
      destruct (mloop len fx1 R1 M1 sp o d cap len 1 ws MF1 ltac:(clear; lia) Lpos ltac:(clear - Lpos; lia) CAP WL WO) as (fx2 & R2 & M2 & MS2 & K2 & R2_10 & R2_8 & R2_1 & LIMBS2 & FR2 & GR2).
      { intros i Hi. exfalso. clear - Hi. lia. }
      { intros i Hi. eapply L5C.u64_at_agree. 4:{ apply LIMBS. clear - Hi; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia.
        intros a Ha. apply FR1. clear - Ha DR CAPR CAP Hi; lia. clear - Ha Hi CAP FRD; lia. }
      { unfold at_mhead. replace (1 - 1)%nat with 0%nat by reflexivity. rewrite mulw_c_0. rewrite <- EX0. change (Z.of_nat 1 - 1) with 0.
        repeat split; try (first [assumption | rewrite (K1 _) by inl; assumption]). }
      exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. exact MS2. }
      split. { intros x Hx. rewrite (K2 x). apply K1. revert Hx; apply (L5K.incl_b KSP); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSP); vm_compute; reflexivity. }
      split. exact R2_10. split. exact R2_8. split. exact R2_1. split. exact LIMBS2.
      split. { intros a Ha Hn Hs. rewrite (FR2 a Ha Hn). apply FR1. exact Ha. clear - Hs; lia. clear - Hs; lia. }
      eapply mem_grows_trans; eauto. }
  destruct PART1 as (fx1 & R1 & M1 & MS1 & K1 & R1_10 & R1_8 & R1_1 & LIMBS1 & FR1 & GR1).
  assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep. exact MFM. exact GR1. intros i Hi Hd _ Hs. apply FR1. exact Hi. clear - Hd CAP CAPR; lia. clear - Hs; lia. }
  assert (HDR1 : forall a v, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR1. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb OD CAP; lia. clear - Hj Ha Hb FRO; lia. }
  assert (FB1 : L5.u8_at RSEGS M1 o fb). { eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FR1. clear - Hj OR; lia. clear - Hj OD CAP; lia. clear - Hj FRO; lia. }
  set (b1 := L5.BO fb (Datatypes.S len) (st_after sto len wl)).
  assert (OB1 : L5.big_at RSEGS M1 o b1 /\ L5C.obj_limbs RSEGS M1 b1 wl).
  { subst b1 d cap. unfold L5.big_at, L5C.obj_limbs, st_after. cbn [L5.bo_fb L5.bo_len L5.bo_st]. destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). split.
      + split. exact FB1. split. exact Ffb. split. { apply HDR1. clear; lia. clear; lia. exact O8. } split. exact B0.
        split. { replace (o + 16) with (o + 16 + 8 * Z.of_nat 0) by (clear; lia). apply LIMBS1. clear; lia. }
        destruct (Nat.eqb_spec len 0) as [L0|Lnz].
        * split. { eapply L5C.u64_at_agree. 4: exact O24. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FR1. clear - Hj OR; lia. clear - Hj L0; lia. clear - Hj FRO; lia. }
          split. exact Hl2. split. apply words_ok_nth; exact WLO. exact Rw1.
        * split. { replace (o + 24) with (o + 16 + 8 * Z.of_nat 1) by (clear; lia). apply LIMBS1. clear - Lnz; lia. }
          split. exact Hl2. split. apply words_ok_nth; exact WLO. apply words_ok_nth; exact WLO.
      + split. exact WLL. split. exact WLO.
        destruct (Nat.eqb_spec len 0) as [L0|Lnz].
        * assert (E1 : forall (l : list Z) v, length l = 1%nat -> l = firstn 1 [nth_w l 0; v]). { intros l v Hl. destruct l as [|a [|b0 l]]; cbn in Hl; try discriminate. reflexivity. }
          rewrite L0. apply E1. rewrite WLL, L0. reflexivity.
        * assert (EL1 : len = 1%nat) by (clear - Hl2 Lnz; lia).
          assert (E2 : forall l : list Z, length l = 2%nat -> l = firstn 2 [nth_w l 0; nth_w l 1]). { intros l Hl. destruct l as [|a [|b0 [|c0 l]]]; cbn in Hl; try discriminate. reflexivity. }
          rewrite EL1. apply E2. rewrite WLL, EL1. reflexivity.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). split.
      + split. exact FB1. split. exact Ffb. split. { apply HDR1. clear; lia. clear; lia. exact O8. } split. exact B1.
        assert (HDR2 : forall a v, o + 16 <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
        { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR1. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb ODYN CAP; lia. clear - Hj Ha Hb FRO; lia. }
        split. { apply HDR2. clear; lia. clear; lia. exact O16. } split. { apply HDR2. clear; lia. clear; lia. exact O24. }
        split. exact Hlc. split. exact Hcap. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH.
      + split. exact WLL. split. exact WLO. intros i Hi. rewrite WLL in Hi. apply LIMBS1. clear - Hi; lia. }
  destruct OB1 as [OB1 OL1].
  assert (XF1 : forall a v, sp - 88 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
  { apply saved_back. 2: clear - SPR; lia. intros a Ha Hs. apply FR1. exact Ha. clear - Hs FRD CAP; lia. clear - Hs; lia. }
  assert (EDC : L5.bo_data o b1 = d /\ L5.bo_cap b1 = cap). { subst b1 d cap. unfold L5.bo_data, L5.bo_cap, st_after. cbn [L5.bo_st]. destruct sto; split; reflexivity. }
  destruct EDC as [ED EC].
  destruct (mul10_tail fx1 R1 M1 sp o r b1 wl v8 v9 v18 v19 v20 v21 v22 v23 v24 v25) as (fx3 & R3 & M3 & MS3 & K3 & T2 & T10 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & OB3 & FR3 & GR3).
  all: try (apply XF1; [clear; lia | clear; lia | assumption]); try assumption.
  { rewrite (K1 2%nat) by inl. exact G2. }
  { rewrite ED, EC. exact MF1. }
  cbn zeta in OB3. replace (L5.bo_fb b1) with fb in OB3 by reflexivity. replace (L5.bo_st b1) with (st_after sto len wl) in OB3 by reflexivity.
  exists fx3, R3, M3. split. { eapply msteps_trans. exact MS1. exact MS3. }
  split. { intros x Hx. rewrite (K3 x Hx). apply K1. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. }
  split. exact T2. split. exact T10. split. exact T8. split. exact T9. split. exact T18. split. exact T19. split. exact T20. split. exact T21. split. exact T22. split. exact T23. split. exact T24. split. exact T25.
  split. { split. exact OB3. intros i Hi. rewrite WLL in Hi. eapply L5C.u64_at_agree. 4:{ apply LIMBS1. clear - Hi; lia. }
           2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia. intros j Hj. apply FR3. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi CAP OD; lia. clear - Hj Hi CAP FRD; lia. }
  split. { intros a Ha Hd Ho Hs. rewrite FR3. apply FR1. exact Ha. exact Hd. clear - Hs; lia. exact Ha. exact Ho. clear - Hs; lia. }
  eapply mem_grows_trans. exact GR1. exact GR3.
Qed.


End SCFG_1.
End L5AMULK.
