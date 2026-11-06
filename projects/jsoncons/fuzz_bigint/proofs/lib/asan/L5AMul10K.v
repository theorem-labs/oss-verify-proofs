(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun As0_code_8e368_8f368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5Mul10W L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ARedP L5ARed L5AMul10P L5AMulArith.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AMULK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AMULP. Import L5MULW.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Import L5AMA.

Definition HEAD : Z := 0x8f0ec.
Definition RZRET : Z := 0x8f094.
Definition REDRET : Z := 0x8f17c.

(* [comment removed for export] *)
Record mfacts (M : word -> option byte) (sp o d cap : Z) : Prop := MF {
  mf_sp : 140735332487296 <= sp <= 140737488355328 /\ sp mod 16 = 0;
  mf_w64 : L5.writable RSEGS M (sp - 64) 64;
  mf_st : L5.img_clear M 860160 880640 /\ L5.u64_at RSEGS M 908088 2147450880 /\ L5.u32_at RSEGS M 908096 1;
  mf_o : 6500352 <= o <= 140737488355296 /\ o mod 8 = 0 /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) /\ (sp - 64 + 64 <= o \/ o + 32 <= sp - 4096);
  mf_oz : L5KA.zeros_at M (o / 8 + SB) 4;
  mf_ow : L5.writable RSEGS M o 32;
  mf_d : (4096 <= d /\ d + 8 * cap <= 140737479966720) /\ d mod 8 = 0 /\ (2147446784 + 17592186048512 <= d \/ d + 8 * cap <= 2147446784) /\ 1 <= cap <= 134217728
         /\ (sp - 64 + 64 <= d \/ d + 8 * cap <= sp - 4096) /\ (o + 16 <= d \/ d + 8 * cap <= o)
         /\ (d + 8 * cap <= d / 8 + SB \/ d / 8 + SB + cap <= d) /\ (d + 8 * cap <= 65536 \/ 6500352 <= d);
  mf_dw : L5.writable RSEGS M d (8 * cap);
  mf_dz : L5KA.zeros_at M (d / 8 + SB) cap }.

Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma mfacts_keep M M' sp o d cap :
  mfacts M sp o d cap -> mem_grows M M' ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * cap) -> ~ (o <= i < o + 16) -> ~ (sp - 80 <= i < sp - 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> mfacts M' sp o d cap.
Proof.
  intros [S1 W [I [C1 C2]] O OZ OW D DW DZ] G K.
  constructor; auto.
  - eapply L5.writable_grows; eauto.
  - split. { intros a Ha. rewrite K. apply I. exact Ha. clear - Ha; lia. clear - Ha D O; lia. clear - Ha O; lia. clear - Ha S1; lia. }
    split. eapply L5C.u64_at_agree. 4: exact C1. 2: clear; lia. 2: clear; lia. intros i Hi; apply K. clear - Hi; lia. clear - Hi D O; lia. clear - Hi O; lia. clear - Hi S1; lia.
    eapply u32_at_agree1. 4: exact C2. 2: clear; lia. 2: clear; lia. intros i Hi; apply K. clear - Hi; lia. clear - Hi D O; lia. clear - Hi O; lia. clear - Hi S1; lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact OZ. intros i Hi. apply K. clear - Hi O; unfold SB in *; lia. clear - Hi O D; unfold SB in *; lia. clear - Hi O; unfold SB in *; lia. clear - Hi O S1; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - eapply L5.writable_grows; eauto.
  - eapply L5.writable_grows; eauto.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact DZ. intros i Hi. apply K. clear - Hi D; unfold SB in *; lia. clear - Hi D; unfold SB in *; lia. clear - Hi D O; unfold SB in *; lia. clear - Hi D S1; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Definition KSL : list nat := [2; 3; 4; 8; 9; 14; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma KS_trans (KS : list nat) R R' R'' : (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> (forall x, In x KS -> getr R'' (reg x) = getr R' (reg x)) ->
  forall x, In x KS -> getr R'' (reg x) = getr R (reg x).
Proof. intros A B x Hx. rewrite (B x Hx). apply A. exact Hx. Qed.

(* [comment removed for export] *)
Definition at_mhead (R : bvmap 5 word) (sp o d : Z) (len J : nat) (c X : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 10 /\
  getr R (reg 10) = Z_to_bv 64 (d + 8 * Z.of_nat J - 8) /\ getr R (reg 11) = Z_to_bv 64 d /\ getr R (reg 12) = Z_to_bv 64 (d + 8 * Z.of_nat J) /\
  getr R (reg 13) = Z_to_bv 64 c /\ getr R (reg 14) = Z_to_bv 64 10 /\ getr R (reg 15) = Z_to_bv 64 (d / 8 + 2147450880 + Z.of_nat J - 1) /\
  getr R (reg 16) = Z_to_bv 64 (Z.of_nat len - Z.of_nat J + 1) /\ getr R (reg 18) = Z_to_bv 64 2147450880 /\ getr R (reg 19) = Z_to_bv 64 (Z.of_nat len) /\
  getr R (reg 20) = Z_to_bv 64 X /\ getr R (reg 21) = Z_to_bv 64 (o / 8 + 2147450880).

Import BigFactsDigits.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mloop (k : nat) : forall fx R M (sp o d cap : Z) (len J : nat) (Vv : Z),
  mfacts M sp o d cap -> (1 <= J)%nat -> (J <= len)%nat -> k = (len - J + 1)%nat -> Z.of_nat len + 1 <= cap -> 0 <= Vv < M64 ^ Z.of_nat len ->
  (forall i, (i < J - 1)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (wordi (10 * Vv) i)) ->
  (forall i, (J - 1 <= i <= len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (wordi Vv i)) ->
  at_mhead R sp o d len J (mcarry 10 Vv (J - 1)) (wordi Vv (J - 1)) ->
  exists fx' R' M',
    msteps RSEGS (st fx R HEAD M) (st fx' R' L5ARED.REDUCE M')
    /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 1) = Z_to_bv 64 REDRET
    /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) (wordi (10 * Vv) i))
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * (Z.of_nat len + 1)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros fx R M sp o d cap len J Vv MFM J1 JL Hk CAP VB LOW HIGH AT. { exfalso. clear - Hk J1 JL. lia. }
  pose proof MFM as [[SPR A16] W64 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ].
  destruct AT as (A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16r & A18 & A19 & A20 & A21).
  set (X := wordi Vv (J - 1)) in *. set (c := mcarry 10 Vv (J - 1)) in *.
  assert (RX : 0 <= X < 2 ^ 64) by (subst X; pose proof (wordi_range Vv (J - 1)) as WR; unfold wordZ in WR; rewrite BigFactsBase.M_val in WR; exact WR).
  assert (Rc : 0 <= c <= 9) by (subst c; pose proof (mcarry_bound 10 Vv (J - 1) ltac:(lia)) as CB; clear - CB; lia).
  set (X' := wordi Vv J).
  assert (RX' : 0 <= X' < 2 ^ 64) by (subst X'; pose proof (wordi_range Vv J) as WR; unfold wordZ in WR; rewrite BigFactsBase.M_val in WR; exact WR).
  assert (CJ : L5.u64_at RSEGS M (d + 8 * Z.of_nat J) X'). { subst X'. apply HIGH. clear - JL; lia. }
  pose proof (mul_step Vv (J - 1) ltac:(clear - VB; lia)) as [STW STC]. fold X c in STW, STC. replace (Datatypes.S (J - 1)) with J in STC by (clear - J1; lia).
  unfold M64 in STW, STC. rewrite <- (limb_valE X c RX Rc) in STW. rewrite <- (car_valE X c RX Rc) in STC.
  (* [comment removed for export] *)
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - FRO; lia). assert (FRDp : sp - 64 + 64 <= d \/ d + 8 * cap <= sp - 64) by (clear - FRD; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia).
  assert (HVJ : 1 <= Z.of_nat J <= 134217728) by (clear - J1 JL CAP CAPR; lia). assert (HVCJ : 1 <= cap - Z.of_nat J <= 134217728) by (clear - JL CAP CAPR J1; lia).
  assert (HVL : 1 <= Z.of_nat len <= 134217728) by (clear - J1 JL CAP CAPR; lia).
  destruct k as [|k'].
  - (* [comment removed for export] *)
    assert (EJ : J = len) by (clear - Hk J1 JL; lia). subst J.
    assert (HV52 : 1 <= Z.of_nat len - Z.of_nat len + 1 <= 1) by (clear; lia). assert (HV3440 : 0 <= Z.of_nat len - Z.of_nat len <= 0) by (clear; lia).
    assert (HVCL : 1 <= cap - Z.of_nat len <= 134217728) by exact HVCJ.
    pose proof (amL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 36%nat => d | 37%nat => cap | 38%nat => X | 39%nat => X'
                  | 40%nat => Z.of_nat len | 41%nat => c | 43%nat => U R 1 | 52%nat => Z.of_nat len - Z.of_nat len + 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & lFR & lFZ & (lMS & lKS & lR1 & lR5 & lR6 & lR7 & lR10 & lR11 & lR12 & lR13 & lR15 & lR16 & lR17 & lR20 & lR28 & lCTOP & lCLIMB)).
    exists fx1, R1, M1. split. exact lMS.
    split. { intros x Hx. apply lKS. revert Hx; apply (L5K.incl_b _ KS_amL); vm_compute; reflexivity. }
    split. exact lR10. split. exact lR1.
    split. { intros i Hi. destruct (Nat.eq_dec i len) as [->|NE].
      { rewrite STC in lCTOP. rewrite (mul_top_word 10 Vv len ltac:(unfold wordZ; rewrite BigFactsBase.M_val; clear; lia)) in lCTOP.
        2:{ rewrite BigFactsBase.M_val. exact VB. } replace (d + 8 * Z.of_nat len) with (8 * Z.of_nat len + d) by (clear; lia). exact lCTOP. }
      destruct (Nat.eq_dec i (len - 1)) as [->|NE2].
      { rewrite STW in lCLIMB. replace (d + 8 * Z.of_nat (len - 1)) with (d + 8 * Z.of_nat len - 8) by (clear - J1; lia). exact lCLIMB. }
      eapply L5C.u64_at_agree. 4:{ apply LOW. clear - Hi NE NE2; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia.
      intros j Hj. apply lFZ. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi NE NE2 J1; lia. }
    split. { intros i Hi Hn. apply lFZ. exact Hi. clear - Hn J1; lia. } exact MG1.
  - (* [comment removed for export] *)
    assert (JL2 : (J < len)%nat) by (clear - Hk J1 JL; lia).
    assert (HV52 : 2 <= Z.of_nat len - Z.of_nat J + 1 <= 134217728) by (clear - JL2 HVL J1; lia).
    pose proof (amI_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 36%nat => d | 37%nat => cap | 38%nat => X | 39%nat => X'
                  | 40%nat => Z.of_nat J | 41%nat => c | 43%nat => U R 1 | 52%nat => Z.of_nat len - Z.of_nat J + 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & iFR & iFZ & (iMS & iKS & iR5 & iR6 & iR7 & iR10 & iR12 & iR13 & iR15 & iR16 & iR17 & iR20 & iR28 & iCLIMB)).
    rewrite STW in iCLIMB. rewrite STC in iR13.
    assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep. exact MFM. exact MG1. intros i Hi Hd _ _. apply iFZ. exact Hi. clear - Hd J1 JL CAP; lia. }
    destruct (IH fx1 R1 M1 sp o d cap len (Datatypes.S J) Vv MF1 ltac:(clear; lia) ltac:(clear - JL2; lia) ltac:(clear - Hk JL2 J1; lia) CAP VB) as (fx' & R' & M' & MS & K & R10' & R1' & LIMBS & FR' & GR').
    + intros i Hi. destruct (Nat.eq_dec i (J - 1)) as [->|NE].
      { replace (d + 8 * Z.of_nat (J - 1)) with (d + 8 * Z.of_nat J - 8) by (clear - J1; lia). exact iCLIMB. }
      eapply L5C.u64_at_agree. 4:{ apply LOW. clear - Hi NE; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi JL; lia.
      intros j Hj. apply iFZ. clear - Hj DR CAPR CAP Hi JL; lia. clear - Hj Hi NE J1; lia.
    + intros i Hi. eapply L5C.u64_at_agree. 4:{ apply HIGH. clear - Hi; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia.
      intros j Hj. apply iFZ. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi J1; lia.
    + unfold at_mhead. replace (Datatypes.S J - 1)%nat with J by (clear; lia). fold X'.
      assert (KK : forall x, In x [2; 8; 9; 11; 14; 18; 19; 21]%nat -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. apply iKS. revert Hx; apply (L5K.incl_b _ KS_amI); vm_compute; reflexivity. }
      repeat split.
      * rewrite (KK 2%nat) by inl; exact A2. * rewrite (KK 8%nat) by inl; exact A8. * rewrite (KK 9%nat) by inl; exact A9.
      * rewrite iR10. f_equal. clear; lia. * rewrite (KK 11%nat) by inl; exact A11. * rewrite iR12. f_equal. clear; lia.
      * rewrite <- iR13. symmetry. apply Z_to_bv_bv_unsigned. * rewrite (KK 14%nat) by inl; exact A14. * rewrite iR15. f_equal. clear; lia.
      * rewrite iR16. f_equal. clear; lia. * rewrite (KK 18%nat) by inl; exact A18. * rewrite (KK 19%nat) by inl; exact A19.
      * exact iR20. * rewrite (KK 21%nat) by inl; exact A21.
    + exists fx', R', M'. split. { eapply msteps_trans. exact iMS. exact MS. }
      split. { intros x Hx. rewrite (K x Hx). apply iKS. revert Hx; apply (L5K.incl_b _ KS_amI); vm_compute; reflexivity. }
      split. exact R10'. split. exact R1'. split. exact LIMBS.
      split. { intros i Hi Hn. rewrite (FR' i Hi Hn). apply iFZ. exact Hi. clear - Hn J1 JL; lia. }
      eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSC : list nat := [3; 4; 22; 23; 24; 25; 26; 27]%nat.
Definition KSP : list nat := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma in_firstn {A} (x : A) : forall n (l : list A), In x (firstn n l) -> In x l.
Proof. induction n as [|n IH]; intros [|y l] H; cbn in H; try contradiction. destruct H as [->|H]. left; reflexivity. right. apply IH. exact H. Qed.

(* [comment removed for export] *)
Definition st_after (sto : L5.bstore) (len : nat) (Vv : Z) : L5.bstore :=
  match sto with
  | L5.BInl _ v1 => L5.BInl (wordi (10 * Vv) 0) (if Nat.eqb len 0 then v1 else wordi (10 * Vv) 1)
  | L5.BDyn c q => L5.BDyn c q
  end.

Theorem mul10_core fx R M (sp o r x0 fb : Z) (len : nat) (sto : L5.bstore) (wsR : list Z) (v8 v9 v18 v19 v20 v21 : Z) :
  let b := L5.BO fb (Datatypes.S len) sto in let d := L5.bo_data o b in let cap := L5.bo_cap b in let Vv := BigFactsBase.val wsR in
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 10 -> getr R (reg 18) = Z_to_bv 64 SB ->
  getr R (reg 19) = Z_to_bv 64 (Z.of_nat len) -> getr R (reg 20) = Z_to_bv 64 x0 -> 0 <= x0 < 2 ^ 64 -> ((1 <= len)%nat -> x0 = nth 0 wsR 0) ->
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
    /\ (let wl := wlist (10 * Vv) (Datatypes.S len) in let n' := L5W.rlen wl in
        L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land fb 253 else fb) n' (st_after sto len Vv)) /\ L5.limbs_at RSEGS M' d wl)
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (o <= a < o + 16) -> ~ (sp - 80 <= a < sp - 64) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.
Proof.
  cbn zeta. intros G2 G8 G9 G18 G19 G20 RX0 X0 G21 C8 RA C16 C24 C32 C40 C48 C56 R8 R9 R18 R19 R20 R21 MFM W80 OB OL TOP0 CAP ODYN.
  pose proof MFM as [[SPR A16] W64 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG) DW DZ].
  unfold L5.bo_data, L5.bo_cap in *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  set (d := match sto with L5.BInl _ _ => o + 16 | L5.BDyn _ q => q end) in *.
  set (cap := match sto with L5.BInl _ _ => 2 | L5.BDyn c _ => c end) in *.
  pose proof OB as (O0 & Ffb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Ffb, O8, OST. destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
  set (Vv := BigFactsBase.val wsR) in *.
  assert (WO : words_ok wsR) by exact Rws.
  assert (WS : L5.limbs_at RSEGS M d wsR).
  { subst d. destruct sto as [w0 w1|c q]. 2: exact LAT. destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). rewrite LAT. intros i Hi. rewrite length_firstn in Hi. cbn [length Nat.min] in Hi.
    destruct i as [|[|i]]. { cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by (clear; lia). exact O16. }
    { destruct len as [|ly]. exfalso; clear - Hi; lia. cbn [firstn nth]. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by (clear; lia). exact O24. }
    exfalso. destruct len as [|[|ly]]; cbn in Hi; clear - Hi Hl2; lia. }
  assert (NTH : forall i, (i <= len)%nat -> nth i wsR 0 = wordi Vv i).
  { intros i Hi. rewrite <- (wlist_nth' Vv (Datatypes.S len) i) by (clear - Hi; lia). subst Vv. rewrite <- Lws. rewrite (wlist_val wsR WO). reflexivity. }
  assert (VB : 0 <= Vv < M64 ^ Z.of_nat len).
  { subst Vv. rewrite <- (val_firstn_zeros wsR len). 2: rewrite Lws; clear; lia. 2:{ intros i Hi. rewrite Lws in Hi. replace i with len by (clear - Hi; lia). exact TOP0. }
    pose proof (BigFactsBase.val_bound (firstn len wsR) ltac:(apply Forall_forall; intros w Hw; apply (proj1 (Forall_forall _ _) WO w); eapply in_firstn; exact Hw)) as VB0.
    rewrite length_firstn, Lws, Nat.min_l in VB0 by (clear; lia). unfold M64. rewrite BigFactsBase.M_val in VB0. exact VB0. }
  assert (LIMBS : forall i, (i <= len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (wordi Vv i)). { intros i Hi. rewrite <- NTH by exact Hi. apply WS. rewrite Lws. clear - Hi; lia. }
  assert (ALS : aligned sp 16) by exact A16. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - FRO; lia). assert (FRDp : sp - 64 + 64 <= d \/ d + 8 * cap <= sp - 64) by (clear - FRD; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia). assert (HVF : 0 <= fb <= 255) by (clear - Ffb; lia).
  assert (HVL : 0 <= Z.of_nat len <= 134217728) by (clear - CAP CAPR; lia). assert (HVCL : 1 <= cap - Z.of_nat len <= 134217728) by (clear - CAP CAPR; lia).
  set (wl := wlist (10 * Vv) (Datatypes.S len)).
  assert (WLL : length wl = Datatypes.S len) by (subst wl; apply BigFactsDigits.wlist_length).
  (* [comment removed for export] *)
  assert (PART1 : exists fx1 R1 M1, msteps RSEGS (st fx R RZRET M) (st fx1 R1 L5ARED.REDUCE M1)
      /\ (forall x, In x KSP -> getr R1 (reg x) = getr R (reg x)) /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 1) = Z_to_bv 64 REDRET
      /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat i) (wordi (10 * Vv) i))
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ mem_grows M M1).
  { destruct (Nat.eq_dec len 0) as [L0|Lpos].
    - (* [comment removed for export] *)
      assert (HVL0 : 0 <= Z.of_nat len <= 0) by (clear - L0; lia).
      assert (RUN : exists fx1 R1 M1, mem_grows M M1 /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (d + 0 <= i < d + 0 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
               /\ msteps RSEGS (st fx R 0x8f094 M) (st fx1 R1 0x90780 M1) /\ (forall x, In x KSP -> getr R1 (reg x) = getr R (reg x))
               /\ getr R1 (reg 1) = Z_to_bv 64 586108 /\ getr R1 (reg 10) = Z_to_bv 64 o /\ L5.u64_at RSEGS M1 d 0).
      { subst d cap. destruct sto as [w0 w1|c q].
        + destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1).
          pose proof (amZi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 42%nat => x0 | 43%nat => U R 1 | 51%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
          feed P ltac:(first [apply UR | apply U_to | sc]).
          destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR1 & zR10 & zR11 & zR13 & zQ)).
          exists fx1, R1, M1. split. exact MG1. split. { intros i Hi Hn. apply zFZ. exact Hi. clear - Hn; lia. } split. exact zMS.
          split. { intros x Hx. apply zKS. revert Hx; apply (L5K.incl_b _ KS_amZi); vm_compute; reflexivity. } split. exact zR1. split. exact zR10. exact zQ.
        + destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
          pose proof (amZd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => c | 42%nat => x0 | 43%nat => U R 1 | 51%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
          assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia). assert (HVC : 0 <= c < 2 ^ 64) by (clear - Hcap; lia).
          feed P ltac:(first [apply UR | apply U_to | sc]).
          destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR1 & zR10 & zR11 & zR13 & zQ)).
          exists fx1, R1, M1. split. exact MG1. split. exact zFZ. split. exact zMS.
          split. { intros x Hx. apply zKS. revert Hx; apply (L5K.incl_b _ KS_amZd); vm_compute; reflexivity. } split. exact zR1. split. exact zR10. exact zQ. }
      destruct RUN as (fx1 & R1 & M1 & MG1 & FZ1 & MS1 & K1 & R1_1 & R1_10 & Q0).
      exists fx1, R1, M1. split. exact MS1. split. exact K1. split. exact R1_10. split. exact R1_1.
      split. { intros i Hi. replace i with 0%nat by (clear - Hi L0; lia). replace (wordi (10 * Vv) 0) with 0. replace (d + 8 * Z.of_nat 0) with d by (clear; lia). exact Q0.
               replace Vv with 0. reflexivity. subst Vv. symmetry. rewrite <- (val_firstn_zeros wsR 0). reflexivity. rewrite Lws; clear; lia.
               intros i0 Hi0. rewrite Lws, L0 in Hi0. replace i0 with 0%nat by (clear - Hi0; lia). rewrite <- L0. exact TOP0. }
      split. { intros a Ha Hn. apply FZ1. exact Ha. clear - Hn; lia. } exact MG1.
    - (* [comment removed for export] *)
      assert (HVL1 : 1 <= Z.of_nat len <= 134217728) by (clear - Lpos HVL; lia).
      assert (EX0 : x0 = wordi Vv 0). { rewrite (X0 ltac:(clear - Lpos; lia)). apply NTH. clear; lia. }
      assert (RUN : exists fx1 R1 M1, mem_grows M M1 /\ (forall a : word, M1 a = M a)
               /\ msteps RSEGS (st fx R 0x8f094 M) (st fx1 R1 0x8f0ec M1) /\ (forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
               /\ getr R1 (reg 10) = Z_to_bv 64 d /\ getr R1 (reg 11) = Z_to_bv 64 d /\ getr R1 (reg 12) = Z_to_bv 64 (d + 8) /\ getr R1 (reg 13) = Z_to_bv 64 0
               /\ getr R1 (reg 14) = Z_to_bv 64 10 /\ getr R1 (reg 15) = Z_to_bv 64 (d / 8 + 2147450880) /\ getr R1 (reg 16) = Z_to_bv 64 (Z.of_nat len)).
      { subst d cap. destruct sto as [w0 w1|c q].
        + destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). assert (HVL2 : 1 <= Z.of_nat len <= 2) by (clear - Lpos Hl2; lia).
          pose proof (amBi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 42%nat => x0 | 43%nat => U R 1 | 51%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
          feed P ltac:(first [apply UR | apply U_to | sc]).
          destruct P as (fx1 & R1 & M1 & MG1 & bFR & bFZ & (bMS & bKS & bR10 & bR11 & bR12 & bR13 & bR14 & bR15 & bR16)).
          exists fx1, R1, M1. split. exact MG1. split. exact bFR. split. exact bMS.
          split. { intros x Hx. apply bKS. revert Hx; apply (L5K.incl_b _ KS_amBi); vm_compute; reflexivity. }
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          repeat split; try assumption; (first [rewrite bR10 | rewrite bR11 | rewrite bR12 | rewrite bR15 | rewrite bR16]; f_equal; clear - O8a; lia).
        + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
          assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia). assert (HVC : 0 <= c < 2 ^ 64) by (clear - Hcap; lia).
          pose proof (amBd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len | 35%nat => fb | 36%nat => q | 37%nat => c | 42%nat => x0 | 43%nat => U R 1 | 51%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
          feed P ltac:(first [apply UR | apply U_to | sc]).
          destruct P as (fx1 & R1 & M1 & MG1 & bFR & bFZ & (bMS & bKS & bR10 & bR11 & bR12 & bR13 & bR14 & bR15 & bR16)).
          exists fx1, R1, M1. split. exact MG1. split. exact bFR. split. exact bMS.
          split. { intros x Hx. apply bKS. revert Hx; apply (L5K.incl_b _ KS_amBd); vm_compute; reflexivity. }
          repeat split; try assumption; (first [rewrite bR10 | rewrite bR11 | rewrite bR12 | rewrite bR15 | rewrite bR16]; f_equal; clear - Q8; lia). }
      destruct RUN as (fx1 & R1 & M1 & MG1 & FR1 & MS1 & K1 & B10 & B11 & B12 & B13 & B14 & B15 & B16).
      assert (EM1 : M1 = M). { apply functional_extensionality. exact FR1. } subst M1.
      destruct (mloop len fx1 R1 M sp o d cap len 1 Vv MFM ltac:(clear; lia) ltac:(clear - Lpos; lia) ltac:(clear - Lpos; lia) CAP VB) as (fx2 & R2 & M2 & MS2 & K2 & R2_10 & R2_1 & LIMBS2 & FR2 & GR2).
      { intros i Hi. exfalso. clear - Hi. lia. }
      { intros i Hi. apply LIMBS. clear - Hi; lia. }
      { unfold at_mhead. replace (1 - 1)%nat with 0%nat by reflexivity. rewrite mcarry_0. rewrite <- EX0. change (Z.of_nat 1) with 1.
        repeat split; try (first [assumption | rewrite (K1 _) by inl; assumption]).
        all: first [rewrite B10 | rewrite B12 | rewrite B15 | rewrite B16]; f_equal; clear; lia. }
      exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. exact MS2. }
      split. { intros x Hx. rewrite (K2 x). apply K1. revert Hx; apply (L5K.incl_b KSP); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSP); vm_compute; reflexivity. }
      split. exact R2_10. split. exact R2_1. split. exact LIMBS2. split. exact FR2. exact GR2. }
  destruct PART1 as (fx1 & R1 & M1 & MS1 & K1 & R1_10 & R1_1 & LIMBS1 & FR1 & GR1).

  assert (MF1 : mfacts M1 sp o d cap). { eapply mfacts_keep. exact MFM. exact GR1. intros i Hi Hd _ _. apply FR1. exact Hi. clear - Hd CAP CAPR; lia. }
  pose proof MF1 as [_ W64a [IMGC1 [CSB1 CUAR1]] _ OZ1 OW1 _ DW1 DZ1].
  assert (W80a : L5.writable RSEGS M1 (sp - 64 - 16) 16). { replace (sp - 64 - 16) with (sp - 80) by (clear; lia). eapply L5.writable_grows. exact GR1. exact W80. }
  assert (HDR1 : forall a v, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR1. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb OD CAP; lia. }
  assert (FB1 : L5.u8_at RSEGS M1 o fb). { eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FR1. clear - Hj OR; lia. clear - Hj OD CAP; lia. }
  set (b1 := L5.BO fb (Datatypes.S len) (st_after sto len Vv)).
  assert (OB1 : L5.big_at RSEGS M1 o b1 /\ L5C.obj_limbs RSEGS M1 b1 wl).
  { subst b1 d cap. unfold L5.big_at, L5C.obj_limbs, st_after. cbn [L5.bo_fb L5.bo_len L5.bo_st]. destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). split.
      + split. exact FB1. split. exact Ffb. split. { apply HDR1. clear; lia. clear; lia. exact O8. } split. exact B0.
        split. { replace (o + 16) with (o + 16 + 8 * Z.of_nat 0) by (clear; lia). apply LIMBS1. clear; lia. }
        split. { destruct (Nat.eqb len 0) eqn:EL. apply Nat.eqb_eq in EL. eapply L5C.u64_at_agree. 4: exact O24. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FR1. clear - Hj OR; lia. rewrite EL. clear - Hj; lia.
                 apply Nat.eqb_neq in EL. replace (o + 24) with (o + 16 + 8 * Z.of_nat 1) by (clear; lia). apply LIMBS1. clear - EL; lia. }
        split. exact Hl2. split. { pose proof (wordi_range (10 * Vv) 0) as WR. unfold wordZ in WR. rewrite BigFactsBase.M_val in WR. exact WR. }
        destruct (Nat.eqb len 0). exact Rw1. pose proof (wordi_range (10 * Vv) 1) as WR. unfold wordZ in WR. rewrite BigFactsBase.M_val in WR. exact WR.
      + split. exact WLL. split. apply Forall_wlist. subst wl. destruct len as [|[|k]]. reflexivity. reflexivity. exfalso; clear - Hl2; lia.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). split.
      + split. exact FB1. split. exact Ffb. split. { apply HDR1. clear; lia. clear; lia. exact O8. } split. exact B1.
        assert (HDR2 : forall a v, o + 16 <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
        { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR1. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb ODYN CAP; lia. }
        split. { apply HDR2. clear; lia. clear; lia. exact O16. } split. { apply HDR2. clear; lia. clear; lia. exact O24. }
        split. exact Hlc. split. exact Hcap. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH.
      + split. exact WLL. split. apply Forall_wlist. intros i Hi. rewrite WLL in Hi. unfold wl. rewrite (wlist_nth' (10 * Vv) (Datatypes.S len) i Hi). apply LIMBS1. clear - Hi; lia. }
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
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  cbn zeta in OB2. replace (L5.bo_fb b1) with fb in OB2 by reflexivity. replace (L5.bo_st b1) with (st_after sto len Vv) in OB2 by reflexivity.
  assert (MF2 : mfacts M2 sp o d cap). { eapply mfacts_keep. exact MF1. exact GR2. intros i Hi _ Ho Hs. apply FR2. exact Hi. exact Ho. clear - Hs; lia. }
  pose proof MF2 as [_ W64b [IMGC2 [CSB2 CUAR2]] _ _ _ _ _ _].
  assert (XF : forall a v, sp - 64 <= a -> a <= sp - 8 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. rewrite FR2. apply FR1.
    clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb FRD CAP; lia. clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb FRO; lia. clear - Hj Ha Hb; lia. }
  assert (HVR : 0 <= r < 2 ^ 64) by (clear - RA; destruct RA; lia).
  (* [comment removed for export] *)
  pose proof (amE_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => o | 43%nat => U R2 1 | 44%nat => r | 45%nat => v8 | 46%nat => v9 | 47%nat => v18 | 48%nat => v19 | 49%nat => v20 | 50%nat => v21 | _ => 0 end)) as P.
  cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XF; [clear; lia | clear; lia | sc]) ]).
  destruct P as (fx3 & R3 & M3 & MG3 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21)).
  assert (EM3 : M3 = M2). { apply functional_extensionality. exact eFR. } subst M3.
  pose proof (ret_to fx3 R3 M2 0x8f1a0 W_8f1a0 r F_8f1a0 eq_refl D_8f1a0 eR1 (proj1 RA) (proj2 RA)) as RET.
  exists fx3, R3, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact eMS. exact RET. }
  split. { intros x Hx. rewrite (eKS x). rewrite (K2 x). apply K1. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity.
           revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSC); vm_compute; reflexivity. }
  split. exact eR2. split. exact eR10. split. exact eR8. split. exact eR9. split. exact eR18. split. exact eR19. split. exact eR20. split. exact eR21.
  split. { split. exact OB2. intros i Hi. rewrite WLL in Hi. eapply L5C.u64_at_agree. 4:{ unfold wl. rewrite (wlist_nth' (10 * Vv) (Datatypes.S len) i Hi). apply LIMBS1. clear - Hi; lia. }
           2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia. intros j Hj. apply FR2. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi CAP OD; lia. clear - Hj Hi CAP FRD; lia. }
  split. { intros a Ha Hd Ho Hs. rewrite FR2. apply FR1. exact Ha. exact Hd. exact Ha. exact Ho. clear - Hs; lia. }
  eapply mem_grows_trans. exact GR1. exact GR2.
Qed.

End SCFG_1.
End L5AMULK.
