(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun Bo0_code_8f368_90368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5Mul10W L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BRedP L5BRed L5BAdddP.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AADDK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AADDP. Import L5MULW.
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

Definition RZRET : Z := 0x8f778. Definition BR1 : Z := 0x8f8a0. Definition BR2 : Z := 0x8f8a4. Definition SETUP : Z := 0x8f8a8. Definition HEAD : Z := 0x8f8ac.
Definition BR3 : Z := 0x8f8f4. Definition STEP : Z := 0x8f8f8. Definition BR4 : Z := 0x8f8fc. Definition CALLRED : Z := 0x8f900. Definition REDRET : Z := 0x8f908.

Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.
Lemma r12' : (12%bv : bv 5) = reg 12. Proof. apply bv_eq; reflexivity. Qed.
Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.
Lemma r14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq; reflexivity. Qed.
Lemma r20 : (20%bv : bv 5) = reg 20. Proof. apply bv_eq; reflexivity. Qed.
Lemma r21 : (21%bv : bv 5) = reg 21. Proof. apply bv_eq; reflexivity. Qed.
Lemma r25 : (25%bv : bv 5) = reg 25. Proof. apply bv_eq; reflexivity. Qed.
Lemma r26 : (26%bv : bv 5) = reg 26. Proof. apply bv_eq; reflexivity. Qed.
Local Ltac ulit := rewrite ?L5.unsigned_lit by lia.
(* [comment removed for export] *)
Local Lemma fz segs (p : word) (z : Z) w : fetch_word segs p = Some w -> p = Z_to_bv 64 z -> fetch_word segs (Z_to_bv 64 z) = Some w.
Proof. intros H E. rewrite <- E. exact H. Qed.
Lemma br1_tk fx R M a b : getr R (reg 21) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a < b ->
  msteps RSEGS (st fx R BR1 M) (st fx R CALLRED M).
Proof. intros Ha Hb Ra Rb Hlt. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 CALLRED) with (btgt (Z_to_bv 64 BR1) (bv_signed (96%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
  eapply (step_bltu_tk RSEGS R _ M _ _ 21%bv 12%bv _ (fz _ _ BR1 _ F_8f8a0 ltac:(apply bv_eq; reflexivity)) eq_refl D_8f8a0). rewrite r21, r12', Ha, Hb. unfold c_ltu, bv_ltu. ulit. apply Z.ltb_lt. exact Hlt. Qed.
Lemma br1_ft fx R M a b : getr R (reg 21) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a ->
  msteps RSEGS (st fx R BR1 M) (st fx R BR2 M).
Proof. intros Ha Hb Ra Rb Hle. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 BR2) with (v_addi (Z_to_bv 64 BR1) 4) by (apply bv_eq; reflexivity).
  eapply (step_bltu_ft RSEGS R _ M _ _ 21%bv 12%bv _ (fz _ _ BR1 _ F_8f8a0 ltac:(apply bv_eq; reflexivity)) eq_refl D_8f8a0). rewrite r21, r12', Ha, Hb. unfold c_ltu, bv_ltu. ulit. apply Z.ltb_ge. exact Hle. Qed.
Lemma br2_tk fx R M a b : getr R (reg 20) = Z_to_bv 64 a -> getr R (reg 11) = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a ->
  msteps RSEGS (st fx R BR2 M) (st fx R CALLRED M).
Proof. intros Ha Hb Ra Rb Hle. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 CALLRED) with (btgt (Z_to_bv 64 BR2) (bv_signed (92%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
  eapply (step_bgeu_tk RSEGS R _ M _ _ 20%bv 11%bv _ (fz _ _ BR2 _ F_8f8a4 ltac:(apply bv_eq; reflexivity)) eq_refl D_8f8a4). rewrite r20, r11, Ha, Hb. unfold c_ltu, bv_ltu. ulit. apply Z.ltb_ge. exact Hle. Qed.
Lemma br2_ft fx R M a b : getr R (reg 20) = Z_to_bv 64 a -> getr R (reg 11) = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a < b ->
  msteps RSEGS (st fx R BR2 M) (st fx R SETUP M).
Proof. intros Ha Hb Ra Rb Hlt. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 SETUP) with (v_addi (Z_to_bv 64 BR2) 4) by (apply bv_eq; reflexivity).
  eapply (step_bgeu_ft RSEGS R _ M _ _ 20%bv 11%bv _ (fz _ _ BR2 _ F_8f8a4 ltac:(apply bv_eq; reflexivity)) eq_refl D_8f8a4). rewrite r20, r11, Ha, Hb. unfold c_ltu, bv_ltu. ulit. apply Z.ltb_lt. exact Hlt. Qed.
Lemma br3_tk fx R M a b : getr R (reg 25) = Z_to_bv 64 a -> getr R (reg 21) = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a ->
  msteps RSEGS (st fx R BR3 M) (st fx R CALLRED M).
Proof. intros Ha Hb Ra Rb Hle. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 CALLRED) with (btgt (Z_to_bv 64 BR3) (bv_signed (12%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
  eapply (step_bgeu_tk RSEGS R _ M _ _ 25%bv 21%bv _ (fz _ _ BR3 _ F_8f8f4 ltac:(apply bv_eq; reflexivity)) eq_refl D_8f8f4). rewrite r25, r21, Ha, Hb. unfold c_ltu, bv_ltu. ulit. apply Z.ltb_ge. exact Hle. Qed.
Lemma br3_ft fx R M a b : getr R (reg 25) = Z_to_bv 64 a -> getr R (reg 21) = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a < b ->
  msteps RSEGS (st fx R BR3 M) (st fx R STEP M).
Proof. intros Ha Hb Ra Rb Hlt. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 STEP) with (v_addi (Z_to_bv 64 BR3) 4) by (apply bv_eq; reflexivity).
  eapply (step_bgeu_ft RSEGS R _ M _ _ 25%bv 21%bv _ (fz _ _ BR3 _ F_8f8f4 ltac:(apply bv_eq; reflexivity)) eq_refl D_8f8f4). rewrite r25, r21, Ha, Hb. unfold c_ltu, bv_ltu. ulit. apply Z.ltb_lt. exact Hlt. Qed.
Lemma br4_tk fx R M : getr R (reg 26) = Z_to_bv 64 0 -> msteps RSEGS (st fx R BR4 M) (st fx R HEAD M).
Proof. intros H. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 HEAD) with (btgt (Z_to_bv 64 BR4) (bv_signed (8112%bv : bv 13))) by (apply bv_eq; vm_compute; reflexivity).
  eapply (step_beq_tk RSEGS R _ M _ _ 26%bv 0%bv _ (fz _ _ BR4 _ F_8f8fc ltac:(apply bv_eq; reflexivity)) eq_refl D_8f8fc). rewrite getr_zero, r26, H. unfold c_eq. rewrite bv_eqb_refl. reflexivity. Qed.
Lemma br4_ft fx R M a : getr R (reg 26) = Z_to_bv 64 a -> 0 < a < 2 ^ 64 -> msteps RSEGS (st fx R BR4 M) (st fx R CALLRED M).
Proof. intros H Ha. eapply mst_step; [reflexivity | | apply mst_refl].
  replace (Z_to_bv 64 CALLRED) with (v_addi (Z_to_bv 64 BR4) 4) by (apply bv_eq; reflexivity).
  eapply (step_beq_ft RSEGS R _ M _ _ 26%bv 0%bv _ (fz _ _ BR4 _ F_8f8fc ltac:(apply bv_eq; reflexivity)) eq_refl D_8f8fc). rewrite getr_zero, r26, H. unfold c_eq. apply bv_eqb_neq.
  intros E. apply (f_equal bv_unsigned) in E. rewrite !L5.unsigned_lit in E by lia. lia. Qed.

(* [comment removed for export] *)
Record afacts (M : word -> option byte) (sp o d cap F fl : Z) : Prop := AF {
  af_sp : 140735332487424 <= sp <= 140737488355328 /\ sp mod 32 = 0;
  af_w : L5.writable RSEGS M (sp - 176) 176;
  af_st : L5.img_clear M 860160 884736 /\ L5.u64_at RSEGS M 911160 2147450880 /\ L5.u32_at RSEGS M 911168 1;
  af_o : 6504448 <= o <= 140737488355296 /\ o mod 8 = 0 /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) /\ (sp <= o \/ o + 32 <= sp - 4096);
  af_oz : L5KA.zeros_at M (o / 8 + SB) 4;
  af_ow : L5.writable RSEGS M o 32;
  af_d : (4096 <= d /\ d + 8 * cap <= 140737479966720) /\ d mod 8 = 0 /\ (2147446784 + 17592186048512 <= d \/ d + 8 * cap <= 2147446784) /\ 1 <= cap <= 134217728
         /\ (sp <= d \/ d + 8 * cap <= sp - 4096) /\ (o + 16 <= d \/ d + 8 * cap <= o)
         /\ (d + 8 * cap <= d / 8 + SB \/ d / 8 + SB + cap <= d) /\ (d + 8 * cap <= 65536 \/ 6504448 <= d)
         /\ (F + 128 <= d \/ d + 8 * cap <= F) /\ (fl + 1 <= d \/ d + 8 * cap <= fl);
  af_dw : L5.writable RSEGS M d (8 * cap);
  af_dz : L5KA.zeros_at M (d / 8 + SB) cap;
  af_vz : L5KA.zeros_at M ((sp - 128) / 8 + SB) 1 }.

Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.
Lemma afacts_keep M M' sp o d cap F fl :
  afacts M sp o d cap F fl -> mem_grows M M' ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * cap) -> ~ (o <= i < o + 16) -> ~ (sp - 176 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> afacts M' sp o d cap F fl.
Proof.
  intros [S1 W [I [C1 C2]] O OZ OW D DW DZ VZ] G K.
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
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact VZ. intros i Hi. apply K.
    clear - Hi S1; unfold SB in *; lia. clear - Hi S1 D; unfold SB in *; lia. clear - Hi S1 O; unfold SB in *; lia. clear - Hi S1; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Definition KSQ : list nat := [2; 3; 4; 8; 9; 18; 19; 22; 23; 27]%nat.
Lemma KS_trans (KS : list nat) R R' R'' : (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> (forall x, In x KS -> getr R'' (reg x) = getr R' (reg x)) ->
  forall x, In x KS -> getr R'' (reg x) = getr R (reg x).
Proof. intros A B x Hx. rewrite (B x Hx). apply A. exact Hx. Qed.

(* [comment removed for export] *)
Definition in_regs (R : bvmap 5 word) (sp o y F : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R (reg 8) = Z_to_bv 64 sp /\ getr R (reg 9) = Z_to_bv 64 (sp - 160) /\ getr R (reg 18) = Z_to_bv 64 F /\
  getr R (reg 19) = Z_to_bv 64 o /\ getr R (reg 21) = Z_to_bv 64 (o + 8) /\ getr R (reg 22) = Z_to_bv 64 (F / 8 + 2147450880) /\
  getr R (reg 23) = Z_to_bv 64 F /\ getr R (reg 25) = Z_to_bv 64 ((o + 8) / 8 + 2147450880) /\ getr R (reg 26) = Z_to_bv 64 (o / 8 + 2147450880).
(* [comment removed for export] *)
Definition in_regsL (R : bvmap 5 word) (sp o F : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R (reg 8) = Z_to_bv 64 sp /\ getr R (reg 9) = Z_to_bv 64 (sp - 160) /\ getr R (reg 18) = Z_to_bv 64 F /\
  getr R (reg 19) = Z_to_bv 64 o /\ getr R (reg 22) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R (reg 23) = Z_to_bv 64 F /\ getr R (reg 24) = Z_to_bv 64 2147450880.
(* [comment removed for export] *)
Definition at_chead (R : bvmap 5 word) (M : word -> option byte) (sp d len : Z) (I : nat) : Prop :=
  getr R (reg 21) = Z_to_bv 64 (len + 1) /\ getr R (reg 25) = Z_to_bv 64 (Z.of_nat I + 1) /\ L5.u64_at RSEGS M (sp - 128) d /\ L5.u64_at RSEGS M (sp - 120) (len + 1).

Import BigFactsDigits.
Lemma wordi_bound v i : 0 <= wordi v i < 2 ^ 64.
Proof. pose proof (wordi_range v i) as WR. unfold wordZ in WR. rewrite BigFactsBase.M_val in WR. exact WR. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cloop (k : nat) : forall fx R M (sp o y F fl d cap : Z) (len I : nat) (Vv : Z),
  afacts M sp o d cap F fl -> in_regsL R sp o F -> 0 <= y <= 9 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
  (1 <= I)%nat -> (I <= len)%nat -> k = (len + 1 - I)%nat -> Z.of_nat len + 1 <= cap -> 0 <= Vv < (2 ^ 64) ^ Z.of_nat len ->
  acarry y Vv I = 1 ->
  (forall i, (i < I)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (wordi (Vv + y) i)) ->
  (forall i, (I <= i <= len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (wordi Vv i)) ->
  at_chead R M sp d (Z.of_nat len) I ->
  exists fx' R' M',
    msteps RSEGS (st fx R HEAD M) (st fx' R' CALLRED M')
    /\ (forall x, In x KSQ -> getr R' (reg x) = getr R (reg x))
    /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M' (d + 8 * Z.of_nat i) (wordi (Vv + y) i))
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * (Z.of_nat len + 1)) -> ~ (sp - 168 <= i < sp - 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros fx R M sp o y F fl d cap len I Vv AFM IR HY HF HFL I1 IL Hk CAP VB AC LOW HIGH AT. { exfalso. clear - Hk I1 IL. lia. }
  pose proof AFM as [[SPR A32] W176 [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG & DF & DFL) DW DZ VZ].
  destruct IR as (G2 & G8 & G9 & G18 & G19 & G22 & G23 & G24). destruct AT as (A21 & A25 & VD & VN).
  set (X := wordi Vv I) in *. pose proof (wordi_bound Vv I) as RX. fold X in RX.
  assert (CI : L5.u64_at RSEGS M (d + 8 * Z.of_nat I) X). { subst X. apply HIGH. clear - IL; lia. }
  pose proof (add_limbS y Vv I ltac:(unfold wordZ; rewrite BigFactsBase.M_val; clear - HY; lia) ltac:(clear - VB; lia) I1) as [STW STC].
  fold X in STW, STC. rewrite AC in STW, STC. cbn [Z.eqb] in STC. change (1 =? 1) with true in STC. cbn iota in STC.
  unfold BigModel.W.add, BigModel.W.wrap in STW, STC. rewrite BigFactsBase.M_val in STW, STC. change 18446744073709551616 with (2 ^ 64) in STW, STC.
  assert (ALS : aligned sp 32) by exact A32. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 176 + 176 <= o \/ o + 32 <= sp - 176) by (clear - FRO; lia). assert (FRDp : sp - 176 + 176 <= d \/ d + 8 * cap <= sp - 176) by (clear - FRD; lia).
  assert (DIMGp : 65536 + 6438912 <= d \/ d + 8 * cap <= 65536) by (clear - DIMG; lia).
  assert (HV2 : 140735332487344 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia).
  assert (HVI : 1 <= Z.of_nat I <= 134217727) by (clear - I1 IL CAP CAPR; lia). assert (HVCI : 1 <= cap - Z.of_nat I <= 134217728) by (clear - IL CAP CAPR I1; lia).
  assert (HVL : 1 <= Z.of_nat len + 1 <= 134217728) by (clear - I1 IL CAP CAPR; lia).
  assert (VZp : L5KA.zeros_at M ((sp - 128) / 8 + 2147450880) 1) by exact VZ.
  (* [comment removed for export] *)
  pose proof (adL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len + 1 | 36%nat => d | 37%nat => cap | 38%nat => X
                | 40%nat => F | 41%nat => fl | 42%nat => Z.of_nat I | 43%nat => U R 1 | 57%nat => U R 26 | 58%nat => U R 20 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1 & MG1 & lFR & lFZ & (lMS & lKS & lR1 & lR10 & lR11 & lR12 & lR13 & lR14 & lR20 & lR26 & lC & lCRA)).
  rewrite STW in lC.
  assert (AF1 : afacts M1 sp o d cap F fl). { eapply afacts_keep. exact AFM. exact MG1. intros i Hi Hd _ Hs. apply lFZ. exact Hi. clear - Hd I1 IL CAP; lia. clear - Hs; lia. }
  assert (LOW1 : forall i, (i <= I)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat i) (wordi (Vv + y) i)).
  { intros i Hi. destruct (Nat.eq_dec i I) as [->|NE]. exact lC.
    eapply L5C.u64_at_agree. 4:{ apply LOW. clear - Hi NE; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi IL; lia. intros j Hj. apply lFZ. clear - Hj DR CAPR CAP Hi IL; lia. clear - Hj Hi NE; lia.
    clear - Hj Hi IL CAP FRD; lia. }
  assert (HIGH1 : forall i, (I < i <= len)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat i) (wordi Vv i)).
  { intros i Hi. eapply L5C.u64_at_agree. 4:{ apply HIGH. clear - Hi; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia. intros j Hj. apply lFZ. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi; lia.
    clear - Hj Hi CAP FRD; lia. }
  assert (KEEP : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Hb SPR; lia. intros j Hj. apply lFZ. clear - Hj Ha Hb SPR; lia. clear - Hj Ha Hb FRD CAP IL; lia. clear - Hj Ha; lia. }
  assert (K1 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 27]%nat -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. apply lKS. revert Hx; apply (L5K.incl_b _ KS_adL); vm_compute; reflexivity. }
  pose proof (wordi_bound (Vv + y) I) as RW.
  destruct (Nat.eq_dec I len) as [EI|NEI].
  - (* [comment removed for export] *)
    subst I. pose proof (br3_tk fx1 R1 M1 (Z.of_nat len + 1) (Z.of_nat len + 1) ltac:(rewrite (K1 25%nat) by inl; exact A25) ltac:(rewrite (K1 21%nat) by inl; exact A21)
                   ltac:(clear - HVL I1; lia) ltac:(clear - HVL I1; lia) ltac:(clear; lia)) as MB.
    exists fx1, R1, M1. split. { eapply msteps_trans. exact lMS. exact MB. }
    split. { intros x Hx. apply K1. revert Hx; apply (L5K.incl_b KSQ); vm_compute; reflexivity. }
    split. exact LOW1. split. { intros i Hi Hn Hs. apply lFZ. exact Hi. clear - Hn I1; lia. clear - Hs; lia. } exact MG1.
  - assert (IL2 : (I < len)%nat) by (clear - IL NEI; lia).
    pose proof (br3_ft fx1 R1 M1 (Z.of_nat I + 1) (Z.of_nat len + 1) ltac:(rewrite (K1 25%nat) by inl; exact A25) ltac:(rewrite (K1 21%nat) by inl; exact A21)
                   ltac:(clear - HVI; lia) ltac:(clear - HVL; lia) ltac:(clear - IL2; lia)) as MB.
    (* [comment removed for export] *)
    pose proof AF1 as [_ W176a [IMGC1 [CSB1 CUAR1]] _ OZ1 OW1 _ DW1 DZ1 VZ1].
    pose proof (adS_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 42%nat => Z.of_nat I | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K1 _) by inl; sc)]).
    destruct P as (fx2 & R2 & M2 & MG2 & sFR & sFZ & (sMS & sKS & sR25)).
    assert (EM2 : M2 = M1). { apply functional_extensionality. exact sFR. } subst M2.
    assert (K2 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 26; 27]%nat -> getr R2 (reg x) = getr R1 (reg x)). { intros x Hx. apply sKS. revert Hx; apply (L5K.incl_b _ KS_adS); vm_compute; reflexivity. }
    assert (R2_26 : getr R2 (reg 26) = Z_to_bv 64 ((X + 1) mod 2 ^ 64)). { rewrite (K2 26%nat) by inl. rewrite <- lR26. symmetry. apply Z_to_bv_bv_unsigned. }
    assert (IR2 : in_regsL R2 sp o F). { unfold in_regsL. repeat split; rewrite (K2 _) by inl; rewrite (K1 _) by inl; assumption. }
    destruct (Z.eq_dec ((X + 1) mod 2 ^ 64) 0) as [Z0|NZ].
    + (* [comment removed for export] *)
      pose proof (br4_tk fx2 R2 M1 ltac:(rewrite R2_26, Z0; reflexivity)) as MB2.
      assert (AC2 : acarry y Vv (Datatypes.S I) = 1). { rewrite STC. rewrite Z0. reflexivity. }
      destruct (IH fx2 R2 M1 sp o y F fl d cap len (Datatypes.S I) Vv AF1 IR2) as (fx' & R' & M' & MS & K & LIMBS & FR' & GR').
      { exact HY. } { exact HF. } { exact HFL. } { clear; lia. } { clear - IL2; lia. } { clear - Hk IL2 I1; lia. } { exact CAP. } { exact VB. } { exact AC2. }
      { intros i Hi. apply LOW1. clear - Hi; lia. } { intros i Hi. apply HIGH1. clear - Hi; lia. }
      { unfold at_chead. split. rewrite (K2 21%nat) by inl; rewrite (K1 21%nat) by inl; exact A21. split. rewrite sR25; f_equal; clear; lia.
        split. apply KEEP. clear; lia. clear; lia. exact VD. apply KEEP. clear; lia. clear; lia. exact VN. }
      exists fx', R', M'. split. { eapply msteps_trans. exact lMS. eapply msteps_trans. exact MB. eapply msteps_trans. exact sMS. eapply msteps_trans. exact MB2. exact MS. }
      split. { intros x Hx. rewrite (K x Hx). rewrite (K2 x). apply K1. revert Hx; apply (L5K.incl_b KSQ); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSQ); vm_compute; reflexivity. }
      split. exact LIMBS. split. { intros i Hi Hn Hs. rewrite (FR' i Hi Hn Hs). apply lFZ. exact Hi. clear - Hn I1 IL; lia. clear - Hs; lia. } eapply mem_grows_trans; eauto.
    + (* [comment removed for export] *)
      pose proof (br4_ft fx2 R2 M1 _ R2_26 ltac:(pose proof (Z.mod_pos_bound (X + 1) (2 ^ 64) ltac:(clear; lia)); clear - H NZ; lia)) as MB2.
      assert (AC2 : acarry y Vv (Datatypes.S I) = 0). { rewrite STC. unfold BigModel.W.b2z, BigModel.W.ltu.
        destruct (Z.ltb_spec ((X + 1) mod 2 ^ 64) 1); [exfalso|reflexivity].
        pose proof (Z.mod_pos_bound (X + 1) (2 ^ 64) ltac:(clear; lia)). clear - H H0 NZ. lia. }
      exists fx2, R2, M1. split. { eapply msteps_trans. exact lMS. eapply msteps_trans. exact MB. eapply msteps_trans. exact sMS. exact MB2. }
      split. { intros x Hx. rewrite (K2 x). apply K1. revert Hx; apply (L5K.incl_b KSQ); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSQ); vm_compute; reflexivity. }
      split. { intros i Hi. destruct (Nat.le_gt_cases i I) as [LE|GT]. apply LOW1. exact LE.
               destruct (add_above_carry y Vv (Datatypes.S I) i ltac:(unfold wordZ; rewrite BigFactsBase.M_val; clear - HY; lia) ltac:(clear - VB; lia) ltac:(clear; lia) AC2 ltac:(clear - GT; lia)) as [E _].
               rewrite E. apply HIGH1. clear - GT Hi; lia. }
      split. { intros i Hi Hn Hs. apply lFZ. exact Hi. clear - Hn I1 IL; lia. clear - Hs; lia. } exact MG1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KSA : list nat := [3; 4; 8; 9; 18; 19; 22; 23; 27]%nat.
Definition st_afterA (sto : L5.bstore) (len : nat) (Vy : Z) : L5.bstore :=
  match sto with
  | L5.BInl _ v1 => L5.BInl (wordi Vy 0) (if Nat.eqb len 0 then v1 else wordi Vy 1)
  | L5.BDyn c q => L5.BDyn c q
  end.
Lemma in_firstn {A} (x : A) : forall n (l : list A), In x (firstn n l) -> In x l.
Proof. induction n as [|n IH]; intros [|z l] H; cbn in H; try contradiction. destruct H as [->|H]. left; reflexivity. right. apply IH. exact H. Qed.

Theorem addd_core fx R M (sp o y F fl fb : Z) (len : nat) (sto : L5.bstore) (wsR : list Z) :
  let b := L5.BO fb (Datatypes.S len) sto in let d := L5.bo_data o b in let cap := L5.bo_cap b in let Vv := BigFactsBase.val wsR in
  in_regs R sp o y F -> getr R (reg 24) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 y -> 0 <= y <= 9 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
  afacts M sp o d cap F fl -> L5.writable RSEGS M (sp - 176) 16 ->
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b wsR -> nth len wsR 0 = 0 -> Z.of_nat len + 1 <= cap ->
  match sto with L5.BDyn c q => o + 32 <= q \/ q + 8 * c <= o | L5.BInl _ _ => True end ->
  exists fx' R' M',
    msteps RSEGS (st fx R RZRET M) (st fx' R' REDRET M')
    /\ (forall x, In x KSA -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R' (reg 10) = Z_to_bv 64 o
    /\ (let wl := wlist (Vv + y) (Datatypes.S len) in let n' := L5W.rlen wl in
        L5.big_at RSEGS M' o (L5.BO (if Nat.eqb n' 0 then Z.land fb 253 else fb) n' (st_afterA sto len (Vv + y))) /\ L5.limbs_at RSEGS M' d wl)
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (o <= a < o + 16) -> ~ (sp - 176 <= a < sp - 160) -> ~ (sp - 128 <= a < sp - 112) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ mem_grows M M'.
Proof.
  cbn zeta. intros IR G24 G20 HY HF HFL AFM W176 OB OL TOP0 CAP ODYN.
  pose proof AFM as [[SPR A32] W176f [IMGC [CSB CUAR]] (OR & O8a & OBIG & FRO) OZ OW (DR & D8 & DBIG & CAPR & FRD & OD & DSH & DIMG & DF & DFL) DW DZ VZ].
  pose proof IR as (G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G25 & G26).
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
  assert (VB : 0 <= Vv < (2 ^ 64) ^ Z.of_nat len).
  { subst Vv. rewrite <- (val_firstn_zeros wsR len). 2: rewrite Lws; clear; lia. 2:{ intros i Hi. rewrite Lws in Hi. replace i with len by (clear - Hi; lia). exact TOP0. }
    pose proof (BigFactsBase.val_bound (firstn len wsR) ltac:(apply Forall_forall; intros w Hw; apply (proj1 (Forall_forall _ _) WO w); eapply in_firstn; exact Hw)) as VB0.
    rewrite length_firstn, Lws, Nat.min_l in VB0 by (clear; lia). rewrite BigFactsBase.M_val in VB0. exact VB0. }
  assert (LIMBS : forall i, (i <= len)%nat -> L5.u64_at RSEGS M (d + 8 * Z.of_nat i) (wordi Vv i)). { intros i Hi. rewrite <- NTH by exact Hi. apply WS. rewrite Lws. clear - Hi; lia. }
  assert (ALS : aligned sp 32) by exact A32. assert (ALO : aligned o 8) by exact O8a. assert (ALD : aligned d 8) by exact D8.
  assert (FROp : sp - 176 + 176 <= o \/ o + 32 <= sp - 176) by (clear - FRO; lia). assert (FRDp : sp - 176 + 176 <= d \/ d + 8 * cap <= sp - 176) by (clear - FRD; lia).
  assert (DIMGp : 65536 + 6438912 <= d \/ d + 8 * cap <= 65536) by (clear - DIMG; lia).
  assert (HV2 : 140735332487344 <= sp <= 140737488355328) by (clear - SPR; lia).
  assert (HVO : 4096 <= o <= 140737488355296) by (clear - OR; lia). assert (HVD : 4096 <= d <= 140737488355328) by (clear - DR CAPR; lia).
  assert (HVDC : 4104 <= d + 8 * cap <= 140737479966720) by (clear - DR CAPR; lia). assert (HVF : 0 <= fb <= 255) by (clear - Ffb; lia).
  assert (HVL : 0 <= Z.of_nat len <= 134217728) by (clear - CAP CAPR; lia).
  set (wl := wlist (Vv + y) (Datatypes.S len)).
  assert (WLL : length wl = Datatypes.S len) by (subst wl; apply BigFactsDigits.wlist_length).
  set (X0 := wordi Vv 0) in *. pose proof (wordi_bound Vv 0) as RX0. fold X0 in RX0.
  pose proof (add_limb0 y Vv ltac:(unfold wordZ; rewrite BigFactsBase.M_val; clear - HY; lia) ltac:(clear - VB; lia)) as [ST0 SC0]. fold X0 in ST0, SC0.
  unfold BigModel.W.add, BigModel.W.wrap, BigModel.W.b2z, BigModel.W.ltu in ST0, SC0. rewrite BigFactsBase.M_val in ST0, SC0. change 18446744073709551616 with (2 ^ 64) in ST0, SC0.
  pose proof (wordi_bound (Vv + y) 0) as RW0.
  (* [comment removed for export] *)
  assert (RUNC : exists fx1 R1 M1, msteps RSEGS (st fx R RZRET M) (st fx1 R1 BR1 M1) /\ mem_grows M M1
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8) -> ~ (sp - 128 <= i < sp - 112) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ (forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 27]%nat -> getr R1 (reg x) = getr R (reg x))
            /\ getr R1 (reg 10) = Z_to_bv 64 d /\ getr R1 (reg 11) = Z_to_bv 64 X0 /\ getr R1 (reg 12) = Z_to_bv 64 2 /\ getr R1 (reg 21) = Z_to_bv 64 (Z.of_nat len + 1)
            /\ getr R1 (reg 20) = Z_to_bv 64 ((X0 + y) mod 2 ^ 64) /\ L5.u64_at RSEGS M1 d (wordi (Vv + y) 0)
            /\ L5.u64_at RSEGS M1 (sp - 128) d /\ L5.u64_at RSEGS M1 (sp - 120) (Z.of_nat len + 1)).
  { assert (L0 : L5.u64_at RSEGS M d X0). { replace d with (d + 8 * Z.of_nat 0) by (clear; lia). apply LIMBS. clear; lia. }
    subst d cap. destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). assert (HVL2 : 1 <= Z.of_nat len + 1 <= 3) by (clear - Hl2; lia). assert (HVL1 : 1 <= Z.of_nat len <= 2 \/ len = 0%nat) by (clear - Hl2; lia).
      pose proof (adCi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len + 1 | 35%nat => fb | 38%nat => X0 | 39%nat => y | 40%nat => F | 41%nat => fl
                    | 43%nat => U R 1 | 56%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
      assert (O8' : L5.u64_at RSEGS M (o + 8) (Z.of_nat len + 1)) by (replace (Z.of_nat len + 1) with (Z.of_nat (Datatypes.S len)) by (clear; lia); exact O8).
      assert (HVL3 : 1 <= Z.of_nat len + 1 <= 2) by (clear - Hl2; lia).
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1 & MG1 & cFR & cFZ & (cMS & cKS & cR10 & cR11 & cR12 & cR20 & cR21 & cC & cVN & cVD)).
      exists fx1, R1, M1. split. exact cMS. split. exact MG1. split. { intros i Hi Hn Hs. apply cFZ. exact Hi. clear - Hs; lia. clear - Hn; lia. }
      split. { intros x Hx. apply cKS. revert Hx; apply (L5K.incl_b _ KS_adCi); vm_compute; reflexivity. }
      split. exact cR10. split. exact cR11. split. exact cR12. split. exact cR21. split. rewrite <- cR20; symmetry; apply Z_to_bv_bv_unsigned.
      split. rewrite <- ST0. exact cC. split. exact cVD. exact cVN.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
      assert (HVQ : 0 <= q < 2 ^ 64) by (clear - Q4096 Q47 Hcap; lia). assert (HVC : 1 <= c <= 134217728) by (clear - Hcap; lia). assert (HVL1 : 1 <= Z.of_nat len + 1 <= 134217728) by (clear - Hlc Hcap; lia).
      pose proof (adCd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => Z.of_nat len + 1 | 35%nat => fb | 36%nat => q | 37%nat => c | 38%nat => X0 | 39%nat => y | 40%nat => F | 41%nat => fl
                    | 43%nat => U R 1 | 56%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
      assert (O8' : L5.u64_at RSEGS M (o + 8) (Z.of_nat len + 1)) by (replace (Z.of_nat len + 1) with (Z.of_nat (Datatypes.S len)) by (clear; lia); exact O8).
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1 & MG1 & cFR & cFZ & (cMS & cKS & cR10 & cR11 & cR12 & cR20 & cR21 & cC & cVN & cVD)).
      exists fx1, R1, M1. split. exact cMS. split. exact MG1. split. { intros i Hi Hn Hs. apply cFZ. exact Hi. clear - Hs; lia. clear - Hn; lia. }
      split. { intros x Hx. apply cKS. revert Hx; apply (L5K.incl_b _ KS_adCd); vm_compute; reflexivity. }
      split. exact cR10. split. exact cR11. split. exact cR12. split. exact cR21. split. rewrite <- cR20; symmetry; apply Z_to_bv_bv_unsigned.
      split. rewrite <- ST0. exact cC. split. exact cVD. exact cVN. }
  destruct RUNC as (fx1 & R1 & M1 & MS1 & MG1 & FZ1 & K1 & R1_10 & R1_11 & R1_12 & R1_21 & R1_20 & C0 & V1D & V1N).
  assert (AF1 : afacts M1 sp o d cap F fl). { eapply afacts_keep. exact AFM. exact MG1. intros i Hi Hd _ Hs. apply FZ1. exact Hi. clear - Hd CAP CAPR; lia. clear - Hs; lia. }
  assert (LIMBS1 : forall i, (1 <= i <= len)%nat -> L5.u64_at RSEGS M1 (d + 8 * Z.of_nat i) (wordi Vv i)).
  { intros i Hi. eapply L5C.u64_at_agree. 4:{ apply LIMBS. clear - Hi; lia. } 2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia. intros j Hj. apply FZ1. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi; lia.
    clear - Hj Hi CAP FRD; lia. }
  assert (IR1 : in_regsL R1 sp o F). { unfold in_regsL. repeat split; rewrite (K1 _) by inl; assumption. }
  (* [comment removed for export] *)
  assert (PART1 : exists fx2 R2 M2, msteps RSEGS (st fx1 R1 BR1 M1) (st fx2 R2 CALLRED M2)
      /\ (forall x, In x KSQ -> getr R2 (reg x) = getr R1 (reg x))
      /\ (forall i, (i <= len)%nat -> L5.u64_at RSEGS M2 (d + 8 * Z.of_nat i) (wordi (Vv + y) i))
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (sp - 168 <= a < sp - 160) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) /\ mem_grows M1 M2).
  { destruct (Nat.eq_dec len 0) as [L0|Lpos].
    - pose proof (br1_tk fx1 R1 M1 (Z.of_nat len + 1) 2 R1_21 R1_12 ltac:(clear - L0; lia) ltac:(clear; lia) ltac:(clear - L0; lia)) as MB.
      exists fx1, R1, M1. split. exact MB. split. intros x _; reflexivity. split. { intros i Hi. replace i with 0%nat by (clear - Hi L0; lia). replace (d + 8 * Z.of_nat 0) with d by (clear; lia). exact C0. }
      split. intros a _ _ _; reflexivity. apply mem_grows_refl.
    - pose proof (br1_ft fx1 R1 M1 (Z.of_nat len + 1) 2 R1_21 R1_12 ltac:(clear - HVL; lia) ltac:(clear; lia) ltac:(clear - Lpos; lia)) as MB.
      destruct (Z_lt_le_dec ((X0 + y) mod 2 ^ 64) X0) as [CARRY|NOC].
      + (* [comment removed for export] *)
        assert (AC1 : acarry y Vv 1 = 1). { rewrite <- SC0. destruct (Z.ltb_spec ((X0 + y) mod 2 ^ 64) X0). reflexivity. exfalso; clear - CARRY H; lia. }
        pose proof (br2_ft fx1 R1 M1 _ _ R1_20 R1_11 ltac:(apply Z.mod_pos_bound; clear; lia) RX0 CARRY) as MB2.
        pose proof AF1 as [_ W176a [IMGC1 [CSB1 CUAR1]] _ _ _ _ _ _ _].
        pose proof (adD_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K1 _) by inl; sc)]).
        destruct P as (fx2 & R2 & M2 & MG2 & dFR & dFZ & (dMS & dKS & dR25)).
        assert (EM2 : M2 = M1). { apply functional_extensionality. exact dFR. } subst M2.
        assert (K2 : forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 27]%nat -> getr R2 (reg x) = getr R1 (reg x)). { intros x Hx. apply dKS. revert Hx; apply (L5K.incl_b _ KS_adD); vm_compute; reflexivity. }
        destruct IR1 as (J2 & J8 & J9 & J18 & J19 & J22 & J23 & J24).
        destruct (cloop len fx2 R2 M1 sp o y F fl d cap len 1 Vv AF1) as (fx3 & R3 & M3 & MS3 & K3 & LIMBS3 & FR3 & GR3).
        { unfold in_regsL. repeat split; rewrite (K2 _) by inl; assumption. }
        { exact HY. } { exact HF. } { exact HFL. } { clear; lia. } { clear - Lpos; lia. } { clear - Lpos; lia. } { exact CAP. } { exact VB. } { exact AC1. }
        { intros i Hi. replace i with 0%nat by (clear - Hi; lia). replace (d + 8 * Z.of_nat 0) with d by (clear; lia). exact C0. }
        { intros i Hi. apply LIMBS1. exact Hi. }
        { unfold at_chead. split. rewrite (K2 21%nat) by inl; exact R1_21. split. exact dR25. split. exact V1D. exact V1N. }
        exists fx3, R3, M3. split. { eapply msteps_trans. exact MB. eapply msteps_trans. exact MB2. eapply msteps_trans. exact dMS. exact MS3. }
        split. { intros x Hx. rewrite (K3 x Hx). apply K2. revert Hx; apply (L5K.incl_b KSQ); vm_compute; reflexivity. }
        split. exact LIMBS3. split. exact FR3. exact GR3.
      + (* [comment removed for export] *)
        assert (AC1 : acarry y Vv 1 = 0). { rewrite <- SC0. destruct (Z.ltb_spec ((X0 + y) mod 2 ^ 64) X0). exfalso; clear - NOC H; lia. reflexivity. }
        pose proof (br2_tk fx1 R1 M1 _ _ R1_20 R1_11 ltac:(apply Z.mod_pos_bound; clear; lia) RX0 NOC) as MB2.
        exists fx1, R1, M1. split. { eapply msteps_trans. exact MB. exact MB2. } split. intros x _; reflexivity.
        split. { intros i Hi. destruct (Nat.eq_dec i 0) as [->|NZ]. replace (d + 8 * Z.of_nat 0) with d by (clear; lia). exact C0.
                 destruct (add_above_carry y Vv 1 i ltac:(unfold wordZ; rewrite BigFactsBase.M_val; clear - HY; lia) ltac:(clear - VB; lia) ltac:(clear; lia) AC1 ltac:(clear - NZ; lia)) as [E _].
                 rewrite E. apply LIMBS1. clear - Hi NZ; lia. }
        split. intros a _ _ _; reflexivity. apply mem_grows_refl. }
  destruct PART1 as (fx2 & R2 & M2 & MS2 & K2 & LIMBS2 & FR2 & GR2).
  assert (AF2 : afacts M2 sp o d cap F fl). { eapply afacts_keep. exact AF1. exact GR2. intros i0 Hi Hd _ Hs. apply FR2. exact Hi. clear - Hd CAP CAPR; lia. clear - Hs; lia. }
  pose proof AF2 as [_ W176g [IMGC2 [CSB2 CUAR2]] _ OZ2 OW2 _ DW2 DZ2 VZ2].
  assert (K02 : forall x, In x KSQ -> getr R2 (reg x) = getr R (reg x)). { intros x Hx. rewrite (K2 x Hx). apply K1. revert Hx; apply (L5K.incl_b KSQ); vm_compute; reflexivity. }
  (* [comment removed for export] *)
  pose proof (adR_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => o | 39%nat => y | 40%nat => F | 43%nat => U R2 1 | 56%nat => U R2 10 | 57%nat => U R2 11
                | 58%nat => U R2 12 | 59%nat => U R2 13 | 20%nat => U R2 20 | 21%nat => U R2 21 | 24%nat => U R2 24 | 25%nat => U R2 25 | 26%nat => U R2 26 | _ => 0 end)) as P. cbn beta iota in P.
  assert (HVO2 : 4096 <= o <= 140737488355296) by exact HVO.
  feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K02 _) by inl; sc)]).
  destruct P as (fx3 & R3 & M3 & MG3 & rFR & rFZ & (rMS & rKS & rR1 & rR10)).
  assert (EM3 : M3 = M2). { apply functional_extensionality. exact rFR. } subst M3.
  assert (K03 : forall x, In x KSQ -> getr R3 (reg x) = getr R (reg x)). { intros x Hx. rewrite (rKS x). apply K02. exact Hx. revert Hx; apply (L5K.incl_b KSQ); vm_compute; reflexivity. }
  (* [comment removed for export] *)
  assert (W176b : L5.writable RSEGS M2 (sp - 160 - 16) 16). { replace (sp - 160 - 16) with (sp - 176) by (clear; lia). eapply L5.writable_grows. 2: exact W176. eapply mem_grows_trans. exact MG1. exact GR2. }
  assert (FR02 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * (Z.of_nat len + 1)) -> ~ (sp - 168 <= a < sp - 160) -> ~ (sp - 128 <= a < sp - 112) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hd Hs Hv. rewrite (FR2 a Ha Hd Hs). apply FZ1. exact Ha. clear - Hd; lia. exact Hv. }
  assert (HDR : forall a v, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
  { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR02. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb OD CAP; lia. clear - Hj Ha Hb FRO; lia. clear - Hj Ha Hb FRO; lia. }
  assert (FB2 : L5.u8_at RSEGS M2 o fb). { eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FR02. clear - Hj OR; lia. clear - Hj OD CAP; lia. clear - Hj FRO; lia. clear - Hj FRO; lia. }
  set (b1 := L5.BO fb (Datatypes.S len) (st_afterA sto len (Vv + y))).
  assert (OB1 : L5.big_at RSEGS M2 o b1 /\ L5C.obj_limbs RSEGS M2 b1 wl).
  { subst b1 d cap. unfold L5.big_at, L5C.obj_limbs, st_afterA. cbn [L5.bo_fb L5.bo_len L5.bo_st]. destruct sto as [w0 w1|c q].
    - destruct OST as (B0 & O16 & O24 & Hl2 & Rw0 & Rw1). split.
      + split. exact FB2. split. exact Ffb. split. { apply HDR. clear; lia. clear; lia. exact O8. } split. exact B0.
        split. { replace (o + 16) with (o + 16 + 8 * Z.of_nat 0) by (clear; lia). apply LIMBS2. clear; lia. }
        split. { destruct (Nat.eqb len 0) eqn:EL. apply Nat.eqb_eq in EL. eapply L5C.u64_at_agree. 4: exact O24. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FR02. clear - Hj OR; lia. rewrite EL. clear - Hj; lia. clear - Hj FRO; lia. clear - Hj FRO; lia.
                 apply Nat.eqb_neq in EL. replace (o + 24) with (o + 16 + 8 * Z.of_nat 1) by (clear; lia). apply LIMBS2. clear - EL; lia. }
        split. exact Hl2. split. apply wordi_bound. destruct (Nat.eqb len 0). exact Rw1. apply wordi_bound.
      + split. exact WLL. split. apply Forall_wlist. subst wl. destruct len as [|[|k]]. reflexivity. reflexivity. exfalso; clear - Hl2; lia.
    - destruct OST as (B1 & O16 & O24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). split.
      + split. exact FB2. split. exact Ffb. split. { apply HDR. clear; lia. clear; lia. exact O8. } split. exact B1.
        assert (HDR2 : forall a v, o + 16 <= a -> a + 8 <= o + 32 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
        { intros a v Ha Hb Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Hb OR; lia. intros j Hj. apply FR02. clear - Hj Ha Hb OR; lia. clear - Hj Ha Hb ODYN CAP; lia. clear - Hj Ha Hb FRO; lia. clear - Hj Ha Hb FRO; lia. }
        split. { apply HDR2. clear; lia. clear; lia. exact O16. } split. { apply HDR2. clear; lia. clear; lia. exact O24. }
        split. exact Hlc. split. exact Hcap. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH.
      + split. exact WLL. split. apply Forall_wlist. intros i0 Hi. rewrite WLL in Hi. unfold wl. rewrite (wlist_nth' (Vv + y) (Datatypes.S len) i0 Hi). apply LIMBS2. clear - Hi; lia. }
  destruct OB1 as [OB1 OL1].
  assert (RAred : L5.ra_ok REDRET). { split. unfold REDRET; clear; lia. reflexivity. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (A16' : (sp - 160) mod 16 = 0) by (clear - A32; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (G2' : getr R3 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (K03 2%nat) by inl; exact G2).
  destruct (L5ARED.reduce_run fx3 R3 M2 o (sp - 160) REDRET b1 wl rR10 rR1 RAred G2' ltac:(clear - SPR; lia) A16' W176b IMGC2 CSB2 CUAR2
              ltac:(clear - OR; lia) O8a OBIG ltac:(clear - FRO; lia) OZ2 OW2 OB1 OL1)
    as (fx4 & R4 & M4 & MS4 & OB4 & K4 & R4_2 & R4_10 & FR4 & GR4).
  { subst b1 d cap. unfold L5.bo_data, L5.bo_cap, st_afterA. cbn [L5.bo_st]. destruct sto as [w0 w1|c q]; cbn iota.
    all: split; [exact DBIG|]. all: split; [clear - FRD; lia|]. all: split; [exact OD|]. all: split; [exact DW2|]. all: split; [exact DZ2|]. all: clear - CAPR; lia. }
  cbn zeta in OB4. replace (L5.bo_fb b1) with fb in OB4 by reflexivity. replace (L5.bo_st b1) with (st_afterA sto len (Vv + y)) in OB4 by reflexivity.
  exists fx4, R4, M4. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact rMS. exact MS4. }
  split. { intros x Hx. rewrite (K4 x). apply K03. revert Hx; apply (L5K.incl_b KSA); vm_compute; reflexivity. revert Hx; apply (L5K.incl_b KSA); vm_compute; reflexivity. }
  split. exact R4_2. split. exact R4_10.
  split. { split. exact OB4. intros i0 Hi. rewrite WLL in Hi. eapply L5C.u64_at_agree. 4:{ unfold wl. rewrite (wlist_nth' (Vv + y) (Datatypes.S len) i0 Hi). apply LIMBS2. clear - Hi; lia. }
           2: clear - DR; lia. 2: clear - DR CAPR CAP Hi; lia. intros j Hj. apply FR4. clear - Hj DR CAPR CAP Hi; lia. clear - Hj Hi CAP OD; lia. clear - Hj Hi CAP FRD; lia. }
  split. { intros a Ha Hd Ho Hs Hv. rewrite FR4. apply FR02. exact Ha. exact Hd. clear - Hs; lia. exact Hv. exact Ha. exact Ho. clear - Hs; lia. }
  eapply mem_grows_trans. eapply mem_grows_trans. exact MG1. exact GR2. exact GR4.
Qed.

End SCFG_1.
End L5AADDK.
