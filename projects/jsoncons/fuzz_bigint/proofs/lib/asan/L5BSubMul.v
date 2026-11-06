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
     AxSymExec3 AxSymExec3Sound SegRun Bo0_code_93368_94368 Bo0_code_94368_9505c BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5BSubMulP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASM.
Import L5A. Import L5CA. Import L5SA. Import L5ASMP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Local Ltac kl KS := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; revert Hx; apply (L5K.incl_b _ KS); vm_compute; reflexivity.
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Definition SUBMUL : Z := 0x9413c.
Definition L1HEAD : Z := 0x941c4.
Definition L2HEAD : Z := 0x942fc.
Definition SM_RET : Z := 0x943c0.
Definition SM_FRAME : Z := 96.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apart (x lx y ly : Z) : Prop := x + lx <= y \/ y + ly <= x.
Definition notshadow (x lx : Z) : Prop := 2147446784 + 17592186048512 <= x \/ x + lx <= 2147446784.
Definition offimg (x lx : Z) : Prop := x + lx <= 65536 \/ 6504448 <= x.

(* [comment removed for export] *)
Record smctxA (M : word -> option byte) (sp a b qa : Z) (n : nat) : Prop := SMC {
  c_sp : 140735332487264 <= sp <= 140737488355328 /\ sp mod 16 = 0;
  c_spw : L5.writable RSEGS M (sp - 96) 96;
  c_st : L5.img_clear M 860160 884736 /\ L5.u64_at RSEGS M 911160 2147450880 /\ L5.u32_at RSEGS M 911168 1;
  c_n : (1 <= n <= 300)%nat;
  c_a : 4096 <= a <= 140737488351232 /\ a mod 8 = 0 /\ notshadow a (8 * Z.of_nat n + 8) /\ offimg a (8 * Z.of_nat n + 8);
  c_aw : L5.writable RSEGS M a (8 * Z.of_nat n + 8);
  c_ad : L5.defined M a (8 * Z.of_nat n + 8);
  c_az : L5KA.zeros_at M (a / 8 + 2147450880) (Z.of_nat n + 1);
  c_b : 4096 <= b <= 140737488351232 /\ b mod 8 = 0 /\ notshadow b (8 * Z.of_nat n);
  c_bd : L5.defined M b (8 * Z.of_nat n);
  c_bz : L5KA.zeros_at M (b / 8 + 2147450880) (Z.of_nat n);
  c_q : 4096 <= qa <= 140737488355320 /\ qa mod 8 = 0 /\ notshadow qa 8 /\ offimg qa 8;
  c_qw : L5.writable RSEGS M qa 8;
  c_qd : L5.defined M qa 8;
  c_qz : L5KA.zeros_at M (qa / 8 + 2147450880) 1;
  c_ap1 : apart (sp - 96) 96 a (8 * Z.of_nat n + 8);
  c_ap2 : apart (sp - 96) 96 b (8 * Z.of_nat n);
  c_ap3 : apart (sp - 96) 96 qa 8;
  c_ap4 : apart a (8 * Z.of_nat n + 8) b (8 * Z.of_nat n);
  c_ap5 : apart a (8 * Z.of_nat n + 8) qa 8;
  c_ap6 : apart b (8 * Z.of_nat n) qa 8 }.

(* [comment removed for export] *)
Definition sm_agree (M M' : word -> option byte) (sp a qa : Z) (n : nat) : Prop :=
  forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp) -> ~ (a <= i < a + 8 * Z.of_nat n + 8) -> ~ (qa <= i < qa + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).

(* [comment removed for export] *)
Definition sm_kept : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition submul_postA (M M' : word -> option byte) (sp a b qa : Z) (n : nat) (R R' : bvmap 5 word) : Prop :=
  (forall i, In i sm_kept -> getr R' (reg i) = getr R (reg i)) /\ regs_preserved R R'
  /\ smctxA M' sp a b qa n /\ sm_agree M M' sp a qa n /\ mem_grows M M'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record smfull (M : word -> option byte) (sp a b qa : Z) (n : nat) : Prop := MK_smfull {
  smfull_0 : 140735332487264 <= sp <= 140737488355328;
  smfull_1 : aligned sp 16;
  smfull_2 : L5.writable RSEGS M (sp - 96) 96;
  smfull_3 : L5.img_clear M 860160 884736;
  smfull_4 : L5.u64_at RSEGS M 911160 2147450880;
  smfull_5 : L5.u32_at RSEGS M 911168 1;
  smfull_6 : 4096 <= a <= 140737488351232;
  smfull_7 : aligned a 8;
  smfull_8 : (2147446784 + 17592186048512 <= a \/ a + ((8 * (Z.of_nat n)) + 8) <= 2147446784);
  smfull_9 : L5.defined M a ((8 * (Z.of_nat n)) + 8);
  smfull_10 : L5KA.zeros_at M ((a / 8) + 2147450880) ((Z.of_nat n) + 1);
  smfull_11 : ((sp - 96) + 96 <= a \/ a + ((8 * (Z.of_nat n)) + 8) <= (sp - 96));
  smfull_12 : (a + ((8 * (Z.of_nat n)) + 8) <= ((a / 8) + 2147450880) \/ ((a / 8) + 2147450880) + ((Z.of_nat n) + 1) <= a);
  smfull_13 : L5.writable RSEGS M a ((8 * (Z.of_nat n)) + 8);
  smfull_14 : 4096 <= b <= 140737488351232;
  smfull_15 : aligned b 8;
  smfull_16 : (2147446784 + 17592186048512 <= b \/ b + (8 * (Z.of_nat n)) <= 2147446784);
  smfull_17 : L5.defined M b (8 * (Z.of_nat n));
  smfull_18 : L5KA.zeros_at M ((b / 8) + 2147450880) (Z.of_nat n);
  smfull_19 : ((sp - 96) + 96 <= b \/ b + (8 * (Z.of_nat n)) <= (sp - 96));
  smfull_20 : (b + (8 * (Z.of_nat n)) <= ((b / 8) + 2147450880) \/ ((b / 8) + 2147450880) + (Z.of_nat n) <= b);
  smfull_21 : 4096 <= qa <= 140737488355320;
  smfull_22 : aligned qa 8;
  smfull_23 : (2147446784 + 17592186048512 <= qa \/ qa + 8 <= 2147446784);
  smfull_24 : L5.defined M qa 8;
  smfull_25 : L5KA.zeros_at M ((qa / 8) + 2147450880) 1;
  smfull_26 : ((sp - 96) + 96 <= qa \/ qa + 8 <= (sp - 96));
  smfull_27 : (qa + 8 <= ((qa / 8) + 2147450880) \/ ((qa / 8) + 2147450880) + 1 <= qa);
  smfull_28 : L5.writable RSEGS M qa 8;
  smfull_29 : 1 <= (Z.of_nat n) <= 300;
  smfull_30 : (a + ((8 * (Z.of_nat n)) + 8) <= b \/ b + (8 * (Z.of_nat n)) <= a);
  smfull_31 : (a + ((8 * (Z.of_nat n)) + 8) <= qa \/ qa + 8 <= a);
  smfull_32 : (b + (8 * (Z.of_nat n)) <= qa \/ qa + 8 <= b);
  smfull_33 : (a + ((8 * (Z.of_nat n)) + 8) <= ((b / 8) + 2147450880) \/ ((b / 8) + 2147450880) + (Z.of_nat n) <= a);
  smfull_34 : (a + ((8 * (Z.of_nat n)) + 8) <= ((qa / 8) + 2147450880) \/ ((qa / 8) + 2147450880) + 1 <= a);
  smfull_35 : (qa + 8 <= ((a / 8) + 2147450880) \/ ((a / 8) + 2147450880) + ((Z.of_nat n) + 1) <= qa);
  smfull_36 : (qa + 8 <= ((b / 8) + 2147450880) \/ ((b / 8) + 2147450880) + (Z.of_nat n) <= qa)
}.

Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma full_of M sp a b qa n : smctxA M sp a b qa n -> smfull M sp a b qa n.
Proof.
  intros [[SPR A16] SPW [IMGC [CSB CUAR]] NR (AR & A8 & ANS & AIM) AW AD AZ (BR & B8 & BNS) BD BZ (QR & Q8 & QNS & QIM) QW QD QZ AP1 AP2 AP3 AP4 AP5 AP6].
  unfold apart, notshadow, offimg in *.
  constructor; try assumption; try (clear - NR; lia);
    try (clear - AR NR ANS; lia); try (clear - BR NR BNS; lia); try (clear - QR QNS; lia);
    try (clear - AR BR NR ANS BNS; lia); try (clear - AR QR NR ANS QNS; lia); try (clear - BR QR NR BNS QNS; lia);
    try (clear - AP1; lia); try (clear - AP2; lia); try (clear - AP3; lia); try (clear - AP4; lia); try (clear - AP5; lia); try (clear - AP6; lia).
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ctx_keep M M' sp a b qa n : smctxA M sp a b qa n -> mem_grows M M' -> sm_agree M M' sp a qa n -> smctxA M' sp a b qa n.
Proof.
  intros [CSP SPW [IMGC [CSB CUAR]] NR CA AW AD AZ CB BD BZ CQ QW QD QZ AP1 AP2 AP3 AP4 AP5 AP6] G AG.
  pose proof CSP as [SPR A16]. pose proof CA as (AR & A8 & ANS & AIM). pose proof CB as (BR & B8 & BNS). pose proof CQ as (QR & Q8 & QNS & QIM).
  unfold apart, notshadow, offimg, sm_agree in *.
  constructor; try assumption; try (eapply L5.writable_grows; eassumption); try (eapply L5.defined_grows; eassumption).
  - split. { intros x Hx. rewrite AG. apply IMGC. exact Hx. clear - Hx; lia. clear - Hx SPR; lia. clear - Hx AIM NR; lia. clear - Hx QIM; lia. }
    split. eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros j Hj. apply AG. clear - Hj; lia. clear - Hj SPR; lia. clear - Hj AIM NR; lia. clear - Hj QIM; lia.
    eapply u32_at_agree1. 4: exact CUAR. intros j Hj. apply AG. clear - Hj; lia. clear - Hj SPR; lia. clear - Hj AIM NR; lia. clear - Hj QIM; lia. clear; lia. clear; lia.
  - eapply L5KA.zeros_at_agree1. 2: exact AZ. intros i Hi. apply AG. clear - Hi AR NR; lia. clear - Hi AR NR SPR; lia. clear - Hi AR NR ANS; lia. clear - Hi AR NR QR QNS; lia.
  - eapply L5KA.zeros_at_agree1. 2: exact BZ. intros i Hi. apply AG. clear - Hi BR NR; lia. clear - Hi BR NR SPR; lia. clear - Hi BR NR AR ANS; lia. clear - Hi BR NR QR QNS; lia.
  - eapply L5KA.zeros_at_agree1. 2: exact QZ. intros i Hi. apply AG. clear - Hi QR; lia. clear - Hi QR SPR; lia. clear - Hi QR NR AR ANS; lia. clear - Hi QR QNS; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma agree_refl M sp a qa n : sm_agree M M sp a qa n. Proof. intros i _ _ _ _. reflexivity. Qed.
Lemma agree_trans M1 M2 M3 sp a qa n : sm_agree M1 M2 sp a qa n -> sm_agree M2 M3 sp a qa n -> sm_agree M1 M3 sp a qa n.
Proof. intros A B i H0 H1 H2 H3. rewrite (B i H0 H1 H2 H3). apply A; assumption. Qed.

(* [comment removed for export] *)
Definition saved (M : word -> option byte) (sp : Z) (R : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (U R 1) /\ L5.u64_at RSEGS M (sp - 16) (U R 8) /\ L5.u64_at RSEGS M (sp - 24) (U R 9) /\ L5.u64_at RSEGS M (sp - 32) (U R 18) /\
  L5.u64_at RSEGS M (sp - 40) (U R 19) /\ L5.u64_at RSEGS M (sp - 48) (U R 20) /\ L5.u64_at RSEGS M (sp - 56) (U R 21) /\ L5.u64_at RSEGS M (sp - 64) (U R 22) /\
  L5.u64_at RSEGS M (sp - 72) (U R 23) /\ L5.u64_at RSEGS M (sp - 80) (U R 24) /\ L5.u64_at RSEGS M (sp - 88) (U R 25).
Lemma saved_keep M M' sp R : 140735332487264 <= sp <= 140737488355328 -> (forall i, sp - 96 <= i < sp -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> saved M sp R -> saved M' sp R.
Proof.
  intros SPR AG (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11). unfold saved.
  repeat split; (eapply L5C.u64_at_agree; [intros j Hj; apply AG; clear - Hj; lia | clear - SPR; lia | clear - SPR; lia | eassumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma r20 : (20%bv : bv 5) = reg 20. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma r15 : (15%bv : bv 5) = reg 15. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma br_93f74 fx R M : msteps RSEGS (st fx R 0x942c8 M) (st fx R (if branch_taken BC_GEU (getr R (reg 20)) (getr R (reg 15)) then 0x94390 else 0x942cc) M).
Proof.
  rewrite <- r20, <- r15.
  apply (L5ACMP.br_site fx R M 0x942c8 0x94390 (0x942c8%bv : word) _ BC_GEU 20 15 _ ltac:(apply bv_eq; vm_compute; reflexivity) F_942c8 eq_refl D_942c8); apply bv_eq; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_l1 (R : bvmap 5 word) (sp a b qa : Z) (n i : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R (reg 5) = Z_to_bv 64 (Z.of_nat i) /\ getr R (reg 6) = Z_to_bv 64 1 /\ getr R (reg 7) = Z_to_bv 64 1 /\
  getr R (reg 8) = Z_to_bv 64 1 /\ getr R (reg 9) = Z_to_bv 64 1 /\ getr R (reg 11) = Z_to_bv 64 a /\ getr R (reg 12) = Z_to_bv 64 b /\
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) /\ getr R (reg 14) = Z_to_bv 64 qa /\ getr R (reg 16) = Z_to_bv 64 (((-1) * a) + (-1)) /\
  getr R (reg 17) = Z_to_bv 64 2147450880 /\ getr R (reg 18) = Z_to_bv 64 1152921504606846974 /\ getr R (reg 29) = Z_to_bv 64 ((8 * Z.of_nat i) + 8) /\
  getr R (reg 30) = Z_to_bv 64 4294967295 /\ getr R (reg 31) = Z_to_bv 64 (qa / 8 + 2147450880).
(* [comment removed for export] *)
Definition KSL : list nat := [2; 3; 4; 6; 7; 8; 9; 11; 12; 13; 14; 16; 17; 18; 26; 27; 30; 31]%nat.
Local Ltac openF C := let F := fresh "F" in pose proof (full_of _ _ _ _ _ _ C) as F;
  destruct F as [F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28 F29 F30 F31 F32 F33 F34 F35 F36].

Lemma loop1 (m : nat) : forall fx R M (sp a b qa : Z) (n i : nat),
  (m = n - i)%nat -> smctxA M sp a b qa n -> at_l1 R sp a b qa n i -> (i < n)%nat ->
  exists fx' R' M', msteps RSEGS (st fx R L1HEAD M) (st fx' R' 0x942c8 M')
    /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x))
    /\ (forall x : word, ~ (a <= bv_unsigned x < a + 8 * Z.of_nat n + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R M sp a b qa n i Hm C AT Hi. { exfalso. clear - Hm Hi. lia. }
  destruct AT as (A2 & A5 & A6 & A7 & A8 & A9 & A11 & A12 & A13 & A14 & A16 & A17 & A18 & A29 & A30 & A31).
  pose proof (c_n _ _ _ _ _ _ C) as NR. openF C.
  assert (HVI : 0 <= Z.of_nat i <= 299) by (clear - Hi NR; lia).
  destruct (Nat.eq_dec (i + 1) n) as [LAST|MORE].
  - (* [comment removed for export] *)
    pose proof (vsmIL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa | 37%nat => Z.of_nat i
                  | 38%nat => U R 28 | _ => 0 end)) as P. cbn beta iota in P.
    assert (HD1 : 1 <= Z.of_nat n - Z.of_nat i <= 1) by (clear - LAST; lia).
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & FR1 & FZ1 & (MS1 & KS1 & _)).
    exists fx1, R1, M1. split. exact MS1. split. { intros x Hx. apply KS1. revert x Hx. kl KS_vsmIL. }
    split. { intros x Hx. apply FR1. clear - Hx Hi. lia. } exact MG1.
  - pose proof (vsmI_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa | 37%nat => Z.of_nat i
                  | 38%nat => U R 28 | _ => 0 end)) as P. cbn beta iota in P.
    assert (HD2 : 2 <= Z.of_nat n - Z.of_nat i <= 300) by (clear - MORE Hi NR; lia).
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & FR1 & FZ1 & (MS1 & KS1 & B5 & B10 & B25 & B29)).
    assert (K1 : forall x, In x KSL -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. apply KS1. revert x Hx. kl KS_vsmI. }
    assert (AG1 : sm_agree M M1 sp a qa n). { intros j Hj _ Hn _. apply FZ1. exact Hj. clear - Hn Hi. lia. }
    assert (C1 : smctxA M1 sp a b qa n) by (eapply ctx_keep; eassumption).
    assert (AT1 : at_l1 R1 sp a b qa n (Datatypes.S i)).
    { unfold at_l1. repeat split.
      - rewrite (K1 2%nat) by inl. exact A2.
      - rewrite B5. f_equal. clear; lia.
      - rewrite (K1 6%nat) by inl. exact A6. - rewrite (K1 7%nat) by inl. exact A7. - rewrite (K1 8%nat) by inl. exact A8. - rewrite (K1 9%nat) by inl. exact A9.
      - rewrite (K1 11%nat) by inl. exact A11. - rewrite (K1 12%nat) by inl. exact A12. - rewrite (K1 13%nat) by inl. exact A13. - rewrite (K1 14%nat) by inl. exact A14.
      - rewrite (K1 16%nat) by inl. exact A16. - rewrite (K1 17%nat) by inl. exact A17. - rewrite (K1 18%nat) by inl. exact A18.
      - rewrite B29. f_equal. clear; lia.
      - rewrite (K1 30%nat) by inl. exact A30. - rewrite (K1 31%nat) by inl. exact A31. }
    destruct (IH fx1 R1 M1 sp a b qa n (Datatypes.S i) ltac:(clear - Hm; lia) C1 AT1 ltac:(clear - MORE Hi; lia)) as (fx' & R' & M' & MS & K & FR & G).
    exists fx', R', M'. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. exact Hx. }
    split. { intros x Hx. rewrite (FR x Hx). apply FR1. clear - Hx Hi. lia. }
    eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_l2 (R : bvmap 5 word) (sp a b qa : Z) (n j : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R (reg 5) = Z_to_bv 64 (Z.of_nat j) /\ getr R (reg 7) = Z_to_bv 64 (((-1) * b) + (-1)) /\
  getr R (reg 10) = Z_to_bv 64 (a + 8 * Z.of_nat j) /\ getr R (reg 11) = Z_to_bv 64 a /\ getr R (reg 12) = Z_to_bv 64 (b + 8 * Z.of_nat j) /\
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) /\ getr R (reg 14) = Z_to_bv 64 (b + 8 * Z.of_nat j) /\ getr R (reg 15) = Z_to_bv 64 (8 * Z.of_nat j) /\
  getr R (reg 16) = Z_to_bv 64 (((-1) * a) + (-1)) /\ getr R (reg 17) = Z_to_bv 64 2147450880 /\ getr R (reg 28) = Z_to_bv 64 (a + 8 * Z.of_nat j).
Definition KSL2 : list nat := [2; 3; 4; 7; 11; 13; 16; 17; 26; 27]%nat.

Lemma loop2 (m : nat) : forall fx R M (sp a b qa : Z) (n j : nat),
  (m = n - j)%nat -> smctxA M sp a b qa n -> at_l2 R sp a b qa n j -> (j < n)%nat ->
  exists fx' R' M', msteps RSEGS (st fx R L2HEAD M) (st fx' R' 0x94368 M')
    /\ (forall x, In x KSL2 -> getr R' (reg x) = getr R (reg x))
    /\ (forall x : word, ~ (a <= bv_unsigned x < a + 8 * Z.of_nat n + 8) -> M' x = M x) /\ mem_grows M M'.
Proof.
  induction m as [|m IH]; intros fx R M sp a b qa n j Hm C AT Hj. { exfalso. clear - Hm Hj. lia. }
  destruct AT as (A2 & A5 & A7 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A28).
  pose proof (c_n _ _ _ _ _ _ C) as NR. openF C.
  assert (HVJ : 0 <= Z.of_nat j <= 299) by (clear - Hj NR; lia).
  destruct (Nat.eq_dec (j + 1) n) as [LAST|MORE].
  - pose proof (vsmJL_conc fx R M (fun k => match k with 2%nat => sp | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa | 37%nat => Z.of_nat j
                  | 38%nat => U R 6 | _ => 0 end)) as P. cbn beta iota in P.
    assert (HD1 : 1 <= Z.of_nat n - Z.of_nat j <= 1) by (clear - LAST; lia).
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & FR1 & FZ1 & (MS1 & KS1 & _)).
    exists fx1, R1, M1. split. exact MS1. split. { intros x Hx. apply KS1. revert x Hx. kl KS_vsmJL. }
    split. { intros x Hx. apply FR1. clear - Hx Hj. lia. } exact MG1.
  - pose proof (vsmJ_conc fx R M (fun k => match k with 2%nat => sp | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa | 37%nat => Z.of_nat j
                  | 38%nat => U R 6 | _ => 0 end)) as P. cbn beta iota in P.
    assert (HD2 : 2 <= Z.of_nat n - Z.of_nat j <= 300) by (clear - MORE Hj NR; lia).
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & FR1 & FZ1 & (MS1 & KS1 & B5 & B10 & B12 & B14 & B15 & B28)).
    assert (K1 : forall x, In x KSL2 -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. apply KS1. revert x Hx. kl KS_vsmJ. }
    assert (AG1 : sm_agree M M1 sp a qa n). { intros k Hk _ Hn _. apply FZ1. exact Hk. clear - Hn Hj. lia. }
    assert (C1 : smctxA M1 sp a b qa n) by (eapply ctx_keep; eassumption).
    assert (AT1 : at_l2 R1 sp a b qa n (Datatypes.S j)).
    { unfold at_l2. repeat split.
      - rewrite (K1 2%nat) by inl. exact A2.
      - rewrite B5. f_equal. clear; lia.
      - rewrite (K1 7%nat) by inl. exact A7.
      - rewrite B10. f_equal. clear; lia.
      - rewrite (K1 11%nat) by inl. exact A11.
      - rewrite B12. f_equal. clear; lia.
      - rewrite (K1 13%nat) by inl. exact A13.
      - rewrite B14. f_equal. clear; lia.
      - rewrite B15. f_equal. clear; lia.
      - rewrite (K1 16%nat) by inl. exact A16. - rewrite (K1 17%nat) by inl. exact A17.
      - rewrite B28. f_equal. clear; lia. }
    destruct (IH fx1 R1 M1 sp a b qa n (Datatypes.S j) ltac:(clear - Hm; lia) C1 AT1 ltac:(clear - MORE Hj; lia)) as (fx' & R' & M' & MS & K & FR & G).
    exists fx', R', M'. split. eapply msteps_trans; eauto.
    split. { intros x Hx. rewrite (K x Hx). apply K1. exact Hx. }
    split. { intros x Hx. rewrite (FR x Hx). apply FR1. clear - Hx Hj. lia. }
    eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma fz segs (p : word) (z : Z) w : fetch_word segs p = Some w -> p = Z_to_bv 64 z -> fetch_word segs (Z_to_bv 64 z) = Some w.
Proof. intros H E. rewrite <- E. exact H. Qed.
Lemma word_agree (M M' : word -> option byte) (P : Z -> Prop) :
  (forall x : word, ~ P (bv_unsigned x) -> M' x = M x) -> forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof. intros H i Hi Hn. apply H. rewrite BG.unsigned_lit by exact Hi. exact Hn. Qed.

Theorem submul_runA (fx : FPState) R M (sp a b qa r : Z) (n : nat) :
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 11) = Z_to_bv 64 a -> getr R (reg 12) = Z_to_bv 64 b ->
  getr R (reg 13) = Z_to_bv 64 (Z.of_nat n) -> getr R (reg 14) = Z_to_bv 64 qa ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> smctxA M sp a b qa n ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R SUBMUL M) (st fx' R' r M') /\ submul_postA M M' sp a b qa n R R'.
Proof.
  intros H2 H11 H12 H13 H14 H1 RA C. unfold SUBMUL.
  pose proof (c_n _ _ _ _ _ _ C) as NR. pose proof (c_sp _ _ _ _ _ _ C) as [SPR A16]. pose proof (c_ap1 _ _ _ _ _ _ C) as AP1. pose proof (c_ap3 _ _ _ _ _ _ C) as AP3.
  unfold apart in AP1, AP3.
  (* [comment removed for export] *)
  assert (S1 : exists fx1 R1 M1, msteps RSEGS (st fx R 0x9413c M) (st fx1 R1 L1HEAD M1) /\ at_l1 R1 sp a b qa n 0
             /\ (forall x, In x [3; 4; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)) /\ saved M1 sp R
             /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M1).
  { openF C.
    pose proof (vsmA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (clear; lia)]).
    destruct P as (fx1 & R1 & M1 & MG1 & FR1 & FZ1 & (MS1 & KS1 & B2 & B5 & B6 & B7 & B8 & B9 & B10 & B15 & B16 & B17 & B18 & B19 & B28 & B29 & B30 & B31 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
    exists fx1, R1, M1. split. exact MS1.
    split. { unfold at_l1. change (Z.of_nat 0) with 0. repeat split; first [ assumption | (rewrite (KS1 _) by inl; assumption) ]. }
    split. { intros x Hx. apply KS1. revert x Hx. kl KS_vsmA. }
    split. { unfold saved, U. repeat split; assumption. }
    split. { intros i Hi Hn. apply FZ1. exact Hi. clear - Hn; lia. } exact MG1. }
  destruct S1 as (fx1 & R1 & M1 & MS1 & AT1 & K1 & SV1 & FR1 & MG1).
  assert (AG1 : sm_agree M M1 sp a qa n). { intros i Hi Hn _ _. apply FR1; assumption. }
  assert (C1 : smctxA M1 sp a b qa n) by (eapply ctx_keep; eassumption).
  (* [comment removed for export] *)
  destruct (loop1 n fx1 R1 M1 sp a b qa n 0 ltac:(clear; lia) C1 AT1 ltac:(clear - NR; lia)) as (fx2 & R2 & M2 & MS2 & K2 & FR2 & MG2).
  assert (FR2z := word_agree M1 M2 (fun i => a <= i < a + 8 * Z.of_nat n + 8) FR2). cbn beta in FR2z.
  assert (AG2 : sm_agree M1 M2 sp a qa n). { intros i Hi _ Hn _. apply FR2z; assumption. }
  assert (C2 : smctxA M2 sp a b qa n) by (eapply ctx_keep; eassumption).
  assert (SV2 : saved M2 sp R). { eapply saved_keep. exact SPR. 2: exact SV1. intros i Hi. apply FR2z. clear - Hi SPR; lia. clear - Hi AP1; lia. }
  assert (R2_2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 96)). { rewrite (K2 2%nat) by inl. exact (proj1 AT1). }
  (* [comment removed for export] *)
  assert (Hr : 0 <= r < 2 ^ 64) by (destruct RA; lia).
  assert (FIN : forall fx3 R3 M3, msteps RSEGS (st fx2 R2 0x942c8 M2) (st fx3 R3 SM_RET M3) ->
            (forall x, In x [3; 4; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x)) ->
            getr R3 (reg 1) = Z_to_bv 64 (U R 1) -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (U R 8) -> getr R3 (reg 9) = Z_to_bv 64 (U R 9) ->
            getr R3 (reg 18) = Z_to_bv 64 (U R 18) -> getr R3 (reg 19) = Z_to_bv 64 (U R 19) -> getr R3 (reg 20) = Z_to_bv 64 (U R 20) -> getr R3 (reg 21) = Z_to_bv 64 (U R 21) ->
            getr R3 (reg 22) = Z_to_bv 64 (U R 22) -> getr R3 (reg 23) = Z_to_bv 64 (U R 23) -> getr R3 (reg 24) = Z_to_bv 64 (U R 24) -> getr R3 (reg 25) = Z_to_bv 64 (U R 25) ->
            sm_agree M2 M3 sp a qa n -> mem_grows M2 M3 ->
            exists (fx' : FPState) R' M', msteps RSEGS (st fx R 0x9413c M) (st fx' R' r M') /\ submul_postA M M' sp a b qa n R R').
  { intros fx3 R3 M3 MS3 K3 E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 AG3 MG3.
    assert (R31 : getr R3 (reg 1) = Z_to_bv 64 r). { rewrite E1, <- U_to. exact H1. }
    pose proof (ret_to fx3 R3 M3 0x943c0 W_943c0 r (fz _ _ 0x943c0 _ F_943c0 ltac:(apply bv_eq; reflexivity)) eq_refl D_943c0 R31 (proj1 RA) (proj2 RA)) as RET'.
    exists fx3, R3, M3. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MS3. exact RET'. }
    assert (KK : forall i, In i sm_kept -> getr R3 (reg i) = getr R (reg i)).
    { intros i Hi. cbn in Hi.
      repeat (destruct Hi as [<-|Hi]; [first [ (rewrite E1; symmetry; apply U_to) | (rewrite E2; symmetry; exact H2) | (rewrite E8; symmetry; apply U_to) | (rewrite E9; symmetry; apply U_to)
         | (rewrite E18; symmetry; apply U_to) | (rewrite E19; symmetry; apply U_to) | (rewrite E20; symmetry; apply U_to) | (rewrite E21; symmetry; apply U_to)
         | (rewrite E22; symmetry; apply U_to) | (rewrite E23; symmetry; apply U_to) | (rewrite E24; symmetry; apply U_to) | (rewrite E25; symmetry; apply U_to)
         | (rewrite (K3 _) by inl; rewrite (K2 _) by inl; apply K1; inl) ] |]). destruct Hi. }
    split. exact KK. split. { apply preserved_by_index. intros k Hk. apply KK. revert k Hk. kl sm_kept. }
    split. { eapply ctx_keep. exact C2. exact MG3. exact AG3. }
    split. { eapply agree_trans. exact AG1. eapply agree_trans. exact AG2. exact AG3. }
    eapply mem_grows_trans. exact MG1. eapply mem_grows_trans. exact MG2. exact MG3. }
  destruct SV2 as (V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25).
  pose proof (br_93f74 fx2 R2 M2) as MB.
  destruct (branch_taken BC_GEU (getr R2 (reg 20)) (getr R2 (reg 15))).
  - (* [comment removed for export] *)
    openF C2.
    pose proof (vsmK_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 41%nat => U R 1 | 42%nat => U R 8 | 43%nat => U R 9 | 44%nat => U R 18 | 45%nat => U R 19
                  | 46%nat => U R 20 | 47%nat => U R 21 | 48%nat => U R 22 | 49%nat => U R 23 | 50%nat => U R 24 | 51%nat => U R 25 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx3 & R3 & M3 & MG3 & kFR & kFZ & (kMS & kKS & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25)).
    apply (FIN fx3 R3 M3); try assumption. { eapply msteps_trans. exact MB. exact kMS. } { intros x Hx. apply kKS. revert x Hx. kl KS_vsmK. }
    { intros i Hi _ _ _. apply kFZ. exact Hi. }
  - (* [comment removed for export] *)
    assert (S3 : exists fx3 R3 M3, msteps RSEGS (st fx2 R2 0x942cc M2) (st fx3 R3 L2HEAD M3) /\ at_l2 R3 sp a b qa n 0
               /\ (forall x, In x [3; 4; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x))
               /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (qa <= i < qa + 8) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)) /\ mem_grows M2 M3).
    { openF C2. destruct AT1 as (A2 & A5 & A6 & A7 & A8 & A9 & A11 & A12 & A13 & A14 & A16' & A17 & A18 & A29 & A30 & A31).
      pose proof (vsmB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K2 _) by inl; sc)]).
      destruct P as (fx3 & R3 & M3 & MG3 & bFR & bFZ & (bMS & bKS & B5 & B6 & B7 & B10 & B14 & B15 & B28)).
      exists fx3, R3, M3. split. exact bMS.
      split. { unfold at_l2. change (Z.of_nat 0) with 0. repeat split.
        - rewrite (bKS 2%nat) by inl. exact R2_2.
        - exact B5.
        - rewrite B7. f_equal; clear; lia.
        - rewrite B10. f_equal; clear; lia.
        - rewrite (bKS 11%nat), (K2 11%nat) by inl. exact A11.
        - rewrite (bKS 12%nat), (K2 12%nat) by inl. rewrite A12. f_equal; clear; lia.
        - rewrite (bKS 13%nat), (K2 13%nat) by inl. exact A13.
        - rewrite B14. f_equal; clear; lia.
        - rewrite B15. f_equal; clear; lia.
        - rewrite (bKS 16%nat), (K2 16%nat) by inl. exact A16'.
        - rewrite (bKS 17%nat), (K2 17%nat) by inl. exact A17.
        - rewrite B28. f_equal; clear; lia. }
      split. { intros x Hx. apply bKS. revert x Hx. kl KS_vsmB. }
      split. { intros i Hi Hn. apply bFZ. exact Hi. clear - Hn; lia. } exact MG3. }
    destruct S3 as (fx3 & R3 & M3 & MS3 & AT3 & K3 & FR3 & MG3).
    assert (AG3 : sm_agree M2 M3 sp a qa n). { intros i Hi _ _ Hn. apply FR3; assumption. }
    assert (C3 : smctxA M3 sp a b qa n) by (eapply ctx_keep; eassumption).
    destruct (loop2 n fx3 R3 M3 sp a b qa n 0 ltac:(clear; lia) C3 AT3 ltac:(clear - NR; lia)) as (fx4 & R4 & M4 & MS4 & K4 & FR4 & MG4).
    assert (FR4z := word_agree M3 M4 (fun i => a <= i < a + 8 * Z.of_nat n + 8) FR4). cbn beta in FR4z.
    assert (AG4 : sm_agree M3 M4 sp a qa n). { intros i Hi _ Hn _. apply FR4z; assumption. }
    assert (C4 : smctxA M4 sp a b qa n) by (eapply ctx_keep; eassumption).
    assert (SV4 : saved M4 sp R).
    { eapply saved_keep. exact SPR. 2:{ eapply saved_keep. exact SPR. 2:{ unfold saved. repeat split; eassumption. }
        intros i Hi. apply FR3. clear - Hi SPR; lia. clear - Hi AP3; lia. }
      intros i Hi. apply FR4z. clear - Hi SPR; lia. clear - Hi AP1; lia. }
    destruct SV4 as (W1 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25).
    destruct AT3 as (A2 & A5 & A7 & A10 & A11 & A12 & A13 & A14 & A15 & A16' & A17 & A28).
    openF C4.
    pose proof (vsmT_conc fx4 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => a | 34%nat => b | 35%nat => Z.of_nat n | 36%nat => qa
                  | 41%nat => U R 1 | 42%nat => U R 8 | 43%nat => U R 9 | 44%nat => U R 18 | 45%nat => U R 19
                  | 46%nat => U R 20 | 47%nat => U R 21 | 48%nat => U R 22 | 49%nat => U R 23 | 50%nat => U R 24 | 51%nat => U R 25 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K4 _) by inl; sc)]).
    destruct P as (fx5 & R5 & M5 & MG5 & tFR & tFZ & (tMS & tKS & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & CZ & DFZ)).
    apply (FIN fx5 R5 M5); try assumption.
    { eapply msteps_trans. exact MB. eapply msteps_trans. exact MS3. eapply msteps_trans. exact MS4. exact tMS. }
    { intros x Hx. rewrite (tKS x). rewrite (K4 x). apply K3. exact Hx. revert x Hx. kl KSL2. revert x Hx. kl KS_vsmT. }
    { eapply agree_trans. exact AG3. eapply agree_trans. exact AG4. intros i Hi _ Hn _. apply tFZ. exact Hi. clear - Hn NR. lia. }
    { eapply mem_grows_trans. exact MG3. eapply mem_grows_trans. exact MG4. exact MG5. }
Qed.

End SCFG_1.
End L5ASM.
