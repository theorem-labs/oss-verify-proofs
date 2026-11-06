(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_23138_2379c BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU L5Defs L5Words L5ReduceU L5ShrU
     L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5DivSpecsU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5UnnormMU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5UNNMU.
Import L5CSU.
Module P1S := LibSegZ_lcuu1s.
Module P1N := LibSegZ_lcuu1n.
Module P2 := LibSegZ_lcuu2.
Module P3Z := LibSegZ_lcuu3z.
Module P3P := LibSegZ_lcuu3p.
Module P4 := LibSegZ_lcuu4.
Module P5 := LibSegZ_lcuu5.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition UNNORM : Z := 0x23140.
Definition OPDIV : Z := 0x23594.
Definition DIVEQ_RET : Z := 0x2318c.  (* [comment removed for export] *)
Definition MID : Z := 0x231ac.        (* [comment removed for export] *)
Definition SHR : Z := 0x23624.
Definition SHR_RET : Z := 0x231bc.
Definition REDUCE : Z := 0x21abc.
Definition RED_RET : Z := 0x231c4.
Definition RETI : Z := 0x231d4.       (* [comment removed for export] *)
Definition MWORD : Z := 2 ^ 64 - 1.

Definition KS1S : list nat := Eval vm_compute in (BGU.kept_list 48 P1S.regs0 P1S.regs_out).
Lemma KS1S_ok : BGU.kept_ok 48 P1S.regs0 P1S.regs_out KS1S = true. Proof. vm_compute. reflexivity. Qed.
Definition KS1N : list nat := Eval vm_compute in (BGU.kept_list 48 P1N.regs0 P1N.regs_out).
Lemma KS1N_ok : BGU.kept_ok 48 P1N.regs0 P1N.regs_out KS1N = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BGU.kept_list 48 P2.regs0 P2.regs_out).
Lemma KS2_ok : BGU.kept_ok 48 P2.regs0 P2.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS3Z : list nat := Eval vm_compute in (BGU.kept_list 48 P3Z.regs0 P3Z.regs_out).
Lemma KS3Z_ok : BGU.kept_ok 48 P3Z.regs0 P3Z.regs_out KS3Z = true. Proof. vm_compute. reflexivity. Qed.
Definition KS3P : list nat := Eval vm_compute in (BGU.kept_list 48 P3P.regs0 P3P.regs_out).
Lemma KS3P_ok : BGU.kept_ok 48 P3P.regs0 P3P.regs_out KS3P = true. Proof. vm_compute. reflexivity. Qed.
Definition KS4 : list nat := Eval vm_compute in (BGU.kept_list 48 P4.regs0 P4.regs_out).
Lemma KS4_ok : BGU.kept_ok 48 P4.regs0 P4.regs_out KS4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS5_ok : BGU.kept_ok 48 P5.regs0 P5.regs_out KS4 = true. Proof. vm_compute. reflexivity. Qed.

Lemma ret_230d0 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M RETI W_231d4 r F_231d4 eq_refl D_231d4 H1 Hr He). Qed.

(* [comment removed for export] *)
Lemma sregs_cases (P : Z -> Prop) :
  (forall j : nat, In j [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> P (Z.of_nat j)) -> forall k, 18 <= k <= 27 -> P k.
Proof.
  intros H k Hk.
  assert (E: k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]];
    [apply (H 18%nat)|apply (H 19%nat)|apply (H 20%nat)|apply (H 21%nat)|apply (H 22%nat)|apply (H 23%nat)|apply (H 24%nat)|apply (H 25%nat)|apply (H 26%nat)|apply (H 27%nat)];
    cbn; tauto.
Qed.

(* [comment removed for export] *)
Ltac lastc H := repeat (lazymatch type of H with _ /\ _ => apply proj2 in H end).

Lemma land253_bit1 fb : Z.testbit fb 1 = false -> Z.testbit (Z.land fb 253) 1 = false.
Proof. intros H. rewrite Z.land_spec, H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1s_run fx R M (sp : Z) :
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 13) = Z_to_bv 64 1 -> sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R UNNORM M) (st fx' R1 OPDIV M1)
    /\ (forall x, In x KS1S -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 DIVEQ_RET /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64)
    /\ getr R1 (reg 8) = getr R (reg 11) /\ getr R1 (reg 9) = getr R (reg 12) /\ getr R1 (reg 10) = getr R (reg 11) /\ getr R1 (reg 11) = Z_to_bv 64 (sp - 56)
    /\ BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8))) /\ BGU.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9)))
    /\ BGU.u8_at M1 (sp - 56) 0 /\ BGU.u64_at M1 (sp - 48) 1 /\ BGU.u64_at M1 (sp - 40) MWORD /\ BGU.u64_at M1 (sp - 32) 0
    /\ (forall a : word, ~ (sp - 64 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H2 H13 A16 SLO SHI WR.
  set (Vf := fun j : nat => getr R (reg j)).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BGU.unsigned_lit; lia).
  assert (U13: bv_unsigned (ev E 13) = 1) by (cbv [E ev Vf]; rewrite H13; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P1S.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P1S.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M P1S.kn0).
  { unfold know_ok. cbv delta [P1S.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U13. lia. }
    apply Forall_nil. }
  destruct (P1S.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P1S.NX0 with 48%nat in Hag.
  assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  assert (CELL: forall off j, In (KWord (SA (EVar 2) off) 8 (EVar j)) P1S.cells -> (j < 32)%nat -> BGU.u64_at M' (sp + off) (bv_unsigned (getr R (reg j)))).
  { intros off j Hin Hj. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. exact Hin. exact A2.
    cbn [edenot]. rewrite AG by lia. reflexivity. }
  assert (CELLc: forall off c, In (KWord (SA (EVar 2) off) 8 (ELit c)) P1S.cells -> 0 <= c < 2 ^ 64 -> BGU.u64_at M' (sp + off) c).
  { intros off c Hin Hc. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. exact Hin. exact A2. cbn [edenot]. apply BGU.unsigned_lit. lia. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P1S.regs0 P1S.regs_out 48 KS1S KS1S_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg P1S.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BGU.out_reg P1S.regs_out E' R' 2 Hregs) by lia. change (nth 2 P1S.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-64))).
           cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
  split. { rewrite (BGU.out_reg P1S.regs_out E' R' 8 Hregs) by lia. change (nth 8 P1S.regs_out (ELit 0)) with (EVar 11). cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { rewrite (BGU.out_reg P1S.regs_out E' R' 9 Hregs) by lia. change (nth 9 P1S.regs_out (ELit 0)) with (EVar 12). cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { rewrite (BGU.out_reg P1S.regs_out E' R' 10 Hregs) by lia. change (nth 10 P1S.regs_out (ELit 0)) with (EVar 11). cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { rewrite (BGU.out_reg P1S.regs_out E' R' 11 Hregs) by lia. change (nth 11 P1S.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-56))).
           cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
  split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [P1S.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [P1S.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [cbv delta [P1S.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 56) with (sp + -56) by lia. eapply (BIU.u8_of_KWord1_e E' M' 2 (-56) (ELit 0) sp 0). apply Hcells. cbv delta [P1S.cells]; cbn; tauto.
           exact A2. reflexivity. lia. }
  split. { replace (sp - 48) with (sp + -48) by lia. apply CELLc. cbv delta [P1S.cells]; cbn; tauto. lia. }
  split. { replace (sp - 40) with (sp + -40) by lia. apply CELLc. cbv delta [P1S.cells]; cbn; tauto. unfold MWORD. lia. }
  split. { replace (sp - 32) with (sp + -32) by lia. apply CELLc. cbv delta [P1S.cells]; cbn; tauto. lia. }
  split. { intros a Ha. apply Hfr. unfold SGP.outside. change P1S.F0 with [(EVar 2, -64, ELit 64)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1n_run fx R M (sp : Z) :
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 13) = Z_to_bv 64 0 -> sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R UNNORM M) (st fx' R1 MID M1)
    /\ (forall x, In x KS1N -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R1 (reg 8) = getr R (reg 11) /\ getr R1 (reg 9) = getr R (reg 12)
    /\ BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8))) /\ BGU.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9)))
    /\ (forall a : word, ~ (sp - 64 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H2 H13 A16 SLO SHI WR.
  set (Vf := fun j : nat => getr R (reg j)).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BGU.unsigned_lit; lia).
  assert (U13: bv_unsigned (ev E 13) = 0) by (cbv [E ev Vf]; rewrite H13; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P1N.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P1N.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M P1N.kn0).
  { unfold know_ok. cbv delta [P1N.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U13. lia. }
    apply Forall_nil. }
  destruct (P1N.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P1N.NX0 with 48%nat in Hag.
  assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  assert (CELL: forall off j, In (KWord (SA (EVar 2) off) 8 (EVar j)) P1N.cells -> (j < 32)%nat -> BGU.u64_at M' (sp + off) (bv_unsigned (getr R (reg j)))).
  { intros off j Hin Hj. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. exact Hin. exact A2.
    cbn [edenot]. rewrite AG by lia. reflexivity. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P1N.regs0 P1N.regs_out 48 KS1N KS1N_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg P1N.regs_out E' R' 2 Hregs) by lia. change (nth 2 P1N.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-64))).
           cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
  split. { rewrite (BGU.out_reg P1N.regs_out E' R' 8 Hregs) by lia. change (nth 8 P1N.regs_out (ELit 0)) with (EVar 11). cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { rewrite (BGU.out_reg P1N.regs_out E' R' 9 Hregs) by lia. change (nth 9 P1N.regs_out (ELit 0)) with (EVar 12). cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [P1N.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [P1N.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [cbv delta [P1N.cells]; cbn; tauto | lia]. }
  split. { intros a Ha. apply Hfr. unfold SGP.outside. change P1N.F0 with [(EVar 2, -64, ELit 64)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2_run fx R M (X xs sp : Z) :
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 xs -> 0 <= X < 2 ^ 64 -> 0 <= xs < 2 ^ 64 ->
  BGU.u8_at M (sp - 56) 0 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R DIVEQ_RET M) (st fx' R1 MID M1)
    /\ (forall x, In x KS2 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R1 (reg 8) = Z_to_bv 64 X /\ getr R1 (reg 9) = Z_to_bv 64 xs
    /\ (forall a : word, M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H2 H8 H9 HX Hxs F0t A16 SLO SHI WR.
  set (Vf := fun j : nat => match j with 2%nat => Z_to_bv 64 sp | 33%nat => Z_to_bv 64 X | 34%nat => Z_to_bv 64 xs | _ => getr R (reg j) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = X) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = xs) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P2.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P2.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P2.kn0).
  { unfold know_ok. cbv delta [P2.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { cbn [kentry_ok]. split. lia. split. { unfold flat. rewrite BGU.estart_var, U2. lia. }
                         rewrite BGU.adenot_var, U2. cbn [edenot]. rewrite BGU.word_to_le_bytes_1 by lia. replace (sp + -56) with (sp - 56) by lia. exact F0t. }
    apply Forall_nil. }
  destruct (P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P2.NX0 with 48%nat in Hag.
  assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
  assert (OUT: forall i j z, (0 < i < 32)%nat -> nth i P2.regs_out (ELit 0) = EVar j -> (j < 48)%nat -> bv_unsigned (ev E j) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros i' j z Hi Hnth Hj Hz. rewrite (BGU.out_reg P2.regs_out E' R' i' Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P2.regs0 P2.regs_out 48 KS2 KS2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg P2.regs_out E' R' 2 Hregs) by lia. change (nth 2 P2.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-64))).
           cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U2), BGU.alu_add_lit. reflexivity. }
  split. { apply (OUT 8%nat 33%nat); [lia | reflexivity | lia | exact U33]. }
  split. { apply (OUT 9%nat 34%nat); [lia | reflexivity | lia | exact U34]. }
  split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p3_run (z : bool) fx R M (X xs sp : Z) :
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 9) = Z_to_bv 64 xs -> 0 <= X < 2 ^ 64 ->
  (if z then xs = 0 else 1 <= xs <= 63) ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R MID M) (st fx' R1 (if z then REDUCE else SHR) M1)
    /\ (forall x, In x (if z then KS3Z else KS3P) -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 (if z then RED_RET else SHR_RET) /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64)
    /\ getr R1 (reg 8) = Z_to_bv 64 X /\ getr R1 (reg 9) = Z_to_bv 64 xs /\ getr R1 (reg 10) = Z_to_bv 64 X /\ (z = false -> getr R1 (reg 11) = Z_to_bv 64 xs)
    /\ (forall a : word, M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H2 H8 H9 HX Hxs A16 SLO SHI WR.
  assert (Hxs': 0 <= xs <= 63) by (destruct z; lia).
  set (Vf := fun j : nat => match j with 2%nat => Z_to_bv 64 sp | 33%nat => Z_to_bv 64 X | 34%nat => Z_to_bv 64 xs | _ => getr R (reg j) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = X) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = xs) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HRX: forall regs0, regs0 = P3Z.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P3Z.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BGU.alu_add_lit. exact H2. }
  assert (SAME: P3P.regs0 = P3Z.regs0) by reflexivity.
  assert (KC: forall K, In K [KRange (EVar 2) 140735332483136 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-64)) (ELit 64)] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK. repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KRange_var. exact U2. lia.
    - eapply BGU.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (F0 : list SGP.region) (KSL : list nat) (ra : Z),
     regs0 = P3Z.regs0 -> BGU.kept_ok 48 regs0 regs_out KSL = true ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [] ->
     nth 1 regs_out (ELit 0) = ELit ra -> nth 2 regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-64)) ->
     nth 8 regs_out (ELit 0) = EVar 33 -> nth 9 regs_out (ELit 0) = EVar 34 -> nth 10 regs_out (ELit 0) = EVar 33 ->
     (z = false -> nth 11 regs_out (ELit 0) = EVar 34) ->
     mem_grows M M' ->
     (forall x, In x KSL -> getr R' (reg x) = getr R (reg x))
     /\ getr R' (reg 1) = Z_to_bv 64 ra /\ getr R' (reg 2) = Z_to_bv 64 (sp - 64)
     /\ getr R' (reg 8) = Z_to_bv 64 X /\ getr R' (reg 9) = Z_to_bv 64 xs /\ getr R' (reg 10) = Z_to_bv 64 X /\ (z = false -> getr R' (reg 11) = Z_to_bv 64 xs)
     /\ (forall a : word, M' a = M a) /\ mem_grows M M').
  { intros fx' E' R' M' regs0 regs_out F0 KSL ra -> KOK Hag Hregs Hfr -> N1 N2 N8 N9 N10 N11 Hgr.
    assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' P3Z.regs0 regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j Hj). }
    split. { rewrite (BGU.out_reg regs_out E' R' 1 Hregs) by lia. rewrite N1. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 2 Hregs) by lia. rewrite N2. cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U2), BGU.alu_add_lit. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 8 Hregs) by lia. rewrite N8. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U33. }
    split. { rewrite (BGU.out_reg regs_out E' R' 9 Hregs) by lia. rewrite N9. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U34. }
    split. { rewrite (BGU.out_reg regs_out E' R' 10 Hregs) by lia. rewrite N10. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U33. }
    split. { intros Hz. rewrite (BGU.out_reg regs_out E' R' 11 Hregs) by lia. rewrite (N11 Hz). cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U34. }
    split. { intros a. apply Hfr. constructor. } exact Hgr. }
  destruct z.
  - assert (HK: know_ok RSEGS E M P3Z.kn0).
    { unfold know_ok. cbv delta [P3Z.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | eapply BGU.kentry_KRange_var; [exact U34 | lia]] |]). apply Forall_nil. }
    destruct (P3Z.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' P3Z.regs0 P3Z.regs_out P3Z.F0 KS3Z RED_RET eq_refl KS3Z_ok Hag Hregs Hfr eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(intros; discriminate) Hgr).
  - assert (HK: know_ok RSEGS E M P3P.kn0).
    { unfold know_ok. cbv delta [P3P.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | eapply BGU.kentry_KRange_var; [exact U34 | lia]] |]). apply Forall_nil. }
    destruct (P3P.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' P3P.regs0 P3P.regs_out P3P.F0 KS3P SHR_RET eq_refl KS3P_ok Hag Hregs Hfr eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(intros; reflexivity) Hgr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p45_run (t : bool) fx R M (sp c8 c16 c24 r : Z) :
  getr R (reg 2) = Z_to_bv 64 (sp - 64) ->
  BGU.u64_at M (sp - 8) c8 -> BGU.u64_at M (sp - 16) c16 -> BGU.u64_at M (sp - 24) c24 -> 0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 -> 0 <= c24 < 2 ^ 64 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R (if t then SHR_RET else RED_RET) M) (st fx' R3 r M3)
    /\ (forall x, In x KS4 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H2 C8 C16 C24 R8 R16 R24 A16 SLO SHI WR Er [Hr He].
  set (Vf := fun j : nat => match j with 2%nat => Z_to_bv 64 sp | 43%nat => Z_to_bv 64 c8 | 44%nat => Z_to_bv 64 c16 | 47%nat => Z_to_bv 64 c24 | _ => getr R (reg j) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U47: bv_unsigned (ev E 47) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HRX: forall regs0, regs0 = P4.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P4.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BGU.alu_add_lit. exact H2. }
  assert (SAME: P5.regs0 = P4.regs0) by reflexivity.
  assert (KC: forall K, In K [KRange (EVar 2) 140735332483136 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-64)) (ELit 64);
                               KWord (SA (EVar 2) (-8)) 8 (EVar 43); KWord (SA (EVar 2) (-16)) 8 (EVar 44); KWord (SA (EVar 2) (-24)) 8 (EVar 47)] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK. repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KRange_var. exact U2. lia.
    - eapply BGU.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C8.
    - eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C16.
    - eapply BGU.kentry_KWord_var. exact U2. exact U47. lia. lia. exact C24. }
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (F0 : list SGP.region) (KSL : list nat) pc0,
     regs0 = P4.regs0 -> BGU.kept_ok 48 regs0 regs_out KSL = true -> incl KS4 KSL ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [] ->
     regs_out = P4.regs_out ->
     msteps RSEGS (st fx R pc0 M) (st fx' R' RETI M') -> mem_grows M M' ->
     exists fx'' R3 M3, msteps RSEGS (st fx R pc0 M) (st fx'' R3 r M3)
     /\ (forall x, In x KS4 -> getr R3 (reg x) = getr R (reg x))
     /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24
     /\ (forall a : word, M3 a = M a) /\ mem_grows M M3).
  { intros fx' E' R' M' regs0 regs_out F0 KSL pc0 -> KOK INCL Hag Hregs Hfr -> -> Hms Hgr.
    assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
    assert (OUT: forall i j z, (0 < i < 32)%nat -> nth i P4.regs_out (ELit 0) = EVar j -> (j < 48)%nat -> bv_unsigned (ev E j) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros i' j z Hi Hnth Hj Hz. rewrite (BGU.out_reg P4.regs_out E' R' i' Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
    assert (R1: getr R' (reg 1) = Z_to_bv 64 c8). { apply (OUT 1%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
    exists fx', R', M'. split.
    { eapply msteps_trans. exact Hms. apply ret_230d0. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' P4.regs0 P4.regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. exact R1.
    split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
    split. { apply (OUT 8%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
    split. { apply (OUT 9%nat 47%nat); [lia | reflexivity | lia | exact U47]. }
    split. { intros a. apply Hfr. constructor. } exact Hgr. }
  destruct t.
  - assert (HK: know_ok RSEGS E M P4.kn0).
    { unfold know_ok. cbv delta [P4.kn0]. repeat (apply Forall_cons; [apply KC; cbn; tauto |]). apply Forall_nil. }
    destruct (P4.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exact (POST fx' E' R' M' P4.regs0 P4.regs_out P4.F0 KS4 SHR_RET eq_refl KS4_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl eq_refl Hms Hgr).
  - assert (HK: know_ok RSEGS E M P5.kn0).
    { unfold know_ok. cbv delta [P5.kn0]. repeat (apply Forall_cons; [apply KC; cbn; tauto |]). apply Forall_nil. }
    destruct (P5.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exact (POST fx' E' R' M' P5.regs0 P5.regs_out P5.F0 KS4 RED_RET eq_refl KS5_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl eq_refl Hms Hgr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kept_not_scratch L LB sp scr W a :
  L5C.kept L LB sp scr W a -> (forall b, In b LB -> fst b + snd b <= hl_ceil L) -> hl_ceil L + scr <= sp -> hl_img_hi L <= sp - scr ->
  ~ (sp - scr <= a < sp).
Proof.
  intros (Ha & CA & NE & OW) LBhi Hsp Himg. destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]].
  - pose proof (LBhi b Hb). lia.
  - exact S2.
  - lia.
Qed.

Lemma Forall_firstn {A} (P : A -> Prop) (l : list A) n : Forall P l -> Forall P (firstn n l).
Proof. revert n. induction l as [|x l IH]; intros [|n] H; cbn; try constructor. inversion H; auto. inversion H; auto. Qed.

(* [comment removed for export] *)
Lemma limbs_of_obj M o fb n st ws :
  L5.big_at RSEGS M o (L5.BO fb n st) -> L5C.obj_limbs RSEGS M (L5.BO fb n st) ws -> L5.limbs_at RSEGS M (L5.bo_data o (L5.BO fb n st)) ws.
Proof.
  intros (O0 & Hfb & O8 & OST) (Lw & Rw & Vw). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in *.
  destruct st as [v0 v1|cap q]. 2: exact Vw.
  destruct OST as (B0 & O16 & O24 & Hl2 & R0 & R1). subst ws.
  destruct n as [|[|[|n]]]; cbn; intros i Hi; cbn in Hi.
  - lia.
  - destruct i as [|i]. rewrite Z.mul_0_r, Z.add_0_r. exact O16. lia.
  - destruct i as [|[|i]]. rewrite Z.mul_0_r, Z.add_0_r. exact O16. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by lia. exact O24. lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma obj_limbs_agree M M' fb n st ws :
  L5C.obj_limbs RSEGS M (L5.BO fb n st) ws ->
  (forall cap q, st = L5.BDyn cap q -> L5C.agree_on M M' q (8 * Z.of_nat (length ws)) /\ 0 <= q /\ q + 8 * Z.of_nat (length ws) <= 2 ^ 64) ->
  L5C.obj_limbs RSEGS M' (L5.BO fb n st) ws.
Proof.
  intros (Lw & Rw & Vw) H. split. exact Lw. split. exact Rw. cbn [L5.bo_st L5.bo_len] in Vw |- *. destruct st as [v0 v1|cap q]. exact Vw.
  destruct (H cap q eq_refl) as (AG & Q0 & Q1). eapply (L5C.limbs_at_agree RSEGS M M'). exact AG. exact Q0. exact Q1. exact Vw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis SHRZ : L5DSU.shrz_spec L HI.
Hypothesis SHRS : L5SHRU.shr_spec.
Hypothesis RED : L5REDU.reduce_spec.

(* [comment removed for export] *)
Lemma from_mid (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit)
      (X xs sp r fb : Z) (len : nat) (sto : L5.bstore)
      (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (cr1 : credit)
      (fb1 : Z) (n1 : nat) (st1 : L5.bstore) (w1 : list Z) :
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr',
        L5DSU.unnorm_post L LB cr M M' R R' X sp (L5.BO fb len sto) cr' ->
        model_but_vm model model' -> hi_heap HI LB cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (L5DSU.cfg R' r M' model') K) ->
  model_ok model -> K [] ->
  getr R 2%bv = Z_to_bv 64 sp -> getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 4%bv = Z_to_bv 64 TP -> 0 <= xs <= 63 ->
  L5C.stk (hl_sptop L) M sp L5DSU.UNNORM_SCR ->
  X mod 8 = 0 -> sp <= X -> X + 32 <= hl_sptop L ->
  (forall cap q, sto = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
  getr R1 (reg 2) = Z_to_bv 64 (sp - 64) -> getr R1 (reg 8) = Z_to_bv 64 X -> getr R1 (reg 9) = Z_to_bv 64 xs ->
  getr R1 (reg 3) = getr R (reg 3) -> getr R1 (reg 4) = getr R (reg 4) ->
  (forall j, In j [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg j) = getr R (reg j)) ->
  BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) -> BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8))) -> BGU.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))) ->
  L5.big_at RSEGS M1 X (L5.BO fb1 n1 st1) -> L5C.obj_limbs RSEGS M1 (L5.BO fb1 n1 st1) w1 -> Z.testbit fb1 1 = false -> (n1 <= 299)%nat ->
  match sto, st1 with
  | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
  | L5.BInl _ _, L5.BInl _ _ => True
  | _, _ => False end ->
  ((1 <= n1)%nat \/ exists cap q, st1 = L5.BDyn cap q) ->
  L5.defined M1 (L5.bo_data X (L5.BO fb len sto)) (8 * L5.bo_cap (L5.BO fb len sto)) ->
  L5.defined M1 X 32 ->
  L5C.hpres L LB sp L5DSU.UNNORM_SCR [(X, 32); (L5.bo_data X (L5.BO fb len sto), 8 * L5.bo_cap (L5.BO fb len sto))] M M1 ->
  hi_heap HI LB cr1 M1 (m_vmmaps model1) -> model_but_vm model model1 ->
  L5DSU.credit_after L cr L5DSU.DIVN_K L5DSU.DIVN_BYTES cr1 ->
  srealizes RSEGS SCFG (mkCfg (st fx1 R1 MID M1) model1) K.
Proof.
  intros KONT MOK HK0 H2 H1 RA H4 Hxs STK Ao Olo Ohi BLK R1_2 R1_8 R1_9 R1_3 R1_4 R1s C8 C16 C24 OB1 OL1 NEG1 Hn1 KIND NZ DEF1 DEFX1 HP1 HH1 MBV1 CRA1.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF).
  unfold L5DSU.UNNORM_SCR, L5DSU.DIVEQ_SCR, L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  pose proof (L5C.halted_but_vm _ _ MBV1) as Mh1. rewrite Mh in Mh1. pose proof (L5C.lazy_but_vm _ _ MBV1) as Ml1. rewrite Ml in Ml1.
  pose proof (L5C.materialized_but_vm _ _ MBV1) as Mm1. rewrite Mm in Mm1.
  destruct HP1 as (PRES1 & SDEF1 & CDEF1).
  unfold L5DSU.UNNORM_SCR, L5DSU.DIVEQ_SCR, L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES1, SDEF1, CDEF1.
  assert (LBhi: forall bb, In bb LB -> fst bb + snd bb <= hl_ceil L).
  { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr1 M1 _ HH1) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  assert (LBimg: forall q c, In (q, c) LB -> 4096 <= q /\ (q + c <= 0x10000 \/ 0x92000 <= q) /\ q + c <= hl_ceil L).
  { intros q c Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr1 M1 _ HH1) _ Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). cbn [fst snd] in Q0, Q1, Q4.
    rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. repeat split; assumption. }
  assert (DEF1z: forall a, sp - (64 + (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))))) <= a < sp -> M1 (Z_to_bv 64 a) <> None).
  { intros a Ha. replace a with (sp - (64 + (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))))) + (a - (sp - (64 + (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))))))) by lia.
    apply SDEF1. lia. }
  assert (WR64: BGU.writable M1 (sp - 64) 64).
  { change (L5.writable RSEGS M1 (sp - 64) 64). apply (L5C.writable_of_defined RSEGS). intros i Hi. apply DEF1z. lia. lia. lia. }
  pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8. pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as RG9.
  change (bv_modulus 64) with (2 ^ 64) in RG1, RG8, RG9.
  assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BGU.unsigned_lit. lia. }
  pose proof OB1 as (O0 & Hfb1 & O8 & OST1). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb1, O8, OST1.
  pose proof OL1 as (Lw1 & Rw1 & Vw1). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Lw1, Vw1.
  (* [comment removed for export] *)
  assert (DC: L5.bo_data X (L5.BO fb1 n1 st1) = L5.bo_data X (L5.BO fb len sto) /\ L5.bo_cap (L5.BO fb1 n1 st1) = L5.bo_cap (L5.BO fb len sto)
              /\ Z.of_nat n1 <= L5.bo_cap (L5.BO fb len sto)
              /\ (4096 <= L5.bo_data X (L5.BO fb len sto) /\ L5.bo_data X (L5.BO fb len sto) + 8 * L5.bo_cap (L5.BO fb len sto) <= 2 ^ 47)
              /\ (forall a, L5.bo_data X (L5.BO fb len sto) <= a < L5.bo_data X (L5.BO fb len sto) + 8 * L5.bo_cap (L5.BO fb len sto) ->
                     (X + 16 <= a < X + 32) \/ (in_block LB a /\ a < hl_ceil L /\ (a + 1 <= 0x10000 \/ 0x92000 <= a)))).
  { destruct sto as [v0 v1|cap q]; destruct st1 as [v0' v1'|cap' q']; try contradiction; cbn [L5.bo_data L5.bo_cap L5.bo_st L5.bo_len].
    - destruct OST1 as (_ & _ & _ & Hl2 & _). split. reflexivity. split. reflexivity. split. lia. split. lia. intros a Ha. left. lia.
    - destruct KIND as [-> ->]. destruct OST1 as (_ & _ & _ & Hlc & Hc & _ & Qlo & Qhi & _). split. reflexivity. split. reflexivity. split. lia. split. lia.
      intros a Ha. right. destruct (LBimg q (8 * cap) (BLK cap q eq_refl)) as (Q0 & Q1 & Q4). split. exists (q, 8 * cap). split. exact (BLK cap q eq_refl). cbn. lia. lia. }
  destruct DC as (DATA & CAP & NCAP & DRANGE & DWHERE).
  pose proof DEF1 as DEF1'. rewrite <- DATA, <- CAP in DEF1'.
  pose proof (limbs_of_obj M1 X fb1 n1 st1 w1 OB1 OL1) as LA1. rewrite DATA in LA1.
  assert (APART1: forall cap q, st1 = L5.BDyn cap q -> q + 8 * cap <= X \/ X + 32 <= q).
  { intros cap q Hq. subst st1. destruct sto as [v0 v1|cap0 q0]; try contradiction. destruct KIND as [-> ->].
    left. pose proof (LBhi _ (BLK cap0 q0 eq_refl)) as Hb. cbn [fst snd] in Hb. lia. }
  (* [comment removed for export] *)
  assert (REGS: forall (R2 R3 R4 : bvmap 5 word) (KA KB : list nat),
     (forall x, In x KA -> getr R2 (reg x) = getr R1 (reg x)) -> incl [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat KA ->
     regs_preserved R2 R3 ->
     (forall x, In x KB -> getr R4 (reg x) = getr R3 (reg x)) -> incl [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat KB ->
     getr R4 (reg 2) = Z_to_bv 64 sp -> getr R4 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) -> getr R4 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) ->
     regs_preserved R R4).
  { intros R2 R3 R4 KA KB K2 IA RP3 K4 IB E2 E8 E9. apply L5K.regs_preserved_by_index. intros i Hi.
    cbn in Hi. destruct Hi as [<-|Hi]. { rewrite E2, <- H2, L5K.rl2. reflexivity. }
    assert (G: forall j, In j [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R (reg j)).
    { intros j Hj. assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
      rewrite (K4 j (IB j Hj)). rewrite (L5K.regs_preserved_index R2 R3 j RP3 MCj). rewrite (K2 j (IA j Hj)).
      cbn in Hj. destruct Hj as [<-|Hj]. exact R1_3. destruct Hj as [<-|Hj]. exact R1_4. apply R1s. L5K.inlist Hj. }
    destruct Hi as [<-|Hi]. { apply G. cbn; tauto. }
    destruct Hi as [<-|Hi]. { apply G. cbn; tauto. }
    destruct Hi as [<-|Hi]. { rewrite E8. symmetry. apply BGU.word_of_unsigned. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite E9. symmetry. apply BGU.word_of_unsigned. reflexivity. }
    apply G. cbn. cbn in Hi. tauto. }
  destruct (Z.eq_dec xs 0) as [Xz|Xnz].
  - (* [comment removed for export] *)
    destruct (p3_run true fx1 R1 M1 X xs sp R1_2 R1_8 R1_9 ltac:(lia) Xz A16 ltac:(lia) ltac:(lia) WR64)
      as (fx2 & R2 & M2 & MS2 & K2 & R2_1 & R2_2 & R2_8 & R2_9 & R2_10 & _ & MF2 & GR2).
    eapply (L5.cps_of_msteps RSEGS). exact Mh1. exact Ml1. exact MS2.
    eapply (RED fx2 R2 M2 model1 K X RED_RET (L5.BO fb1 n1 st1) w1).
    + exact Mh1.
    + exact Ml1.
    + exact R2_10.
    + exact R2_1.
    + split. unfold RED_RET. lia. reflexivity.
    + eapply (L5C.big_at_agree RSEGS M1 M2). intros i Hi. apply MF2. lia. lia. exact OB1.
    + exact Ao.
    + lia.
    + lia.
    + change (L5.writable RSEGS M2 X 16). apply (L5C.writable_of_defined RSEGS). intros i Hi. rewrite (MF2 (Z_to_bv 64 _)). apply DEFX1. lia. lia. lia.
    + intros i Hi. rewrite (MF2 (Z_to_bv 64 _)). apply DEF1'. exact Hi.
    + rewrite DATA. eapply (L5C.limbs_at_agree RSEGS M1 M2). intros i Hi. apply MF2. lia. rewrite Lw1. lia. exact LA1.
    + exact Lw1.
    + exact Rw1.
    + cbn [L5.bo_st]. exact APART1.
    + (* [comment removed for export] *)
      intros fx3 R3 M3 POST3. unfold L5REDU.reduce_post in POST3. cbv zeta in POST3. cbn [L5.bo_fb L5.bo_len L5.bo_st] in POST3.
      destruct POST3 as (OB3 & RP3 & R3_10 & FR3 & GR3).
      assert (FR3z: forall a, 0 <= a < 2 ^ 64 -> ~ (X <= a < X + 16) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha Hna. rewrite FR3. apply MF2. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. rewrite BGU.unsigned_lit by lia. lia. }
      assert (T3: forall a v, sp - 64 <= a -> a + 8 <= sp -> BGU.u64_at M1 a v -> BGU.u64_at M3 a v).
      { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M3). intros i Hi. apply FR3z; lia. lia. lia. exact Hu. }
      assert (WR3: BGU.writable M3 (sp - 64) 64).
      { change (L5.writable RSEGS M3 (sp - 64) 64). eapply L5.writable_grows. exact GR3. eapply L5.writable_grows. exact GR2. exact WR64. }
      assert (R3_2: getr R3 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite <- L5K.rl2, (RP3 2%bv ltac:(cbn; tauto)), L5K.rl2. exact R2_2. }
      destruct (p45_run false fx3 R3 M3 sp _ _ _ r R3_2 (T3 (sp - 8) _ ltac:(lia) ltac:(lia) C8) (T3 (sp - 16) _ ltac:(lia) ltac:(lia) C16) (T3 (sp - 24) _ ltac:(lia) ltac:(lia) C24)
                  RG1 RG8 RG9 A16 ltac:(lia) ltac:(lia) WR3 E1 RA)
        as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_9 & MF4 & GR4).
      eapply (L5.cps_of_msteps RSEGS). exact Mh1. exact Ml1. exact MS4.
      apply (KONT fx4 R4 M4 model1 cr1).
      * split. { apply (REGS R2 R3 R4 KS3Z KS4 K2 ltac:(intros x Hx; L5K.inlist Hx) RP3 K4 ltac:(intros x Hx; L5K.inlist Hx) R4_2 R4_8 R4_9). }
        split.
        { set (k := L5W.rlen w1). pose proof (L5W.rlen_le w1) as RLE. fold k in RLE. rewrite Lw1 in RLE.
          exists (if Nat.eqb k 0 then Z.land fb1 253 else fb1), k, st1, (firstn k w1).
          split. { eapply (L5C.big_at_agree RSEGS M3 M4). intros i Hi. apply MF4. lia. lia. exact OB3. }
          split. { split. cbn [L5.bo_len]. rewrite length_firstn, Lw1. lia. split. apply Forall_firstn. exact Rw1.
                   cbn [L5.bo_st L5.bo_len]. destruct st1 as [v0 v1|cap q].
                   - rewrite Vw1. apply L5C.firstn_firstn_le. exact RLE.
                   - apply L5C.limbs_at_firstn. pose proof (APART1 cap q eq_refl) as AP. destruct OST1 as (_ & _ & _ & Hlc & Hc & _ & Qlo & Qhi & _).
                     eapply (L5C.limbs_at_agree RSEGS M1 M4). 2: lia. 2: rewrite Lw1; lia. 2: exact Vw1.
                     intros i Hi. rewrite Lw1 in Hi. rewrite (MF4 (Z_to_bv 64 i)). apply FR3z. lia. lia. }
          split. { destruct (Nat.eqb k 0). apply land253_bit1. exact NEG1. exact NEG1. }
          destruct sto as [v0 v1|cap q]; destruct st1 as [v0' v1'|cap' q']; try contradiction. exact I.
          destruct KIND as [-> ->]. split. reflexivity. split. reflexivity.
          cbn [L5.bo_data L5.bo_cap L5.bo_st] in DEF1. intros i Hi. apply GR4. apply GR3. apply GR2. apply DEF1. exact Hi. }
        split. exact CRA1.
        (* [comment removed for export] *)
        split.
        { intros a Ka. pose proof Ka as (Ha & _ & _ & OW). apply L5C.outside_cons_inv in OW as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
          rewrite (MF4 (Z_to_bv 64 a)). rewrite FR3z. apply PRES1. exact Ka. lia. lia. }
        split. { intros i Hi. apply GR4. apply GR3. apply GR2. apply SDEF1. exact Hi. }
        intros a Ha CA NE D0. apply GR4. apply GR3. apply GR2. apply (CDEF1 a Ha CA NE D0).
      * exact MBV1.
      * eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH1. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
        intros a Ha. destruct (Z_lt_le_dec a X) as [Hlt|Hge]. left. rewrite (MF4 (Z_to_bv 64 a)). apply FR3z; lia.
        destruct (Z_lt_le_dec a (X + 16)) as [Hlt'|Hge']. right; left. unfold hl_ceil. lia. left. rewrite (MF4 (Z_to_bv 64 a)). apply FR3z; lia.
        eapply mem_grows_trans. exact GR2. eapply mem_grows_trans. exact GR3. exact GR4.
  - (* [comment removed for export] *)
    destruct (p3_run false fx1 R1 M1 X xs sp R1_2 R1_8 R1_9 ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia) WR64)
      as (fx2 & R2 & M2 & MS2 & K2 & R2_1 & R2_2 & R2_8 & R2_9 & R2_10 & R2_11 & MF2 & GR2).
    specialize (R2_11 eq_refl).
    eapply (L5.cps_of_msteps RSEGS). exact Mh1. exact Ml1. exact MS2.
    assert (HH2: hi_heap HI LB cr1 M2 (m_vmmaps model1)).
    { eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH1. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia. intros a Ha. left. apply MF2. exact GR2. }
    destruct (Nat.eq_dec n1 0) as [N0|N1].
    + (* [comment removed for export] *)
      destruct NZ as [Hge1|(cz & qz & Ez)]. exfalso; lia. subst st1. clear LA1 Vw1 Rw1 Lw1. subst n1.
      destruct sto as [v0 v1|cap q]. contradiction. destruct KIND as [-> ->].
      eapply (SHRZ fx2 R2 M2 model1 K LB cr1 X xs (sp - 64) SHR_RET fb1 (L5.BDyn cap q)).
      * exact HH2.
      * split. exact Mh1. split. exact Ml1. exact Mm1.
      * exact HK0.
      * exact R2_10.
      * exact R2_11.
      * lia.
      * exact R2_1.
      * split. unfold SHR_RET. lia. reflexivity.
      * exact R2_2.
      * rewrite <- H4. rewrite L5K.rl4. rewrite (K2 4%nat) by (apply L5K.In_of_mem; reflexivity). exact R1_4.
      * split. { replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
        unfold L5DSU.SHRZ_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
        intros i Hi. rewrite (MF2 (Z_to_bv 64 _)). apply DEF1z. lia.
      * eapply (L5C.big_at_agree RSEGS M1 M2). intros i Hi. apply MF2. lia. lia. exact OB1.
      * exists cap, q. split. reflexivity. exact (BLK cap q eq_refl).
      * exact Ao.
      * lia.
      * exact Ohi.
      * change (L5.writable RSEGS M2 X 32). apply (L5C.writable_of_defined RSEGS). intros i Hi. rewrite (MF2 (Z_to_bv 64 _)). apply DEFX1. lia. lia. lia.
      * (* [comment removed for export] *)
        intros fx3 R3 M3 model3 RP3 R3_10 OB3 HP3 MBV3 HH3.
        destruct HP3 as (PRES3 & SDEF3 & CDEF3). unfold L5DSU.SHRZ_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES3, SDEF3, CDEF3.
        pose proof (L5C.halted_but_vm _ _ MBV3) as Mh3. rewrite Mh1 in Mh3. pose proof (L5C.lazy_but_vm _ _ MBV3) as Ml3. rewrite Ml1 in Ml3.
        assert (CL3: forall a, sp - 64 <= a < sp -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros a Ha. rewrite PRES3. apply MF2. apply (L5C.kept_stack L LB (sp - 64) _ _). lia. lia. lia. rewrite (ly_errno L LY). lia. lia.
          apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. lia. apply L5C.outside_nil. }
        assert (T3: forall a v, sp - 64 <= a -> a + 8 <= sp -> BGU.u64_at M1 a v -> BGU.u64_at M3 a v).
        { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M3). intros i Hi. apply CL3; lia. lia. lia. exact Hu. }
        assert (WR3: BGU.writable M3 (sp - 64) 64).
        { change (L5.writable RSEGS M3 (sp - 64) 64). apply (L5C.writable_of_defined RSEGS). 2: lia. 2: lia. intros i Hi. rewrite CL3 by lia. apply DEF1z. lia. }
        assert (R3_2: getr R3 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite <- L5K.rl2, (RP3 2%bv ltac:(cbn; tauto)), L5K.rl2. exact R2_2. }
        destruct (p45_run true fx3 R3 M3 sp _ _ _ r R3_2 (T3 (sp - 8) _ ltac:(lia) ltac:(lia) C8) (T3 (sp - 16) _ ltac:(lia) ltac:(lia) C16) (T3 (sp - 24) _ ltac:(lia) ltac:(lia) C24)
                    RG1 RG8 RG9 A16 ltac:(lia) ltac:(lia) WR3 E1 RA)
          as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_9 & MF4 & GR4).
        eapply (L5.cps_of_msteps RSEGS). exact Mh3. exact Ml3. exact MS4.
        apply (KONT fx4 R4 M4 model3 cr1).
        -- split. { apply (REGS R2 R3 R4 KS3P KS4 K2 ltac:(intros x Hx; L5K.inlist Hx) RP3 K4 ltac:(intros x Hx; L5K.inlist Hx) R4_2 R4_8 R4_9). }
           split.
           { exists fb1, 0%nat, (L5.BDyn cap q), []. split. { eapply (L5C.big_at_agree RSEGS M3 M4). intros i Hi. apply MF4. lia. lia. exact OB3. }
             split. { split. reflexivity. split. constructor. cbn [L5.bo_st]. apply L5C.limbs_at_nil. }
             split. exact NEG1. split. reflexivity. split. reflexivity.
             cbn [L5.bo_data L5.bo_cap L5.bo_st] in DEF1. destruct (LBimg q (8 * cap) (BLK cap q eq_refl)) as (Q0 & Q1 & Q4).
             intros i Hi. rewrite (MF4 (Z_to_bv 64 _)). apply (CDEF3 (q + i)). lia. left. exists (q, 8 * cap). split. exact (BLK cap q eq_refl). cbn. lia.
             unfold in_errno. rewrite (ly_errno L LY). lia. rewrite (MF2 (Z_to_bv 64 _)). apply DEF1. exact Hi. }
           split. exact CRA1.
           unfold L5DSU.UNNORM_SCR, L5DSU.DIVEQ_SCR, L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK.
           split.
           { intros a Ka. pose proof Ka as (Ha & _).
             pose proof (kept_not_scratch L LB sp _ _ a Ka LBhi ltac:(unfold hl_ceil; lia) ltac:(rewrite (ly_img_hi L LY); lia)) as NS.
             rewrite (MF4 (Z_to_bv 64 a)). rewrite (PRES3 a). rewrite (MF2 (Z_to_bv 64 a)). apply PRES1. exact Ka.
             eapply L5C.kept_inner. exact Ka. lia. lia. intros OW. apply L5C.outside_cons_inv in OW as [NW _]. apply L5C.outside_cons. exact NW. apply L5C.outside_nil. }
           split.
           { intros i Hi. rewrite (MF4 (Z_to_bv 64 _)).
             destruct (Z_lt_le_dec (sp - (64 + (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))))) + i) (sp - 64 - (80 + (64 + (48 + (64 + (16 + 8224))))))) as [Hlt|Hge].
             - apply (CDEF3 _). lia. right. left. unfold hl_ceil. lia. unfold in_errno. rewrite (ly_errno L LY). lia. rewrite (MF2 (Z_to_bv 64 _)). apply SDEF1. lia.
             - destruct (Z_lt_le_dec (sp - (64 + (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))))) + i) (sp - 64)) as [Hlt'|Hge'].
               + replace (sp - (64 + (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))))) + i)
                   with (sp - 64 - (80 + (64 + (48 + (64 + (16 + 8224))))) + (i - 528)) by lia. apply SDEF3. lia.
               + apply (CDEF3 _). lia. right. left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. rewrite (MF2 (Z_to_bv 64 _)). apply SDEF1. lia. }
           intros a Ha CA NE D0. rewrite (MF4 (Z_to_bv 64 a)). apply (CDEF3 a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE.
           rewrite (MF2 (Z_to_bv 64 a)). apply (CDEF1 a Ha CA NE D0).
        -- eapply L5C.model_but_vm_trans. exact MBV1. exact MBV3.
        -- eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH3. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
           intros a Ha. left. apply MF4. exact GR4.
    + (* [comment removed for export] *)
      eapply (SHRS fx2 R2 M2 model1 K X (sp - 64) SHR_RET xs (L5.BO fb1 n1 st1) w1).
      * exact Mh1.
      * exact Ml1.
      * exact R2_10.
      * exact R2_11.
      * lia.
      * exact R2_1.
      * split. unfold SHR_RET. lia. reflexivity.
      * exact R2_2.
      * replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
      * lia.
      * lia.
      * lia.
      * exact Ao.
      * intros i Hi. rewrite (MF2 (Z_to_bv 64 _)). apply DEF1z. lia.
      * intros i Hi. rewrite (MF2 (Z_to_bv 64 _)). apply DEFX1. exact Hi.
      * eapply (L5C.big_at_agree RSEGS M1 M2). intros i Hi. apply MF2. lia. lia. exact OB1.
      * cbn [L5.bo_len]. lia.
      * rewrite DATA. eapply (L5C.limbs_at_agree RSEGS M1 M2). intros i Hi. apply MF2. lia. rewrite Lw1. lia. exact LA1.
      * exact Lw1.
      * exact Rw1.
      * intros i Hi. rewrite (MF2 (Z_to_bv 64 _)). apply DEF1'. exact Hi.
      * cbn [L5.bo_st]. intros cap q Hq. pose proof (APART1 cap q Hq). subst st1. destruct sto as [v0 v1|cap0 q0]; try contradiction. destruct KIND as [-> ->].
        pose proof (LBhi _ (BLK cap0 q0 eq_refl)) as Hb. cbn [fst snd] in Hb. unfold hl_ceil in Hb. lia.
      * (* [comment removed for export] *)
        intros fx3 R3 M3 rw st' SP3. unfold L5SHRU.shr_post in SP3. cbv zeta in SP3. cbn [L5.bo_fb L5.bo_len L5.bo_st] in SP3.
        destruct SP3 as (RP3 & R3_10 & Lrw & WOK & OB3 & LA3 & MST & FR3 & GR3).
        rewrite DATA in LA3, FR3.
        assert (FR3z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 - 80 <= a < sp - 64) -> ~ (X <= a < X + 16) ->
                                ~ (L5.bo_data X (L5.BO fb len sto) <= a < L5.bo_data X (L5.BO fb len sto) + 8 * Z.of_nat n1) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros a Ha N1' N2 N3. rewrite FR3. apply MF2. all: rewrite BGU.unsigned_lit by lia. exact N1'. exact N2. exact N3. }
        assert (T3: forall a v, sp - 64 <= a -> a + 8 <= sp -> BGU.u64_at M1 a v -> BGU.u64_at M3 a v).
        { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M3). 2: lia. 2: lia. 2: exact Hu. intros i Hi. apply FR3z. lia. lia. lia.
          intros Hc. destruct (DWHERE i ltac:(lia)) as [W1|(W2 & W3 & W4)]. lia. unfold hl_ceil in W3. lia. }
        assert (WR3: BGU.writable M3 (sp - 64) 64).
        { change (L5.writable RSEGS M3 (sp - 64) 64). eapply L5.writable_grows. exact GR3. eapply L5.writable_grows. exact GR2. exact WR64. }
        assert (R3_2: getr R3 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite <- L5K.rl2, (RP3 2%bv ltac:(cbn; tauto)), L5K.rl2. exact R2_2. }
        destruct (p45_run true fx3 R3 M3 sp _ _ _ r R3_2 (T3 (sp - 8) _ ltac:(lia) ltac:(lia) C8) (T3 (sp - 16) _ ltac:(lia) ltac:(lia) C16) (T3 (sp - 24) _ ltac:(lia) ltac:(lia) C24)
                    RG1 RG8 RG9 A16 ltac:(lia) ltac:(lia) WR3 E1 RA)
          as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_9 & MF4 & GR4).
        eapply (L5.cps_of_msteps RSEGS). exact Mh1. exact Ml1. exact MS4.
        apply (KONT fx4 R4 M4 model1 cr1).
        -- split. { apply (REGS R2 R3 R4 KS3P KS4 K2 ltac:(intros x Hx; L5K.inlist Hx) RP3 K4 ltac:(intros x Hx; L5K.inlist Hx) R4_2 R4_8 R4_9). }
           split.
           { set (k := L5W.rlen rw) in *. pose proof (L5W.rlen_le rw) as RLE. fold k in RLE. rewrite Lrw in RLE.
             pose proof OB3 as (_ & _ & _ & OST3). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OST3.
             exists (if Nat.eqb k 0 then Z.land fb1 253 else fb1), k, st',
                    (match st' with L5.BInl u0 u1 => firstn k [u0; u1] | L5.BDyn _ _ => firstn k rw end).
             split. { eapply (L5C.big_at_agree RSEGS M3 M4). intros i Hi. apply MF4. lia. lia. exact OB3. }
             split. { destruct st' as [u0 u1|cap' q'].
                      - destruct OST3 as (_ & _ & _ & Hk2 & U0 & U1). split. cbn [L5.bo_len]. rewrite length_firstn. cbn [length]. lia.
                        split. apply Forall_firstn. constructor. exact U0. constructor. exact U1. constructor. cbn [L5.bo_st L5.bo_len]. reflexivity.
                      - split. cbn [L5.bo_len]. rewrite length_firstn, Lrw. lia. split. apply Forall_firstn. exact WOK.
                        cbn [L5.bo_st L5.bo_len]. destruct st1 as [v0' v1'|cap1 q1]. contradiction. destruct MST as [-> ->].
                        destruct sto as [v0 v1|cap0 q0]. contradiction. destruct KIND as [-> ->]. cbn [L5.bo_data L5.bo_st] in LA3.
                        apply L5C.limbs_at_firstn. eapply (L5C.limbs_at_agree RSEGS M3 M4). intros i Hi. apply MF4. 3: exact LA3.
                        pose proof (LBimg _ _ (BLK cap0 q0 eq_refl)). lia. pose proof (LBimg _ _ (BLK cap0 q0 eq_refl)). rewrite Lrw. destruct OST1 as (_ & _ & _ & Hlc & _). unfold hl_ceil in *. lia. }
             split. { destruct (Nat.eqb k 0). apply land253_bit1. exact NEG1. exact NEG1. }
             destruct sto as [v0 v1|cap0 q0]; destruct st1 as [v0' v1'|cap1 q1]; try contradiction; destruct st' as [u0 u1|cap' q']; try contradiction. exact I.
             destruct KIND as [-> ->]. destruct MST as [-> ->]. split. reflexivity. split. reflexivity.
             cbn [L5.bo_data L5.bo_cap L5.bo_st] in DEF1. intros i Hi. apply GR4. apply GR3. apply GR2. apply DEF1. exact Hi. }
           split. exact CRA1.
           unfold L5DSU.UNNORM_SCR, L5DSU.DIVEQ_SCR, L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK.
           split.
           { intros a Ka. pose proof Ka as (Ha & _ & _ & OW).
             pose proof (kept_not_scratch L LB sp _ _ a Ka LBhi ltac:(unfold hl_ceil; lia) ltac:(rewrite (ly_img_hi L LY); lia)) as NS.
             apply L5C.outside_cons_inv in OW as [NW1 OW]. apply L5C.outside_cons_inv in OW as [NW2 _]. unfold L5.in_rng in NW1, NW2. cbn [fst snd] in NW1, NW2.
             rewrite (MF4 (Z_to_bv 64 a)). rewrite FR3z. apply PRES1. exact Ka. lia. lia. lia. lia. }
           split. { intros i Hi. apply GR4. apply GR3. apply GR2. apply SDEF1. exact Hi. }
           intros a Ha CA NE D0. apply GR4. apply GR3. apply GR2. apply (CDEF1 a Ha CA NE D0).
        -- exact MBV1.
        -- eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH1. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
           2:{ eapply mem_grows_trans. exact GR2. eapply mem_grows_trans. exact GR3. exact GR4. }
           intros a Ha.
           destruct (Z_lt_le_dec a (sp - 64 - 80)) as [F1|F1]; [|destruct (Z_lt_le_dec a (sp - 64)) as [F2|F2]; [right; left; unfold hl_ceil; lia|]].
           all: destruct (Z_lt_le_dec a X) as [B1|B1]; [|destruct (Z_lt_le_dec a (X + 16)) as [B2|B2]; [right; left; unfold hl_ceil; lia|]].
           all: destruct (Z_lt_le_dec a (L5.bo_data X (L5.BO fb len sto))) as [C1|C1];
                [|destruct (Z_lt_le_dec a (L5.bo_data X (L5.BO fb len sto) + 8 * Z.of_nat n1)) as [C2|C2];
                  [right; destruct (DWHERE a ltac:(lia)) as [W1|(W2 & W3 & W4)]; [left; unfold hl_ceil; lia| right; exact W2] |]].
           all: left; rewrite (MF4 (Z_to_bv 64 a)); apply FR3z; lia.
Qed.

End WithHeap.
End SCFG_1.
End L5UNNMU.
