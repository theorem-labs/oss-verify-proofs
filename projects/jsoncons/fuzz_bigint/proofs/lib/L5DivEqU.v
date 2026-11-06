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
     Ub0_code_23138_2379c BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU L5Defs L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5DivSpecsU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5DivEqU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5DIVEQU.
Import L5CSU.
Module PD1 := LibSegZ_lcdu1.
Module P2I := LibSegZ_lcdu2i.
Module P2D := LibSegZ_lcdu2d.
Module PD3 := LibSegZ_lcdu3.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition OPDIV : Z := 0x23594.
Definition DIVIDE : Z := 0x224f4.
Definition DIVN_RET : Z := 0x235c4.   (* [comment removed for export] *)
Definition AFTER_DTOR : Z := 0x235e4. (* [comment removed for export] *)
Definition RETI : Z := 0x235f4.       (* [comment removed for export] *)

Definition KS1 : list nat := Eval vm_compute in (BGU.kept_list 48 PD1.regs0 PD1.regs_out).
Lemma KS1_ok : BGU.kept_ok 48 PD1.regs0 PD1.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2I : list nat := Eval vm_compute in (BGU.kept_list 48 P2I.regs0 P2I.regs_out).
Lemma KS2I_ok : BGU.kept_ok 48 P2I.regs0 P2I.regs_out KS2I = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2D : list nat := Eval vm_compute in (BGU.kept_list 48 P2D.regs0 P2D.regs_out).
Lemma KS2D_ok : BGU.kept_ok 48 P2D.regs0 P2D.regs_out KS2D = true. Proof. vm_compute. reflexivity. Qed.
Definition KS3 : list nat := Eval vm_compute in (BGU.kept_list 48 PD3.regs0 PD3.regs_out).
Lemma KS3_ok : BGU.kept_ok 48 PD3.regs0 PD3.regs_out KS3 = true. Proof. vm_compute. reflexivity. Qed.

Lemma ret_234f0 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M RETI W_235f4 r F_235f4 eq_refl D_235f4 H1 Hr He). Qed.

Lemma land1_of_bit0 fb (b : bool) : 0 <= fb -> Z.testbit fb 0 = b -> Z.land fb 1 = (if b then 1 else 0).
Proof.
  intros Hfb Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Hb. destruct b; reflexivity. }
  replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
  destruct b. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity.
Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run fx R M (sp : Z) :
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 48) 48 ->
  exists fx' R1 M1, msteps RSEGS (st fx R OPDIV M) (st fx' R1 DIVIDE M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 DIVN_RET /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 48)
    /\ getr R1 (reg 8) = getr R (reg 10) /\ getr R1 (reg 12) = getr R (reg 10) /\ getr R1 (reg 13) = Z_to_bv 64 (sp - 48) /\ getr R1 (reg 14) = Z_to_bv 64 0
    /\ BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BGU.u64_at M1 (sp - 24) 0 /\ BGU.u64_at M1 (sp - 32) 0 /\ BGU.u64_at M1 (sp - 40) 0 /\ BGU.u8_at M1 (sp - 48) 0
    /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H2 A16 SLO SHI WR.
  set (Vf := fun j : nat => getr R (reg j)).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E PD1.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PD1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M PD1.kn0).
  { unfold know_ok. cbv delta [PD1.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_nil. }
  destruct (PD1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PD1.NX0 with 48%nat in Hag.
  assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  assert (CELL: forall off j, In (KWord (SA (EVar 2) off) 8 (EVar j)) PD1.cells -> (j < 32)%nat -> BGU.u64_at M' (sp + off) (bv_unsigned (getr R (reg j)))).
  { intros off j Hin Hj. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. exact Hin. exact A2.
    cbn [edenot]. rewrite AG by lia. reflexivity. }
  assert (CELL0: forall off, In (KWord (SA (EVar 2) off) 8 (ELit 0)) PD1.cells -> BGU.u64_at M' (sp + off) 0).
  { intros off Hin. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. exact Hin. exact A2. cbn [edenot]. apply BGU.unsigned_lit. lia. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PD1.regs0 PD1.regs_out 48 KS1 KS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg PD1.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BGU.out_reg PD1.regs_out E' R' 2 Hregs) by lia. change (nth 2 PD1.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-48))).
           cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
  split. { rewrite (BGU.out_reg PD1.regs_out E' R' 8 Hregs) by lia. change (nth 8 PD1.regs_out (ELit 0)) with (EVar 10). cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { rewrite (BGU.out_reg PD1.regs_out E' R' 12 Hregs) by lia. change (nth 12 PD1.regs_out (ELit 0)) with (EVar 10). cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { rewrite (BGU.out_reg PD1.regs_out E' R' 13 Hregs) by lia. change (nth 13 PD1.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-48))).
           cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
  split. { rewrite (BGU.out_reg PD1.regs_out E' R' 14 Hregs) by lia. reflexivity. }
  split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [PD1.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [PD1.cells]; cbn; tauto | lia]. }
  split. { replace (sp - 24) with (sp + -24) by lia. apply CELL0. cbv delta [PD1.cells]; cbn; tauto. }
  split. { replace (sp - 32) with (sp + -32) by lia. apply CELL0. cbv delta [PD1.cells]; cbn; tauto. }
  split. { replace (sp - 40) with (sp + -40) by lia. apply CELL0. cbv delta [PD1.cells]; cbn; tauto. }
  split. { replace (sp - 48) with (sp + -48) by lia. eapply (BIU.u8_of_KWord1_e E' M' 2 (-48) (ELit 0) sp 0). apply Hcells. cbv delta [PD1.cells]; cbn; tauto.
           exact A2. reflexivity. lia. }
  split. { intros a Ha. apply Hfr. unfold SGP.outside. change PD1.F0 with [(EVar 2, -48, ELit 48)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2i_run fx R M (X sp fr c8 c16 r : Z) :
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 2) = Z_to_bv 64 (sp - 48) ->
  BGU.u64_at M (sp - 8) c8 -> BGU.u64_at M (sp - 16) c16 -> 0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 ->
  BGU.u8_at M (sp - 48) fr -> 0 <= fr < 256 -> Z.testbit fr 0 = false ->
  0 <= X < 2 ^ 64 -> sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 48) 48 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R DIVN_RET M) (st fx' R3 r M3)
    /\ (forall x, In x KS2I -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 10) = Z_to_bv 64 X
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H2 C8 C16 R8 R16 F0r Hfr Bfr HX A16 SLO SHI WR Er [Hr He].
  set (Vf := fun j : nat => match j with 2%nat => Z_to_bv 64 sp | 33%nat => Z_to_bv 64 X | 36%nat => Z_to_bv 64 fr
                                         | 43%nat => Z_to_bv 64 c8 | 44%nat => Z_to_bv 64 c16 | _ => getr R (reg j) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = X) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = fr) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P2I.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P2I.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P2I.kn0).
  { unfold know_ok. cbv delta [P2I.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C16. }
    apply Forall_cons. { eapply (BDU.kentry_KWord1_var E M 2 (-48) 36 sp fr U2 U36). lia. lia. lia. exact F0r. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U36. lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U36, (land1_of_bit0 fr false) by (lia || exact Bfr). lia. }
    apply Forall_nil. }
  destruct (P2I.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr' & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P2I.NX0 with 48%nat in Hag.
  assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr'. constructor. }
  assert (OUT: forall i j z, (0 < i < 32)%nat -> nth i P2I.regs_out (ELit 0) = EVar j -> (j < 48)%nat -> bv_unsigned (ev E j) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros i' j z Hi Hnth Hj Hz. rewrite (BGU.out_reg P2I.regs_out E' R' i' Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8). { apply (OUT 1%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc P2I.ps0) with RETI. apply ret_234f0. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P2I.regs0 P2I.regs_out 48 KS2I KS2I_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
  split. { apply (OUT 10%nat 33%nat); [lia | reflexivity | lia | exact U33]. }
  split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2d_run fx R M (X sp fr qr cr8 c8 c16 : Z) :
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 2) = Z_to_bv 64 (sp - 48) ->
  BGU.u64_at M (sp - 8) c8 -> BGU.u64_at M (sp - 16) c16 -> 0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 ->
  BGU.u8_at M (sp - 48) fr -> 0 <= fr < 256 -> Z.testbit fr 0 = true ->
  BGU.u64_at M (sp - 24) qr -> 4096 <= qr -> qr + 64 <= 2 ^ 47 -> BGU.u64_at M (sp - 32) cr8 -> 1 <= cr8 <= 2 ^ 27 ->
  0 <= X < 2 ^ 64 -> sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 48) 48 ->
  exists fx' R3 M3, msteps RSEGS (st fx R DIVN_RET M) (st fx' R3 OPDEL_SIZED M3)
    /\ (forall x, In x KS2D -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 AFTER_DTOR /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R3 (reg 8) = Z_to_bv 64 X
    /\ getr R3 (reg 10) = Z_to_bv 64 qr /\ getr R3 (reg 11) = Z_to_bv 64 (8 * cr8)
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H2 C8 C16 R8 R16 F0r Hfr Bfr C24 Qlo Qhi C32 Hc HX A16 SLO SHI WR.
  set (Vf := fun j : nat => match j with 2%nat => Z_to_bv 64 sp | 33%nat => Z_to_bv 64 X | 36%nat => Z_to_bv 64 fr | 37%nat => Z_to_bv 64 qr | 38%nat => Z_to_bv 64 cr8
                                         | 43%nat => Z_to_bv 64 c8 | 44%nat => Z_to_bv 64 c16 | _ => getr R (reg j) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = X) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = fr) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = qr) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U38: bv_unsigned (ev E 38) = cr8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P2D.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P2D.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P2D.kn0).
  { unfold know_ok. cbv delta [P2D.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C16. }
    apply Forall_cons. { eapply (BDU.kentry_KWord1_var E M 2 (-48) 36 sp fr U2 U36). lia. lia. lia. exact F0r. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U36. lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U36, (land1_of_bit0 fr true) by (lia || exact Bfr). lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U37. lia. lia. exact C24. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U37. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U38. lia. lia. exact C32. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U38. lia. }
    apply Forall_nil. }
  destruct (P2D.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr' & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P2D.NX0 with 48%nat in Hag.
  assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr'. constructor. }
  assert (OUT: forall i j z, (0 < i < 32)%nat -> nth i P2D.regs_out (ELit 0) = EVar j -> (j < 48)%nat -> bv_unsigned (ev E j) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros i' j z Hi Hnth Hj Hz. rewrite (BGU.out_reg P2D.regs_out E' R' i' Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P2D.regs0 P2D.regs_out 48 KS2D KS2D_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg P2D.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BGU.out_reg P2D.regs_out E' R' 2 Hregs) by lia. change (nth 2 P2D.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-48))).
           cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U2), BGU.alu_add_lit. reflexivity. }
  split. { apply (OUT 8%nat 33%nat); [lia | reflexivity | lia | exact U33]. }
  split. { apply (OUT 10%nat 37%nat); [lia | reflexivity | lia | exact U37]. }
  split. { rewrite (BGU.out_reg P2D.regs_out E' R' 11 Hregs) by lia. change (nth 11 P2D.regs_out (ELit 0)) with (EMd M_MUL (ELit 8) (EVar 38)).
           cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U38), BGU.md_mul_lit. reflexivity. }
  split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p3_run fx R M (X sp c8 c16 r : Z) :
  getr R (reg 8) = Z_to_bv 64 X -> getr R (reg 2) = Z_to_bv 64 (sp - 48) ->
  BGU.u64_at M (sp - 8) c8 -> BGU.u64_at M (sp - 16) c16 -> 0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 ->
  0 <= X < 2 ^ 64 -> sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 48) 48 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R AFTER_DTOR M) (st fx' R3 r M3)
    /\ (forall x, In x KS3 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 10) = Z_to_bv 64 X
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H2 C8 C16 R8 R16 HX A16 SLO SHI WR Er [Hr He].
  set (Vf := fun j : nat => match j with 2%nat => Z_to_bv 64 sp | 33%nat => Z_to_bv 64 X
                                         | 43%nat => Z_to_bv 64 c8 | 44%nat => Z_to_bv 64 c16 | _ => getr R (reg j) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = X) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E PD3.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PD3.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M PD3.kn0).
  { unfold know_ok. cbv delta [PD3.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C16. }
    apply Forall_nil. }
  destruct (PD3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr' & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PD3.NX0 with 48%nat in Hag.
  assert (AG: forall j, (j < 48)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr'. constructor. }
  assert (OUT: forall i j z, (0 < i < 32)%nat -> nth i PD3.regs_out (ELit 0) = EVar j -> (j < 48)%nat -> bv_unsigned (ev E j) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros i' j z Hi Hnth Hj Hz. rewrite (BGU.out_reg PD3.regs_out E' R' i' Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8). { apply (OUT 1%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc PD3.ps0) with RETI. apply ret_234f0. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PD3.regs0 PD3.regs_out 48 KS3 KS3_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
  split. { apply (OUT 10%nat 33%nat); [lia | reflexivity | lia | exact U33]. }
  split. exact MM. exact Hgr.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis DIVN : L5DSU.divN_spec L HI.
Hypothesis OPDELS : opdel_sized_spec L HI.

Theorem diveq_ok : L5DSU.diveq_spec L HI.
Proof.
  unfold L5DSU.diveq_spec. intros fx R M model K LB cr X qX dv fdv sp r bX wX HH MOK HK0 H10 H11 H1 RA H2 H3 H4 STK IMG OB OL HST HLEN NEG BLK DEFQ
    Ao Olo Ohi DEFX MW Adv Dvlo Dvhi APART CR KONT KE3.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF).
  unfold L5DSU.DIVEQ_SCR, L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  assert (DEFz: forall a, sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) <= a < sp -> M (Z_to_bv 64 a) <> None).
  { intros a Ha. replace a with (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + (a - (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))))))) by lia.
    apply DEF. lia. }
  destruct bX as [fb len sto]. cbn [L5.bo_fb L5.bo_len L5.bo_st] in HST, HLEN, NEG, KE3. subst sto.
  assert (LBhi: forall bb, In bb LB -> fst bb + snd bb <= hl_ceil L).
  { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  pose proof (LBhi _ BLK) as QXhi. cbn [fst snd] in QXhi.
  pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST.
  destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Aq & Qlo & Qhi & HAP).
  assert (WR48: BGU.writable M (sp - 48) 48).
  { change (L5.writable RSEGS M (sp - 48) 48). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
  change (bv_modulus 64) with (2 ^ 64) in RG1, RG8.
  assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BGU.unsigned_lit. lia. }
  destruct (p1_run fx R M sp H2 A16 ltac:(lia) ltac:(lia) WR48)
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_12 & R1_13 & R1_14 & C8 & C16 & C24 & C32 & C40 & C48 & FR1 & GR1).
  rewrite <- L5K.rl10, H10 in R1_8, R1_12.
  assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 48 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR1. rewrite BGU.unsigned_lit by lia. exact Hna. }
  assert (Z1: L5DSU.zero_obj M1 (sp - 48)).
  { unfold L5DSU.zero_obj, L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st Z.of_nat]. split. exact C48. split. lia.
    split. replace (sp - 48 + 8) with (sp - 40) by lia. exact C40. split. reflexivity.
    split. replace (sp - 48 + 16) with (sp - 32) by lia. exact C32. split. replace (sp - 48 + 24) with (sp - 24) by lia. exact C24.
    split. lia. lia. }
  unfold L5DSU.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (DIVN fx1 R1 M1 model K LB cr X qX (sp - 48) dv fdv (sp - 48) DIVN_RET (L5.BO fb len (L5.BDyn 8 qX)) wX).
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 48)) as [Hlt|Hge]. left. apply FR1z; lia.
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1z; lia. exact GR1.
  - exact MOK.
  - exact HK0.
  - rewrite <- H10. apply (K1 10%nat). apply L5K.In_of_mem; reflexivity.
  - rewrite <- H11. apply (K1 11%nat). apply L5K.In_of_mem; reflexivity.
  - exact R1_12.
  - exact R1_13.
  - exact R1_14.
  - exact R1_1.
  - split. unfold DIVN_RET. lia. reflexivity.
  - exact R1_2.
  - rewrite <- H3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity.
  - rewrite <- H4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity.
  - split. { replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
    intros i Hi. apply GR1. replace (sp - 48 - (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))) + i)
      with (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i) by lia. apply DEF. lia.
  - intros i Hi. rewrite FR1z by lia. apply IMG. exact Hi.
  - eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact OB.
  - destruct OL as (Lw & Rw & Vw). cbn [L5.bo_st L5.bo_len] in Lw, Vw. split. exact Lw. split. exact Rw. cbn [L5.bo_st L5.bo_len].
    eapply (L5C.limbs_at_agree RSEGS M M1). intros i Hi. rewrite Lw in Hi. apply FR1z; lia. lia. rewrite Lw. lia. exact Vw.
  - reflexivity.
  - exact HLEN.
  - exact NEG.
  - exact BLK.
  - intros i Hi. apply GR1. apply DEFQ. exact Hi.
  - exact Ao.
  - lia.
  - exact Ohi.
  - intros i Hi. apply GR1. apply DEFX. exact Hi.
  - destruct MW as [MW1 MW2]. split. eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact MW1. exact MW2.
  - exact Adv.
  - lia.
  - exact Dvhi.
  - exact Z1.
  - assert (A8: sp mod 8 = 0). { apply Z.mod_divide. lia. apply Z.mod_divide in A16. 2: lia. destruct A16 as [c Hc]. exists (2 * c). lia. }
    replace (sp - 48) with (sp + (-6) * 8) by lia. rewrite Z_mod_plus_full. exact A8.
  - lia.
  - lia.
  - intros i Hi. apply GR1. apply DEFz. lia.
  - exact APART.
  - lia.
  - lia.
  - exact CR.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 LB' cr' POST MBV HH2.
    destruct POST as (RP & XO & (fbr & nr & str & wr & OBR & OLR & MR) & MW2 & CRA & HP).
    destruct HP as (PRES & SDEF & CDEF). unfold L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES, SDEF, CDEF.
    pose proof (L5C.halted_but_vm _ _ MBV) as Mh2. rewrite Mh in Mh2. pose proof (L5C.lazy_but_vm _ _ MBV) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV) as Mm2. rewrite Mm in Mm2.
    (* [comment removed for export] *)
    assert (CL: forall a, sp - 16 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply PRES. apply (L5C.kept_stack L LB (sp - 48) _ _). lia. lia. lia. rewrite (ly_errno L LY). lia. lia.
      apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. lia.
      apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. lia.
      apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. lia. apply L5C.outside_nil. }
    assert (T1: forall a v, sp - 16 <= a -> a + 8 <= sp -> BGU.u64_at M1 a v -> BGU.u64_at M2 a v).
    { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact Hu. }
    assert (WR2 : BGU.writable M2 (sp - 48) 48).
    { change (L5.writable RSEGS M2 (sp - 48) 48). apply (L5C.writable_of_defined RSEGS). 2: lia. 2: lia.
      intros i Hi. apply (CDEF (sp - 48 + i)). lia. right. left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply GR1. apply DEFz. lia. }
    pose proof OBR as (R0 & Hfbr & R8 & RST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in R0, Hfbr, R8, RST.
    (* [comment removed for export] *)
    assert (KIN: forall a, L5C.kept L LB sp (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) [(X, 32); (qX, 64)] a ->
                 L5C.kept L LB (sp - 48) (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))) [(X, 32); (qX, 64); (sp - 48, 32)] a
                 /\ ~ (sp - 48 <= a < sp)).
    { intros a Ka. pose proof (kept_not_scratch L LB sp _ _ a Ka LBhi ltac:(unfold hl_ceil; lia) ltac:(rewrite (ly_img_hi L LY); lia)) as NS.
      split. 2: lia. eapply L5C.kept_inner. exact Ka. lia. lia.
      intros OW. apply L5C.outside_cons_inv in OW as [N1 OW]. apply L5C.outside_cons_inv in OW as [N2 _].
      apply L5C.outside_cons. exact N1. apply L5C.outside_cons. exact N2. apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. lia. apply L5C.outside_nil. }
    destruct str as [v0 v1|capr qr].
    + (* [comment removed for export] *)
      subst LB'. destruct RST as (Br0 & _).
      destruct (p2i_run fx2 R2 M2 X sp fbr (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) r
                  ltac:(rewrite <- L5K.rl8, (RP 8%bv ltac:(cbn; tauto)), L5K.rl8; exact R1_8)
                  ltac:(rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2; exact R1_2)
                  (T1 (sp - 8) _ ltac:(lia) ltac:(lia) C8) (T1 (sp - 16) _ ltac:(lia) ltac:(lia) C16) ltac:(lia) ltac:(lia)
                  R0 Hfbr Br0 ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 E1 RA)
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_10 & MF3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      apply (KONT fx3 R3 M3 model2 cr').
      * split.
        { apply L5K.regs_preserved_by_index. intros i Hi.
          cbn in Hi. destruct Hi as [<-|Hi]. { rewrite R3_2, <- H2, L5K.rl2. reflexivity. }
          destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity. }
          destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity. }
          destruct Hi as [<-|Hi]. { rewrite R3_8. symmetry. apply BGU.word_of_unsigned. reflexivity. }
          assert (G: forall j, In j [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
          { intros j Hj.
            assert (M3j: In j KS2I) by (pose proof Hj as H'; L5K.inlist H').
            assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
            assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
            rewrite (K3 j M3j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
          apply G. L5K.inlist Hi. }
        split. exact R3_10.
        split. { destruct XO as (fbq & nq & wq & OBX & OLX & NEGq & Hnq & DEFq). exists fbq, nq, wq.
                 split. eapply (L5C.big_at_agree RSEGS M2 M3). intros i Hi. apply MF3. lia. lia. exact OBX.
                 split. destruct OLX as (Lq & Rq & Vq). cbn [L5.bo_st L5.bo_len] in Lq, Vq. split. exact Lq. split. exact Rq. cbn [L5.bo_st L5.bo_len].
                 eapply (L5C.limbs_at_agree RSEGS M2 M3). intros i Hi. apply MF3. lia. rewrite Lq. lia. exact Vq.
                 split. exact NEGq. split. exact Hnq. intros i Hi. apply GR3. apply DEFq. exact Hi. }
        split. { destruct MW2 as [MW3 MW4]. split. eapply (L5C.big_at_agree RSEGS M2 M3). intros i Hi. apply MF3. lia. lia. exact MW3. exact MW4. }
        split. exact CRA.
        (* [comment removed for export] *)
        unfold L5DSU.DIVEQ_SCR, L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK.
        split.
        { intros a Ka. pose proof Ka as (Ha & _). destruct (KIN a Ka) as [Ki NS]. rewrite (MF3 (Z_to_bv 64 a)). rewrite (PRES a Ki). apply FR1z. lia. exact NS. }
        split.
        { intros i Hi. rewrite (MF3 (Z_to_bv 64 _)).
          destruct (Z_lt_le_dec (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i) (sp - 48)) as [Hlt|Hge].
          -- replace (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i)
               with (sp - 48 - (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))) + i) by lia. apply SDEF. lia.
          -- apply (CDEF _). lia. right. left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply GR1. apply DEFz. lia. }
        intros a Ha CA NE D0. rewrite (MF3 (Z_to_bv 64 a)). apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE. apply GR1. exact D0.
      * exact MBV.
      * eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
        intros a Ha. left. apply MF3. exact GR3.
    + (* [comment removed for export] *)
      destruct MR as (Hcap8 & ELB & FBR). subst capr LB'.
      destruct RST as (Br0 & R16 & R24 & Hlcr & Hc8 & Aqr & Qrlo & Qrhi & HAPr).
      pose proof (L5C.fresh_block_bounds L LB M2 qr 64 FBR) as (BR0 & BR1 & BR2 & BR3 & BR4).
      destruct (p2d_run fx2 R2 M2 X sp fbr qr 8 (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8)))
                  ltac:(rewrite <- L5K.rl8, (RP 8%bv ltac:(cbn; tauto)), L5K.rl8; exact R1_8)
                  ltac:(rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2; exact R1_2)
                  (T1 (sp - 8) _ ltac:(lia) ltac:(lia) C8) (T1 (sp - 16) _ ltac:(lia) ltac:(lia) C16) ltac:(lia) ltac:(lia)
                  R0 Hfbr Br0 ltac:(replace (sp - 24) with (sp - 48 + 24) by lia; exact R24) ltac:(lia) ltac:(lia)
                  ltac:(replace (sp - 32) with (sp - 48 + 16) by lia; exact R16) ltac:(lia)
                  ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2)
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_10 & R3_11 & MF3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      eapply (OPDELS fx3 R3 M3 model2 K ((qr, 64) :: LB) cr' qr 64 (sp - 48) AFTER_DTOR).
      * eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
        intros a Ha. left. apply MF3. exact GR3.
      * split. exact Mh2. split. exact Ml2. exact Mm2.
      * exact HK0.
      * left. reflexivity.
      * exact R3_10.
      * exact R3_1.
      * split. unfold AFTER_DTOR. lia. reflexivity.
      * exact R3_2.
      * rewrite <- H4. rewrite L5K.rl4. rewrite (K3 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4.
        apply (K1 4%nat). apply L5K.In_of_mem; reflexivity.
      * split. { replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
        unfold OPDEL_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
        intros i Hi. rewrite (MF3 (Z_to_bv 64 _)). replace (sp - 48 - 8224 + i) with (sp - 48 - (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))) + (352 + (64 + (144 + (64 + (48 + (64 + 16))))) + i)) by lia.
        apply SDEF. lia.
      * (* [comment removed for export] *)
        intros fx4 R4 M4 model4 RP4 HP4 MBV4 HH4.
        cbn [lb_remove fst] in HP4, HH4. rewrite Z.eqb_refl in HP4, HH4.
        destruct HP4 as (PRES4 & SDEF4 & CDEF4). unfold OPDEL_SCR, HEAP_STACK in PRES4, SDEF4, CDEF4.
        pose proof (L5C.halted_but_vm _ _ MBV4) as Mh4. rewrite Mh2 in Mh4. pose proof (L5C.lazy_but_vm _ _ MBV4) as Ml4. rewrite Ml2 in Ml4.
        assert (CL4: forall a, sp - 48 <= a < 2 ^ 47 -> L5.outside [(X, 32); (qX, 64)] a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
        { intros a Ha OW. apply PRES4. apply (L5C.kept_stack L LB (sp - 48) 8224 []). lia. lia. lia. rewrite (ly_errno L LY). lia. lia. apply L5C.outside_nil. }
        assert (T4: forall a v, sp - 16 <= a -> a + 8 <= sp -> BGU.u64_at M2 a v -> BGU.u64_at M4 a v).
        { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M2 M4). 2: lia. 2: lia. 2: exact Hu.
          intros i Hi. rewrite CL4. apply MF3. lia. apply L5C.outside_cons. unfold L5.in_rng; cbn [fst snd]; lia.
          apply L5C.outside_cons. unfold L5.in_rng; cbn [fst snd]; lia. apply L5C.outside_nil. }
        assert (WR4 : BGU.writable M4 (sp - 48) 48).
        { change (L5.writable RSEGS M4 (sp - 48) 48). apply (L5C.writable_of_defined RSEGS). 2: lia. 2: lia.
          intros i Hi. apply (CDEF4 (sp - 48 + i)). lia. right. left. lia. unfold in_errno. rewrite (ly_errno L LY). lia.
          rewrite (MF3 (Z_to_bv 64 _)). apply (CDEF (sp - 48 + i)). lia. right. left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply GR1. apply DEFz. lia. }
        destruct (p3_run fx4 R4 M4 X sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) r
                    ltac:(rewrite <- L5K.rl8, (RP4 8%bv ltac:(cbn; tauto)), L5K.rl8; exact R3_8)
                    ltac:(rewrite <- L5K.rl2, (RP4 2%bv ltac:(cbn; tauto)), L5K.rl2; exact R3_2)
                    (T4 (sp - 8) _ ltac:(lia) ltac:(lia) (T1 (sp - 8) _ ltac:(lia) ltac:(lia) C8))
                    (T4 (sp - 16) _ ltac:(lia) ltac:(lia) (T1 (sp - 16) _ ltac:(lia) ltac:(lia) C16)) ltac:(lia) ltac:(lia)
                    ltac:(lia) A16 ltac:(lia) ltac:(lia) WR4 E1 RA)
          as (fx5 & R5 & M5 & MS5 & K5 & R5_1 & R5_2 & R5_8 & R5_10 & MF5 & GR5).
        eapply (L5.cps_of_msteps RSEGS). exact Mh4. exact Ml4. exact MS5.
        apply (KONT fx5 R5 M5 model4 cr').
        -- split.
           { apply L5K.regs_preserved_by_index. intros i Hi.
             cbn in Hi. destruct Hi as [<-|Hi]. { rewrite R5_2, <- H2, L5K.rl2. reflexivity. }
             destruct Hi as [<-|Hi]. { rewrite (K5 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl3, (RP4 3%bv) by (cbn; tauto). rewrite L5K.rl3.
               rewrite (K3 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity. }
             destruct Hi as [<-|Hi]. { rewrite (K5 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl4, (RP4 4%bv) by (cbn; tauto). rewrite L5K.rl4.
               rewrite (K3 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity. }
             destruct Hi as [<-|Hi]. { rewrite R5_8. symmetry. apply BGU.word_of_unsigned. reflexivity. }
             assert (G: forall j, In j [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg j) = getr R (reg j)).
             { intros j Hj.
               assert (M5j: In j KS3) by (pose proof Hj as H'; L5K.inlist H').
               assert (M3j: In j KS2D) by (pose proof Hj as H'; L5K.inlist H').
               assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
               assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
               rewrite (K5 j M5j). rewrite (L5K.regs_preserved_index R3 R4 j RP4 MCj). rewrite (K3 j M3j).
               rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
             apply G. L5K.inlist Hi. }
           split. exact R5_10.
           (* [comment removed for export] *)
           assert (KX: forall a, (X <= a < X + 32 \/ qX <= a < qX + 64 \/ dv <= a < dv + 32) -> M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
           { intros a Ha. rewrite (MF5 (Z_to_bv 64 a)). rewrite PRES4. apply MF3.
             destruct Ha as [Ha|[Ha|Ha]].
             - apply (L5C.kept_stack L LB (sp - 48) 8224 []). lia. lia. lia. rewrite (ly_errno L LY). lia. lia. apply L5C.outside_nil.
             - apply (L5C.kept_block L LB (sp - 48) 8224 [] qX 64). exact BLK. lia. lia. lia. rewrite (ly_errno L LY).
               pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) _ BLK) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). cbn [fst snd] in Q1. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. lia.
               apply L5C.outside_nil.
             - apply (L5C.kept_stack L LB (sp - 48) 8224 []). lia. lia. lia. rewrite (ly_errno L LY). lia. lia. apply L5C.outside_nil. }
           split. { destruct XO as (fbq & nq & wq & OBX & OLX & NEGq & Hnq & DEFq). exists fbq, nq, wq.
                    split. eapply (L5C.big_at_agree RSEGS M2 M5). intros i Hi. apply KX. lia. lia. lia. exact OBX.
                    split. destruct OLX as (Lq & Rq & Vq). cbn [L5.bo_st L5.bo_len] in Lq, Vq. split. exact Lq. split. exact Rq. cbn [L5.bo_st L5.bo_len].
                    eapply (L5C.limbs_at_agree RSEGS M2 M5). intros i Hi. rewrite Lq in Hi. apply KX. lia. lia. rewrite Lq. lia. exact Vq.
                    split. exact NEGq. split. exact Hnq.
                    intros i Hi. rewrite (MF5 (Z_to_bv 64 _)). apply (CDEF4 (qX + i)). lia. left. exists (qX, 64). split. exact BLK. cbn. lia.
                    unfold in_errno. rewrite (ly_errno L LY).
                    pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) _ BLK) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). cbn [fst snd] in Q1. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. lia.
                    rewrite (MF3 (Z_to_bv 64 _)). apply DEFq. exact Hi. }
           split. { destruct MW2 as [MW3 MW4]. split. eapply (L5C.big_at_agree RSEGS M2 M5). intros i Hi. apply KX. lia. lia. lia. exact MW3. exact MW4. }
           split. exact CRA.
           (* [comment removed for export] *)
           unfold L5DSU.DIVEQ_SCR, L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK.
           split.
           { intros a Ka. pose proof Ka as (Ha & _). destruct (KIN a Ka) as [Ki NS]. rewrite (MF5 (Z_to_bv 64 a)).
             rewrite (PRES4 a). rewrite (MF3 (Z_to_bv 64 a)). rewrite (PRES a Ki). apply FR1z. lia. exact NS.
             eapply L5C.kept_inner. exact Ka. lia. lia. intros _. apply L5C.outside_nil. }
           split.
           { intros i Hi. rewrite (MF5 (Z_to_bv 64 _)).
             destruct (Z_lt_le_dec (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i) (sp - 48 - 8224)) as [Hlt|Hge].
             -- apply (CDEF4 _). lia. right. left. unfold hl_ceil. lia. unfold in_errno. rewrite (ly_errno L LY). lia.
                rewrite (MF3 (Z_to_bv 64 _)).
                replace (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i)
                  with (sp - 48 - (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))) + i) by lia. apply SDEF. lia.
             -- destruct (Z_lt_le_dec (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i) (sp - 48)) as [Hlt'|Hge'].
                ++ replace (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i) with (sp - 48 - 8224 + (i - (352 + (64 + (144 + (64 + (48 + (64 + 16)))))))) by lia.
                   apply SDEF4. lia.
                ++ apply (CDEF4 _). lia. right. left. lia. unfold in_errno. rewrite (ly_errno L LY). lia.
                   rewrite (MF3 (Z_to_bv 64 _)). apply (CDEF _). lia. right. left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply GR1. apply DEFz. lia. }
           intros a Ha CA NE D0. rewrite (MF5 (Z_to_bv 64 a)). apply (CDEF4 a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE.
           rewrite (MF3 (Z_to_bv 64 a)). apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE. apply GR1. exact D0.
        -- eapply L5C.model_but_vm_trans. exact MBV. exact MBV4.
        -- eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH4. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
           intros a Ha. left. apply MF5. exact GR5.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 LB' cr' E3 MBV HH2.
    apply (KE3 fx2 R2 M2 model2 LB' cr'). 2: exact MBV. 2: exact HH2.
    pose proof E3 as E3'. destruct E3' as (eB0 & eB1 & en & efd0 & efn0 & efn & efden & efd3 & efbX & HX). lastc HX.
    destruct HX as (PRES & SDEF & CDEF). unfold L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES, SDEF, CDEF.
    assert (CL: forall a, sp - 48 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply PRES. apply (L5C.kept_stack L LB (sp - 48) _ []). lia. lia. lia. rewrite (ly_errno L LY). lia. lia. apply L5C.outside_nil. }
    exists R1, M1.
    split. exact R1_1. split. exact R1_2. split. exact R1_8.
    split. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity.
    split. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity.
    split. apply (K1 9%nat). apply L5K.In_of_mem; reflexivity.
    split. { apply sregs_cases. intros j Hj. apply (K1 j). L5K.inlist Hj. }
    split. exact E3.
    split. { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact C8. }
    split. { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact C16. }
    split. { unfold L5DSU.zero_obj. eapply (L5C.big_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact Z1. }
    unfold L5DSU.DIVEQ_SCR, L5DSU.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK.
    split.
    { intros a Ka. pose proof Ka as (Ha & _).
      pose proof (kept_not_scratch L LB sp _ _ a Ka LBhi ltac:(unfold hl_ceil; lia) ltac:(rewrite (ly_img_hi L LY); lia)) as NS.
      rewrite (PRES a). apply FR1z. lia. intros HC; apply NS; lia. eapply L5C.kept_inner. exact Ka. lia. lia. intros _. apply L5C.outside_nil. }
    split.
    { intros i Hi.
      destruct (Z_lt_le_dec (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i) (sp - 48)) as [Hlt|Hge].
      -- replace (sp - (48 + (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))))) + i)
           with (sp - 48 - (352 + (64 + (144 + (64 + (48 + (64 + (16 + 8224))))))) + i) by lia. apply SDEF. lia.
      -- apply (CDEF _). lia. right. left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply GR1. apply DEFz. lia. }
    intros a Ha CA NE D0. apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE. apply GR1. exact D0.
Qed.

End WithHeap.
End SCFG_1.
End L5DIVEQU.
