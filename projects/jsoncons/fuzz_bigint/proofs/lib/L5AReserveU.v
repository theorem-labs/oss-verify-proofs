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
     Ub0_code_21248_21b5c BigLinkBase BigLinkGlueUb0 BigLinkDivBaseU L5Defs L5Core L5CoreKit L5CoreSpecsU L5OpnewU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5AReserveU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5ARESU.
Import L5CSU.
Module P1 := LibSegZ_lcars1u.
Module P2 := LibSegZ_lcars2u.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition RET1 : Z := 0x21898.      (* [comment removed for export] *)
Definition RETI : Z := 0x218f0.      (* [comment removed for export] *)

Definition KS1 : list nat := Eval vm_compute in (BGU.kept_list 48 P1.regs0 P1.regs_out).
Lemma KS1_ok : BGU.kept_ok 48 P1.regs0 P1.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BGU.kept_list 48 P2.regs0 P2.regs_out).
Lemma KS2_ok : BGU.kept_ok 48 P2.regs0 P2.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.

Lemma kn0_1 : P1.kn0 = [KRange (EVar 2) 140735332483184 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-112)) (ELit 112); KRange (EVar 11) 1 8388608].
Proof. vm_compute. reflexivity. Qed.
Lemma cells_1 : P1.cells = [KWord (SA (EVar 2) (-88)) 8 (EVar 9); KWord (SA (EVar 2) (-80)) 8 (EVar 10); KWord (SA (EVar 2) (-72)) 8 (ELit 137348);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18); KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8); KWord (SA (EVar 2) (-8)) 8 (EVar 1)].
Proof. vm_compute. reflexivity. Qed.
Definition e9 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL (EVar 11) (ELit 3))) (ELit 8).
Definition z9 : BL.za := Eval vm_compute in (BL.zc e9).
Lemma z9_ok : BL.zcomp e9 = Some z9. Proof. vm_compute. reflexivity. Qed.
Definition e10 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 64) (EAlu ALU_SRL (EVar 11) (ELit 3))) (ELit 64).
Definition z10 : BL.za := Eval vm_compute in (BL.zc e10).
Lemma z10_ok : BL.zcomp e10 = Some z10. Proof. vm_compute. reflexivity. Qed.
Lemma r1_1 : nth 1 P1.regs_out (ELit 0) = ELit 137368. Proof. vm_compute. reflexivity. Qed.
Lemma r2_1 : nth 2 P1.regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-64)). Proof. vm_compute. reflexivity. Qed.
Lemma r8_1 : nth 8 P1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma r9_1 : nth 9 P1.regs_out (ELit 0) = e9. Proof. vm_compute. reflexivity. Qed.
Lemma r10_1 : nth 10 P1.regs_out (ELit 0) = e10. Proof. vm_compute. reflexivity. Qed.

Lemma kn0_2 : P2.kn0 = [KRange (EVar 2) 140735332483136 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-64)) (ELit 64);
   KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 8; KWr (SA (EVar 40) 0) (ELit 32);
   KDisj (SA (EVar 40) 0) (ELit 32) (SA (EVar 2) (-64)) (ELit 64);
   KWord (SA (EVar 40) 8) 8 (ELit 0); KWord (SA (EVar 40) 24) 8 (ELit 0);
   KWord (SA (EVar 2) (-8)) 8 (EVar 42); KWord (SA (EVar 2) (-16)) 8 (EVar 43); KWord (SA (EVar 2) (-24)) 8 (EVar 44);
   KWord (SA (EVar 2) (-32)) 8 (EVar 45)].
Proof. vm_compute. reflexivity. Qed.
Lemma cells_2 : P2.cells = [KWord (SA (EVar 40) 24) 8 (EVar 10); KWord (SA (EVar 40) 16) 8 (EVar 41)].
Proof. vm_compute. reflexivity. Qed.
Lemma r1_2 : nth 1 P2.regs_out (ELit 0) = EVar 42. Proof. vm_compute. reflexivity. Qed.
Lemma r2_2 : nth 2 P2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma r8_2 : nth 8 P2.regs_out (ELit 0) = EVar 43. Proof. vm_compute. reflexivity. Qed.
Lemma r9_2 : nth 9 P2.regs_out (ELit 0) = EVar 44. Proof. vm_compute. reflexivity. Qed.
Lemma r18_2 : nth 18 P2.regs_out (ELit 0) = EVar 45. Proof. vm_compute. reflexivity. Qed.

Definition z16 : BL.za := Eval vm_compute in (BL.zc (ELit 16)).
Definition z32 : BL.za := Eval vm_compute in (BL.zc (ELit 32)).
Definition z64 : BL.za := Eval vm_compute in (BL.zc (ELit 64)).
Lemma z32_ok : BL.zcomp (ELit 32) = Some z32. Proof. vm_compute. reflexivity. Qed.
Lemma z64_ok : BL.zcomp (ELit 64) = Some z64. Proof. vm_compute. reflexivity. Qed.

Lemma round_up_bounds n : 1 <= n <= 2 ^ 23 -> n + 1 <= round_up n <= n + 8 /\ round_up n mod 8 = 0.
Proof.
  intros Hn. unfold round_up. pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
  split. lia. replace (8 * (n / 8) + 8) with ((n / 8 + 1) * 8) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run fx R M (o n sp : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> 0 <= o < 2 ^ 64 -> getr R (reg 11) = Z_to_bv 64 n -> 1 <= n <= 2 ^ 23 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 112 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 112) 112 ->
  exists fx' R1 M1, msteps RSEGS (st fx R ARESERVE M) (st fx' R1 OPNEW M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R1 (reg 8) = Z_to_bv 64 o
    /\ getr R1 (reg 9) = Z_to_bv 64 (round_up n) /\ getr R1 (reg 10) = Z_to_bv 64 (8 * round_up n)
    /\ BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BGU.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BGU.u64_at M1 (sp - 32) (bv_unsigned (getr R (reg 18)))
    /\ (forall a : word, ~ (sp - 112 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 Ho H11 Hn H2 A16 SLO SHI WR.
  set (Vf := fun k : nat => getr R (reg k)).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BGU.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbv [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U11: bv_unsigned (ev E 11) = n) by (cbv [E ev Vf]; rewrite H11; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P1.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M P1.kn0).
  { unfold know_ok. rewrite kn0_1.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U11. lia. }
    apply Forall_nil. }
  destruct (P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P1.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  pose proof (round_up_bounds n Hn) as [RB RM].
  assert (Z9: bv_unsigned (edenot E' e9) = round_up n).
  { rewrite (BGU.edenot_kept 48 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E e9 z9 z9_ok). cbn [BL.zden z9]. unfold BL.uv. rewrite U11.
    unfold BL.MM, round_up. change (2 ^ 3) with 8. rewrite (Z.mod_small (8 * _)) by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Z10: bv_unsigned (edenot E' e10) = 8 * round_up n).
  { rewrite (BGU.edenot_kept 48 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E e10 z10 z10_ok). cbn [BL.zden z10]. unfold BL.uv. rewrite U11.
    unfold BL.MM, round_up. change (2 ^ 3) with 8. rewrite (Z.mod_small (64 * _)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (CELL: forall off k, In (KWord (SA (EVar 2) off) 8 (EVar k)) P1.cells -> (k < 48)%nat -> BGU.u64_at M' (sp + off) (bv_unsigned (getr R (reg k)))).
  { intros off k Hin Hk. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. exact Hin. exact A2.
    cbn [edenot]. rewrite AG by lia. reflexivity. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P1.regs0 P1.regs_out 48 KS1 KS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg P1.regs_out E' R' 1 Hregs) by lia. rewrite r1_1. reflexivity. }
  split. { rewrite (BGU.out_reg P1.regs_out E' R' 2 Hregs) by lia. rewrite r2_1. cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
  split. { rewrite (BGU.out_reg P1.regs_out E' R' 8 Hregs) by lia. rewrite r8_1. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U10. }
  split. { rewrite (BGU.out_reg P1.regs_out E' R' 9 Hregs) by lia. rewrite r9_1. apply BGU.word_of_unsigned. exact Z9. }
  split. { rewrite (BGU.out_reg P1.regs_out E' R' 10 Hregs) by lia. rewrite r10_1. apply BGU.word_of_unsigned. exact Z10. }
  split. { replace (sp - 8) with (sp + -8) by lia. apply CELL. rewrite cells_1. cbn. tauto. lia. }
  split. { replace (sp - 16) with (sp + -16) by lia. apply CELL. rewrite cells_1. cbn. tauto. lia. }
  split. { replace (sp - 24) with (sp + -24) by lia. apply CELL. rewrite cells_1. cbn. tauto. lia. }
  split. { replace (sp - 32) with (sp + -32) by lia. apply CELL. rewrite cells_1. cbn. tauto. lia. }
  split. { intros a Ha. apply Hfr. unfold SGP.outside. change P1.F0 with [(EVar 2, -112, ELit 112)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_217b8 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M RETI W_218f0 r F_218f0 eq_refl D_218f0 H1 Hr He). Qed.

Lemma p2_run fx R M (A o cap sp r : Z) (c8 c16 c24 c32 : Z) :
  getr R (reg 10) = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
  getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 cap -> 0 <= cap < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BGU.writable M o 32 ->
  BGU.u64_at M (o + 8) 0 -> BGU.u64_at M (o + 24) 0 ->
  BGU.u64_at M (sp - 8) c8 -> BGU.u64_at M (sp - 16) c16 -> BGU.u64_at M (sp - 24) c24 -> BGU.u64_at M (sp - 32) c32 ->
  0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 -> 0 <= c24 < 2 ^ 64 -> 0 <= c32 < 2 ^ 64 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 r M3)
    /\ (forall x, In x KS2 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16
    /\ getr R3 (reg 9) = Z_to_bv 64 c24 /\ getr R3 (reg 18) = Z_to_bv 64 c32
    /\ BGU.u64_at M3 (o + 16) cap /\ BGU.u64_at M3 (o + 24) A
    /\ (forall a : word, ~ (o + 16 <= bv_unsigned a < o + 32) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H10 HA H8 H9 Hcap H2 A16 SLO SHI WR Ao Olo Ohi WO O8 O24 C8 C16 C24 C32 R8 R16 R24 R32 Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 40%nat => Z_to_bv 64 o | 41%nat => Z_to_bv 64 cap
                                         | 42%nat => Z_to_bv 64 c8 | 43%nat => Z_to_bv 64 c16 | 44%nat => Z_to_bv 64 c24
                                         | 45%nat => Z_to_bv 64 c32 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = A) by (cbv [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U40: bv_unsigned (ev E 40) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = cap) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U45: bv_unsigned (ev E 45) = c32) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P2.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P2.regs0 nth edenot ev E Vf]. repeat split; try reflexivity.
    rewrite BGU.alu_add_lit. exact H2. exact H8. exact H9. }
  assert (HK: know_ok RSEGS E M P2.kn0).
  { unfold know_ok. rewrite kn0_2.
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U40. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U40. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U40. lia. lia. lia. rewrite Z.add_0_r. exact WO. }
    apply Forall_cons. { eapply (BGU.kentry_KDisj_z E M 40 0 (ELit 32) z32 32 2 (-64) (ELit 64) z64 64 o sp U40 U2 z32_ok eq_refl z64_ok eq_refl). lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_lit. exact U40. lia. lia. exact O8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_lit. exact U40. lia. lia. exact O24. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C16. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C24. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U45. lia. lia. exact C32. }
    apply Forall_nil. }
  destruct (P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P2.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A40: bv_unsigned (ev E' 40) = o) by (rewrite AG by lia; exact U40).
  assert (MF: forall a : word, ~ (o + 16 <= bv_unsigned a < o + 32) -> M' a = M a).
  { intros a Ha. apply Hfr. unfold SGP.outside. change P2.F0 with [(EVar 40, 16, ELit 16)].
    constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A40. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P2.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg P2.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 42%nat); [lia | exact r1_2 | lia | exact U42]).
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc P2.ps0) with RETI. apply ret_217b8. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P2.regs0 P2.regs_out 48 KS2 KS2_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | exact r2_2 | lia | exact U2]. }
  split. { apply (OUT 8%nat 43%nat); [lia | exact r8_2 | lia | exact U43]. }
  split. { apply (OUT 9%nat 44%nat); [lia | exact r9_2 | lia | exact U44]. }
  split. { apply (OUT 18%nat 45%nat); [lia | exact r18_2 | lia | exact U45]. }
  split. { eapply (BGU.u64_of_KWord E' M' 40 16). apply Hcells. change (SR.ps_cells P2.ps0) with P2.cells. rewrite cells_2. right; left; reflexivity. exact A40.
           cbn [edenot]. rewrite AG by lia. exact U41. }
  split. { eapply (BGU.u64_of_KWord E' M' 40 24). apply Hcells. change (SR.ps_cells P2.ps0) with P2.cells. rewrite cells_2. left; reflexivity. exact A40.
           cbn [edenot]. rewrite AG by lia. exact U10. }
  split. exact MF. exact Hgr.
Qed.

(* [comment removed for export] *)
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem areserve_ok : areserve_spec L HI.
Proof.
  unfold areserve_spec. intros fx R M model K LB cr o n sp r HH MOK HK0 H10 H11 Hn CR H1 RA H2 H4 STK Ao Olo Ohi WO O8 O24 KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  assert (WR112: BGU.writable M (sp - 112) 112).
  { change (L5.writable RSEGS M (sp - 112) 112). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct (p1_run fx R M o n sp H10 ltac:(lia) H11 Hn H2 A16 ltac:(lia) ltac:(lia) WR112)
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & C8 & C16 & C24 & C32 & FR1 & GR1).
  pose proof (round_up_bounds n Hn) as [RB RM].
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  eapply (L5NEWU.opnew_ok L HI LY HIok fx1 R1 M1 model K LB cr (8 * round_up n) (sp - 64) RET1).
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 112)) as [Hlt|Hge]. left. apply FR1. rewrite BGU.unsigned_lit by lia. lia.
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1. rewrite BGU.unsigned_lit by lia. lia.
    exact GR1.
  - exact MOK.
  - exact HK0.
  - exact R1_10.
  - lia.
  - exact CR.
  - exact R1_1.
  - split. unfold RET1. lia. reflexivity.
  - exact R1_2.
  - rewrite <- H4. apply (K1 4%nat). apply L5K.In_of_mem. reflexivity.
  - split. { replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
    intros i Hi. apply GR1. replace (sp - 64 - (16 + 8224) + i) with (sp - (64 + (16 + 8224)) + i) by lia. apply DEF. lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 A HA RP FB HP MBV HH2.
    pose proof FB as ((BR0 & BR1 & BR2 & BR3 & BR4) & BA & DEFA). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1.
    destruct HP as (PRES & SDEF & CDEF). unfold OPNEW_SCR, HEAP_STACK in PRES, SDEF, CDEF.
    (* [comment removed for export] *)
    assert (CL: forall a, sp - 64 <= a < 2 ^ 47 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply PRES. apply (L5C.kept_stack L LB (sp - 64) (16 + 8224) []). lia. lia. lia.
      rewrite (ly_errno L LY). lia. lia. apply L5C.outside_nil. }
    assert (T1: forall a v, sp - 64 <= a -> a + 8 <= 2 ^ 47 -> BGU.u64_at M1 a v -> BGU.u64_at M2 a v).
    { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact Hu. }
    assert (T0: forall a v, sp <= a -> a + 8 <= 2 ^ 47 -> BGU.u64_at M a v -> BGU.u64_at M2 a v).
    { intros a v H1a H2a Hu. apply T1. lia. lia. eapply (BGU.u64_at_frame M M1). lia. lia. intros x Hx. apply FR1. rewrite BGU.unsigned_lit by lia. lia. exact Hu. }
    pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
    pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as RG9. pose proof (bv_unsigned_in_range _ (getr R (reg 18))) as RG18.
    change (bv_modulus 64) with (2 ^ 64) in RG1, RG8, RG9, RG18.
    assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BGU.unsigned_lit. lia. }
    assert (WR2 : BGU.writable M2 (sp - 64) 64).
    { change (L5.writable RSEGS M2 (sp - 64) 64). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia.
      eapply L5.writable_grows. exact GR1. eapply L5.writable_sub. exact WR112. lia. lia. }
    assert (WO2 : BGU.writable M2 o 32).
    { change (L5.writable RSEGS M2 o 32). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia.
      eapply L5.writable_grows. exact GR1. exact WO. }
    destruct (p2_run fx2 R2 M2 A o (round_up n) sp r (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9)))
                (bv_unsigned (getr R (reg 18)))
                ltac:(rewrite <- L5K.rl10; exact HA) ltac:(lia)
                ltac:(rewrite <- L5K.rl8, (RP 8%bv ltac:(cbn; tauto)), L5K.rl8; exact R1_8)
                ltac:(rewrite <- L5K.rl9, (RP 9%bv ltac:(cbn; tauto)), L5K.rl9; exact R1_9) ltac:(lia)
                ltac:(rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2; exact R1_2) A16 ltac:(lia) ltac:(lia) WR2
                Ao Olo ltac:(lia) WO2 (T0 (o + 8) 0 ltac:(lia) ltac:(lia) O8) (T0 (o + 24) 0 ltac:(lia) ltac:(lia) O24)
                (T1 (sp - 8) _ ltac:(lia) ltac:(lia) C8) (T1 (sp - 16) _ ltac:(lia) ltac:(lia) C16) (T1 (sp - 24) _ ltac:(lia) ltac:(lia) C24)
                (T1 (sp - 32) _ ltac:(lia) ltac:(lia) C32)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E1 RA)
      as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & D16 & D24 & MF3 & GR3).
    eapply (L5.cps_of_msteps RSEGS). { rewrite (L5C.halted_but_vm _ _ MBV). exact Mh. } { rewrite (L5C.lazy_but_vm _ _ MBV). exact Ml. }
    exact MS3.
    apply (KONT fx3 R3 M3 model2 A).
    + (* [comment removed for export] *)
      apply L5K.regs_preserved_by_index. intros i Hi.
      cbn in Hi. destruct Hi as [<-|Hi]. { rewrite R3_2, <- H2, L5K.rl2. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_8. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_9. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_18. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      assert (G: forall j, In j [19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
      { intros j Hj.
        assert (M2j: In j KS2) by (pose proof Hj as H'; L5K.inlist H').
        assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
        assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
        rewrite (K3 j M2j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
      apply G. L5K.inlist Hi.
    + (* [comment removed for export] *)
      split. exact (proj1 FB). split. exact BA. intros i Hi. rewrite (MF3 (Z_to_bv 64 (A + i))). apply DEFA. exact Hi.
      rewrite BGU.unsigned_lit by lia. lia.
    + split. exact D16. exact D24.
    + (* [comment removed for export] *)
      split.
      * intros a (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
        rewrite (MF3 (Z_to_bv 64 a)) by (rewrite BGU.unsigned_lit by lia; lia).
        assert (FA: ~ (sp - (64 + (16 + 8224)) <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros Hna. apply FR1. rewrite BGU.unsigned_lit by lia. lia. }
        destruct CA as [IB|[[S1 S2]|IM]].
        -- rewrite PRES. apply FA.
           { destruct IB as (b & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _).
             lia. }
           split. lia. split. left. exact IB. split. exact NE. apply L5C.outside_nil.
        -- unfold ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in S2. rewrite PRES. apply FA. lia.
           split. lia. split. right. left. split. exact S1. lia. split. exact NE. apply L5C.outside_nil.
        -- rewrite PRES. apply FA. rewrite (ly_img_hi L LY) in IM. lia.
           split. lia. split. right. right. exact IM. split. exact NE. apply L5C.outside_nil.
      * split.
        { unfold ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi. rewrite (MF3 (Z_to_bv 64 _)) by (rewrite BGU.unsigned_lit by lia; lia).
          destruct (Z_lt_le_dec (sp - (64 + (16 + 8224)) + i) (sp - 64)) as [Hlt|Hge].
          -- replace (sp - (64 + (16 + 8224)) + i) with (sp - 64 - (16 + 8224) + (i)) by lia. apply SDEF. lia.
          -- rewrite CL by lia. apply GR1. apply DEF. lia. }
        intros a Ha CA NE D0. unfold ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply GR3. apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE.
        apply GR1. exact D0.
    + exact MBV.
    + eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
      intros a Ha. destruct (Z_lt_le_dec a (o + 16)) as [Hlt|Hge]. left. apply MF3. rewrite BGU.unsigned_lit by lia. lia.
      destruct (Z_lt_le_dec a (o + 32)) as [Hlt'|Hge']. right; left. lia. left. apply MF3. rewrite BGU.unsigned_lit by lia. lia.
      exact GR3.
Qed.

End WithHeap.
End SCFG_1.

End L5ARESU.
