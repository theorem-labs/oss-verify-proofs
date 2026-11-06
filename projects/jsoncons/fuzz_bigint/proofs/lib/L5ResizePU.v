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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore AsanPlanSoundSums Ub0Sums
     Ub0_code_21248_21b5c BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU L5Defs L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5ReserveU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5ResizePU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5RSZPU.
Import L5CSU.
Module P1 := LibSegZ_lcrsz1u.
Module PA := LibSegZ_lcrsz2au.
Module PB := LibSegZ_lcrsz2bu.
Module PC0 := LibSegZ_lcrsz2c0u.
Module PC1 := LibSegZ_lcrsz2c1u.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition RET1 : Z := 0x21508.      (* [comment removed for export] *)
Definition RETI : Z := 0x21564.      (* [comment removed for export] *)
Definition MEMSET : Z := 0x599a0.

Definition KS1 : list nat := Eval vm_compute in (BGU.kept_list 48 P1.regs0 P1.regs_out).
Lemma KS1_ok : BGU.kept_ok 48 P1.regs0 P1.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSA : list nat := Eval vm_compute in (BGU.kept_list 48 PA.regs0 PA.regs_out).
Lemma KSA_ok : BGU.kept_ok 48 PA.regs0 PA.regs_out KSA = true. Proof. vm_compute. reflexivity. Qed.
Definition KSB : list nat := Eval vm_compute in (BGU.kept_list 48 PB.regs0 PB.regs_out).
Lemma KSB_ok : BGU.kept_ok 48 PB.regs0 PB.regs_out KSB = true. Proof. vm_compute. reflexivity. Qed.
Definition KSC0 : list nat := Eval vm_compute in (BGU.kept_list 48 PC0.regs0 PC0.regs_out).
Lemma KSC0_ok : BGU.kept_ok 48 PC0.regs0 PC0.regs_out KSC0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSC1 : list nat := Eval vm_compute in (BGU.kept_list 48 PC1.regs0 PC1.regs_out).
Lemma KSC1_ok : BGU.kept_ok 48 PC1.regs0 PC1.regs_out KSC1 = true. Proof. vm_compute. reflexivity. Qed.

Definition z32 : BL.za := Eval vm_compute in (BL.zc (ELit 32)).
Definition z64 : BL.za := Eval vm_compute in (BL.zc (ELit 64)).
Lemma z32_ok : BL.zcomp (ELit 32) = Some z32. Proof. vm_compute. reflexivity. Qed.
Lemma z64_ok : BL.zcomp (ELit 64) = Some z64. Proof. vm_compute. reflexivity. Qed.

Lemma ret_2142c fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M RETI W_21564 r F_21564 eq_refl D_21564 H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run fx R M (o n sp len : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> 0 <= o < 2 ^ 64 -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BGU.u64_at M (o + 8) len -> 0 <= len < 2 ^ 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R RESIZE M) (st fx' R1 RESERVE M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64)
    /\ getr R1 (reg 8) = Z_to_bv 64 n /\ getr R1 (reg 9) = Z_to_bv 64 o /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 n
    /\ getr R1 (reg 18) = Z_to_bv 64 len
    /\ BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BGU.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BGU.u64_at M1 (sp - 32) (bv_unsigned (getr R (reg 18)))
    /\ (forall a : word, ~ (sp - 64 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 Ho H11 Hn H2 A16 SLO SHI WR Ao Olo Ohi O8 Hlen.
  set (Vf := fun k : nat => match k with 34%nat => Z_to_bv 64 len | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BGU.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbv [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U11: bv_unsigned (ev E 11) = n) by (cbv [E ev Vf]; rewrite H11; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = len) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P1.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M P1.kn0).
  { unfold know_ok. cbv delta [P1.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply (BGU.kentry_KDisj_z E M 10 0 (ELit 32) z32 32 2 (-64) (ELit 64) z64 64 o sp U10 U2 z32_ok eq_refl z64_ok eq_refl). lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U10. exact U34. lia. lia. exact O8. }
    apply Forall_nil. }
  destruct (P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P1.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P1.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg P1.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  assert (CELL: forall off k, In (KWord (SA (EVar 2) off) 8 (EVar k)) P1.cells -> (k < 32)%nat -> Vf k = getr R (reg k) -> BGU.u64_at M' (sp + off) (bv_unsigned (getr R (reg k)))).
  { intros off k Hin Hk HV. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. exact Hin. exact A2.
    cbn [edenot]. rewrite AG by lia. change (ev E k) with (Vf k). rewrite HV. reflexivity. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P1.regs0 P1.regs_out 48 KS1 KS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BGU.out_reg P1.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BGU.out_reg P1.regs_out E' R' 2 Hregs) by lia. change (nth 2 P1.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-64))).
           cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
  split. { apply (OUT 8%nat 11%nat); [lia | reflexivity | lia | exact U11]. }
  split. { apply (OUT 9%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
  split. { apply (OUT 10%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
  split. { apply (OUT 11%nat 11%nat); [lia | reflexivity | lia | exact U11]. }
  split. { apply (OUT 18%nat 34%nat); [lia | reflexivity | lia | exact U34]. }
  split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 32) with (sp + -32) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { intros a Ha. apply Hfr. unfold SGP.outside. change P1.F0 with [(EVar 2, -64, ELit 64)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_ret1 (R : bvmap 5 word) (M : word -> option byte) (o n old sp c8 c16 c24 c32 : Z) : Prop :=
  getr R (reg 8) = Z_to_bv 64 n /\ getr R (reg 9) = Z_to_bv 64 o /\ getr R (reg 18) = Z_to_bv 64 old /\ getr R (reg 2) = Z_to_bv 64 (sp - 64) /\
  BGU.u64_at M (sp - 8) c8 /\ BGU.u64_at M (sp - 16) c16 /\ BGU.u64_at M (sp - 24) c24 /\ BGU.u64_at M (sp - 32) c32 /\
  0 <= c8 < 2 ^ 64 /\ 0 <= c16 < 2 ^ 64 /\ 0 <= c24 < 2 ^ 64 /\ 0 <= c32 < 2 ^ 64.

(* [comment removed for export] *)
Lemma p2a_run fx R M (o n old sp r c8 c16 c24 c32 : Z) :
  at_ret1 R M o n old sp c8 c16 c24 c32 -> 0 <= n <= old -> old < 2 ^ 64 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BGU.writable M (o + 8) 8 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 r M3)
    /\ (forall x, In x KSA -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24 /\ getr R3 (reg 18) = Z_to_bv 64 c32
    /\ BGU.u64_at M3 (o + 8) n
    /\ (forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros (H8 & H9 & H18 & H2 & C8 & C16 & C24 & C32 & R8 & R16 & R24 & R32) Hn Hold A16 SLO SHI WR Ao Olo Ohi WO Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 32%nat => Z_to_bv 64 n | 34%nat => Z_to_bv 64 old
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | 44%nat => Z_to_bv 64 c32 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U32: bv_unsigned (ev E 32) = n) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = old) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c32) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E PA.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PA.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M PA.kn0).
  { unfold know_ok. cbv delta [PA.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U35. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U35. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U35. lia. lia. lia. exact WO. }
    apply Forall_cons. { eapply (BGU.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-64) (ELit 64) z64 64 o sp U35 U2 z32_ok eq_refl z64_ok eq_refl). lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite (BL.zalu_sound ALU_SLTU (ev E 34) (ev E 32) 0). lia. cbn [BL.zalu]. rewrite U34, U32.
                         destruct (Z.ltb_spec old n); [lia|reflexivity]. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C32. }
    apply Forall_nil. }
  destruct (PA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PA.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A35: bv_unsigned (ev E' 35) = o) by (rewrite AG by lia; exact U35).
  assert (MF: forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> M' a = M a).
  { intros a Ha. apply Hfr. unfold SGP.outside. change PA.F0 with [(EVar 35, 8, ELit 8)].
    constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A35. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i PA.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg PA.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]).
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc PA.ps0) with RETI. apply ret_2142c. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PA.regs0 PA.regs_out 48 KSA KSA_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
  split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
  split. { eapply (BGU.u64_of_KWord E' M' 35 8). apply Hcells. change (SR.ps_cells PA.ps0) with PA.cells. cbv delta [PA.cells]. cbn. tauto. exact A35.
           cbn [edenot]. rewrite AG by lia. exact U32. }
  split. exact MF. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eA0 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 34)) (EVar 37).
Definition zA0 : BL.za := Eval vm_compute in (BL.zc eA0).
Lemma zA0_ok : BL.zcomp eA0 = Some zA0. Proof. vm_compute. reflexivity. Qed.
Definition eA2 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (EMd M_MUL (ELit (-8)) (EVar 34)).
Definition zA2 : BL.za := Eval vm_compute in (BL.zc eA2).
Lemma zA2_ok : BL.zcomp eA2 = Some zA2. Proof. vm_compute. reflexivity. Qed.

Lemma p2b_run fx R M (o n old sp fb q c8 c16 c24 c32 : Z) :
  at_ret1 R M o n old sp c8 c16 c24 c32 -> 0 <= old < n -> n <= 2 ^ 27 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BGU.writable M (o + 8) 8 ->
  BGU.u8_at M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = true -> BGU.u64_at M (o + 24) q -> 4096 <= q -> q + 8 * n <= 2 ^ 47 ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 MEMSET M3)
    /\ (forall x, In x KSB -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24 /\ getr R3 (reg 18) = Z_to_bv 64 c32
    /\ getr R3 (reg 10) = Z_to_bv 64 (q + 8 * old) /\ getr R3 (reg 11) = Z_to_bv 64 0 /\ getr R3 (reg 12) = Z_to_bv 64 (8 * (n - old))
    /\ BGU.u64_at M3 (o + 8) n
    /\ (forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros (H8 & H9 & H18 & H2 & C8 & C16 & C24 & C32 & R8 & R16 & R24 & R32) Hn Hn2 A16 SLO SHI WR Ao Olo Ohi WO O0 Hfb B0 O24 Hq Hq2.
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 32%nat => Z_to_bv 64 n | 34%nat => Z_to_bv 64 old | 33%nat => Z_to_bv 64 fb | 37%nat => Z_to_bv 64 q
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | 44%nat => Z_to_bv 64 c32 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U32: bv_unsigned (ev E 32) = n) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = old) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = q) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c32) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E PB.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PB.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M PB.kn0).
  { unfold know_ok. cbv delta [PB.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U35. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U35. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U35. lia. lia. lia. exact WO. }
    apply Forall_cons. { eapply (BGU.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-64) (ELit 64) z64 64 o sp U35 U2 z32_ok eq_refl z64_ok eq_refl). lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite (BL.zalu_sound ALU_SLTU (ev E 34) (ev E 32) 1). lia. cbn [BL.zalu]. rewrite U34, U32.
                         destruct (Z.ltb_spec old n); [reflexivity|lia]. }
    apply Forall_cons. { eapply (BDU.kentry_KWord1_var E M 35 0 33 o fb U35 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U33, (L5RESU.land1_of_bit0 fb true) by (lia || exact B0). lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U35. exact U37. lia. lia. exact O24. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U37. lia. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U34. lia. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U32. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C32. }
    apply Forall_nil. }
  destruct (PB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PB.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A35: bv_unsigned (ev E' 35) = o) by (rewrite AG by lia; exact U35).
  assert (MF: forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> M' a = M a).
  { intros a Ha. apply Hfr. unfold SGP.outside. change PB.F0 with [(EVar 35, 8, ELit 8)].
    constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A35. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i PB.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg PB.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PB.regs0 PB.regs_out 48 KSB KSB_ok HR Hag Hregs j Hj). }
  split. { apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]. }
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
  split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
  split. { rewrite (BGU.out_reg PB.regs_out E' R' 10 Hregs) by lia. change (nth 10 PB.regs_out (ELit 0)) with eA0. apply BGU.word_of_unsigned.
           rewrite (BGU.edenot_kept 48 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E eA0 zA0 zA0_ok). cbn [BL.zden zA0]. unfold BL.uv. rewrite U34, U37.
           unfold BL.MM. rewrite (Z.mod_small (8 * old)) by lia. rewrite Z.mod_small by lia. lia. }
  split. { rewrite (BGU.out_reg PB.regs_out E' R' 11 Hregs) by lia. reflexivity. }
  split. { rewrite (BGU.out_reg PB.regs_out E' R' 12 Hregs) by lia. change (nth 12 PB.regs_out (ELit 0)) with eA2. apply BGU.word_of_unsigned.
           rewrite (BGU.edenot_kept 48 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E eA2 zA2 zA2_ok). cbn [BL.zden zA2]. unfold BL.uv. rewrite U34, U32.
           unfold BL.MM. rewrite (Z.mod_small (8 * n)) by lia.
           replace (18446744073709551608 * old) with ((2 ^ 64 - 8) * old) by reflexivity.
           replace ((2 ^ 64 - 8) * old) with (- (8 * old) + old * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
           rewrite Zplus_mod_idemp_r. replace (8 * n + - (8 * old)) with (8 * (n - old)) by lia. apply Z.mod_small. lia. }
  split. { eapply (BGU.u64_of_KWord E' M' 35 8). apply Hcells. change (SR.ps_cells PB.ps0) with PB.cells. cbv delta [PB.cells]. cbn. tauto. exact A35.
           cbn [edenot]. rewrite AG by lia. exact U32. }
  split. exact MF. exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma memset_run fx R M (dst k r : Z) :
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 k ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  0 <= k -> 0 <= dst -> dst + k < 2 ^ 64 -> L5.writable RSEGS M dst k ->
  exists R3, msteps RSEGS (st fx R MEMSET M) (st fx R3 r (wbytes M (Z_to_bv 64 dst) (repeat (Z_to_bv 8 0) (Z.to_nat k))))
    /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 dst.
Proof.
  intros H10 H11 H12 H1 RA Hk Hd Hdk W.
  destruct (ub0_fill_spec_memset fx M (Z_to_bv 64 dst) (Z_to_bv 64 0) k R (Z_to_bv 64 r) Hk
              ltac:(rewrite BGU.unsigned_lit by lia; lia)
              ltac:(replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
              ltac:(rewrite BGU.unsigned_lit by lia; unfold AX2.two64; lia)
              (L5K.ret_ok_lit r RA) H1 H10 H11 H12) as (R3 & MS & KO & A10).
  exists R3. split. { rewrite BGU.unsigned_lit in MS by lia. exact MS. }
  split. { intros i Hi. apply (L5K.kept_ok_index R R3 i KO Hi). } exact A10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2c_run fx R M (o n old sp fb c8 c16 c24 c32 r : Z) :
  at_ret1 R M o n old sp c8 c16 c24 c32 -> 0 <= old < n -> n <= 2 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 64) 64 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BGU.writable M (o + 8) 24 ->
  BGU.u8_at M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = false ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 r M3)
    /\ (forall x, In x KSC0 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24 /\ getr R3 (reg 18) = Z_to_bv 64 c32
    /\ BGU.u64_at M3 (o + 8) n /\ (old = 0 -> BGU.u64_at M3 (o + 16) 0) /\ BGU.u64_at M3 (o + 24) 0
    /\ (forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> ~ (o + 16 + 8 * old <= bv_unsigned a < o + 32) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros (H8 & H9 & H18 & H2 & C8 & C16 & C24 & C32 & R8 & R16 & R24 & R32) Hn Hn2 A16 SLO SHI WR Ao Olo Ohi WO O0 Hfb B0 Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 32%nat => Z_to_bv 64 n | 33%nat => Z_to_bv 64 fb
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | 44%nat => Z_to_bv 64 c32 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U32: bv_unsigned (ev E 32) = n) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c32) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (KCOMMON: forall d, d = (if Z.eqb old 0 then 0 else 1) -> Forall (kentry_ok RSEGS E M)
    ([KRange (EVar 2) 140735332483136 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-64)) (ELit 64);
      KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8; KWr (SA (EVar 35) 8) (ELit 24);
      KDisj (SA (EVar 35) 0) (ELit 32) (SA (EVar 2) (-64)) (ELit 64)] ++
     (if Z.eqb old 0 then [KRange (EVar 32) 1 2] else []) ++
     [KWord (SA (EVar 35) 0) 1 (EVar 33); KRange (EVar 33) 0 255; KRange (EAlu ALU_AND (EVar 33) (ELit 1)) 0 0;
      KWord (SA (EVar 2) (-8)) 8 (EVar 41); KWord (SA (EVar 2) (-16)) 8 (EVar 42); KWord (SA (EVar 2) (-24)) 8 (EVar 43); KWord (SA (EVar 2) (-32)) 8 (EVar 44)])).
  { intros d _. apply Forall_app. split.
    { apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
      apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
      apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
      apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U35. lia. }
      apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U35. lia. lia. }
      apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U35. lia. lia. lia. exact WO. }
      apply Forall_cons. { eapply (BGU.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-64) (ELit 64) z64 64 o sp U35 U2 z32_ok eq_refl z64_ok eq_refl). lia. }
      apply Forall_nil. }
    apply Forall_app. split.
    { destruct (Z.eqb_spec old 0). apply Forall_cons. eapply BGU.kentry_KRange_var. exact U32. lia. apply Forall_nil. apply Forall_nil. }
    apply Forall_cons. { eapply (BDU.kentry_KWord1_var E M 35 0 33 o fb U35 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0. }
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U33, (L5RESU.land1_of_bit0 fb false) by (lia || exact B0). lia. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C32. }
    apply Forall_nil. }
  destruct (Z.eq_dec old 0) as [OLD0|OLD1].
  - (* [comment removed for export] *)
    assert (HR: regs_ok E PC0.regs0 R).
    { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PC0.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
      rewrite BGU.alu_add_lit. exact H2. rewrite H18. subst old. reflexivity. }
    assert (HK: know_ok RSEGS E M PC0.kn0).
    { unfold know_ok. specialize (KCOMMON 0). rewrite OLD0 in KCOMMON. cbn [Z.eqb app] in KCOMMON. exact (KCOMMON eq_refl). }
    destruct (PC0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0. change PC0.NX0 with 48%nat in Hag.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A35: bv_unsigned (ev E' 35) = o) by (rewrite AG by lia; exact U35).
    assert (MF: forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> ~ (o + 16 + 8 * old <= bv_unsigned a < o + 32) -> M' a = M a).
    { intros a Ha Hb. apply Hfr. unfold SGP.outside. change PC0.F0 with [(EVar 35, 8, ELit 24)].
      constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A35. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i PC0.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg PC0.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
    assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]).
    exists fx', R', M'. split.
    { eapply msteps_trans. exact Hms. change (SR.ps_pc PC0.ps0) with RETI. apply ret_2142c. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' PC0.regs0 PC0.regs_out 48 KSC0 KSC0_ok HR Hag Hregs j Hj). }
    split. exact R1.
    split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
    split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
    split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
    split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
    split. { eapply (BGU.u64_of_KWord E' M' 35 8). apply Hcells. change (SR.ps_cells PC0.ps0) with PC0.cells. cbv delta [PC0.cells]. cbn. tauto. exact A35.
             cbn [edenot]. rewrite AG by lia. exact U32. }
    split. { intros _. eapply (BGU.u64_of_KWord E' M' 35 16). apply Hcells. change (SR.ps_cells PC0.ps0) with PC0.cells. cbv delta [PC0.cells]. cbn. tauto. exact A35. reflexivity. }
    split. { eapply (BGU.u64_of_KWord E' M' 35 24). apply Hcells. change (SR.ps_cells PC0.ps0) with PC0.cells. cbv delta [PC0.cells]. cbn. tauto. exact A35. reflexivity. }
    split. exact MF. exact Hgr.
  - (* [comment removed for export] *)
    assert (OLD: old = 1) by lia. assert (N2: n = 2) by lia.
    assert (HR: regs_ok E PC1.regs0 R).
    { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PC1.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
      rewrite BGU.alu_add_lit. exact H2. rewrite H8, N2. reflexivity. rewrite H18, OLD. reflexivity. }
    assert (HK: know_ok RSEGS E M PC1.kn0).
    { unfold know_ok. specialize (KCOMMON 1). rewrite (proj2 (Z.eqb_neq old 0) OLD1) in KCOMMON. cbn [app] in KCOMMON. exact (KCOMMON eq_refl). }
    destruct (PC1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0. change PC1.NX0 with 48%nat in Hag.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A35: bv_unsigned (ev E' 35) = o) by (rewrite AG by lia; exact U35).
    assert (MF: forall a : word, ~ (o + 8 <= bv_unsigned a < o + 16) -> ~ (o + 16 + 8 * old <= bv_unsigned a < o + 32) -> M' a = M a).
    { intros a Ha Hb. apply Hfr. unfold SGP.outside. change PC1.F0 with [(EVar 35, 8, ELit 8); (EVar 35, 24, ELit 8)].
      constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A35. rewrite BGU.unsigned_lit by lia. lia. }
      constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A35. rewrite BGU.unsigned_lit by lia. subst old. lia. } constructor. }
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i PC1.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg PC1.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
    assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]).
    exists fx', R', M'. split.
    { eapply msteps_trans. exact Hms. change (SR.ps_pc PC1.ps0) with RETI. apply ret_2142c. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
    split. { intros j Hj. change KSC0 with KSC1 in Hj. apply (BGU.kept_regs E E' R R' PC1.regs0 PC1.regs_out 48 KSC1 KSC1_ok HR Hag Hregs j Hj). }
    split. exact R1.
    split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
    split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
    split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
    split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
    split. { rewrite N2. eapply (BGU.u64_of_KWord E' M' 35 8). apply Hcells. change (SR.ps_cells PC1.ps0) with PC1.cells. cbv delta [PC1.cells]. cbn. tauto. exact A35. reflexivity. }
    split. { intros X. exfalso. lia. }
    split. { eapply (BGU.u64_of_KWord E' M' 35 24). apply Hcells. change (SR.ps_cells PC1.ps0) with PC1.cells. cbv delta [PC1.cells]. cbn. tauto. exact A35. reflexivity. }
    split. exact MF. exact Hgr.
Qed.
End SCFG_1.


End L5RSZPU.
