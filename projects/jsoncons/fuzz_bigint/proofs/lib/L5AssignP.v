(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore AsanPlanSoundSums Src0Sums
     Src0_code_20088_210bc BigLinkBase BigLinkGlue BigLinkInlBase BigLinkShl BigLinkReduce L5Defs L5Core L5CoreKit L5CoreKitS L5CoreSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5AssignP.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5ASGP.
Import L5CS.
Module P1 := LibSegZ_lcasg1.
Module PZ := LibSegZ_lcasg2z.
Module PDD := LibSegZ_lcasg2dd.
Module PDI := LibSegZ_lcasg2di.
Module PID := LibSegZ_lcasg2id.
Module PII := LibSegZ_lcasg2ii.
Module P3 := LibSegZ_lcasg3.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition RET1 : Z := 0x21050.      (* [comment removed for export] *)
Definition RET2 : Z := 0x21098.      (* [comment removed for export] *)
Definition RETI : Z := 0x210b8.      (* [comment removed for export] *)
Definition MEMCPY : Z := 0x58924.

Definition KS1 : list nat := Eval vm_compute in (BG.kept_list 48 P1.regs0 P1.regs_out).
Lemma KS1_ok : BG.kept_ok 48 P1.regs0 P1.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSZ : list nat := Eval vm_compute in (BG.kept_list 48 PZ.regs0 PZ.regs_out).
Lemma KSZ_ok : BG.kept_ok 48 PZ.regs0 PZ.regs_out KSZ = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BG.kept_list 48 PII.regs0 PII.regs_out).
Lemma KS2dd_ok : BG.kept_ok 48 PDD.regs0 PDD.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS2di_ok : BG.kept_ok 48 PDI.regs0 PDI.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS2id_ok : BG.kept_ok 48 PID.regs0 PID.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS2ii_ok : BG.kept_ok 48 PII.regs0 PII.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS3 : list nat := Eval vm_compute in (BG.kept_list 48 P3.regs0 P3.regs_out).
Lemma KS3_ok : BG.kept_ok 48 P3.regs0 P3.regs_out KS3 = true. Proof. vm_compute. reflexivity. Qed.

Definition z32 : BL.za := Eval vm_compute in (BL.zc (ELit 32)).
Definition z48 : BL.za := Eval vm_compute in (BL.zc (ELit 48)).
Lemma z32_ok : BL.zcomp (ELit 32) = Some z32. Proof. vm_compute. reflexivity. Qed.
Lemma z48_ok : BL.zcomp (ELit 48) = Some z48. Proof. vm_compute. reflexivity. Qed.

Lemma ret_20f80 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M RETI W_210b8 r F_210b8 eq_refl D_210b8 H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run fx R M (o o' sp fb' len' y24 : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 o' -> o <> o' -> 4096 <= o -> o < 2 ^ 47 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 48) 48 ->
  o' mod 8 = 0 -> sp <= o' -> o' + 32 <= 2 ^ 47 ->
  BG.u8_at M o' fb' -> 0 <= fb' < 256 -> BG.u64_at M (o' + 8) len' -> 0 <= len' < 2 ^ 64 -> BG.u64_at M (o' + 24) y24 -> 0 <= y24 < 2 ^ 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R ASSIGN M) (st fx' R1 RESIZE M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 48)
    /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 9) = Z_to_bv 64 y24 /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 len'
    /\ getr R1 (reg 18) = Z_to_bv 64 len' /\ getr R1 (reg 19) = Z_to_bv 64 o' /\ getr R1 (reg 20) = Z_to_bv 64 fb'
    /\ BG.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BG.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BG.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BG.u64_at M1 (sp - 32) (bv_unsigned (getr R (reg 18)))
    /\ BG.u64_at M1 (sp - 40) (bv_unsigned (getr R (reg 19))) /\ BG.u64_at M1 (sp - 48) (bv_unsigned (getr R (reg 20)))
    /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 H11 Hne Olo Ohi H2 A16 SLO SHI WR Ao' Olo' Ohi' O0' Hfb' O8' Hlen' O24' Hy24.
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb' | 34%nat => Z_to_bv 64 len' | 37%nat => Z_to_bv 64 y24 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BG.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbv [E ev Vf]; rewrite H10; apply BG.unsigned_lit; lia).
  assert (U11: bv_unsigned (ev E 11) = o') by (cbv [E ev Vf]; rewrite H11; apply BG.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb') by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = len') by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = y24) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (HR: regs_ok E P1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M P1.kn0).
  { unfold know_ok. cbv delta [P1.kn0].
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U11. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U11. lia. lia. }
    apply Forall_cons. { eapply (BG.kentry_KDisj_z E M 11 0 (ELit 32) z32 32 2 (-48) (ELit 48) z48 48 o' sp U11 U2 z32_ok eq_refl z48_ok eq_refl). lia. }
    apply Forall_cons. { cbn [kentry_ok edenot].
                         rewrite (BL.zalu_sound ALU_SLTU (alu64 ALU_SUB (ev E 10) (ev E 11)) (Z_to_bv 64 1) 0). lia.
                         cbn [BL.zalu]. rewrite (BL.zalu_sound ALU_SUB (ev E 10) (ev E 11) ((o - o') mod BL.MM)) by (cbn [BL.zalu]; rewrite U10, U11; reflexivity).
                         rewrite BG.unsigned_lit by lia. unfold BL.MM.
                         destruct (Z.ltb_spec ((o - o') mod 2 ^ 64) 1); [|reflexivity]. exfalso.
                         destruct (Z_lt_le_dec o o') as [Hl|Hg].
                         - replace (o - o') with ((2 ^ 64 + (o - o')) + (-1) * 2 ^ 64) in H by lia. rewrite Z_mod_plus_full, Z.mod_small in H by lia. lia.
                         - rewrite Z.mod_small in H by lia. lia. }
    apply Forall_cons. { eapply (BSHL.kentry_KWord1_var E M 11 0 33 o' fb' U11 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0'. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U11. exact U34. lia. lia. exact O8'. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U11. exact U37. lia. lia. exact O24'. }
    apply Forall_nil. }
  destruct (P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BSHL.nth_error_single in Hnth. subst ps0. change P1.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P1.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg P1.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
  assert (CELL: forall off k, In (KWord (SA (EVar 2) off) 8 (EVar k)) P1.cells -> (k < 32)%nat -> Vf k = getr R (reg k) -> BG.u64_at M' (sp + off) (bv_unsigned (getr R (reg k)))).
  { intros off k Hin Hk HV. eapply (BG.u64_of_KWord E' M' 2 off). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. exact Hin. exact A2.
    cbn [edenot]. rewrite AG by lia. change (ev E k) with (Vf k). rewrite HV. reflexivity. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' P1.regs0 P1.regs_out 48 KS1 KS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 2 Hregs) by lia. change (nth 2 P1.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-48))).
           cbn [edenot]. rewrite (BG.word_of_unsigned _ _ A2), BG.alu_add_lit. reflexivity. }
  split. { apply (OUT 8%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
  split. { apply (OUT 9%nat 37%nat); [lia | reflexivity | lia | exact U37]. }
  split. { apply (OUT 10%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
  split. { apply (OUT 11%nat 34%nat); [lia | reflexivity | lia | exact U34]. }
  split. { apply (OUT 18%nat 34%nat); [lia | reflexivity | lia | exact U34]. }
  split. { apply (OUT 19%nat 11%nat); [lia | reflexivity | lia | exact U11]. }
  split. { apply (OUT 20%nat 33%nat); [lia | reflexivity | lia | exact U33]. }
  split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 32) with (sp + -32) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 40) with (sp + -40) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 48) with (sp + -48) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { intros a Ha. apply Hfr. unfold SGP.outside. change P1.F0 with [(EVar 2, -48, ELit 48)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BG.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_ret1 (R : bvmap 5 word) (M : word -> option byte) (o y24 n o' fb' sp c8 c16 c24 c32 c40 c48 : Z) : Prop :=
  getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 y24 /\ getr R (reg 18) = Z_to_bv 64 n /\ getr R (reg 19) = Z_to_bv 64 o' /\
  getr R (reg 20) = Z_to_bv 64 fb' /\ getr R (reg 2) = Z_to_bv 64 (sp - 48) /\
  BG.u64_at M (sp - 8) c8 /\ BG.u64_at M (sp - 16) c16 /\ BG.u64_at M (sp - 24) c24 /\ BG.u64_at M (sp - 32) c32 /\ BG.u64_at M (sp - 40) c40 /\ BG.u64_at M (sp - 48) c48 /\
  0 <= c8 < 2 ^ 64 /\ 0 <= c16 < 2 ^ 64 /\ 0 <= c24 < 2 ^ 64 /\ 0 <= c32 < 2 ^ 64 /\ 0 <= c40 < 2 ^ 64 /\ 0 <= c48 < 2 ^ 64.

(* [comment removed for export] *)
Lemma epilogue_run fx R M (pc : Z) (o y24 n o' fb' sp c8 c16 c24 c32 c40 c48 r : Z) :
  (pc = RET1 /\ n = 0 \/ pc = RET2) ->
  at_ret1 R M o y24 n o' fb' sp c8 c16 c24 c32 c40 c48 -> 0 <= o < 2 ^ 64 -> 0 <= y24 < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o' < 2 ^ 64 -> 0 <= fb' < 2 ^ 64 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 48) 48 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R pc M) (st fx' R3 r M3)
    /\ (forall x, In x KS3 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24
    /\ getr R3 (reg 18) = Z_to_bv 64 c32 /\ getr R3 (reg 19) = Z_to_bv 64 c40 /\ getr R3 (reg 20) = Z_to_bv 64 c48 /\ getr R3 (reg 10) = Z_to_bv 64 o
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros Hpc (H8 & H9 & H18 & H19 & H20 & H2 & C8 & C16 & C24 & C32 & C40 & C48 & R8 & R16 & R24 & R32 & R40 & R48) Ho Hy Hn Ho' Hf A16 SLO SHI WR Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 37%nat => Z_to_bv 64 y24 | 34%nat => Z_to_bv 64 n | 36%nat => Z_to_bv 64 o' | 33%nat => Z_to_bv 64 fb'
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | 44%nat => Z_to_bv 64 c32
                                         | 45%nat => Z_to_bv 64 c40 | 46%nat => Z_to_bv 64 c48 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c32) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U45: bv_unsigned (ev E 45) = c40) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U46: bv_unsigned (ev E 46) = c48) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (KCOMMON: Forall (kentry_ok RSEGS E M)
    [KRange (EVar 2) 140735332483120 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-48)) (ELit 48);
     KWord (SA (EVar 2) (-8)) 8 (EVar 41); KWord (SA (EVar 2) (-16)) 8 (EVar 42); KWord (SA (EVar 2) (-24)) 8 (EVar 43);
     KWord (SA (EVar 2) (-32)) 8 (EVar 44); KWord (SA (EVar 2) (-40)) 8 (EVar 45); KWord (SA (EVar 2) (-48)) 8 (EVar 46)]).
  { apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C32. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U45. lia. lia. exact C40. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U46. lia. lia. exact C48. }
    apply Forall_nil. }
  destruct Hpc as [[-> N0] | ->].
  - assert (HR: regs_ok E PZ.regs0 R).
    { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl PZ.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
      rewrite BG.alu_add_lit. exact H2. rewrite H18, N0. reflexivity. }
    assert (HK: know_ok RSEGS E M PZ.kn0) by (unfold know_ok; cbv delta [PZ.kn0]; exact KCOMMON).
    destruct (PZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0. change PZ.NX0 with 48%nat in Hag.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i PZ.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg PZ.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
    assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]).
    exists fx', R', M'. split.
    { eapply msteps_trans. exact Hms. change (SR.ps_pc PZ.ps0) with RETI. apply ret_20f80. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
    split. { intros j Hj. change KS3 with KSZ in Hj. apply (BG.kept_regs E E' R R' PZ.regs0 PZ.regs_out 48 KSZ KSZ_ok HR Hag Hregs j Hj). }
    split. exact R1.
    split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
    split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
    split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
    split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
    split. { apply (OUT 19%nat 45%nat); [lia | reflexivity | lia | exact U45]. }
    split. { apply (OUT 20%nat 46%nat); [lia | reflexivity | lia | exact U46]. }
    split. { apply (OUT 10%nat 35%nat); [lia | reflexivity | lia | exact U35]. }
    split. exact MM. exact Hgr.
  - assert (HR: regs_ok E P3.regs0 R).
    { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P3.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
      rewrite BG.alu_add_lit. exact H2. }
    assert (HK: know_ok RSEGS E M P3.kn0) by (unfold know_ok; cbv delta [P3.kn0]; exact KCOMMON).
    destruct (P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0. change P3.NX0 with 48%nat in Hag.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P3.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg P3.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
    assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]).
    exists fx', R', M'. split.
    { eapply msteps_trans. exact Hms. change (SR.ps_pc P3.ps0) with RETI. apply ret_20f80. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' P3.regs0 P3.regs_out 48 KS3 KS3_ok HR Hag Hregs j Hj). }
    split. exact R1.
    split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
    split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
    split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
    split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
    split. { apply (OUT 19%nat 45%nat); [lia | reflexivity | lia | exact U45]. }
    split. { apply (OUT 20%nat 46%nat); [lia | reflexivity | lia | exact U46]. }
    split. { apply (OUT 10%nat 35%nat); [lia | reflexivity | lia | exact U35]. }
    split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efl : expr := EAlu ALU_OR (EAlu ALU_AND (EVar 33) (ELit 2)) (EAlu ALU_AND (EVar 38) (ELit 253)).
Definition zfl : BL.za := Eval vm_compute in (BL.zc efl).
Lemma zfl_ok : BL.zcomp efl = Some zfl. Proof. vm_compute. reflexivity. Qed.
Definition assign_flags (f fb' : Z) : Z := Z.lor (Z.land fb' 2) (Z.land f 253).
Lemma assign_flags_range f fb' : 0 <= f < 256 -> 0 <= fb' < 256 -> 0 <= assign_flags f fb' < 256.
Proof.
  intros Hf Hfb. unfold assign_flags.
  pose proof (L5K.byte_cases (fun x => forallb (fun y => Z.ltb (Z.lor (Z.land x 2) (Z.land (Z.of_nat y) 253)) 256 && Z.leb 0 (Z.lor (Z.land x 2) (Z.land (Z.of_nat y) 253)))%bool (seq 0 256)) ltac:(vm_compute; reflexivity) fb' Hfb) as T.
  cbn beta in T. rewrite forallb_forall in T. specialize (T (Z.to_nat f) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T by lia.
  apply andb_prop in T as [T1 T2]. apply Z.ltb_lt in T1. apply Z.leb_le in T2. lia.
Qed.

Lemma p2_run (td od : bool) fx R M (o y24 n o' fb' sp f qd : Z) :
  getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 y24 -> getr R (reg 18) = Z_to_bv 64 n -> getr R (reg 19) = Z_to_bv 64 o' ->
  getr R (reg 20) = Z_to_bv 64 fb' -> getr R (reg 2) = Z_to_bv 64 (sp - 48) ->
  1 <= n <= 2 ^ 27 -> 0 <= y24 < 2 ^ 64 -> 0 <= qd < 2 ^ 64 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 48) 48 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BG.writable M o 1 ->
  o' mod 8 = 0 -> sp <= o' -> o' + 32 <= 2 ^ 47 -> (o + 32 <= o' \/ o' + 32 <= o) ->
  BG.u8_at M o f -> 0 <= f < 256 -> Z.testbit f 0 = td -> (td = true -> BG.u64_at M (o + 24) qd) ->
  BG.u8_at M o' fb' -> 0 <= fb' < 256 -> Z.testbit fb' 0 = od ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 MEMCPY M3)
    /\ (forall x, In x KS2 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 RET2 /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R3 (reg 8) = Z_to_bv 64 o
    /\ getr R3 (reg 10) = Z_to_bv 64 (if td then qd else o + 16) /\ getr R3 (reg 11) = Z_to_bv 64 (if od then y24 else o' + 16)
    /\ getr R3 (reg 12) = Z_to_bv 64 (8 * n) /\ getr R3 (reg 18) = Z_to_bv 64 n /\ getr R3 (reg 19) = Z_to_bv 64 o' /\ getr R3 (reg 20) = Z_to_bv 64 fb'
    /\ getr R3 (reg 9) = Z_to_bv 64 (if od then y24 else o' + 16)
    /\ BG.u8_at M3 o (assign_flags f fb')
    /\ (forall a : word, ~ (o <= bv_unsigned a < o + 1) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H9 H18 H19 H20 H2 Hn Hy Hq A16 SLO SHI WR Ao Olo Ohi WO Ao' Olo' Ohi' AP O0 Hf Bf O24 O0' Hfb' Bfb'.
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 37%nat => Z_to_bv 64 y24 | 34%nat => Z_to_bv 64 n | 36%nat => Z_to_bv 64 o' | 33%nat => Z_to_bv 64 fb'
                                         | 38%nat => Z_to_bv 64 f | 39%nat => Z_to_bv 64 qd | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = y24) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = n) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = o') by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb') by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U38: bv_unsigned (ev E 38) = f) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U39: bv_unsigned (ev E 39) = qd) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (KC: forall K, In K
    [KRange (EVar 2) 140735332483120 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-48)) (ELit 48);
     KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8; KWr (SA (EVar 35) 0) (ELit 1);
     KDisj (SA (EVar 35) 0) (ELit 32) (SA (EVar 2) (-48)) (ELit 48);
     KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 8;
     KDisj (SA (EVar 36) 0) (ELit 32) (SA (EVar 2) (-48)) (ELit 48); KDisj (SA (EVar 36) 0) (ELit 32) (SA (EVar 35) 0) (ELit 32);
     KRange (EVar 34) 1 134217728;
     KWord (SA (EVar 35) 0) 1 (EVar 38); KRange (EVar 38) 0 255;
     KWord (SA (EVar 36) 0) 1 (EVar 33); KRange (EVar 33) 0 255] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BG.kentry_KRange_var. exact U2. lia.
    - eapply BG.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BG.kentry_KRange_var. exact U35. lia.
    - eapply BG.kentry_KAlign_var. exact U35. lia. lia.
    - eapply BG.kentry_KWr_var. exact U35. lia. lia. lia. rewrite Z.add_0_r. exact WO.
    - eapply (BG.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-48) (ELit 48) z48 48 o sp U35 U2 z32_ok eq_refl z48_ok eq_refl). lia.
    - eapply BG.kentry_KRange_var. exact U36. lia.
    - eapply BG.kentry_KAlign_var. exact U36. lia. lia.
    - eapply (BG.kentry_KDisj_z E M 36 0 (ELit 32) z32 32 2 (-48) (ELit 48) z48 48 o' sp U36 U2 z32_ok eq_refl z48_ok eq_refl). lia.
    - eapply (BG.kentry_KDisj_z E M 36 0 (ELit 32) z32 32 35 0 (ELit 32) z32 32 o' o U36 U35 z32_ok eq_refl z32_ok eq_refl). lia.
    - eapply BG.kentry_KRange_var. exact U34. lia.
    - eapply (BSHL.kentry_KWord1_var E M 35 0 38 o f U35 U38). lia. lia. lia. rewrite Z.add_0_r. exact O0.
    - eapply BG.kentry_KRange_var. exact U38. lia.
    - eapply (BSHL.kentry_KWord1_var E M 36 0 33 o' fb' U36 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0'.
    - eapply BG.kentry_KRange_var. exact U33. lia. }
  assert (KT: forall d, Z.land f 1 = d -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 38) (ELit 1)) d d)).
  { intros d Hd. cbn [kentry_ok edenot]. rewrite BSHL.and_lit_val by lia. rewrite U38, Hd. lia. }
  assert (KO: forall d, Z.land fb' 1 = d -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 33) (ELit 1)) d d)).
  { intros d Hd. cbn [kentry_ok edenot]. rewrite BSHL.and_lit_val by lia. rewrite U33, Hd. lia. }
  assert (KQ: td = true -> kentry_ok RSEGS E M (KWord (SA (EVar 35) 24) 8 (EVar 39))).
  { intros Htd. eapply BG.kentry_KWord_var. exact U35. exact U39. lia. lia. exact (O24 Htd). }
  assert (LT: Z.land f 1 = (if td then 1 else 0)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Bf. destruct td; reflexivity. }
    replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
    destruct td. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity. }
  assert (LO: Z.land fb' 1 = (if od then 1 else 0)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Bfb'. destruct od; reflexivity. }
    replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
    destruct od. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity. }
  assert (HRX: forall regs0, regs0 = PDD.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl PDD.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BG.alu_add_lit. exact H2. }
  assert (SAME: PDI.regs0 = PDD.regs0 /\ PID.regs0 = PDD.regs0 /\ PII.regs0 = PDD.regs0) by (repeat split; reflexivity).
  (* [comment removed for export] *)
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (KSL : list nat),
     regs0 = PDD.regs0 -> BG.kept_ok 48 regs0 regs_out KSL = true -> incl KS2 KSL ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(EVar 35, 0, ELit 1)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) -> In (KWord (SA (EVar 35) 0) 1 efl) cells ->
     nth 1 regs_out (ELit 0) = ELit 135320 -> nth 2 regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-48)) -> nth 8 regs_out (ELit 0) = EVar 35 ->
     nth 10 regs_out (ELit 0) = (if td then EVar 39 else EAlu ALU_ADD (EVar 35) (ELit 16)) ->
     nth 11 regs_out (ELit 0) = (if od then EVar 37 else EAlu ALU_ADD (EVar 36) (ELit 16)) ->
     nth 12 regs_out (ELit 0) = EMd M_MUL (ELit 8) (EVar 34) -> nth 18 regs_out (ELit 0) = EVar 34 -> nth 19 regs_out (ELit 0) = EVar 36 -> nth 20 regs_out (ELit 0) = EVar 33 ->
     nth 9 regs_out (ELit 0) = (if od then EVar 37 else EAlu ALU_ADD (EVar 36) (ELit 16)) ->
     mem_grows M M' ->
     (forall x, In x KS2 -> getr R' (reg x) = getr R (reg x))
     /\ getr R' (reg 1) = Z_to_bv 64 RET2 /\ getr R' (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R' (reg 8) = Z_to_bv 64 o
     /\ getr R' (reg 10) = Z_to_bv 64 (if td then qd else o + 16) /\ getr R' (reg 11) = Z_to_bv 64 (if od then y24 else o' + 16)
     /\ getr R' (reg 12) = Z_to_bv 64 (8 * n) /\ getr R' (reg 18) = Z_to_bv 64 n /\ getr R' (reg 19) = Z_to_bv 64 o' /\ getr R' (reg 20) = Z_to_bv 64 fb'
     /\ getr R' (reg 9) = Z_to_bv 64 (if od then y24 else o' + 16)
     /\ BG.u8_at M' o (assign_flags f fb')
     /\ (forall a : word, ~ (o <= bv_unsigned a < o + 1) -> M' a = M a) /\ mem_grows M M').
  { intros fx' E' R' M' regs0 regs_out cells F0 KSL -> KOK INCL Hag Hregs Hfr -> Hcells Hin N1 N2 N8 N10 N11 N12 N18 N19 N20 N9 Hgr.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A35: bv_unsigned (ev E' 35) = o) by (rewrite AG by lia; exact U35).
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PDD.regs0 regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. { rewrite (BG.out_reg regs_out E' R' 1 Hregs) by lia. rewrite N1. reflexivity. }
    split. { rewrite (BG.out_reg regs_out E' R' 2 Hregs) by lia. rewrite N2. cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U2), BG.alu_add_lit. reflexivity. }
    split. { apply (OUT 8%nat 35%nat); [lia | exact N8 | lia | exact U35]. }
    split. { rewrite (BG.out_reg regs_out E' R' 10 Hregs) by lia. rewrite N10. destruct td.
             cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U39.
             cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U35), BG.alu_add_lit. reflexivity. }
    split. { rewrite (BG.out_reg regs_out E' R' 11 Hregs) by lia. rewrite N11. destruct od.
             cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U37.
             cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U36), BG.alu_add_lit. reflexivity. }
    split. { rewrite (BG.out_reg regs_out E' R' 12 Hregs) by lia. rewrite N12. cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U34), BG.md_mul_lit. reflexivity. }
    split. { apply (OUT 18%nat 34%nat); [lia | exact N18 | lia | exact U34]. }
    split. { apply (OUT 19%nat 36%nat); [lia | exact N19 | lia | exact U36]. }
    split. { apply (OUT 20%nat 33%nat); [lia | exact N20 | lia | exact U33]. }
    split. { rewrite (BG.out_reg regs_out E' R' 9 Hregs) by lia. rewrite N9. destruct od.
             cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U37.
             cbn [edenot]. rewrite AG by lia. rewrite (BG.word_of_unsigned _ _ U36), BG.alu_add_lit. reflexivity. }
    split. { replace o with (o + 0) by lia. eapply (BI.u8_of_KWord1_e E' M' 35 0 efl o (assign_flags f fb')). apply Hcells. exact Hin. exact A35.
             apply BG.word_of_unsigned. rewrite (BG.edenot_kept 48 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E efl zfl zfl_ok).
             cbn [BL.zden zfl]. unfold BL.uv. rewrite U33, U38. reflexivity. apply assign_flags_range; lia. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside. constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A35. rewrite BG.unsigned_lit by lia. lia. } constructor. }
    exact Hgr. }
  destruct td; destruct od.
  - assert (HK: know_ok RSEGS E M PDD.kn0).
    { unfold know_ok. cbv delta [PDD.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply KO; exact LO | apply KQ; reflexivity] |]). apply Forall_nil. }
    destruct (PDD.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PDD.regs0 PDD.regs_out PDD.cells PDD.F0 KS2 eq_refl KS2dd_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells);
      try reflexivity. cbv delta [PDD.cells]. cbn. tauto. exact Hgr.
  - assert (HK: know_ok RSEGS E M PDI.kn0).
    { unfold know_ok. cbv delta [PDI.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply KO; exact LO | apply KQ; reflexivity] |]). apply Forall_nil. }
    destruct (PDI.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PDI.regs0 PDI.regs_out PDI.cells PDI.F0 KS2 eq_refl KS2di_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells);
      try reflexivity. cbv delta [PDI.cells]. cbn. tauto. exact Hgr.
  - assert (HK: know_ok RSEGS E M PID.kn0).
    { unfold know_ok. cbv delta [PID.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply KO; exact LO | apply KQ; reflexivity] |]). apply Forall_nil. }
    destruct (PID.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PID.regs0 PID.regs_out PID.cells PID.F0 KS2 eq_refl KS2id_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells);
      try reflexivity. cbv delta [PID.cells]. cbn. tauto. exact Hgr.
  - assert (HK: know_ok RSEGS E M PII.kn0).
    { unfold know_ok. cbv delta [PII.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply KO; exact LO | apply KQ; reflexivity] |]). apply Forall_nil. }
    destruct (PII.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PII.regs0 PII.regs_out PII.cells PII.F0 KS2 eq_refl KS2ii_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells);
      try reflexivity. cbv delta [PII.cells]. cbn. tauto. exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma memcpy_run fx R M (dst src r : Z) (ws : list Z) :
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 (8 * Z.of_nat (length ws)) ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  0 <= dst -> dst + 8 * Z.of_nat (length ws) < 2 ^ 64 -> 0 <= src -> src + 8 * Z.of_nat (length ws) < 2 ^ 64 ->
  (dst + 8 * Z.of_nat (length ws) <= src \/ src + 8 * Z.of_nat (length ws) <= dst) ->
  L5.writable RSEGS M dst (8 * Z.of_nat (length ws)) -> L5.limbs_at RSEGS M src ws ->
  exists R3, msteps RSEGS (st fx R MEMCPY M) (st fx R3 r (wbytes M (Z_to_bv 64 dst) (L5K.limb_bytes ws)))
    /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 dst.
Proof.
  intros H10 H11 H12 H1 RA Hd Hdn Hs Hsn AP W LIMBS.
  pose proof (L5K.limb_bytes_length ws) as LEN.
  destruct (src0_copy_spec_memcpy fx M (Z_to_bv 64 dst) (Z_to_bv 64 src) (8 * Z.of_nat (length ws)) (L5K.limb_bytes ws) R (Z_to_bv 64 r)
              ltac:(lia) ltac:(rewrite LEN; lia)
              ltac:(rewrite LEN; apply L5K.rdn_of_limbs_at; [exact LIMBS | lia | lia])
              ltac:(rewrite LEN; replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
              ltac:(rewrite !BG.unsigned_lit by lia; lia) ltac:(rewrite BG.unsigned_lit by lia; lia) ltac:(rewrite BG.unsigned_lit by lia; lia)
              (L5K.ret_ok_lit r RA) H1 H10 H11 H12) as (R3 & MS & KO & A10).
  exists R3. split. exact MS. split. { intros i Hi. apply (L5K.kept_ok_index R R3 i KO Hi). } exact A10.
Qed.
End SCFG_1.


End L5ASGP.
