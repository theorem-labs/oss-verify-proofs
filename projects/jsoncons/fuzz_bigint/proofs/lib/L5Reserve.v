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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_21134_21d54 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkShl BigLinkReduce L5Defs L5Core L5CoreKit L5CoreKitS L5CoreSpecs L5AReserve.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5Reserve.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5RES.
Import L5CS.
Module PD := LibSegZ_lcres0d.
Module PI := LibSegZ_lcres0i.
Module P1 := LibSegZ_lcres1.
Module P2 := LibSegZ_lcres2.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition RET1 : Z := 0x2125c.      (* [comment removed for export] *)
Definition RETI : Z := 0x212a8.      (* [comment removed for export] *)

Definition KSD : list nat := Eval vm_compute in (BG.kept_list 48 PD.regs0 PD.regs_out).
Lemma KSD_ok : BG.kept_ok 48 PD.regs0 PD.regs_out KSD = true. Proof. vm_compute. reflexivity. Qed.
Definition KSI : list nat := Eval vm_compute in (BG.kept_list 48 PI.regs0 PI.regs_out).
Lemma KSI_ok : BG.kept_ok 48 PI.regs0 PI.regs_out KSI = true. Proof. vm_compute. reflexivity. Qed.
Definition KS1 : list nat := Eval vm_compute in (BG.kept_list 48 P1.regs0 P1.regs_out).
Lemma KS1_ok : BG.kept_ok 48 P1.regs0 P1.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BG.kept_list 48 P2.regs0 P2.regs_out).
Lemma KS2_ok : BG.kept_ok 48 P2.regs0 P2.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.

Definition z32 : BL.za := Eval vm_compute in (BL.zc (ELit 32)).
Definition z64 : BL.za := Eval vm_compute in (BL.zc (ELit 64)).
Definition z16 : BL.za := Eval vm_compute in (BL.zc (ELit 16)).
Lemma z32_ok : BL.zcomp (ELit 32) = Some z32. Proof. vm_compute. reflexivity. Qed.
Lemma z64_ok : BL.zcomp (ELit 64) = Some z64. Proof. vm_compute. reflexivity. Qed.
Lemma z16_ok : BL.zcomp (ELit 16) = Some z16. Proof. vm_compute. reflexivity. Qed.

Lemma ret_21170 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M RETI W_212a8 r F_212a8 eq_refl D_212a8 H1 Hr He). Qed.

(* [comment removed for export] *)
Definition fgrow1 (fb : Z) : Z := 4 * (fb / 4) + 1.                                      (* [comment removed for export] *)
Definition fgrow2 (f1 fb : Z) : Z := Z.lor (Z.land f1 253) (Z.land fb 2).                 (* [comment removed for export] *)
Lemma fgrow_eq fb : 0 <= fb < 256 -> Z.testbit fb 0 = false -> fgrow2 (fgrow1 fb) fb = Z.lor fb 1.
Proof.
  intros Hfb B0.
  pose proof (L5K.byte_cases (fun fb => implb (negb (Z.testbit fb 0)) (Z.eqb (fgrow2 (fgrow1 fb) fb) (Z.lor fb 1))) ltac:(vm_compute; reflexivity) fb Hfb) as H.
  cbn beta in H. rewrite B0 in H. cbn in H. apply Z.eqb_eq. exact H.
Qed.
Lemma fgrow1_range fb : 0 <= fb < 256 -> 0 <= fgrow1 fb < 256.
Proof. intros. unfold fgrow1. pose proof (Z.div_mod fb 4 ltac:(lia)). pose proof (Z.mod_pos_bound fb 4 ltac:(lia)). lia. Qed.
Lemma lor1_range fb : 0 <= fb < 256 -> 0 <= Z.lor fb 1 < 256.
Proof.
  intros Hfb. pose proof (L5K.byte_cases (fun fb => (Z.leb 0 (Z.lor fb 1) && Z.ltb (Z.lor fb 1) 256)%bool) ltac:(vm_compute; reflexivity) fb Hfb) as H.
  cbn beta in H. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.
Lemma lor1_bit0 fb : Z.testbit (Z.lor fb 1) 0 = true.
Proof. rewrite Z.lor_spec. change (Z.testbit 1 0) with true. apply Bool.orb_true_r. Qed.
Lemma land1_of_bit0 fb (b : bool) : 0 <= fb -> Z.testbit fb 0 = b -> Z.land fb 1 = (if b then 1 else 0).
Proof.
  intros Hfb B0. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite B0. destruct b; reflexivity. }
  replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
  destruct b. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma noop_run fx R M (o n sp fb c16 : Z) (dyn : bool) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 64) 64 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 ->
  BG.u8_at M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = dyn -> BG.u64_at M (o + 16) c16 -> 0 <= c16 < 2 ^ 64 ->
  (if dyn then n <= c16 else n <= 2) ->
  exists fx' R1 M1, msteps RSEGS (st fx R RESERVE M) (st fx' R1 RETI M1)
    /\ (forall x, In x KSD -> getr R1 (reg x) = getr R (reg x))
    /\ (forall a : word, ~ (sp - 64 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 H11 Hn H2 A16 SLO SHI WR Ao Olo Ohi O0 Hfb B0 O16 Hc16 CAP.
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb | 36%nat => Z_to_bv 64 c16 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BG.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbv [E ev Vf]; rewrite H10; apply BG.unsigned_lit; lia).
  assert (U11: bv_unsigned (ev E 11) = n) by (cbv [E ev Vf]; rewrite H11; apply BG.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = c16) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (KAND: forall d, Z.land fb 1 = d -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 33) (ELit 1)) d d)).
  { intros d Hd. cbn [kentry_ok edenot]. rewrite BSHL.and_lit_val by lia. rewrite U33, Hd. lia. }
  assert (KCOMMON: Forall (kentry_ok RSEGS E M)
     [KRange (EVar 2) 140735332483136 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-64)) (ELit 64);
      KRange (EVar 10) 4096 140737488355328; KAlign (EVar 10) 8; KDisj (SA (EVar 10) 0) (ELit 32) (SA (EVar 2) (-64)) (ELit 64);
      KWord (SA (EVar 10) 0) 1 (EVar 33); KRange (EVar 33) 0 255]).
  { apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply (BG.kentry_KDisj_z E M 10 0 (ELit 32) z32 32 2 (-64) (ELit 64) z64 64 o sp U10 U2 z32_ok eq_refl z64_ok eq_refl). lia. }
    apply Forall_cons. { eapply (BSHL.kentry_KWord1_var E M 10 0 33 o fb U10 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U33. lia. } apply Forall_nil. }
  destruct dyn.
  - assert (HR: regs_ok E PD.regs0 R).
    { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl PD.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
    assert (HK: know_ok RSEGS E M PD.kn0).
    { unfold know_ok. cbv delta [PD.kn0].
      repeat (apply Forall_cons; [eapply (proj1 (Forall_forall _ _) KCOMMON); cbn; tauto|]).
      apply Forall_cons. { apply KAND. apply (land1_of_bit0 fb true). lia. exact B0. }
      apply Forall_cons. { eapply BG.kentry_KWord_var. exact U10. exact U36. lia. lia. exact O16. }
      apply Forall_cons. { cbn [kentry_ok edenot]. rewrite (BL.zalu_sound ALU_SLTU (ev E 36) (ev E 11) 0). lia. cbn [BL.zalu]. rewrite U36, U11.
                           destruct (Z.ltb_spec c16 n); [lia|reflexivity]. }
      apply Forall_nil. }
    destruct (PD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0. change PD.NX0 with 48%nat in Hag.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PD.regs0 PD.regs_out 48 KSD KSD_ok HR Hag Hregs j Hj). }
    split. { intros a Ha. apply Hfr. unfold SGP.outside. change PD.F0 with [(EVar 2, -64, ELit 64)].
             constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BG.unsigned_lit by lia. lia. } constructor. }
    exact Hgr.
  - assert (HR: regs_ok E PI.regs0 R).
    { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl PI.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
    assert (HK: know_ok RSEGS E M PI.kn0).
    { unfold know_ok. cbv delta [PI.kn0].
      repeat (apply Forall_cons; [eapply (proj1 (Forall_forall _ _) KCOMMON); cbn; tauto|]).
      apply Forall_cons. { apply KAND. apply (land1_of_bit0 fb false). lia. exact B0. }
      apply Forall_cons. { eapply BG.kentry_KWord_var. exact U10. exact U36. lia. lia. exact O16. }
      apply Forall_cons. { eapply BG.kentry_KRange_var. exact U11. lia. }
      apply Forall_nil. }
    destruct (PI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BSHL.nth_error_single in Hnth. subst ps0. change PI.NX0 with 48%nat in Hag.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. change KSD with KSI in Hj. apply (BG.kept_regs E E' R R' PI.regs0 PI.regs_out 48 KSI KSI_ok HR Hag Hregs j Hj). }
    split. { intros a Ha. apply Hfr. unfold SGP.outside. change PI.F0 with [(EVar 2, -64, ELit 64)].
             constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BG.unsigned_lit by lia. lia. } constructor. }
    exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efg1 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4) (EAlu ALU_SRL (EVar 33) (ELit 2))) (ELit 1).
Definition zfg1 : BL.za := Eval vm_compute in (BL.zc efg1).
Lemma zfg1_ok : BL.zcomp efg1 = Some zfg1. Proof. vm_compute. reflexivity. Qed.

Lemma grow1_run fx R M (o n sp fb len v0 v1 : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 n -> 3 <= n <= 2 ^ 23 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 64) 64 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BG.writable M o 32 ->
  BG.u8_at M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = false ->
  BG.u64_at M (o + 8) len -> 0 <= len < 2 ^ 64 -> BG.u64_at M (o + 16) v0 -> 0 <= v0 < 2 ^ 64 -> BG.u64_at M (o + 24) v1 -> 0 <= v1 < 2 ^ 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R RESERVE M) (st fx' R1 ARESERVE M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64)
    /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 9) = Z_to_bv 64 n /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 n
    /\ getr R1 (reg 18) = Z_to_bv 64 v0 /\ getr R1 (reg 19) = Z_to_bv 64 v1 /\ getr R1 (reg 20) = Z_to_bv 64 (Z.land fb 2) /\ getr R1 (reg 21) = Z_to_bv 64 len
    /\ BG.u8_at M1 o (fgrow1 fb) /\ BG.u64_at M1 (o + 8) 0 /\ BG.u64_at M1 (o + 16) 0 /\ BG.u64_at M1 (o + 24) 0
    /\ BG.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BG.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BG.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BG.u64_at M1 (sp - 32) (bv_unsigned (getr R (reg 18)))
    /\ BG.u64_at M1 (sp - 40) (bv_unsigned (getr R (reg 19))) /\ BG.u64_at M1 (sp - 48) (bv_unsigned (getr R (reg 20)))
    /\ BG.u64_at M1 (sp - 56) (bv_unsigned (getr R (reg 21)))
    /\ (forall a : word, ~ (sp - 64 <= bv_unsigned a < sp) -> ~ (o <= bv_unsigned a < o + 32) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 H11 Hn H2 A16 SLO SHI WR Ao Olo Ohi WO O0 Hfb B0 O8 Hlen O16 Hv0 O24 Hv1.
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb | 34%nat => Z_to_bv 64 len | 36%nat => Z_to_bv 64 v0 | 37%nat => Z_to_bv 64 v1 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BG.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbv [E ev Vf]; rewrite H10; apply BG.unsigned_lit; lia).
  assert (U11: bv_unsigned (ev E 11) = n) by (cbv [E ev Vf]; rewrite H11; apply BG.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = len) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = v0) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = v1) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (HR: regs_ok E P1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M P1.kn0).
  { unfold know_ok. cbv delta [P1.kn0].
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U10. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U10. lia. lia. lia. rewrite Z.add_0_r. exact WO. }
    apply Forall_cons. { eapply (BG.kentry_KDisj_z E M 10 0 (ELit 32) z32 32 2 (-64) (ELit 64) z64 64 o sp U10 U2 z32_ok eq_refl z64_ok eq_refl). lia. }
    apply Forall_cons. { eapply (BSHL.kentry_KWord1_var E M 10 0 33 o fb U10 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { cbn [kentry_ok edenot]. rewrite BSHL.and_lit_val by lia. rewrite U33, (land1_of_bit0 fb false) by (lia || exact B0). lia. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U10. exact U34. lia. lia. exact O8. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U10. exact U36. lia. lia. exact O16. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U10. exact U37. lia. lia. exact O24. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U11. lia. }
    apply Forall_nil. }
  destruct (P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BSHL.nth_error_single in Hnth. subst ps0. change P1.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  assert (A10: bv_unsigned (ev E' 10) = o) by (rewrite AG by lia; exact U10).
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P1.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg P1.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
  assert (CELL: forall off k, In (KWord (SA (EVar 2) off) 8 (EVar k)) P1.cells -> (k < 32)%nat -> Vf k = getr R (reg k) -> BG.u64_at M' (sp + off) (bv_unsigned (getr R (reg k)))).
  { intros off k Hin Hk HV. eapply (BG.u64_of_KWord E' M' 2 off). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. exact Hin. exact A2.
    cbn [edenot]. rewrite AG by lia. change (ev E k) with (Vf k). rewrite HV. reflexivity. }
  assert (CELLO: forall off, In (KWord (SA (EVar 10) off) 8 (ELit 0)) P1.cells -> BG.u64_at M' (o + off) 0).
  { intros off Hin. eapply (BG.u64_of_KWord E' M' 10 off). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. exact Hin. exact A10. reflexivity. }
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' P1.regs0 P1.regs_out 48 KS1 KS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 1 Hregs) by lia. reflexivity. }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 2 Hregs) by lia. change (nth 2 P1.regs_out (ELit 0)) with (EAlu ALU_ADD (EVar 2) (ELit (-64))).
           cbn [edenot]. rewrite (BG.word_of_unsigned _ _ A2), BG.alu_add_lit. reflexivity. }
  split. { apply (OUT 8%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
  split. { apply (OUT 9%nat 11%nat); [lia | reflexivity | lia | exact U11]. }
  split. { apply (OUT 10%nat 10%nat); [lia | reflexivity | lia | exact U10]. }
  split. { apply (OUT 11%nat 11%nat); [lia | reflexivity | lia | exact U11]. }
  split. { apply (OUT 18%nat 36%nat); [lia | reflexivity | lia | exact U36]. }
  split. { apply (OUT 19%nat 37%nat); [lia | reflexivity | lia | exact U37]. }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 20 Hregs) by lia. change (nth 20 P1.regs_out (ELit 0)) with (EAlu ALU_AND (EVar 33) (ELit 2)).
           cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. rewrite BSHL.and_lit_val by lia. rewrite U33. reflexivity. }
  split. { apply (OUT 21%nat 34%nat); [lia | reflexivity | lia | exact U34]. }
  split. { replace o with (o + 0) by lia. eapply (BI.u8_of_KWord1_e E' M' 10 0 efg1 o (fgrow1 fb)).
           apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. cbv delta [P1.cells]. cbn. tauto. exact A10.
           apply BG.word_of_unsigned. rewrite (BG.edenot_kept 48 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E efg1 zfg1 zfg1_ok).
           cbn [BL.zden zfg1]. unfold BL.uv. rewrite U33. unfold BL.MM, fgrow1. change (2 ^ 2) with 4.
           pose proof (Z.div_mod fb 4 ltac:(lia)). pose proof (Z.mod_pos_bound fb 4 ltac:(lia)).
           rewrite (Z.mod_small (4 * _)) by lia. rewrite Z.mod_small by lia. reflexivity. apply fgrow1_range. lia. }
  split. { apply (CELLO 8). cbv delta [P1.cells]. cbn. tauto. }
  split. { apply (CELLO 16). cbv delta [P1.cells]. cbn. tauto. }
  split. { apply (CELLO 24). cbv delta [P1.cells]. cbn. tauto. }
  split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 32) with (sp + -32) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 40) with (sp + -40) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 48) with (sp + -48) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { replace (sp - 56) with (sp + -56) by lia. apply CELL; [cbv delta [P1.cells]; cbn; tauto | lia | reflexivity]. }
  split. { intros a Ha Hb. apply Hfr. unfold SGP.outside. change P1.F0 with [(EVar 2, -64, ELit 64); (EVar 10, 0, ELit 32)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BG.unsigned_lit by lia. lia. }
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A10. rewrite BG.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efg2 : expr := EAlu ALU_OR (EAlu ALU_AND (EVar 38) (ELit 253)) (EAlu ALU_AND (EVar 33) (ELit 2)).
Definition zfg2 : BL.za := Eval vm_compute in (BL.zc efg2).
Lemma zfg2_ok : BL.zcomp efg2 = Some zfg2. Proof. vm_compute. reflexivity. Qed.

Lemma grow2_run fx R M (o n sp fb len v0 v1 f1 cap A r : Z) (c8 c16 c24 c32 c40 c48 c56 : Z) :
  getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 n -> 3 <= n <= 2 ^ 23 ->
  getr R (reg 18) = Z_to_bv 64 v0 -> getr R (reg 19) = Z_to_bv 64 v1 -> getr R (reg 20) = Z_to_bv 64 (Z.land fb 2) -> getr R (reg 21) = Z_to_bv 64 len ->
  0 <= v0 < 2 ^ 64 -> 0 <= v1 < 2 ^ 64 -> 0 <= fb < 256 -> 0 <= len < 2 ^ 64 -> 0 <= f1 < 256 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> sp mod 16 = 0 -> 0x7fff7f800000 + 64 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 64) 64 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BG.writable M o 32 ->
  BG.u8_at M o f1 -> BG.u64_at M (o + 16) cap -> 0 <= cap < 2 ^ 64 -> BG.u64_at M (o + 24) A ->
  4096 <= A -> A + 16 <= sp - 64 -> A mod 8 = 0 -> BG.writable M A 16 ->
  BG.u64_at M (sp - 8) c8 -> BG.u64_at M (sp - 16) c16 -> BG.u64_at M (sp - 24) c24 -> BG.u64_at M (sp - 32) c32 ->
  BG.u64_at M (sp - 40) c40 -> BG.u64_at M (sp - 48) c48 -> BG.u64_at M (sp - 56) c56 ->
  0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 -> 0 <= c24 < 2 ^ 64 -> 0 <= c32 < 2 ^ 64 -> 0 <= c40 < 2 ^ 64 -> 0 <= c48 < 2 ^ 64 -> 0 <= c56 < 2 ^ 64 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 r M3)
    /\ (forall x, In x KS2 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24
    /\ getr R3 (reg 18) = Z_to_bv 64 c32 /\ getr R3 (reg 19) = Z_to_bv 64 c40 /\ getr R3 (reg 20) = Z_to_bv 64 c48 /\ getr R3 (reg 21) = Z_to_bv 64 c56
    /\ BG.u8_at M3 o (fgrow2 f1 fb) /\ BG.u64_at M3 (o + 8) len /\ BG.u64_at M3 A v0 /\ BG.u64_at M3 (A + 8) v1
    /\ (forall a : word, ~ (o <= bv_unsigned a < o + 16) -> ~ (A <= bv_unsigned a < A + 16) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H9 Hn H18 H19 H20 H21 Hv0 Hv1 Hfb Hlen Hf1 H2 A16 SLO SHI WR Ao Olo Ohi WO O0 O16 Hcap O24 Alo Ahi Aal WA
         C8 C16 C24 C32 C40 C48 C56 R8 R16 R24 R32 R40 R48 R56 Er [Hr He].
  pose proof (L5.land_byte_range fb 2 ltac:(lia)) as Hfb2.
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 32%nat => Z_to_bv 64 n | 33%nat => Z_to_bv 64 fb | 34%nat => Z_to_bv 64 len
                                         | 36%nat => Z_to_bv 64 v0 | 37%nat => Z_to_bv 64 v1 | 38%nat => Z_to_bv 64 f1 | 39%nat => Z_to_bv 64 cap | 40%nat => Z_to_bv 64 A
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | 44%nat => Z_to_bv 64 c32
                                         | 45%nat => Z_to_bv 64 c40 | 46%nat => Z_to_bv 64 c48 | 47%nat => Z_to_bv 64 c56 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U32: bv_unsigned (ev E 32) = n) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = len) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = v0) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = v1) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U38: bv_unsigned (ev E 38) = f1) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U39: bv_unsigned (ev E 39) = cap) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U40: bv_unsigned (ev E 40) = A) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c32) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U45: bv_unsigned (ev E 45) = c40) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U46: bv_unsigned (ev E 46) = c48) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U47: bv_unsigned (ev E 47) = c56) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (HR: regs_ok E P2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P2.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BG.alu_add_lit. exact H2. etransitivity. exact H20. symmetry. apply BG.word_of_unsigned. rewrite BSHL.and_lit_val by lia. rewrite BG.unsigned_lit by lia. reflexivity. }
  assert (HK: know_ok RSEGS E M P2.kn0).
  { unfold know_ok. cbv delta [P2.kn0].
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U35. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U35. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U35. lia. lia. lia. rewrite Z.add_0_r. exact WO. }
    apply Forall_cons. { eapply (BG.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-64) (ELit 64) z64 64 o sp U35 U2 z32_ok eq_refl z64_ok eq_refl). lia. }
    apply Forall_cons. { eapply (BSHL.kentry_KWord1_var E M 35 0 38 o f1 U35 U38). lia. lia. lia. rewrite Z.add_0_r. exact O0. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U38. lia. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U33. lia. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U35. exact U39. lia. lia. exact O16. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U35. exact U40. lia. lia. exact O24. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U40. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U40. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U40. lia. lia. lia. rewrite Z.add_0_r. exact WA. }
    apply Forall_cons. { eapply (BG.kentry_KDisj_z E M 40 0 (ELit 16) z16 16 2 (-64) (ELit 64) z64 64 A sp U40 U2 z16_ok eq_refl z64_ok eq_refl). lia. }
    apply Forall_cons. { eapply (BG.kentry_KDisj_z E M 40 0 (ELit 16) z16 16 35 0 (ELit 32) z32 32 A o U40 U35 z16_ok eq_refl z32_ok eq_refl). lia. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U32. lia. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C32. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U45. lia. lia. exact C40. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U46. lia. lia. exact C48. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U47. lia. lia. exact C56. }
    apply Forall_nil. }
  destruct (P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BSHL.nth_error_single in Hnth. subst ps0. change P2.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A35: bv_unsigned (ev E' 35) = o) by (rewrite AG by lia; exact U35).
  assert (A40: bv_unsigned (ev E' 40) = A) by (rewrite AG by lia; exact U40).
  assert (MF: forall a : word, ~ (o <= bv_unsigned a < o + 16) -> ~ (A <= bv_unsigned a < A + 16) -> M' a = M a).
  { intros a Ha Hb. apply Hfr. unfold SGP.outside. change P2.F0 with [(EVar 35, 0, ELit 16); (EVar 40, 0, ELit 16)].
    constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A35. rewrite BG.unsigned_lit by lia. lia. }
    constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A40. rewrite BG.unsigned_lit by lia. lia. } constructor. }
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P2.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BG.out_reg P2.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]).
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc P2.ps0) with RETI. apply ret_21170. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' P2.regs0 P2.regs_out 48 KS2 KS2_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
  split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
  split. { apply (OUT 19%nat 45%nat); [lia | reflexivity | lia | exact U45]. }
  split. { apply (OUT 20%nat 46%nat); [lia | reflexivity | lia | exact U46]. }
  split. { apply (OUT 21%nat 47%nat); [lia | reflexivity | lia | exact U47]. }
  split. { replace o with (o + 0) by lia. eapply (BI.u8_of_KWord1_e E' M' 35 0 efg2 o (fgrow2 f1 fb)).
           apply Hcells. change (SR.ps_cells P2.ps0) with P2.cells. cbv delta [P2.cells]. cbn. tauto. exact A35.
           apply BG.word_of_unsigned. rewrite (BG.edenot_kept 48 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E efg2 zfg2 zfg2_ok).
           cbn [BL.zden zfg2]. unfold BL.uv. rewrite U38, U33. reflexivity.
           unfold fgrow2. pose proof (L5.land_byte_range f1 253 ltac:(lia)).
           pose proof (L5K.byte_cases (fun x => forallb (fun y => Z.ltb (Z.lor (Z.land (Z.of_nat y) 253) (Z.land x 2)) 256 && Z.leb 0 (Z.lor (Z.land (Z.of_nat y) 253) (Z.land x 2)))%bool (seq 0 256)) ltac:(vm_compute; reflexivity) fb Hfb) as T.
           cbn beta in T. rewrite forallb_forall in T. specialize (T (Z.to_nat f1) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T by lia.
           apply andb_prop in T as [T1 T2]. apply Z.ltb_lt in T1. apply Z.leb_le in T2. lia. }
  split. { eapply (BG.u64_of_KWord E' M' 35 8). apply Hcells. change (SR.ps_cells P2.ps0) with P2.cells. cbv delta [P2.cells]. cbn. tauto. exact A35.
           cbn [edenot]. rewrite AG by lia. exact U34. }
  split. { replace A with (A + 0) by lia. eapply (BG.u64_of_KWord E' M' 40 0). apply Hcells. change (SR.ps_cells P2.ps0) with P2.cells. cbv delta [P2.cells]. cbn. tauto. exact A40.
           cbn [edenot]. rewrite AG by lia. exact U36. }
  split. { eapply (BG.u64_of_KWord E' M' 40 8). apply Hcells. change (SR.ps_cells P2.ps0) with P2.cells. cbv delta [P2.cells]. cbn. tauto. exact A40.
           cbn [edenot]. rewrite AG by lia. exact U37. }
  split. exact MF. exact Hgr.
Qed.

(* [comment removed for export] *)
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem reserve_ok : reserve_spec L HI.
Proof.
  unfold reserve_spec. intros fx R M model K LB cr o n sp r b HH MOK HK0 H10 H11 Hn CAP CR H1 RA H2 H4 STK OB Ao Olo Ohi WO KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  assert (WR64: BG.writable M (sp - 64) 64).
  { change (L5.writable RSEGS M (sp - 64) 64). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct b as [fb len st]. pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap] in *.
  (* [comment removed for export] *)
  assert (C16: exists c16, BG.u64_at M (o + 16) c16 /\ 0 <= c16 < 2 ^ 64 /\
               match st with L5.BInl v0 _ => c16 = v0 | L5.BDyn cap _ => c16 = cap end).
  { destruct st as [v0 v1|cap q]. destruct OST as (B0 & O16 & O24 & Hl & R0 & R1). exists v0. repeat split; try lia. exact O16.
    destruct OST as (B0 & O16 & O24 & Hl & Hc & Aq & Qlo & Qhi). exists cap. repeat split; try lia. exact O16. }
  destruct C16 as (c16 & O16 & Hc16 & Ec16).
  (* [comment removed for export] *)
  assert (NOOP: forall dyn, Z.testbit fb 0 = dyn -> (if dyn then n <= c16 else n <= 2) -> (dyn = true \/ n <= 2) ->
            srealizes RSEGS SCFG (cfg R RESERVE M model) K).
  { intros dyn B0 HC HG.
    destruct (noop_run fx R M o n sp fb c16 dyn H10 H11 ltac:(lia) H2 A16 ltac:(lia) ltac:(lia) WR64 Ao Olo ltac:(lia) O0 Hfb B0 O16 Hc16 HC)
      as (fx1 & R1 & M1 & MS1 & K1 & FR1 & GR1).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml.
    { eapply msteps_trans. exact MS1. apply ret_21170. rewrite (K1 1%nat) by (apply L5K.In_of_mem; reflexivity). exact H1. exact Hr. exact He. }
    apply (KONT fx1 R1 M1 model Same LB cr).
    - split. { apply L5K.regs_preserved_by_index. intros i Hi. apply K1. L5K.inlist Hi. }
      split. { destruct HG as [HG|HG]. left. rewrite <- HG. exact B0. right. exact HG. }
      split. reflexivity. split. reflexivity.
      split. { eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1. rewrite BG.unsigned_lit by lia. lia. lia. lia. exact OB. }
      split.
      + intros a (Ha & CA & NE & _). apply FR1. rewrite BG.unsigned_lit by lia.
        destruct CA as [IB|[[S1 S2]|IM]].
        * destruct IB as (bb & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _).
          lia.
        * unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in S2. lia.
        * rewrite (ly_img_hi L LY) in IM. lia.
      + split. { unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi. apply GR1. apply DEF. lia. }
        intros a Ha CA NE DM. apply GR1. exact DM.
    - apply L5C.model_but_vm_refl.
    - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
      intros a Ha. destruct (Z_lt_le_dec a (sp - 64)) as [Hlt|Hge]. left. apply FR1. rewrite BG.unsigned_lit by lia. lia.
      destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1. rewrite BG.unsigned_lit by lia. lia. exact GR1. }
  destruct st as [v0 v1|cap q].
  2: { (* [comment removed for export] *) destruct OST as (B0 & _). apply (NOOP true B0). subst c16. apply CAP. exact B0. left; reflexivity. }
  destruct OST as (B0 & OV0 & OV1 & Hl2 & Rv0 & Rv1). subst c16.
  destruct (Z_lt_le_dec 2 n) as [GROW | SMALL].
  2: { apply (NOOP false B0). exact SMALL. right. exact SMALL. }
  (* [comment removed for export] *)
  pose proof (L5ARES.round_up_bounds n ltac:(lia)) as [RB RM].
  assert (Hlen: 0 <= Z.of_nat len < 2 ^ 64) by lia.
  destruct (grow1_run fx R M o n sp fb (Z.of_nat len) v0 v1 H10 H11 ltac:(lia) H2 A16 ltac:(lia) ltac:(lia) WR64 Ao Olo ltac:(lia) WO
              O0 Hfb B0 O8 Hlen OV0 Rv0 OV1 Rv1)
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & R1_18 & R1_19 & R1_20 & R1_21 & D0 & D8 & D16 & D24
        & C8 & C16 & C24 & C32 & C40 & C48 & C56 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  eapply (L5ARES.areserve_ok L HI LY HIok fx1 R1 M1 model K LB cr o n (sp - 64) RET1).
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 64)) as [Hlt|Hge]. left. apply FR1; rewrite BG.unsigned_lit by lia; lia.
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia.
    destruct (Z_lt_le_dec a o) as [Hlt''|Hge'']. left. apply FR1; rewrite BG.unsigned_lit by lia; lia.
    destruct (Z_lt_le_dec a (o + 32)) as [Hlt3|Hge3]. right; left. lia. left. apply FR1; rewrite BG.unsigned_lit by lia; lia.
    exact GR1.
  - exact MOK.
  - exact HK0.
  - exact R1_10.
  - exact R1_11.
  - lia.
  - apply CR. exact B0. lia.
  - exact R1_1.
  - split. unfold RET1. lia. reflexivity.
  - exact R1_2.
  - rewrite <- H4. apply (K1 4%nat). apply L5K.In_of_mem. reflexivity.
  - split. { replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
    intros i Hi. apply GR1. replace (sp - 64 - (64 + (16 + 8224)) + i) with (sp - (64 + (64 + (16 + 8224))) + i) by lia. apply DEF. lia.
  - exact Ao.
  - lia.
  - exact Ohi.
  - change (L5.writable RSEGS M1 o 32). eapply L5.writable_grows. exact GR1. exact WO.
  - exact D8.
  - exact D24.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 A RP FB [E16 E24] HP MBV HH2.
    pose proof FB as ((BR0 & BR1 & BR2 & BR3 & BR4) & BA & DEFA). pose proof BR1 as BR1'. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1'.
    destruct HP as (PRES & SDEF & CDEF). unfold ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES, SDEF, CDEF.
    assert (LBhi: forall bb, In bb LB -> fst bb + snd bb <= hl_ceil L).
    { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
    (* [comment removed for export] *)
    assert (CL: forall a, sp - 64 <= a < 2 ^ 47 -> ~ (o + 16 <= a < o + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha Hna. apply PRES. apply (L5C.kept_stack L LB (sp - 64) (64 + (16 + 8224))). lia. lia. lia.
      rewrite (ly_errno L LY). lia. lia. apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. lia. apply L5C.outside_nil. }
    assert (T1: forall a v, sp - 64 <= a -> a + 8 <= 2 ^ 47 -> (a + 8 <= o + 16 \/ o + 32 <= a) -> BG.u64_at M1 a v -> BG.u64_at M2 a v).
    { intros a v H1a H2a H3a Hu. eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. lia. exact Hu. }
    pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
    pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as RG9. pose proof (bv_unsigned_in_range _ (getr R (reg 18))) as RG18.
    pose proof (bv_unsigned_in_range _ (getr R (reg 19))) as RG19. pose proof (bv_unsigned_in_range _ (getr R (reg 20))) as RG20.
    pose proof (bv_unsigned_in_range _ (getr R (reg 21))) as RG21.
    change (bv_modulus 64) with (2 ^ 64) in RG1, RG8, RG9, RG18, RG19, RG20, RG21.
    assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BG.unsigned_lit. lia. }
    assert (WR2 : BG.writable M2 (sp - 64) 64).
    { change (L5.writable RSEGS M2 (sp - 64) 64). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. lia.
      eapply L5.writable_grows. exact GR1. exact WR64. }
    assert (D0' : BG.u8_at M2 o (fgrow1 fb)).
    { eapply (L5C.u8_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. lia. exact D0. }
    assert (WO2 : BG.writable M2 o 32).
    { change (L5.writable RSEGS M2 o (16 + 16)). apply L5C.writable_app. lia. lia. lia. lia.
      - eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. lia.
        eapply L5.writable_grows. exact GR1. eapply L5.writable_sub. exact WO. lia. lia.
      - apply L5C.writable_of_defined; [|lia|lia]. apply (L5C.defined_app M2 (o + 16) 8 8); [| |lia].
        eapply L5KS.u64_at_defined. exact E16. unfold L5KS.IMG_HI; lia. lia.
        replace (o + 16 + 8) with (o + 24) by lia. eapply L5KS.u64_at_defined. exact E24. unfold L5KS.IMG_HI; lia. lia. }
    assert (A8 : A mod 8 = 0).
    { pose proof (Z.div_mod A 16 ltac:(lia)) as X. rewrite BR2, Z.add_0_r in X. rewrite X.
      replace (16 * (A / 16)) with ((2 * (A / 16)) * 8) by lia. apply Z_mod_mult. }
    assert (WA2 : BG.writable M2 A 16).
    { change (L5.writable RSEGS M2 A 16). apply L5C.writable_of_defined; [|lia|lia]. eapply L5.defined_sub. exact DEFA. lia. lia. }
    destruct (grow2_run fx2 R2 M2 o n sp fb (Z.of_nat len) v0 v1 (fgrow1 fb) (round_up n) A r
                (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr R (reg 18)))
                (bv_unsigned (getr R (reg 19))) (bv_unsigned (getr R (reg 20))) (bv_unsigned (getr R (reg 21)))
                ltac:(rewrite <- L5K.rl8, (RP 8%bv ltac:(cbn; tauto)), L5K.rl8; exact R1_8)
                ltac:(rewrite <- L5K.rl9, (RP 9%bv ltac:(cbn; tauto)), L5K.rl9; exact R1_9) ltac:(lia)
                ltac:(rewrite <- L5K.rl18, (RP 18%bv ltac:(cbn; tauto)), L5K.rl18; exact R1_18)
                ltac:(rewrite <- L5K.rl19, (RP 19%bv ltac:(cbn; tauto)), L5K.rl19; exact R1_19)
                ltac:(rewrite <- L5K.rl20, (RP 20%bv ltac:(cbn; tauto)), L5K.rl20; exact R1_20)
                ltac:(rewrite <- L5K.rl21, (RP 21%bv ltac:(cbn; tauto)), L5K.rl21; exact R1_21)
                Rv0 Rv1 Hfb Hlen (fgrow1_range fb Hfb)
                ltac:(rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2; exact R1_2) A16 ltac:(lia) ltac:(lia) WR2
                Ao Olo ltac:(lia) WO2 D0' E16 ltac:(lia) E24 ltac:(lia) ltac:(lia) A8 WA2
                (T1 (sp - 8) _ ltac:(lia) ltac:(lia) ltac:(lia) C8) (T1 (sp - 16) _ ltac:(lia) ltac:(lia) ltac:(lia) C16)
                (T1 (sp - 24) _ ltac:(lia) ltac:(lia) ltac:(lia) C24) (T1 (sp - 32) _ ltac:(lia) ltac:(lia) ltac:(lia) C32)
                (T1 (sp - 40) _ ltac:(lia) ltac:(lia) ltac:(lia) C40) (T1 (sp - 48) _ ltac:(lia) ltac:(lia) ltac:(lia) C48)
                (T1 (sp - 56) _ ltac:(lia) ltac:(lia) ltac:(lia) C56)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E1 RA)
      as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & R3_19 & R3_20 & R3_21 & F0 & F8 & FA0 & FA8 & MF3 & GR3).
    eapply (L5.cps_of_msteps RSEGS). { rewrite (L5C.halted_but_vm _ _ MBV). exact Mh. } { rewrite (L5C.lazy_but_vm _ _ MBV). exact Ml. }
    exact MS3.
    apply (KONT fx3 R3 M3 model2 (Grown A (round_up n)) ((A, 8 * round_up n) :: LB) (debit L cr (8 * round_up n))).
    + cbn [reserve_post]. split.
      { (* [comment removed for export] *)
        apply L5K.regs_preserved_by_index. intros i Hi.
        cbn in Hi. destruct Hi as [<-|Hi]. { rewrite R3_2, <- H2, L5K.rl2. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R3_8. symmetry. apply BG.word_of_unsigned. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R3_9. symmetry. apply BG.word_of_unsigned. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R3_18. symmetry. apply BG.word_of_unsigned. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R3_19. symmetry. apply BG.word_of_unsigned. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R3_20. symmetry. apply BG.word_of_unsigned. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R3_21. symmetry. apply BG.word_of_unsigned. reflexivity. }
        assert (G: forall j, In j [22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
        { intros j Hj.
          assert (M2j: In j KS2) by (pose proof Hj as H'; L5K.inlist H').
          assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
          assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
          rewrite (K3 j M2j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
        apply G. L5K.inlist Hi. }
      split. exact B0. split. lia. split. reflexivity. split. reflexivity. split. reflexivity.
      split. { (* [comment removed for export] *)
        split. exact (proj1 FB). split. exact BA. intros i Hi. apply GR3. apply DEFA. exact Hi. }
      split. { exists v0, v1. split. reflexivity. split. exact FA0. exact FA8. }
      split. { (* [comment removed for export] *)
        unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
        split. { rewrite <- (fgrow_eq fb Hfb B0). exact F0. }
        split. { apply lor1_range. exact Hfb. }
        split. exact F8.
        split. apply lor1_bit0.
        split. { eapply (BG.u64_at_frame M2 M3). lia. lia. intros i Hi. apply MF3; rewrite BG.unsigned_lit by lia; lia. exact E16. }
        split. { eapply (BG.u64_at_frame M2 M3). lia. lia. intros i Hi. apply MF3; rewrite BG.unsigned_lit by lia; lia. exact E24. }
        repeat split; try lia. apply L5KS.hull_apart_of. exact BR1'. }
      (* [comment removed for export] *)
      split.
      * intros a KA. pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
        pose proof (L5C.kept_not_fresh L LB sp RESERVE_SCR [(o, 32)] a A (8 * round_up n) KA BA BR1 BR4 LBhi) as NA.
        rewrite (MF3 (Z_to_bv 64 a)) by (rewrite BG.unsigned_lit by lia; lia).
        assert (FA: ~ (sp - (64 + (64 + (16 + 8224))) <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros Hna. apply FR1; rewrite BG.unsigned_lit by lia; lia. }
        destruct CA as [IB|[[S1 S2]|IM]].
        -- rewrite PRES. apply FA. { destruct IB as (bb & Hb & Hin). pose proof (LBhi bb Hb). lia. }
           split. lia. split. left. exact IB. split. exact NE. apply L5C.outside_cons. unfold L5.in_rng; cbn [fst snd]; lia. apply L5C.outside_nil.
        -- unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in S2. rewrite PRES. apply FA. lia.
           split. lia. split. right. left. split. exact S1. lia. split. exact NE. apply L5C.outside_cons. unfold L5.in_rng; cbn [fst snd]; lia. apply L5C.outside_nil.
        -- rewrite PRES. apply FA. rewrite (ly_img_hi L LY) in IM. lia.
           split. lia. split. right. right. exact IM. split. exact NE. apply L5C.outside_cons. unfold L5.in_rng; cbn [fst snd]; lia. apply L5C.outside_nil.
      * split.
        { unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi. rewrite (MF3 (Z_to_bv 64 _)); [| rewrite BG.unsigned_lit by lia; lia | rewrite BG.unsigned_lit by lia; lia].
          destruct (Z_lt_le_dec (sp - (64 + (64 + (16 + 8224))) + i) (sp - 64)) as [Hlt|Hge].
          -- replace (sp - (64 + (64 + (16 + 8224))) + i) with (sp - 64 - (64 + (16 + 8224)) + i) by lia. apply SDEF. lia.
          -- rewrite CL by lia. apply GR1. apply DEF. lia. }
        intros a Ha CA NE DM. unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply GR3. apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE.
        apply GR1. exact DM.
    + exact MBV.
    + eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
      intros a Ha. destruct (Z_lt_le_dec a o) as [H1a|H1a].
      { destruct (Z_lt_le_dec a A) as [H2a|H2a]. left. apply MF3; rewrite BG.unsigned_lit by lia; lia.
        destruct (Z_lt_le_dec a (A + 16)) as [H3a|H3a]. right; right. exists (A, 8 * round_up n). split. left; reflexivity. cbn. lia.
        left. apply MF3; rewrite BG.unsigned_lit by lia; lia. }
      destruct (Z_lt_le_dec a (o + 16)) as [H4a|H4a]. right; left. lia. left. apply MF3; rewrite BG.unsigned_lit by lia; lia.
      exact GR3.
Qed.

End WithHeap.
End SCFG_1.

End L5RES.
