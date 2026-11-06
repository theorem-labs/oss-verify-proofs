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
     Ub0_code_21248_21b5c BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU L5Defs L5Core L5CoreKit L5CoreKitU L5CoreSpecsU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5AssignPU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5ASGPU.
Import L5CSU.
Module P1D := LibSegZ_lcasg1du.
Module P1I := LibSegZ_lcasg1iu.
Module PZD := LibSegZ_lcasg2zdu.
Module PZI := LibSegZ_lcasg2ziu.
Module PD := LibSegZ_lcasg2du.
Module PI := LibSegZ_lcasg2iu.
Module P3 := LibSegZ_lcasg3u.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Definition RET1 : Z := 0x21474.      (* [comment removed for export] *)
Definition RET2 : Z := 0x214c0.      (* [comment removed for export] *)
Definition RETI : Z := 0x214dc.      (* [comment removed for export] *)
Definition MEMCPY : Z := 0x59420.

Definition KS1 : list nat := Eval vm_compute in (BGU.kept_list 48 P1D.regs0 P1D.regs_out).
Lemma KS1d_ok : BGU.kept_ok 48 P1D.regs0 P1D.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS1i_ok : BGU.kept_ok 48 P1I.regs0 P1I.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KSZ : list nat := Eval vm_compute in (BGU.kept_list 48 PZD.regs0 PZD.regs_out).
Lemma KSZd_ok : BGU.kept_ok 48 PZD.regs0 PZD.regs_out KSZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma KSZi_ok : BGU.kept_ok 48 PZI.regs0 PZI.regs_out KSZ = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BGU.kept_list 48 PD.regs0 PD.regs_out).
Lemma KS2d_ok : BGU.kept_ok 48 PD.regs0 PD.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS2i_ok : BGU.kept_ok 48 PI.regs0 PI.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS3 : list nat := Eval vm_compute in (BGU.kept_list 48 P3.regs0 P3.regs_out).
Lemma KS3_ok : BGU.kept_ok 48 P3.regs0 P3.regs_out KS3 = true. Proof. vm_compute. reflexivity. Qed.

Definition z32 : BL.za := Eval vm_compute in (BL.zc (ELit 32)).
Definition z48 : BL.za := Eval vm_compute in (BL.zc (ELit 48)).
Lemma z32_ok : BL.zcomp (ELit 32) = Some z32. Proof. vm_compute. reflexivity. Qed.
Lemma z48_ok : BL.zcomp (ELit 48) = Some z48. Proof. vm_compute. reflexivity. Qed.

Lemma ret_213a4 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_to fx R M RETI W_214dc r F_214dc eq_refl D_214dc H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run (od : bool) fx R M (o o' sp fb' len' y24 : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 o' -> o <> o' -> 4096 <= o -> o < 2 ^ 47 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 48) 48 ->
  o' mod 8 = 0 -> sp <= o' -> o' + 32 <= 2 ^ 47 ->
  BGU.u8_at M o' fb' -> 0 <= fb' < 256 -> Z.testbit fb' 0 = od -> BGU.u64_at M (o' + 8) len' -> 0 <= len' < 2 ^ 64 -> BGU.u64_at M (o' + 24) y24 -> 0 <= y24 < 2 ^ 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R ASSIGN M) (st fx' R1 RESIZE M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 48)
    /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 9) = Z_to_bv 64 (if od then y24 else o' + 16) /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 len'
    /\ getr R1 (reg 18) = Z_to_bv 64 o' /\ getr R1 (reg 19) = Z_to_bv 64 len'
    /\ BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BGU.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BGU.u64_at M1 (sp - 32) (bv_unsigned (getr R (reg 18)))
    /\ BGU.u64_at M1 (sp - 40) (bv_unsigned (getr R (reg 19)))
    /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 H11 Hne Olo Ohi H2 A16 SLO SHI WR Ao' Olo' Ohi' O0' Hfb' Bfb' O8' Hlen' O24' Hy24.
  set (Vf := fun k : nat => match k with 33%nat => Z_to_bv 64 fb' | 34%nat => Z_to_bv 64 len' | 37%nat => Z_to_bv 64 y24 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BGU.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = o) by (cbv [E ev Vf]; rewrite H10; apply BGU.unsigned_lit; lia).
  assert (U11: bv_unsigned (ev E 11) = o') by (cbv [E ev Vf]; rewrite H11; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb') by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = len') by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = y24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (LO: Z.land fb' 1 = (if od then 1 else 0)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Bfb'. destruct od; reflexivity. }
    replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
    destruct od. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity. }
  assert (KC: forall K, In K
    [KRange (EVar 2) 140735332483120 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-48)) (ELit 48);
     KRange (EVar 10) 4096 140737488355328; KRange (EVar 11) 4096 140737488355328; KAlign (EVar 11) 8;
     KDisj (SA (EVar 11) 0) (ELit 32) (SA (EVar 2) (-48)) (ELit 48);
     KRange (EAlu ALU_SLTU (EAlu ALU_SUB (EVar 10) (EVar 11)) (ELit 1)) 0 0;
     KWord (SA (EVar 11) 0) 1 (EVar 33); KRange (EVar 33) 0 255;
     KWord (SA (EVar 11) 8) 8 (EVar 34); KWord (SA (EVar 11) 24) 8 (EVar 37)] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KRange_var. exact U2. lia.
    - eapply BGU.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BGU.kentry_KRange_var. exact U10. lia.
    - eapply BGU.kentry_KRange_var. exact U11. lia.
    - eapply BGU.kentry_KAlign_var. exact U11. lia. lia.
    - eapply (BGU.kentry_KDisj_z E M 11 0 (ELit 32) z32 32 2 (-48) (ELit 48) z48 48 o' sp U11 U2 z32_ok eq_refl z48_ok eq_refl). lia.
    - cbn [kentry_ok edenot].
      rewrite (BL.zalu_sound ALU_SLTU (alu64 ALU_SUB (ev E 10) (ev E 11)) (Z_to_bv 64 1) 0). lia.
      cbn [BL.zalu]. rewrite (BL.zalu_sound ALU_SUB (ev E 10) (ev E 11) ((o - o') mod BL.MM)) by (cbn [BL.zalu]; rewrite U10, U11; reflexivity).
      rewrite BGU.unsigned_lit by lia. unfold BL.MM.
      destruct (Z.ltb_spec ((o - o') mod 2 ^ 64) 1); [|reflexivity]. exfalso.
      destruct (Z_lt_le_dec o o') as [Hl|Hg].
      + replace (o - o') with ((2 ^ 64 + (o - o')) + (-1) * 2 ^ 64) in H by lia. rewrite Z_mod_plus_full, Z.mod_small in H by lia. lia.
      + rewrite Z.mod_small in H by lia. lia.
    - eapply (BDU.kentry_KWord1_var E M 11 0 33 o' fb' U11 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0'.
    - eapply BGU.kentry_KRange_var. exact U33. lia.
    - eapply BGU.kentry_KWord_var. exact U11. exact U34. lia. lia. exact O8'.
    - eapply BGU.kentry_KWord_var. exact U11. exact U37. lia. lia. exact O24'. }
  assert (KO: forall d, Z.land fb' 1 = d -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 33) (ELit 1)) d d)).
  { intros d Hd. cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U33, Hd. lia. }
  assert (HRX: forall regs0, regs0 = P1D.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P1D.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (SAME: P1I.regs0 = P1D.regs0) by reflexivity.
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (KSL : list nat),
     regs0 = P1D.regs0 -> BGU.kept_ok 48 regs0 regs_out KSL = true -> incl KS1 KSL ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(EVar 2, -48, ELit 48)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) -> cells = P1D.cells ->
     nth 1 regs_out (ELit 0) = ELit 136308 -> nth 2 regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-48)) -> nth 8 regs_out (ELit 0) = EVar 10 ->
     nth 9 regs_out (ELit 0) = (if od then EVar 37 else EAlu ALU_ADD (EVar 11) (ELit 16)) ->
     nth 10 regs_out (ELit 0) = EVar 10 -> nth 11 regs_out (ELit 0) = EVar 34 -> nth 18 regs_out (ELit 0) = EVar 11 -> nth 19 regs_out (ELit 0) = EVar 34 ->
     mem_grows M M' ->
     (forall x, In x KS1 -> getr R' (reg x) = getr R (reg x))
     /\ getr R' (reg 1) = Z_to_bv 64 RET1 /\ getr R' (reg 2) = Z_to_bv 64 (sp - 48)
     /\ getr R' (reg 8) = Z_to_bv 64 o /\ getr R' (reg 9) = Z_to_bv 64 (if od then y24 else o' + 16) /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 11) = Z_to_bv 64 len'
     /\ getr R' (reg 18) = Z_to_bv 64 o' /\ getr R' (reg 19) = Z_to_bv 64 len'
     /\ BGU.u64_at M' (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M' (sp - 16) (bv_unsigned (getr R (reg 8)))
     /\ BGU.u64_at M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BGU.u64_at M' (sp - 32) (bv_unsigned (getr R (reg 18)))
     /\ BGU.u64_at M' (sp - 40) (bv_unsigned (getr R (reg 19)))
     /\ (forall a : word, ~ (sp - 48 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M').
  { intros fx' E' R' M' regs0 regs_out cells F0 KSL -> KOK INCL Hag Hregs Hfr -> Hcells -> N1 N2 N8 N9 N10 N11 N18 N19 Hgr.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
    assert (CELL: forall off k, In (KWord (SA (EVar 2) off) 8 (EVar k)) P1D.cells -> (k < 32)%nat -> Vf k = getr R (reg k) -> BGU.u64_at M' (sp + off) (bv_unsigned (getr R (reg k)))).
    { intros off k Hin Hk HV. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. exact Hin. exact A2.
      cbn [edenot]. rewrite AG by lia. change (ev E k) with (Vf k). rewrite HV. reflexivity. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' P1D.regs0 regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. { rewrite (BGU.out_reg regs_out E' R' 1 Hregs) by lia. rewrite N1. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 2 Hregs) by lia. rewrite N2. cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
    split. { apply (OUT 8%nat 10%nat); [lia | exact N8 | lia | exact U10]. }
    split. { rewrite (BGU.out_reg regs_out E' R' 9 Hregs) by lia. rewrite N9. destruct od.
             cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U37.
             cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U11), BGU.alu_add_lit. reflexivity. }
    split. { apply (OUT 10%nat 10%nat); [lia | exact N10 | lia | exact U10]. }
    split. { apply (OUT 11%nat 34%nat); [lia | exact N11 | lia | exact U34]. }
    split. { apply (OUT 18%nat 11%nat); [lia | exact N18 | lia | exact U11]. }
    split. { apply (OUT 19%nat 34%nat); [lia | exact N19 | lia | exact U34]. }
    split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 32) with (sp + -32) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 40) with (sp + -40) by lia. apply CELL; [cbv delta [P1D.cells]; cbn; tauto | lia | reflexivity]. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside.
             constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
    exact Hgr. }
  destruct od.
  - assert (HK: know_ok RSEGS E M P1D.kn0).
    { unfold know_ok. cbv delta [P1D.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KO; exact LO] |]). apply Forall_nil. }
    destruct (P1D.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' P1D.regs0 P1D.regs_out P1D.cells P1D.F0 KS1 eq_refl KS1d_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells eq_refl);
      try reflexivity. exact Hgr.
  - assert (HK: know_ok RSEGS E M P1I.kn0).
    { unfold know_ok. cbv delta [P1I.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KO; exact LO] |]). apply Forall_nil. }
    destruct (P1I.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' P1I.regs0 P1I.regs_out P1I.cells P1I.F0 KS1 eq_refl KS1i_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells eq_refl);
      try reflexivity. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition at_ret1 (R : bvmap 5 word) (M : word -> option byte) (o src n o' sp c8 c16 c24 c32 c40 : Z) : Prop :=
  getr R (reg 8) = Z_to_bv 64 o /\ getr R (reg 9) = Z_to_bv 64 src /\ getr R (reg 18) = Z_to_bv 64 o' /\ getr R (reg 19) = Z_to_bv 64 n /\
  getr R (reg 2) = Z_to_bv 64 (sp - 48) /\
  BGU.u64_at M (sp - 8) c8 /\ BGU.u64_at M (sp - 16) c16 /\ BGU.u64_at M (sp - 24) c24 /\ BGU.u64_at M (sp - 32) c32 /\ BGU.u64_at M (sp - 40) c40 /\
  0 <= c8 < 2 ^ 64 /\ 0 <= c16 < 2 ^ 64 /\ 0 <= c24 < 2 ^ 64 /\ 0 <= c32 < 2 ^ 64 /\ 0 <= c40 < 2 ^ 64.

Definition epi_post (R R3 : bvmap 5 word) (M M3 : word -> option byte) (o sp c8 c16 c24 c32 c40 : Z) : Prop :=
  (forall x, In x KSZ -> getr R3 (reg x) = getr R (reg x))
  /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24
  /\ getr R3 (reg 18) = Z_to_bv 64 c32 /\ getr R3 (reg 19) = Z_to_bv 64 c40 /\ getr R3 (reg 10) = Z_to_bv 64 o
  /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.

(* [comment removed for export] *)
Lemma epilogue_run fx R M (o src n o' sp c8 c16 c24 c32 c40 r : Z) :
  at_ret1 R M o src n o' sp c8 c16 c24 c32 c40 -> 0 <= o < 2 ^ 64 -> 0 <= src < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o' < 2 ^ 64 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 48) 48 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET2 M) (st fx' R3 r M3) /\ epi_post R R3 M M3 o sp c8 c16 c24 c32 c40.
Proof.
  intros (H8 & H9 & H18 & H19 & H2 & C8 & C16 & C24 & C32 & C40 & R8 & R16 & R24 & R32 & R40) Ho Hs Hn Ho' A16 SLO SHI WR Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 40%nat => Z_to_bv 64 src | 34%nat => Z_to_bv 64 n | 36%nat => Z_to_bv 64 o'
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | 44%nat => Z_to_bv 64 c32
                                         | 45%nat => Z_to_bv 64 c40 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c32) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U45: bv_unsigned (ev E 45) = c40) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E P3.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl P3.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P3.kn0).
  { unfold know_ok; cbv delta [P3.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C32. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U45. lia. lia. exact C40. }
    apply Forall_nil. }
  destruct (P3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change P3.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
  assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i P3.regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg P3.regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | reflexivity | lia | exact U41]).
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc P3.ps0) with RETI. apply ret_213a4. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' P3.regs0 P3.regs_out 48 KS3 KS3_ok HR Hag Hregs j). L5K.inlist Hj. }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 42%nat); [lia | reflexivity | lia | exact U42]. }
  split. { apply (OUT 9%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  split. { apply (OUT 18%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
  split. { apply (OUT 19%nat 45%nat); [lia | reflexivity | lia | exact U45]. }
  split. { apply (OUT 10%nat 35%nat); [lia | reflexivity | lia | exact U35]. }
  split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
Lemma epilogue_z_run (td : bool) fx R M (o src o' sp c8 c16 c24 c32 c40 r f qd : Z) :
  at_ret1 R M o src 0 o' sp c8 c16 c24 c32 c40 -> 0 <= o < 2 ^ 64 -> 0 <= src < 2 ^ 64 -> 0 <= o' < 2 ^ 64 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 48) 48 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 ->
  BGU.u8_at M o f -> 0 <= f < 256 -> Z.testbit f 0 = td -> (td = true -> BGU.u64_at M (o + 24) qd) -> 0 <= qd < 2 ^ 64 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 r M3) /\ epi_post R R3 M M3 o sp c8 c16 c24 c32 c40.
Proof.
  intros (H8 & H9 & H18 & H19 & H2 & C8 & C16 & C24 & C32 & C40 & R8 & R16 & R24 & R32 & R40) Ho Hs Ho' A16 SLO SHI WR Ao Olo Ohi O0 Hf Bf O24 Hq Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 40%nat => Z_to_bv 64 src | 36%nat => Z_to_bv 64 o'
                                         | 38%nat => Z_to_bv 64 f | 39%nat => Z_to_bv 64 qd
                                         | 41%nat => Z_to_bv 64 c8 | 42%nat => Z_to_bv 64 c16 | 43%nat => Z_to_bv 64 c24 | 44%nat => Z_to_bv 64 c32
                                         | 45%nat => Z_to_bv 64 c40 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U38: bv_unsigned (ev E 38) = f) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U39: bv_unsigned (ev E 39) = qd) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U42: bv_unsigned (ev E 42) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c32) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U45: bv_unsigned (ev E 45) = c40) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (LT: Z.land f 1 = (if td then 1 else 0)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Bf. destruct td; reflexivity. }
    replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
    destruct td. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity. }
  assert (KC: forall K, In K
    [KRange (EVar 2) 140735332483120 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-48)) (ELit 48);
     KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8;
     KDisj (SA (EVar 35) 0) (ELit 32) (SA (EVar 2) (-48)) (ELit 48);
     KWord (SA (EVar 35) 0) 1 (EVar 38); KRange (EVar 38) 0 255;
     KWord (SA (EVar 2) (-8)) 8 (EVar 41); KWord (SA (EVar 2) (-16)) 8 (EVar 42); KWord (SA (EVar 2) (-24)) 8 (EVar 43);
     KWord (SA (EVar 2) (-32)) 8 (EVar 44); KWord (SA (EVar 2) (-40)) 8 (EVar 45)] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KRange_var. exact U2. lia.
    - eapply BGU.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BGU.kentry_KRange_var. exact U35. lia.
    - eapply BGU.kentry_KAlign_var. exact U35. lia. lia.
    - eapply (BGU.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-48) (ELit 48) z48 48 o sp U35 U2 z32_ok eq_refl z48_ok eq_refl). lia.
    - eapply (BDU.kentry_KWord1_var E M 35 0 38 o f U35 U38). lia. lia. lia. rewrite Z.add_0_r. exact O0.
    - eapply BGU.kentry_KRange_var. exact U38. lia.
    - eapply BGU.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C8.
    - eapply BGU.kentry_KWord_var. exact U2. exact U42. lia. lia. exact C16.
    - eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C24.
    - eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C32.
    - eapply BGU.kentry_KWord_var. exact U2. exact U45. lia. lia. exact C40. }
  assert (KT: forall d, Z.land f 1 = d -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 38) (ELit 1)) d d)).
  { intros d Hd. cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U38, Hd. lia. }
  assert (KQ: td = true -> kentry_ok RSEGS E M (KWord (SA (EVar 35) 24) 8 (EVar 39))).
  { intros Htd. eapply BGU.kentry_KWord_var. exact U35. exact U39. lia. lia. exact (O24 Htd). }
  assert (HRX: forall regs0, regs0 = PZD.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PZD.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit. exact H2. }
  assert (SAME: PZI.regs0 = PZD.regs0) by reflexivity.
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (F0 : list SGP.region) (KSL : list nat) (pc' : Z),
     regs0 = PZD.regs0 -> BGU.kept_ok 48 regs0 regs_out KSL = true -> incl KSZ KSL ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [] ->
     nth 1 regs_out (ELit 0) = EVar 41 -> nth 2 regs_out (ELit 0) = EVar 2 -> nth 8 regs_out (ELit 0) = EVar 42 -> nth 9 regs_out (ELit 0) = EVar 43 ->
     nth 18 regs_out (ELit 0) = EVar 44 -> nth 19 regs_out (ELit 0) = EVar 45 -> nth 10 regs_out (ELit 0) = EVar 35 ->
     mem_grows M M' -> msteps RSEGS (st fx R RET1 M) (st fx' R' pc' M') -> pc' = RETI ->
     exists fx'' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx'' R3 r M3) /\ epi_post R R3 M M3 o sp c8 c16 c24 c32 c40).
  { intros fx' E' R' M' regs0 regs_out F0 KSL pc' -> KOK INCL Hag Hregs Hfr -> N1 N2 N8 N9 N18 N19 N10 Hgr Hms ->.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
    assert (R1: getr R' (reg 1) = Z_to_bv 64 c8) by (apply (OUT 1%nat 41%nat); [lia | exact N1 | lia | exact U41]).
    exists fx', R', M'. split.
    { eapply msteps_trans. exact Hms. apply ret_213a4. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' PZD.regs0 regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. exact R1.
    split. { apply (OUT 2%nat 2%nat); [lia | exact N2 | lia | exact U2]. }
    split. { apply (OUT 8%nat 42%nat); [lia | exact N8 | lia | exact U42]. }
    split. { apply (OUT 9%nat 43%nat); [lia | exact N9 | lia | exact U43]. }
    split. { apply (OUT 18%nat 44%nat); [lia | exact N18 | lia | exact U44]. }
    split. { apply (OUT 19%nat 45%nat); [lia | exact N19 | lia | exact U45]. }
    split. { apply (OUT 10%nat 35%nat); [lia | exact N10 | lia | exact U35]. }
    split. exact MM. exact Hgr. }
  destruct td.
  - assert (HK: know_ok RSEGS E M PZD.kn0).
    { unfold know_ok. cbv delta [PZD.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply KQ; reflexivity] |]). apply Forall_nil. }
    destruct (PZD.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    apply (POST fx' E' R' M' PZD.regs0 PZD.regs_out PZD.F0 KSZ (SR.ps_pc PZD.ps0) eq_refl KSZd_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl);
      try reflexivity. exact Hgr. exact Hms.
  - assert (HK: know_ok RSEGS E M PZI.kn0).
    { unfold know_ok. cbv delta [PZI.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply KQ; reflexivity] |]). apply Forall_nil. }
    destruct (PZI.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    apply (POST fx' E' R' M' PZI.regs0 PZI.regs_out PZI.F0 KSZ (SR.ps_pc PZI.ps0) eq_refl KSZi_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl);
      try reflexivity. exact Hgr. exact Hms.
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

Lemma p2_run (td : bool) fx R M (o src n o' fb' sp f qd : Z) :
  getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 src -> getr R (reg 18) = Z_to_bv 64 o' -> getr R (reg 19) = Z_to_bv 64 n ->
  getr R (reg 2) = Z_to_bv 64 (sp - 48) ->
  1 <= n <= 2 ^ 27 -> 4096 <= src < 2 ^ 47 -> src mod 8 = 0 -> 4096 <= qd < 2 ^ 47 -> qd mod 8 = 0 ->
  sp mod 16 = 0 -> 0x7fff7f800000 + 48 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 48) 48 ->
  o mod 8 = 0 -> sp <= o -> o + 32 <= 2 ^ 47 -> BGU.writable M o 1 ->
  o' mod 8 = 0 -> sp <= o' -> o' + 32 <= 2 ^ 47 -> (o + 32 <= o' \/ o' + 32 <= o) ->
  BGU.u8_at M o f -> 0 <= f < 256 -> Z.testbit f 0 = td -> (td = true -> BGU.u64_at M (o + 24) qd) ->
  BGU.u8_at M o' fb' -> 0 <= fb' < 256 ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 MEMCPY M3)
    /\ (forall x, In x KS2 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 RET2 /\ getr R3 (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R3 (reg 8) = Z_to_bv 64 o
    /\ getr R3 (reg 10) = Z_to_bv 64 (if td then qd else o + 16) /\ getr R3 (reg 11) = Z_to_bv 64 src
    /\ getr R3 (reg 12) = Z_to_bv 64 (8 * n) /\ getr R3 (reg 18) = Z_to_bv 64 o' /\ getr R3 (reg 19) = Z_to_bv 64 n
    /\ getr R3 (reg 9) = Z_to_bv 64 src
    /\ BGU.u8_at M3 o (assign_flags f fb')
    /\ (forall a : word, ~ (o <= bv_unsigned a < o + 1) -> M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H9 H18 H19 H2 Hn Hs As Hq Aq A16 SLO SHI WR Ao Olo Ohi WO Ao' Olo' Ohi' AP O0 Hf Bf O24 O0' Hfb'.
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 35%nat => Z_to_bv 64 o | 40%nat => Z_to_bv 64 src | 34%nat => Z_to_bv 64 n | 36%nat => Z_to_bv 64 o' | 33%nat => Z_to_bv 64 fb'
                                         | 38%nat => Z_to_bv 64 f | 39%nat => Z_to_bv 64 qd | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U40: bv_unsigned (ev E 40) = src) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = n) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = o') by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = fb') by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U38: bv_unsigned (ev E 38) = f) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U39: bv_unsigned (ev E 39) = qd) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (KC: forall K, In K
    [KRange (EVar 2) 140735332483120 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-48)) (ELit 48);
     KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 8; KWr (SA (EVar 35) 0) (ELit 1);
     KDisj (SA (EVar 35) 0) (ELit 32) (SA (EVar 2) (-48)) (ELit 48);
     KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 8;
     KDisj (SA (EVar 36) 0) (ELit 32) (SA (EVar 2) (-48)) (ELit 48); KDisj (SA (EVar 36) 0) (ELit 32) (SA (EVar 35) 0) (ELit 32);
     KRange (EVar 34) 1 134217728; KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 8;
     KWord (SA (EVar 35) 0) 1 (EVar 38); KRange (EVar 38) 0 255;
     KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 8;
     KWord (SA (EVar 36) 0) 1 (EVar 33); KRange (EVar 33) 0 255] -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KRange_var. exact U2. lia.
    - eapply BGU.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BGU.kentry_KRange_var. exact U35. lia.
    - eapply BGU.kentry_KAlign_var. exact U35. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U35. lia. lia. lia. rewrite Z.add_0_r. exact WO.
    - eapply (BGU.kentry_KDisj_z E M 35 0 (ELit 32) z32 32 2 (-48) (ELit 48) z48 48 o sp U35 U2 z32_ok eq_refl z48_ok eq_refl). lia.
    - eapply BGU.kentry_KRange_var. exact U36. lia.
    - eapply BGU.kentry_KAlign_var. exact U36. lia. lia.
    - eapply (BGU.kentry_KDisj_z E M 36 0 (ELit 32) z32 32 2 (-48) (ELit 48) z48 48 o' sp U36 U2 z32_ok eq_refl z48_ok eq_refl). lia.
    - eapply (BGU.kentry_KDisj_z E M 36 0 (ELit 32) z32 32 35 0 (ELit 32) z32 32 o' o U36 U35 z32_ok eq_refl z32_ok eq_refl). lia.
    - eapply BGU.kentry_KRange_var. exact U34. lia.
    - eapply BGU.kentry_KRange_var. exact U40. lia.
    - eapply BGU.kentry_KAlign_var. exact U40. lia. lia.
    - eapply (BDU.kentry_KWord1_var E M 35 0 38 o f U35 U38). lia. lia. lia. rewrite Z.add_0_r. exact O0.
    - eapply BGU.kentry_KRange_var. exact U38. lia.
    - eapply BGU.kentry_KRange_var. exact U39. lia.
    - eapply BGU.kentry_KAlign_var. exact U39. lia. lia.
    - eapply (BDU.kentry_KWord1_var E M 36 0 33 o' fb' U36 U33). lia. lia. lia. rewrite Z.add_0_r. exact O0'.
    - eapply BGU.kentry_KRange_var. exact U33. lia. }
  assert (KT: forall d, Z.land f 1 = d -> kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 38) (ELit 1)) d d)).
  { intros d Hd. cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U38, Hd. lia. }
  assert (KQ: td = true -> kentry_ok RSEGS E M (KWord (SA (EVar 35) 24) 8 (EVar 39))).
  { intros Htd. eapply BGU.kentry_KWord_var. exact U35. exact U39. lia. lia. exact (O24 Htd). }
  assert (LT: Z.land f 1 = (if td then 1 else 0)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Bf. destruct td; reflexivity. }
    replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
    destruct td. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity. }
  assert (HRX: forall regs0, regs0 = PD.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PD.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption.
    rewrite BGU.alu_add_lit. exact H2. }
  assert (SAME: PI.regs0 = PD.regs0) by reflexivity.
  (* [comment removed for export] *)
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (KSL : list nat),
     regs0 = PD.regs0 -> BGU.kept_ok 48 regs0 regs_out KSL = true -> incl KS2 KSL ->
     env_agree 48 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(EVar 35, 0, ELit 1)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) -> In (KWord (SA (EVar 35) 0) 1 efl) cells ->
     nth 1 regs_out (ELit 0) = ELit 136384 -> nth 2 regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-48)) -> nth 8 regs_out (ELit 0) = EVar 35 ->
     nth 10 regs_out (ELit 0) = (if td then EVar 39 else EAlu ALU_ADD (EVar 35) (ELit 16)) ->
     nth 11 regs_out (ELit 0) = EVar 40 ->
     nth 12 regs_out (ELit 0) = EMd M_MUL (ELit 8) (EVar 34) -> nth 18 regs_out (ELit 0) = EVar 36 -> nth 19 regs_out (ELit 0) = EVar 34 ->
     nth 9 regs_out (ELit 0) = EVar 40 ->
     mem_grows M M' ->
     (forall x, In x KS2 -> getr R' (reg x) = getr R (reg x))
     /\ getr R' (reg 1) = Z_to_bv 64 RET2 /\ getr R' (reg 2) = Z_to_bv 64 (sp - 48) /\ getr R' (reg 8) = Z_to_bv 64 o
     /\ getr R' (reg 10) = Z_to_bv 64 (if td then qd else o + 16) /\ getr R' (reg 11) = Z_to_bv 64 src
     /\ getr R' (reg 12) = Z_to_bv 64 (8 * n) /\ getr R' (reg 18) = Z_to_bv 64 o' /\ getr R' (reg 19) = Z_to_bv 64 n
     /\ getr R' (reg 9) = Z_to_bv 64 src
     /\ BGU.u8_at M' o (assign_flags f fb')
     /\ (forall a : word, ~ (o <= bv_unsigned a < o + 1) -> M' a = M a) /\ mem_grows M M').
  { intros fx' E' R' M' regs0 regs_out cells F0 KSL -> KOK INCL Hag Hregs Hfr -> Hcells Hin N1 N2 N8 N10 N11 N12 N18 N19 N9 Hgr.
    assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
    assert (A35: bv_unsigned (ev E' 35) = o) by (rewrite AG by lia; exact U35).
    assert (OUT: forall i k z, (0 < i < 32)%nat -> nth i regs_out (ELit 0) = EVar k -> (k < 48)%nat -> bv_unsigned (ev E k) = z -> getr R' (reg i) = Z_to_bv 64 z).
    { intros j k z Hj Hnth Hk Hz. rewrite (BGU.out_reg regs_out E' R' j Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' PD.regs0 regs_out 48 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. { rewrite (BGU.out_reg regs_out E' R' 1 Hregs) by lia. rewrite N1. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 2 Hregs) by lia. rewrite N2. cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U2), BGU.alu_add_lit. reflexivity. }
    split. { apply (OUT 8%nat 35%nat); [lia | exact N8 | lia | exact U35]. }
    split. { rewrite (BGU.out_reg regs_out E' R' 10 Hregs) by lia. rewrite N10. destruct td.
             cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U39.
             cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U35), BGU.alu_add_lit. reflexivity. }
    split. { apply (OUT 11%nat 40%nat); [lia | exact N11 | lia | exact U40]. }
    split. { rewrite (BGU.out_reg regs_out E' R' 12 Hregs) by lia. rewrite N12. cbn [edenot]. rewrite AG by lia. rewrite (BGU.word_of_unsigned _ _ U34), BGU.md_mul_lit. reflexivity. }
    split. { apply (OUT 18%nat 36%nat); [lia | exact N18 | lia | exact U36]. }
    split. { apply (OUT 19%nat 34%nat); [lia | exact N19 | lia | exact U34]. }
    split. { apply (OUT 9%nat 40%nat); [lia | exact N9 | lia | exact U40]. }
    split. { replace o with (o + 0) by lia. eapply (BIU.u8_of_KWord1_e E' M' 35 0 efl o (assign_flags f fb')). apply Hcells. exact Hin. exact A35.
             apply BGU.word_of_unsigned. rewrite (BGU.edenot_kept 48 E E') by (auto; reflexivity). rewrite (BL.zcomp_sound E efl zfl zfl_ok).
             cbn [BL.zden zfl]. unfold BL.uv. rewrite U33, U38. reflexivity. apply assign_flags_range; lia. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside. constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A35. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
    exact Hgr. }
  destruct td.
  - assert (HK: know_ok RSEGS E M PD.kn0).
    { unfold know_ok. cbv delta [PD.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply KQ; reflexivity] |]). apply Forall_nil. }
    destruct (PD.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PD.regs0 PD.regs_out PD.cells PD.F0 KS2 eq_refl KS2d_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells);
      try reflexivity. cbv delta [PD.cells]. cbn. tauto. exact Hgr.
  - assert (HK: know_ok RSEGS E M PI.kn0).
    { unfold know_ok. cbv delta [PI.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | apply KT; exact LT | apply KQ; reflexivity] |]). apply Forall_nil. }
    destruct (PI.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PI.regs0 PI.regs_out PI.cells PI.F0 KS2 eq_refl KS2i_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells);
      try reflexivity. cbv delta [PI.cells]. cbn. tauto. exact Hgr.
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
  destruct (ub0_copy_spec_memcpy fx M (Z_to_bv 64 dst) (Z_to_bv 64 src) (8 * Z.of_nat (length ws)) (L5K.limb_bytes ws) R (Z_to_bv 64 r)
              ltac:(lia) ltac:(rewrite LEN; lia)
              ltac:(rewrite LEN; apply L5K.rdn_of_limbs_at; [exact LIMBS | lia | lia])
              ltac:(rewrite LEN; replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
              ltac:(rewrite !BGU.unsigned_lit by lia; lia) ltac:(rewrite BGU.unsigned_lit by lia; lia) ltac:(rewrite BGU.unsigned_lit by lia; lia)
              (L5K.ret_ok_lit r RA) H1 H10 H11 H12) as (R3 & MS & KO & A10).
  exists R3. split. exact MS. split. { intros i Hi. apply (L5K.kept_ok_index R R3 i KO Hi). } exact A10.
Qed.
End SCFG_1.


End L5ASGPU.
