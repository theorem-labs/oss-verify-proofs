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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_L5ShrzU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5SHRZU.
Import L5CSU.
Module PZI := LibSegZ_lczu1i.
Module PZD := LibSegZ_lczu1d.
Module PZ2 := LibSegZ_lczu2.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition SHR : Z := 0x23624.
Definition RET1 : Z := 0x236ec.      (* [comment removed for export] *)
Definition RETI : Z := 0x23798.      (* [comment removed for export] *)

Definition KS1 : list nat := Eval vm_compute in (BGU.kept_list 56 PZD.regs0 PZD.regs_out).
Lemma KS1d_ok : BGU.kept_ok 56 PZD.regs0 PZD.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS1i_ok : BGU.kept_ok 56 PZI.regs0 PZI.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BGU.kept_list 56 PZ2.regs0 PZ2.regs_out).
Lemma KS2_ok : BGU.kept_ok 56 PZ2.regs0 PZ2.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.

Definition z32 : BL.za := Eval vm_compute in (BL.zc (ELit 32)).
Definition z80 : BL.za := Eval vm_compute in (BL.zc (ELit 80)).
Lemma z32_ok : BL.zcomp (ELit 32) = Some z32. Proof. vm_compute. reflexivity. Qed.
Lemma z80_ok : BL.zcomp (ELit 80) = Some z80. Proof. vm_compute. reflexivity. Qed.

Lemma ret_23694 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (BDU.ret_23704 fx R M r H1 Hr He). Qed.

Lemma land1_of_bit0 fb (b : bool) : 0 <= fb -> Z.testbit fb 0 = b -> Z.land fb 1 = (if b then 1 else 0).
Proof.
  intros Hfb Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0]. { rewrite Hb. destruct b; reflexivity. }
  replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r.
  destruct b. symmetry; apply Z.bits_above_log2; cbn; lia. rewrite Z.bits_0. reflexivity.
Qed.

(* [comment removed for export] *)
Definition SVL : list (Z * nat) := [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat); (-32, 18%nat); (-40, 19%nat); (-48, 20%nat); (-56, 21%nat); (-64, 22%nat)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run (dyn : bool) fx R M (o sp fb k c24 : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 k -> 0 <= k <= 63 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 80 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 80) 80 ->
  4096 <= o -> sp <= o -> o + 32 <= 2 ^ 47 -> o mod 8 = 0 ->
  BGU.u8_at M o fb -> 0 <= fb < 256 -> Z.testbit fb 0 = dyn -> BGU.u64_at M (o + 8) 0 -> BGU.u64_at M (o + 24) c24 -> 0 <= c24 < 2 ^ 64 ->
  exists fx' R1 M1, msteps RSEGS (st fx R SHR M) (st fx' R1 RESIZE M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 80)
    /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 10) = Z_to_bv 64 o /\ getr R1 (reg 11) = Z_to_bv 64 0
    /\ BGU.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ BGU.u64_at M1 (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BGU.u64_at M1 (sp - 32) (bv_unsigned (getr R (reg 18)))
    /\ BGU.u64_at M1 (sp - 40) (bv_unsigned (getr R (reg 19))) /\ BGU.u64_at M1 (sp - 48) (bv_unsigned (getr R (reg 20)))
    /\ BGU.u64_at M1 (sp - 56) (bv_unsigned (getr R (reg 21))) /\ BGU.u64_at M1 (sp - 64) (bv_unsigned (getr R (reg 22)))
    /\ (forall a : word, ~ (sp - 80 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 H11 Hk H2 A16 SLO SHI WR Olo Oge Ohi Ao O0 Hfb Bfb O8 O24 Hc.
  set (Vf := fun j : nat => match j with 33%nat => Z_to_bv 64 o | 34%nat => Z_to_bv 64 k | 35%nat => Z_to_bv 64 0 | 36%nat => Z_to_bv 64 fb
                                         | 37%nat => Z_to_bv 64 c24 | 41%nat => Z_to_bv 64 c24 | _ => getr R (reg j) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U34: bv_unsigned (ev E 34) = k) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U35: bv_unsigned (ev E 35) = 0) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U36: bv_unsigned (ev E 36) = fb) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U37: bv_unsigned (ev E 37) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (KC: forall K, In K
    [KRange (EVar 2) 140735332483152 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-80)) (ELit 80);
     KRange (EVar 33) 4096 140737488355296; KAlign (EVar 33) 8;
     KDisj (SA (EVar 2) (-80)) (ELit 80) (SA (EVar 33) 0) (ELit 32);
     KWord (SA (EVar 33) 0) 1 (EVar 36); KRange (EVar 36) 0 255; KWord (SA (EVar 33) 8) 8 (EVar 35); KRange (EVar 35) 0 0; KRange (EVar 34) 0 63]
     -> kentry_ok RSEGS E M K).
  { intros K HK. cbn in HK.
    repeat (destruct HK as [<-|HK]); try contradiction.
    - eapply BGU.kentry_KRange_var. exact U2. lia.
    - eapply BGU.kentry_KAlign_var. exact U2. lia. lia.
    - eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR.
    - eapply BGU.kentry_KRange_var. exact U33. lia.
    - eapply BGU.kentry_KAlign_var. exact U33. lia. lia.
    - eapply (BGU.kentry_KDisj_z E M 2 (-80) (ELit 80) z80 80 33 0 (ELit 32) z32 32 sp o U2 U33 z80_ok eq_refl z32_ok eq_refl). lia.
    - eapply (BDU.kentry_KWord1_var E M 33 0 36 o fb U33 U36). lia. lia. lia. rewrite Z.add_0_r. exact O0.
    - eapply BGU.kentry_KRange_var. exact U36. lia.
    - eapply BGU.kentry_KWord_var. exact U33. exact U35. lia. lia. exact O8.
    - eapply BGU.kentry_KRange_var. exact U35. lia.
    - eapply BGU.kentry_KRange_var. exact U34. lia. }
  assert (KO: kentry_ok RSEGS E M (KRange (EAlu ALU_AND (EVar 36) (ELit 1)) (if dyn then 1 else 0) (if dyn then 1 else 0))).
  { cbn [kentry_ok edenot]. rewrite BDU.and_lit_val by lia. rewrite U36, (land1_of_bit0 fb dyn) by (lia || exact Bfb). destruct dyn; lia. }
  assert (K24: forall j, (j = 37%nat \/ j = 41%nat) -> kentry_ok RSEGS E M (KWord (SA (EVar 33) 24) 8 (EVar j))).
  { intros j [-> | ->]. eapply BGU.kentry_KWord_var. exact U33. exact U37. lia. lia. exact O24.
    eapply BGU.kentry_KWord_var. exact U33. exact U41. lia. lia. exact O24. }
  assert (HRX: forall regs0, regs0 = PZD.regs0 -> regs_ok E regs0 R).
  { intros regs0 ->. apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PZD.regs0 nth edenot ev E Vf]. repeat split; try reflexivity. exact H10. exact H11. }
  assert (SAME: PZI.regs0 = PZD.regs0) by reflexivity.
  assert (POST: forall (fx' : FPState) E' (R' : bvmap 5 word) (M' : word -> option byte) (regs0 regs_out : list expr) (cells : list kentry) (F0 : list SGP.region) (KSL : list nat),
     regs0 = PZD.regs0 -> BGU.kept_ok 56 regs0 regs_out KSL = true -> incl KS1 KSL ->
     env_agree 56 E E' ->
     (forall i e, In (i, e) (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (reg i) = edenot E' e) ->
     (forall a : word, SGP.outside E' F0 a -> M' a = M a) -> F0 = [(EVar 2, -80, ELit 80)] ->
     (forall K, In K cells -> kentry_ok RSEGS E' M' K) ->
     (forall off j, In (off, j) SVL -> In (KWord (SA (EVar 2) off) 8 (EVar j)) cells) ->
     nth 1 regs_out (ELit 0) = ELit 145132 -> nth 2 regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-80)) ->
     nth 8 regs_out (ELit 0) = EVar 33 -> nth 10 regs_out (ELit 0) = EVar 33 -> nth 11 regs_out (ELit 0) = ELit 0 ->
     mem_grows M M' ->
     (forall x, In x KS1 -> getr R' (reg x) = getr R (reg x))
     /\ getr R' (reg 1) = Z_to_bv 64 RET1 /\ getr R' (reg 2) = Z_to_bv 64 (sp - 80)
     /\ getr R' (reg 8) = Z_to_bv 64 o /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 11) = Z_to_bv 64 0
     /\ BGU.u64_at M' (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BGU.u64_at M' (sp - 16) (bv_unsigned (getr R (reg 8)))
     /\ BGU.u64_at M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ BGU.u64_at M' (sp - 32) (bv_unsigned (getr R (reg 18)))
     /\ BGU.u64_at M' (sp - 40) (bv_unsigned (getr R (reg 19))) /\ BGU.u64_at M' (sp - 48) (bv_unsigned (getr R (reg 20)))
     /\ BGU.u64_at M' (sp - 56) (bv_unsigned (getr R (reg 21))) /\ BGU.u64_at M' (sp - 64) (bv_unsigned (getr R (reg 22)))
     /\ (forall a : word, ~ (sp - 80 <= bv_unsigned a < sp) -> M' a = M a) /\ mem_grows M M').
  { intros fx' E' R' M' regs0 regs_out cells F0 KSL -> KOK INCL Hag Hregs Hfr -> Hcells SAVEDIN N1 N2 N8 N10 N11 Hgr.
    assert (AG: forall j, (j < 56)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
    assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
    assert (CELL: forall off j, In (off, j) SVL -> (j < 32)%nat -> Vf j = getr R (reg j) -> BGU.u64_at M' (sp + off) (bv_unsigned (getr R (reg j)))).
    { intros off j Hin Hj HV. eapply (BGU.u64_of_KWord E' M' 2 off). apply Hcells. apply SAVEDIN. exact Hin. exact A2.
      cbn [edenot]. rewrite AG by lia. change (ev E j) with (Vf j). rewrite HV. reflexivity. }
    split. { intros j Hj. apply (BGU.kept_regs E E' R R' PZD.regs0 regs_out 56 KSL KOK (HRX _ eq_refl) Hag Hregs j (INCL j Hj)). }
    split. { rewrite (BGU.out_reg regs_out E' R' 1 Hregs) by lia. rewrite N1. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 2 Hregs) by lia. rewrite N2. cbn [edenot]. rewrite (BGU.word_of_unsigned _ _ A2), BGU.alu_add_lit. reflexivity. }
    split. { rewrite (BGU.out_reg regs_out E' R' 8 Hregs) by lia. rewrite N8. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U33. }
    split. { rewrite (BGU.out_reg regs_out E' R' 10 Hregs) by lia. rewrite N10. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact U33. }
    split. { rewrite (BGU.out_reg regs_out E' R' 11 Hregs) by lia. rewrite N11. reflexivity. }
    split. { replace (sp - 8) with (sp + -8) by lia. apply CELL; [unfold SVL; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 16) with (sp + -16) by lia. apply CELL; [unfold SVL; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 24) with (sp + -24) by lia. apply CELL; [unfold SVL; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 32) with (sp + -32) by lia. apply CELL; [unfold SVL; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 40) with (sp + -40) by lia. apply CELL; [unfold SVL; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 48) with (sp + -48) by lia. apply CELL; [unfold SVL; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 56) with (sp + -56) by lia. apply CELL; [unfold SVL; cbn; tauto | lia | reflexivity]. }
    split. { replace (sp - 64) with (sp + -64) by lia. apply CELL; [unfold SVL; cbn; tauto | lia | reflexivity]. }
    split. { intros a Ha. apply Hfr. unfold SGP.outside.
             constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BGU.unsigned_lit by lia. lia. } constructor. }
    exact Hgr. }
  destruct dyn.
  - assert (HK: know_ok RSEGS E M PZD.kn0).
    { unfold know_ok. cbv delta [PZD.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | exact KO | apply K24; tauto] |]). apply Forall_nil. }
    destruct (PZD.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PZD.regs0 PZD.regs_out PZD.cells PZD.F0 KS1 eq_refl KS1d_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells
                ltac:(intros off j Hin; unfold SVL in Hin; cbn in Hin; decompose [or] Hin; try contradiction;
                      match goal with H : (_, _) = (off, j) |- _ => injection H; intros <- <- end; cbv delta [PZD.cells]; cbn; tauto)
                eq_refl eq_refl eq_refl eq_refl eq_refl Hgr).
  - assert (HK: know_ok RSEGS E M PZI.kn0).
    { unfold know_ok. cbv delta [PZI.kn0]. repeat (apply Forall_cons; [first [apply KC; cbn; tauto | exact KO | apply K24; tauto] |]). apply Forall_nil. }
    destruct (PZI.seg_sound_ax fx E R M (HRX _ eq_refl) HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
    apply BDU.nth_error_single in Hnth. subst ps0.
    exists fx', R', M'. split. exact Hms.
    apply (POST fx' E' R' M' PZI.regs0 PZI.regs_out PZI.cells PZI.F0 KS1 eq_refl KS1i_ok ltac:(intros x Hx; exact Hx) Hag Hregs Hfr eq_refl Hcells
                ltac:(intros off j Hin; unfold SVL in Hin; cbn in Hin; decompose [or] Hin; try contradiction;
                      match goal with H : (_, _) = (off, j) |- _ => injection H; intros <- <- end; cbv delta [PZI.cells]; cbn; tauto)
                eq_refl eq_refl eq_refl eq_refl eq_refl Hgr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2_run fx R M (o sp c8 c16 c24 c32 c40 c48 c56 c64 r : Z) :
  getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 2) = Z_to_bv 64 (sp - 80) ->
  BGU.u64_at M (sp - 8) c8 -> BGU.u64_at M (sp - 16) c16 -> BGU.u64_at M (sp - 24) c24 -> BGU.u64_at M (sp - 32) c32 -> BGU.u64_at M (sp - 40) c40 ->
  BGU.u64_at M (sp - 48) c48 -> BGU.u64_at M (sp - 56) c56 -> BGU.u64_at M (sp - 64) c64 ->
  0 <= c8 < 2 ^ 64 -> 0 <= c16 < 2 ^ 64 -> 0 <= c24 < 2 ^ 64 -> 0 <= c32 < 2 ^ 64 -> 0 <= c40 < 2 ^ 64 ->
  0 <= c48 < 2 ^ 64 -> 0 <= c56 < 2 ^ 64 -> 0 <= c64 < 2 ^ 64 ->
  0 <= o < 2 ^ 64 -> sp mod 16 = 0 -> 0x7fff7f800000 + 80 <= sp -> sp <= 2 ^ 47 -> BGU.writable M (sp - 80) 80 ->
  c8 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 r M3)
    /\ (forall x, In x KS2 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 c8 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 c16 /\ getr R3 (reg 9) = Z_to_bv 64 c24
    /\ getr R3 (reg 18) = Z_to_bv 64 c32 /\ getr R3 (reg 19) = Z_to_bv 64 c40 /\ getr R3 (reg 20) = Z_to_bv 64 c48
    /\ getr R3 (reg 21) = Z_to_bv 64 c56 /\ getr R3 (reg 22) = Z_to_bv 64 c64 /\ getr R3 (reg 10) = Z_to_bv 64 o
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H8 H2 C8 C16 C24 C32 C40 C48 C56 C64 R8 R16 R24 R32 R40 R48 R56 R64 Ho A16 SLO SHI WR Er [Hr He].
  set (Vf := fun j : nat => match j with 2%nat => Z_to_bv 64 sp | 33%nat => Z_to_bv 64 o
                                         | 43%nat => Z_to_bv 64 c8 | 44%nat => Z_to_bv 64 c16 | 47%nat => Z_to_bv 64 c24
                                         | 48%nat => Z_to_bv 64 c32 | 49%nat => Z_to_bv 64 c40 | 50%nat => Z_to_bv 64 c48
                                         | 51%nat => Z_to_bv 64 c56 | 52%nat => Z_to_bv 64 c64 | _ => getr R (reg j) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U33: bv_unsigned (ev E 33) = o) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U43: bv_unsigned (ev E 43) = c8) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U44: bv_unsigned (ev E 44) = c16) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U47: bv_unsigned (ev E 47) = c24) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U48: bv_unsigned (ev E 48) = c32) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U49: bv_unsigned (ev E 49) = c40) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U50: bv_unsigned (ev E 50) = c48) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U51: bv_unsigned (ev E 51) = c56) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (U52: bv_unsigned (ev E 52) = c64) by (cbv [E ev Vf]; apply BGU.unsigned_lit; lia).
  assert (HR: regs_ok E PZ2.regs0 R).
  { apply BGU.regs_ok_of_slots. reflexivity. cbv [BGU.slots tl PZ2.regs0 nth edenot ev E Vf]. repeat split; try reflexivity; try assumption. rewrite BGU.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M PZ2.kn0).
  { unfold know_ok. cbv delta [PZ2.kn0].
    apply Forall_cons. { eapply BGU.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BGU.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BGU.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U43. lia. lia. exact C8. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U44. lia. lia. exact C16. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U47. lia. lia. exact C24. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U48. lia. lia. exact C32. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U49. lia. lia. exact C40. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U50. lia. lia. exact C48. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U51. lia. lia. exact C56. }
    apply Forall_cons. { eapply BGU.kentry_KWord_var. exact U2. exact U52. lia. lia. exact C64. }
    apply Forall_nil. }
  destruct (PZ2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & HX0 & Hrok & Hfr & Hcells & Hgr).
  apply BDU.nth_error_single in Hnth. subst ps0. change PZ2.NX0 with 56%nat in Hag.
  assert (AG: forall j, (j < 56)%nat -> ev E' j = ev E j) by (intros j Hj; symmetry; apply (proj1 Hag j Hj)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
  assert (OUT: forall i j z, (0 < i < 32)%nat -> nth i PZ2.regs_out (ELit 0) = EVar j -> (j < 56)%nat -> bv_unsigned (ev E j) = z -> getr R' (reg i) = Z_to_bv 64 z).
  { intros i' j z Hi Hnth Hj Hz. rewrite (BGU.out_reg PZ2.regs_out E' R' i' Hregs) by lia. rewrite Hnth. cbn [edenot]. rewrite AG by lia. apply BGU.word_of_unsigned. exact Hz. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 c8). { apply (OUT 1%nat 43%nat); [lia | reflexivity | lia | exact U43]. }
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc PZ2.ps0) with RETI. apply ret_23694. rewrite R1. subst c8. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BGU.kept_regs E E' R R' PZ2.regs0 PZ2.regs_out 56 KS2 KS2_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { apply (OUT 2%nat 2%nat); [lia | reflexivity | lia | exact U2]. }
  split. { apply (OUT 8%nat 44%nat); [lia | reflexivity | lia | exact U44]. }
  split. { apply (OUT 9%nat 47%nat); [lia | reflexivity | lia | exact U47]. }
  split. { apply (OUT 18%nat 48%nat); [lia | reflexivity | lia | exact U48]. }
  split. { apply (OUT 19%nat 49%nat); [lia | reflexivity | lia | exact U49]. }
  split. { apply (OUT 20%nat 50%nat); [lia | reflexivity | lia | exact U50]. }
  split. { apply (OUT 21%nat 51%nat); [lia | reflexivity | lia | exact U51]. }
  split. { apply (OUT 22%nat 52%nat); [lia | reflexivity | lia | exact U52]. }
  split. { apply (OUT 10%nat 33%nat); [lia | reflexivity | lia | exact U33]. }
  split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis RSZ : resize_spec L HI.

Theorem shrz_ok : L5DSU.shrz_spec L HI.
Proof.
  unfold L5DSU.shrz_spec. intros fx R M model K LB cr X k sp r fb sto HH MOK HK0 H10 H11 Hk H1 RA H2 H4 STK OB DYN Ao Olo Ohi WO KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF).
  unfold L5DSU.SHRZ_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  destruct DYN as (cap & q & Hst & BLK). subst sto.
  pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST.
  destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Aq & Qlo & Qhi & HAP).
  assert (WR48: BGU.writable M (sp - 80) 80).
  { change (L5.writable RSEGS M (sp - 80) 80). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
  pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as RG9. pose proof (bv_unsigned_in_range _ (getr R (reg 18))) as RG18.
  pose proof (bv_unsigned_in_range _ (getr R (reg 19))) as RG19. pose proof (bv_unsigned_in_range _ (getr R (reg 20))) as RG20.
  pose proof (bv_unsigned_in_range _ (getr R (reg 21))) as RG21. pose proof (bv_unsigned_in_range _ (getr R (reg 22))) as RG22.
  change (bv_modulus 64) with (2 ^ 64) in RG1, RG8, RG9, RG18, RG19, RG20, RG21, RG22.
  assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BGU.unsigned_lit. lia. }
  destruct (p1_run true fx R M X sp fb k q H10 H11 Hk H2 A16 ltac:(lia) ltac:(lia) WR48 ltac:(lia) Olo ltac:(lia) Ao O0 Hfb B0 O8 O24 ltac:(lia))
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_10 & R1_11 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & FR1 & GR1).
  assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR1. rewrite BGU.unsigned_lit by lia. exact Hna. }
  unfold L5DSU.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (RSZ fx1 R1 M1 model K LB cr X (sp - 80) RET1 0%nat (L5.BO fb 0 (L5.BDyn cap q)) []).
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 80)) as [Hlt|Hge]. left. apply FR1z; lia.
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1z; lia. exact GR1.
  - exact MOK.
  - exact HK0.
  - exact R1_10.
  - exact R1_11.
  - cbn. lia.
  - cbn [L5.bo_dyn L5.bo_cap L5.bo_fb L5.bo_st]. intros _. lia.
  - intros H3 _. exfalso. lia.
  - exact R1_1.
  - split. unfold RET1. lia. reflexivity.
  - exact R1_2.
  - rewrite <- H4. apply (K1 4%nat). apply L5K.In_of_mem. reflexivity.
  - split. { replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
    intros i Hi. apply GR1. replace (sp - 80 - (64 + (48 + (64 + (16 + 8224)))) + i) with (sp - (80 + (64 + (48 + (64 + (16 + 8224))))) + i) by lia. apply DEF. lia.
  - eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact OB.
  - split. reflexivity. split. constructor. cbn [L5.bo_st]. apply L5C.limbs_at_nil.
  - exact Ao.
  - lia.
  - exact Ohi.
  - change (L5.writable RSEGS M1 X 32). eapply L5.writable_grows. exact GR1. exact WO.
  - cbn [L5.bo_st]. intros c' q' Hcq. injection Hcq. intros <- <-. exact BLK.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB' cr' POST MBV HH2.
    destruct g as [|A cg].
    2:{ destruct POST as (_ & _ & H3 & _). exfalso. lia. }
    destruct POST as (RP & _ & ELB & ECR & (st' & OB2 & OL2 & MST) & HP). subst LB' cr'.
    cbn [L5.bo_st] in MST. destruct st' as [v0 v1|cap' q']. contradiction. destruct MST as [-> ->].
    destruct HP as (PRES & SDEF & CDEF). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES, SDEF, CDEF.
    assert (CL: forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply PRES. apply (L5C.kept_stack L LB (sp - 80) (64 + (48 + (64 + (16 + 8224)))) _). lia. lia. lia.
      rewrite (ly_errno L LY). lia. lia.
      apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. lia.
      apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd L5.bo_data L5.bo_len L5.bo_st]. lia. apply L5C.outside_nil. }
    assert (T1: forall a v, sp - 80 <= a -> a + 8 <= sp -> BGU.u64_at M1 a v -> BGU.u64_at M2 a v).
    { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact Hu. }
    assert (WR2 : BGU.writable M2 (sp - 80) 80).
    { change (L5.writable RSEGS M2 (sp - 80) 80). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia.
      eapply L5.writable_grows. exact GR1. exact WR48. }
    destruct (p2_run fx2 R2 M2 X sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9)))
                (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19))) (bv_unsigned (getr R (reg 20)))
                (bv_unsigned (getr R (reg 21))) (bv_unsigned (getr R (reg 22))) r
                ltac:(rewrite <- L5K.rl8, (RP 8%bv ltac:(cbn; tauto)), L5K.rl8; exact R1_8)
                ltac:(rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2; exact R1_2)
                (T1 (sp - 8) _ ltac:(lia) ltac:(lia) C8) (T1 (sp - 16) _ ltac:(lia) ltac:(lia) C16) (T1 (sp - 24) _ ltac:(lia) ltac:(lia) C24)
                (T1 (sp - 32) _ ltac:(lia) ltac:(lia) C32) (T1 (sp - 40) _ ltac:(lia) ltac:(lia) C40) (T1 (sp - 48) _ ltac:(lia) ltac:(lia) C48)
                (T1 (sp - 56) _ ltac:(lia) ltac:(lia) C56) (T1 (sp - 64) _ ltac:(lia) ltac:(lia) C64)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 E1 RA)
      as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & R3_19 & R3_20 & R3_21 & R3_22 & R3_10 & MF3 & GR3).
    eapply (L5.cps_of_msteps RSEGS). { rewrite (L5C.halted_but_vm _ _ MBV). exact Mh. } { rewrite (L5C.lazy_but_vm _ _ MBV). exact Ml. }
    exact MS3.
    apply (KONT fx3 R3 M3 model2).
    + (* [comment removed for export] *)
      apply L5K.regs_preserved_by_index. intros i Hi.
      cbn in Hi. destruct Hi as [<-|Hi]. { rewrite R3_2, <- H2, L5K.rl2. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_8. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_9. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_18. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_19. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_20. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_21. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite R3_22. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      assert (G: forall j, In j [23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
      { intros j Hj.
        assert (M2j: In j KS2) by (pose proof Hj as H'; L5K.inlist H').
        assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
        assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
        rewrite (K3 j M2j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
      apply G. L5K.inlist Hi.
    + exact R3_10.
    + eapply (L5C.big_at_agree RSEGS M2 M3). intros i Hi. apply MF3. lia. lia. exact OB2.
    + (* [comment removed for export] *)
      unfold L5DSU.SHRZ_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK.
      split.
      * intros a (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
        rewrite (MF3 (Z_to_bv 64 a)).
        assert (FA: ~ (sp - 80 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)). { intros Hna. apply FR1z. lia. exact Hna. }
        destruct CA as [IB|[[S1 S2]|IM]].
        -- rewrite PRES. apply FA.
           { destruct IB as (b & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). lia. }
           split. lia. split. left. exact IB. split. exact NE.
           apply L5C.outside_cons. exact NW. apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd L5.bo_data L5.bo_len L5.bo_st]. lia. apply L5C.outside_nil.
        -- rewrite PRES. apply FA. lia.
           split. lia. split. right. left. split. exact S1. lia. split. exact NE.
           apply L5C.outside_cons. exact NW. apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd L5.bo_data L5.bo_len L5.bo_st]. lia. apply L5C.outside_nil.
        -- rewrite PRES. apply FA. rewrite (ly_img_hi L LY) in IM. lia.
           split. lia. split. right. right. exact IM. split. exact NE.
           apply L5C.outside_cons. exact NW. apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd L5.bo_data L5.bo_len L5.bo_st]. lia. apply L5C.outside_nil.
      * split.
        { intros i Hi. rewrite (MF3 (Z_to_bv 64 _)).
          destruct (Z_lt_le_dec (sp - (80 + (64 + (48 + (64 + (16 + 8224))))) + i) (sp - 80)) as [Hlt|Hge].
          -- replace (sp - (80 + (64 + (48 + (64 + (16 + 8224))))) + i) with (sp - 80 - (64 + (48 + (64 + (16 + 8224)))) + (i)) by lia. apply SDEF. lia.
          -- rewrite CL by lia. apply GR1. apply DEF. lia. }
        intros a Ha CA NE D0. rewrite (MF3 (Z_to_bv 64 a)). apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE.
        apply GR1. exact D0.
    + exact MBV.
    + eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
      intros a Ha. left. apply MF3. exact GR3.
Qed.

End WithHeap.
End SCFG_1.
End L5SHRZU.
