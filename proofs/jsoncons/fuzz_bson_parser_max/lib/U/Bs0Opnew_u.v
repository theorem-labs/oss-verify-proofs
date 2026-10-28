(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0_code_r59000_59c90_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require Import LibSegBs_lcnew1_u LibSegBs_lcnew2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5NEW.

(* [comment removed for export] *)
Module L5CS.
Abbreviation RSEGS := PMS.RSEGS.
Definition HEAP_STACK : Z := 8224.
Definition OPNEW : Z := 0xb03b8.
Definition OPNEW_SCR : Z := 16 + HEAP_STACK.
Definition OPDEL : Z := 0x5671c.            (* [comment removed for export] *)
Definition OPDEL_SIZED : Z := 0x56720.      (* [comment removed for export] *)
Definition OPDEL_SCR : Z := HEAP_STACK.
Definition TP : Z := 0xc9fc0.
End L5CS.
Lemma nth_error_single {A} (x y : A) i : nth_error [x] i = Some y -> y = x.
Proof. destruct i; simpl. congruence. destruct i; discriminate. Qed.
Import L5CS.
Module P1 := LibSegBs_lcnew1_u.
Module P2 := LibSegBs_lcnew2_u.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition MALLOC : Z := 0x9cdd4.
Definition RET1 : Z := 0xb03d4.      (* [comment removed for export] *)
Definition RETI : Z := 0xb03fc.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KS1 : list nat := Eval vm_compute in (BG.kept_list 48 P1.regs0 P1.regs_out).
Lemma KS1_ok : BG.kept_ok 48 P1.regs0 P1.regs_out KS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BG.kept_list 48 P2.regs0 P2.regs_out).
Lemma KS2_ok : BG.kept_ok 48 P2.regs0 P2.regs_out KS2 = true. Proof. vm_compute. reflexivity. Qed.

Lemma kn0_1 : P1.kn0 = [KRange (EVar 2) 140735332483088 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-16)) (ELit 16); KRange (EVar 10) 1 134217728].
Proof. vm_compute. reflexivity. Qed.
Lemma cells_1 : P1.cells = [KWord (SA (EVar 2) (-16)) 8 (EVar 8); KWord (SA (EVar 2) (-8)) 8 (EVar 1)].
Proof. vm_compute. reflexivity. Qed.
Lemma r1_1 : nth 1 P1.regs_out (ELit 0) = ELit 721876. Proof. vm_compute. reflexivity. Qed.
Lemma r2_1 : nth 2 P1.regs_out (ELit 0) = EAlu ALU_ADD (EVar 2) (ELit (-16)). Proof. vm_compute. reflexivity. Qed.
Lemma r8_1 : nth 8 P1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.
Lemma r10_1 : nth 10 P1.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.

Lemma kn0_2 : P2.kn0 = [KRange (EVar 2) 140735332483088 140737488355328; KAlign (EVar 2) 16; KWr (SA (EVar 2) (-16)) (ELit 16);
   KRange (EVar 10) 1 18446744073709551615; KWord (SA (EVar 2) (-8)) 8 (EVar 40); KWord (SA (EVar 2) (-16)) 8 (EVar 41)].
Proof. vm_compute. reflexivity. Qed.
Lemma r1_2 : nth 1 P2.regs_out (ELit 0) = EVar 40. Proof. vm_compute. reflexivity. Qed.
Lemma r2_2 : nth 2 P2.regs_out (ELit 0) = EVar 2. Proof. vm_compute. reflexivity. Qed.
Lemma r8_2 : nth 8 P2.regs_out (ELit 0) = EVar 41. Proof. vm_compute. reflexivity. Qed.
Lemma r10_2 : nth 10 P2.regs_out (ELit 0) = EVar 10. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p1_run fx R M (n sp : Z) :
  getr R (reg 10) = Z_to_bv 64 n -> 1 <= n <= 2 ^ 27 ->
  getr R (reg 2) = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0x7fff7f800000 + 16 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 16) 16 ->
  exists fx' R1 M1, msteps RSEGS (st fx R OPNEW M) (st fx' R1 MALLOC M1)
    /\ (forall x, In x KS1 -> getr R1 (reg x) = getr R (reg x))
    /\ getr R1 (reg 1) = Z_to_bv 64 RET1 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 16) /\ getr R1 (reg 8) = Z_to_bv 64 n /\ getr R1 (reg 10) = Z_to_bv 64 n
    /\ BG.u64_at M1 (sp - 8) (bv_unsigned (getr R (reg 1))) /\ BG.u64_at M1 (sp - 16) (bv_unsigned (getr R (reg 8)))
    /\ (forall a : word, ~ (sp - 16 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1.
Proof.
  intros H10 Hn H2 A16 SLO SHI WR.
  set (Vf := fun k : nat => getr R (reg k)).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BG.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = n) by (cbv [E ev Vf]; rewrite H10; apply BG.unsigned_lit; lia).
  assert (HR: regs_ok E P1.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl P1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
  assert (HK: know_ok RSEGS E M P1.kn0).
  { unfold know_ok. rewrite kn0_1.
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U10. lia. }
    apply Forall_nil. }
  destruct (P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply nth_error_single in Hnth. subst ps0. change P1.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs E E' R R' P1.regs0 P1.regs_out 48 KS1 KS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 1 Hregs) by lia. rewrite r1_1. reflexivity. }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 2 Hregs) by lia. rewrite r2_1. cbn [edenot].
           rewrite (BG.word_of_unsigned _ _ A2), BG.alu_add_lit. reflexivity. }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 8 Hregs) by lia. rewrite r8_1. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U10. }
  split. { rewrite (BG.out_reg P1.regs_out E' R' 10 Hregs) by lia. rewrite r10_1. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U10. }
  split. { eapply (BG.u64_of_KWord E' M' 2 (-8)). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. rewrite cells_1. right; left; reflexivity. exact A2.
           cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { eapply (BG.u64_of_KWord E' M' 2 (-16)). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. rewrite cells_1. left; reflexivity. exact A2.
           cbn [edenot]. rewrite AG by lia. reflexivity. }
  split. { intros a Ha. apply Hfr. unfold SGP.outside. change P1.F0 with [(EVar 2, -16, ELit 16)].
           constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BG.unsigned_lit by lia. lia. } constructor. }
  exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_aed78 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RETI M) (st fx R r M).
Proof. intros H1 Hr He. apply (PMK.ret_to RSEGS fx R M RETI W_aedc8 r F_aedc8 eq_refl D_aedc8 H1 Hr He). Qed.

Lemma p2_run fx R M (A sp ra0 s00 r : Z) :
  getr R (reg 10) = Z_to_bv 64 A -> 1 <= A < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (sp - 16) -> sp mod 16 = 0 -> 0x7fff7f800000 + 16 <= sp -> sp <= 2 ^ 47 -> BG.writable M (sp - 16) 16 ->
  BG.u64_at M (sp - 8) ra0 -> BG.u64_at M (sp - 16) s00 -> 0 <= ra0 < 2 ^ 64 -> 0 <= s00 < 2 ^ 64 ->
  ra0 = r -> L5.ra_ok r ->
  exists fx' R3 M3, msteps RSEGS (st fx R RET1 M) (st fx' R3 r M3)
    /\ (forall x, In x KS2 -> getr R3 (reg x) = getr R (reg x))
    /\ getr R3 (reg 1) = Z_to_bv 64 ra0 /\ getr R3 (reg 2) = Z_to_bv 64 sp /\ getr R3 (reg 8) = Z_to_bv 64 s00 /\ getr R3 (reg 10) = Z_to_bv 64 A
    /\ (forall a : word, M3 a = M a) /\ mem_grows M M3.
Proof.
  intros H10 HA H2 A16 SLO SHI WR C8 C16 Hra0 Hs00 Er [Hr He].
  set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 40%nat => Z_to_bv 64 ra0 | 41%nat => Z_to_bv 64 s00 | _ => getr R (reg k) end).
  set (E := Env Vf (fun _ => [])).
  assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U10: bv_unsigned (ev E 10) = A) by (cbv [E ev Vf]; rewrite H10; apply BG.unsigned_lit; lia).
  assert (U40: bv_unsigned (ev E 40) = ra0) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (U41: bv_unsigned (ev E 41) = s00) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
  assert (HR: regs_ok E P2.regs0 R).
  { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P2.regs0 nth edenot ev E Vf]. repeat split; try reflexivity.
    rewrite BG.alu_add_lit. exact H2. }
  assert (HK: know_ok RSEGS E M P2.kn0).
  { unfold know_ok. rewrite kn0_2.
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
    apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
    apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
    apply Forall_cons. { eapply BG.kentry_KRange_var. exact U10. lia. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U40. lia. lia. exact C8. }
    apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C16. }
    apply Forall_nil. }
  destruct (P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply nth_error_single in Hnth. subst ps0. change P2.NX0 with 48%nat in Hag.
  assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
  assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
  assert (R1: getr R' (reg 1) = Z_to_bv 64 ra0).
  { rewrite (BG.out_reg P2.regs_out E' R' 1 Hregs) by lia. rewrite r1_2. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U40. }
  exists fx', R', M'. split.
  { eapply msteps_trans. exact Hms. change (SR.ps_pc P2.ps0) with RETI. apply ret_aed78. rewrite R1. subst ra0. reflexivity. exact Hr. exact He. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' P2.regs0 P2.regs_out 48 KS2 KS2_ok HR Hag Hregs j Hj). }
  split. exact R1.
  split. { rewrite (BG.out_reg P2.regs_out E' R' 2 Hregs) by lia. rewrite r2_2. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U2. }
  split. { rewrite (BG.out_reg P2.regs_out E' R' 8 Hregs) by lia. rewrite r8_2. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U41. }
  split. { rewrite (BG.out_reg P2.regs_out E' R' 10 Hregs) by lia. rewrite r10_2. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U10. }
  split. exact MM. exact Hgr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem opnew_ok : PMS.opnew_spec L HI.
Proof.
  unfold PMS.opnew_spec, PMSP.opnew_spec. change (pa_opnew PMS.AD) with OPNEW. change PMSP.OPNEW_SCR with OPNEW_SCR. intros fx R M model K LB cr n sp r HH (Mh & Ml & Mm) HK0 H10 Hn CR H1 RA H2 H4 STK KONT.
  pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  assert (WR16: BG.writable M (sp - 16) 16).
  { change (L5.writable RSEGS M (sp - 16) 16). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct (p1_run fx R M n sp H10 ltac:(lia) H2 A16 ltac:(lia) ltac:(lia) WR16)
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_10 & C8 & C16 & FR1 & GR1).
  unfold PMSP.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  pose proof (hio_malloc L SCFG HI HIok) as HM. unfold malloc_spec in HM. rewrite (PMS.ly_segs L LY), (PMS.ly_malloc L LY) in HM.
  change (Z_to_bv 64 MALLOC) with (Z_to_bv 64 0x9cdd4).
  eapply (HM fx1 R1 M1 model LB cr n K); clear HM.
  - (* [comment removed for export] *)
    eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH.
    + exact (PMS.ly_ro L LY).
    + rewrite (PMS.ly_img_hi L LY). lia.
    + lia.
    + intros a Ha. destruct (Z_lt_le_dec a (sp - 16)) as [Hlt|Hge]. left. apply FR1. rewrite BG.unsigned_lit by lia. lia.
      destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1. rewrite BG.unsigned_lit by lia. lia.
    + exact GR1.
  - exact Mh. - exact Ml. - exact Mm.
  - exact R1_10.
  - lia.
  - exact CR.
  - rewrite (PMS.ly_tp L LY). rewrite <- H4. apply (K1 4%nat). cbn; tauto.
  - rewrite L5K.rl1, R1_1. apply L5K.ret_ok_lit. split. unfold RET1. lia. reflexivity.
  - rewrite L5K.rl2, R1_2, BG.unsigned_lit by lia. unfold stack_ok. rewrite (PMS.ly_stack L LY), (PMS.ly_segs L LY). unfold HEAP_STACK.
    split. { replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    split. lia. split. lia. split. lia.
    assert (W1 : L5.writable RSEGS M1 (sp - 16 - 8224) 8224).
    { eapply L5.writable_grows. exact GR1. eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS M _ _ DEF); lia. lia. lia. }
    intros d m Hd Hm. apply W1. lia. lia.
  - exact HK0.
  - (* [comment removed for export] *)
    intros R2 M2 model2 A HA RP BR BA DEFA PRES MBV HH2.
    rewrite L5K.rl1, R1_1.
    pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4). rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in BR1.
    rewrite L5K.rl2, R1_2, BG.unsigned_lit in PRES by lia. destruct PRES as [PRES SDEF]. rewrite (PMS.ly_stack L LY) in PRES, SDEF. unfold HEAP_STACK in PRES, SDEF.
    (* [comment removed for export] *)
    assert (CL: forall a, sp - 16 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply PRES. lia. right. left. lia. unfold in_errno. rewrite (PMS.ly_errno L LY). lia. }
    assert (C8' : BG.u64_at M2 (sp - 8) (bv_unsigned (getr R (reg 1)))).
    { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact C8. }
    assert (C16' : BG.u64_at M2 (sp - 16) (bv_unsigned (getr R (reg 8)))).
    { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact C16. }
    assert (WR2 : BG.writable M2 (sp - 16) 16).
    { change (L5.writable RSEGS M2 (sp - 16) 16). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia.
      eapply L5.writable_grows. exact GR1. exact WR16. }
    pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
    change (bv_modulus 64) with (2 ^ 64) in RG1, RG8.
    assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BG.unsigned_lit. lia. }
    destruct (p2_run fx1 R2 M2 A sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) r
                HA ltac:(lia) ltac:(rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2; exact R1_2) A16 ltac:(lia) ltac:(lia) WR2
                C8' C16' ltac:(lia) ltac:(lia) E1 RA)
      as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_10 & MM3 & GR3).
    eapply (L5.cps_of_msteps RSEGS). { rewrite (L5C.halted_but_vm _ _ MBV). exact Mh. } { rewrite (L5C.lazy_but_vm _ _ MBV). exact Ml. }
    exact MS3.
    apply (KONT fx3 R3 M3 model2 A).
    + rewrite L5K.rl10. exact R3_10.
    + (* [comment removed for export] *)
      apply L5K.regs_preserved_by_index. intros i Hi.
      cbn in Hi. destruct Hi as [<-|Hi]. { rewrite R3_2, <- H2, L5K.rl2. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (cbn; tauto). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). cbn; tauto. }
      destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (cbn; tauto). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). cbn; tauto. }
      destruct Hi as [<-|Hi]. { rewrite R3_8. symmetry. apply BG.word_of_unsigned. reflexivity. }
      assert (G: forall j, In j [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
      { intros j Hj.
        assert (M2j: In j KS2) by (pose proof Hj as H'; L5K.inlist H').
        assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
        assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
        rewrite (K3 j M2j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
      apply G. L5K.inlist Hi.
    + (* [comment removed for export] *)
      split. exact BR. split. exact BA. intros i Hi. rewrite (MM3 (Z_to_bv 64 (A + i))). apply DEFA. exact Hi.
    + (* [comment removed for export] *)
      split.
      * intros a (Ha & CA & NE & _). rewrite (MM3 (Z_to_bv 64 a)).
        destruct CA as [IB|[[S1 S2]|IM]].
        -- rewrite PRES. apply FR1. rewrite BG.unsigned_lit by lia.
           { destruct IB as (b & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _).
             lia. }
           lia. left. exact IB. exact NE.
        -- unfold OPNEW_SCR, HEAP_STACK in S2. rewrite PRES. apply FR1. rewrite BG.unsigned_lit by lia. lia. lia.
           right. left. split. exact S1. lia. exact NE.
        -- rewrite PRES. apply FR1. rewrite BG.unsigned_lit by lia. rewrite (PMS.ly_img_hi L LY) in IM. lia. lia. right. right. exact IM. exact NE.
      * split.
        { unfold OPNEW_SCR, HEAP_STACK. intros i Hi. rewrite (MM3 (Z_to_bv 64 _)).
          destruct (Z_lt_le_dec (sp - (16 + 8224) + i) (sp - 16)) as [Hlt|Hge].
          -- apply SDEF. lia.
          -- rewrite CL by lia. apply GR1. apply DEF. lia. }
        (* [comment removed for export] *)
        intros a Ha CA NE D0. rewrite (MM3 (Z_to_bv 64 a)). unfold OPNEW_SCR, HEAP_STACK in CA.
        rewrite PRES; [apply GR1; exact D0 | lia | | exact NE].
        eapply L5K.client_inner. exact CA. lia. lia.
    + exact MBV.
    + eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (PMS.ly_ro L LY). rewrite (PMS.ly_img_hi L LY); lia. lia.
      intros a Ha. left. apply MM3. exact GR3.
Qed.

End WithHeap.
End SCFG_1.

End L5NEW.
