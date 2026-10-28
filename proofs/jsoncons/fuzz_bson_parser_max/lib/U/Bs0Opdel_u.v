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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require Import LibSegBs_lcdel0_u LibSegBs_lcdel1_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DEL.

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
Module P0 := LibSegBs_lcdel0_u.
Module P1 := LibSegBs_lcdel1_u.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition FREE : Z := 0x9cc94.
Definition KS : list nat := Eval vm_compute in (BG.kept_list 48 P1.regs0 P1.regs_out).
Lemma KS0_ok : BG.kept_ok 48 P0.regs0 P0.regs_out KS = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS1_ok : BG.kept_ok 48 P1.regs0 P1.regs_out KS = true. Proof. vm_compute. reflexivity. Qed.
Lemma KS_all : KS = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma jumps_run (pc : Z) fx R M :
  (pc = OPDEL \/ pc = OPDEL_SIZED) ->
  exists fx' R1 M1, msteps RSEGS (st fx R pc M) (st fx' R1 FREE M1)
    /\ (forall x, In x KS -> getr R1 (reg x) = getr R (reg x)) /\ (forall a : word, M1 a = M a) /\ mem_grows M M1.
Proof.
  intros Hpc.
  set (Vf := fun k : nat => getr R (reg k)). set (E := Env Vf (fun _ => [])).
  destruct Hpc as [-> | ->].
  - assert (HR: regs_ok E P0.regs0 R).
    { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P0.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
    assert (HK: know_ok RSEGS E M P0.kn0) by (apply Forall_nil).
    destruct (P0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply nth_error_single in Hnth. subst ps0. change P0.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' P0.regs0 P0.regs_out 48 KS KS0_ok HR Hag Hregs j Hj). }
    split. { intros a. apply Hfr. constructor. } exact Hgr.
  - assert (HR: regs_ok E P1.regs0 R).
    { apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
    assert (HK: know_ok RSEGS E M P1.kn0) by (apply Forall_nil).
    destruct (P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply nth_error_single in Hnth. subst ps0. change P1.NX0 with 48%nat in Hag.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs E E' R R' P1.regs0 P1.regs_out 48 KS KS1_ok HR Hag Hregs j Hj). }
    split. { intros a. apply Hfr. constructor. } exact Hgr.
Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Lemma opdel_ok_at (pc : Z) : (pc = OPDEL \/ pc = OPDEL_SIZED) -> PMSP.opdel_spec_at PMS.RSEGS PMS.AD L HI pc.
Proof.
  intros Hpc. unfold PMSP.opdel_spec_at. change (pa_tp PMS.AD) with TP. change PMSP.OPDEL_SCR with OPDEL_SCR. intros fx R M model K LB cr A n sp r HH (Mh & Ml & Mm) HK0 HIN H10 H1 RA H2 H4 STK KONT.
  pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold OPDEL_SCR, HEAP_STACK in SLO, DEF. pose proof RA as [Hr He].
  destruct (jumps_run pc fx R M Hpc) as (fx1 & R1 & M1 & MS1 & K1 & MM1 & GR1).
  assert (KA: forall j, (0 < j < 32)%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj. apply K1. rewrite KS_all. cbn. lia. }
  unfold PMSP.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  pose proof (hio_free L SCFG HI HIok) as HF. unfold free_spec in HF. rewrite (PMS.ly_segs L LY), (PMS.ly_free L LY) in HF.
  change (Z_to_bv 64 FREE) with (Z_to_bv 64 0x9cc94).
  eapply (HF fx1 R1 M1 model LB cr A n K); clear HF.
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (PMS.ly_ro L LY). rewrite (PMS.ly_img_hi L LY); lia. lia.
    intros a Ha. left. apply MM1. exact GR1.
  - exact Mh. - exact Ml. - exact Mm.
  - exact HIN.
  - rewrite L5K.rl10, KA, <- L5K.rl10 by lia. exact H10.
  - rewrite (PMS.ly_tp L LY). rewrite L5K.rl4, KA, <- L5K.rl4 by lia. exact H4.
  - rewrite L5K.rl1, KA, <- L5K.rl1, H1 by lia. apply L5K.ret_ok_lit. exact RA.
  - rewrite L5K.rl2, KA, <- L5K.rl2, H2, BG.unsigned_lit by lia. unfold stack_ok. rewrite (PMS.ly_stack L LY), (PMS.ly_segs L LY). unfold HEAP_STACK.
    split. exact A16. split. lia. split. lia. split. lia.
    assert (W1 : L5.writable RSEGS M1 (sp - 8224) 8224).
    { eapply L5.writable_grows. exact GR1. apply (L5C.writable_of_defined RSEGS M _ _ DEF); lia. }
    intros d m Hd Hm. apply W1. lia. lia.
  - exact HK0.
  - intros R2 M2 model2 RP [[PRES SDEF] _] MBV HH2.
    rewrite L5K.rl1, KA, <- L5K.rl1, H1 by lia.
    rewrite L5K.rl2, KA, <- L5K.rl2, H2, BG.unsigned_lit in PRES, SDEF by lia. rewrite (PMS.ly_stack L LY) in PRES, SDEF. unfold HEAP_STACK in PRES, SDEF.
    apply (KONT fx1 R2 M2 model2).
    + apply L5K.regs_preserved_by_index. intros i Hi. rewrite (L5K.regs_preserved_index R1 R2 i RP Hi). apply KA. unfold L5K.CS in Hi. cbn in Hi. lia.
    + split.
      * intros a (Ha & CA & NE & _). rewrite PRES. apply (MM1 (Z_to_bv 64 a)). lia. exact CA. exact NE.
      * split. { unfold OPDEL_SCR, HEAP_STACK. intros i Hi. apply SDEF. lia. }
        intros a Ha CA NE D0. unfold OPDEL_SCR, HEAP_STACK in CA. rewrite PRES; [| lia | exact CA | exact NE]. rewrite MM1. exact D0.
    + exact MBV.
    + exact HH2.
Qed.

Theorem opdel_ok : PMS.opdel_spec L HI.
Proof. apply opdel_ok_at. first [left; reflexivity | right; reflexivity]. Qed.
Theorem opdel_sized_ok : PMS.opdel_sized_spec L HI.
Proof. apply opdel_ok_at. first [left; reflexivity | right; reflexivity]. Qed.

End WithHeap.
End SCFG_1.

End L5DEL.
