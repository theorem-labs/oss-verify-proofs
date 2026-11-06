(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Js0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmStatics PmSpecs PmSpecsS PmStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require Import LibSegJs_lcdel0 LibSegJs_lcdel1.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Opdel () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigLinkGlue.BG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Opdel.L5DEL.L5CS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Opdel.L5DEL.P0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Opdel.L5DEL.P1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Opdel.L5DEL.SCFG_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0HI"; "0L"; "4bvmap"; "0M"]; ["0M1"; "0R"; "0R1"; "5kept_ok"; "6msteps"; "7OPDEL"; "7OPDEL_SIZED"; "8regs0"; "8regs_out"; "9regs0"; "9regs_out"; ":FREE"; ":KS"; ";ADDR_S"; "<opdel_spec_at"; "=opdel_sized_spec"]; ["=opdel_spec"; ">FPState"; ">getr"; ">mkst"; ">seg_rom"; "?mem_grows"; "@loaded_segments"; "0SCFG_P"; "AIn"; "Bof_nat"; "0a"; "0fx"; "0fx'"; "0pc"; "CZ_to_bv"; "Cbv"]; ["0x"]]).
Local Ltac lia := L5FastLia.plia.
Module L5DEL.
Module L5CS.
Abbreviation RSEGS := PMS.RSEGS.
Definition HEAP_STACK : Z := 8224.
Definition OPNEW : Z := 0xae098.
Definition OPNEW_SCR : Z := 16 + HEAP_STACK.
Definition OPDEL : Z := 0x543fc.
Definition OPDEL_SIZED : Z := 0x54400.
Definition OPDEL_SCR : Z := HEAP_STACK.
Definition TP : Z := 0xc7c60.
End L5CS.
Lemma nth_error_single {A} (x y : A) i : nth_error [x] i = Some y -> y = x.
Proof. destruct i; simpl. congruence. destruct i; discriminate. Qed.
Import L5CS.
Module P0 := LibSegJs_lcdel0.
Module P1 := LibSegJs_lcdel1.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Definition FREE : Z := 0x9a974.
Definition KS : list nat := Eval vm_compute in (BG.kept_list 48 P1.regs0 P1.regs_out).
Lemma KS0_ok : ltac2:(TCodec.tc2 tcn__Js0Opdel ":'8'0&CuQ@&G&H&L%544321(6%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma KS1_ok : ltac2:(TCodec.tc2 tcn__Js0Opdel ":'8'0&CuQ@&I&J&L%544321(6%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma KS_all : ltac2:(TCodec.tc2 tcn__Js0Opdel "R7'8'2'3%211&L(1u1u2u3u4u5u6u7u8u9u:u;u<u=u>u?u@uAuBuCuDuEuFuGuHuIuJuKuLuMuNuO(4%11Q4%Q23Q531%Q33Q651%Q43Q771%Q53Q891%Q63Q9;1%Q73Q:=1%Q83Q;?1%Q93Q<A1%Q:3Q=C1%Q;3Q>E1%Q<3Q?G1%Q=3Q@I1%Q>3QAK1%Q?3QBM1%Q@3QCO1%QA3QDQ11%QB3QEQ31%QC3QFQ51%QD3QGQ71%QE3QHQ91%QF3QIQ;1%QG3QJQ=1%QH3QKQ?1%QI3QLQA1%QJ3QMQC1%QK3QNQE1%QL3QOQG1%QM3R0QI1%QN3R1QK1%QO3R2QM1%R03R3QO1%R63R3R21").
Proof. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_jumps_run := (ltac2:(TCodec.tc2 tcn__Js0Opdel "R;';'Q1&>y5'Q?yR0%211%5241'5y8%611%311p061':'8r4&E%33A21&F%53C41%7231'9'7'D&Q6&Q3r7r6&Q>r8%22I1r5&Q4%119%9587431r3r2&K%:2Q11r1%?554217%B3A71'3&Q8&L%23361&Q2&Q9%11<%E2Q>1%42Q31%52F2%Q63Q>21p081pS2<1%C1@%M1A%Q;3Q>21pRFQD1&Q5%12ME%Q7231%Q8281%Q92F1qQ2QD1%Q<2QE1qQ6QK1%Q>2QL1qRJR31%Q@2R41p0QB1pQ0QK1pQ4R11pRHR81pRLR:1")) (only parsing).
Variable pc : ltac:(sec_ty2 constr:(SEC_T_jumps_run) 0%nat 0%nat).
Variable fx : ltac:(sec_ty2 constr:(SEC_T_jumps_run) 1%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_jumps_run) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_jumps_run) 3%nat 0%nat).
Lemma jumps_run : ltac:(sec_stmt2 constr:(SEC_T_jumps_run) 4%nat 0%nat).
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
End SE.
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Section SE.
Variables (pc : Z).
Lemma opdel_ok_at : (pc = OPDEL \/ pc = OPDEL_SIZED) -> PMSP.opdel_spec_at PMS.RSEGS PMS.AD L HI pc.
Proof.
intros Hpc. unfold PMSP.opdel_spec_at. change (pa_tp PMS.AD) with TP. change PMSP.OPDEL_SCR with OPDEL_SCR. intros fx R M model K LB cr A n sp r HH (Mh & Ml & Mm) HK0 HIN H10 H1 RA H2 H4 STK KONT.
pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold OPDEL_SCR, HEAP_STACK in SLO, DEF. pose proof RA as [Hr He].
destruct (jumps_run pc fx R M Hpc) as (fx1 & R1 & M1 & MS1 & K1 & MM1 & GR1).
assert (KA: forall j, (0 < j < 32)%nat -> getr R1 (reg j) = getr R (reg j)).
{ intros j Hj. apply K1. rewrite KS_all. cbn. lia. }
unfold PMSP.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
pose proof (hio_free L SCFG HI HIok) as HF. unfold free_spec in HF. rewrite (PMS.ly_segs L LY), (PMS.ly_free L LY) in HF.
change (Z_to_bv 64 FREE) with (Z_to_bv 64 0x9a974).
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
End SE.
Theorem opdel_ok : ltac2:(TCodec.tc2 tcn__Js0Opdel "5&Q0vQ7v=v<%43321").
Proof. apply opdel_ok_at. first [left; reflexivity | right; reflexivity]. Qed.
Theorem opdel_sized_ok : ltac2:(TCodec.tc2 tcn__Js0Opdel "5&OvQ7v=v<%43321").
Proof. apply opdel_ok_at. first [left; reflexivity | right; reflexivity]. Qed.
End WithHeap.
End SCFG_1.
End L5DEL.
