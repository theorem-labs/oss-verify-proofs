(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA LibIface LibIfaceAJ L5Defs L5Core L5DefsA HeapIfaceAJx
PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAa PmTopAL PmAHarnessStmts Ja0ExitCells.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAStaticsTop () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ExitCells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIfaceAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "2ex"; "3Z"; "0L"; "0M"; "4asan_run"; "5atexit_cellsA"; "6u8_at"; "7cellz"; "7ls_ok"; "8lib_statics_frameA"; "8lib_statics_initA"; "9Lay"; ":AADDR_A"; ":ADDR_A"]; [";st"; "<TopLSA"; "=loaded_segments"; "0a"; "0ar"; "0ax"; "0g"; ">bv"]]).
Module PMSTT.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section T.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells).
Hypothesis LY : PMA.layout L C.
Let LYa := PMA.ly_as0 L C LY.
Local Notation Lay := (PMHAS.Lay L).
Local Notation LSt := (PMSTA.TopLSA RSEGS PMA.AD PMA.AAD).
Lemma u8_of_cellz : ltac2:(TCodec.tc2 tcn__PmAStaticsTop "F'GyR0%211'1y8%511%311p051'3&9&Br2r1u1z%6554321&8r3%248174p041pQ8<1p<>1").
Proof. intros M a. unfold cellz, L5.u8_at. intros H. rewrite H. reflexivity. Qed.
Theorem statics_initA : ltac2:(TCodec.tc2 tcn__PmAStaticsTop ";&<&=v4%211vD&A&B&?&>%43321%:3761").
Proof.
unfold lib_statics_initA. intros av uid rnd tid canary hw M (IF & CELLS).
unfold lib_init_facts in IF. cbv zeta in IF.
cbn [lib_view heap_view ll_heap ll_init_img ll_guard HeapIface.hl_segs lla_L lla_init_img lla_guard PMHAS.Lay PMTAL.TopLayA_a] in IF.
cbn [lla_L lla_init_cells PMHAS.Lay PMTAL.TopLayA_a] in CELLS. unfold PMTAL.init_cells_a, PMTAL.ATEXIT_a in CELLS.
rewrite (L5A.aly_segs L C LYa) in IF, CELLS.
destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & _).
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end. clear CELLS.
cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in *.
assert (IC : forall lo hi, In (lo, hi) [(0x10000, 0x134000); (0x136d70, 0x136e18); (0x66d351, 0x66d354); (0x66d355, 0x66ecb0)] -> L5.img_clear M lo hi).
{ intros lo hi Hin i Hi. exact (IMG (lo, hi) i Hin Hi). }
pose proof (IC _ _ ltac:(left; reflexivity)) as I1. pose proof (IC _ _ ltac:(right; right; right; left; reflexivity)) as I3. clear IC IMG.
cbn [LibIface.ls_ok ls_g0 PMSTA.TopLSA]. unfold PMSTA.ls_okA, PMST.g0. cbn [PMST.st_loc PMST.st_sys PMST.st_err].
split; [|split; [|split]].
- split; [|split; [|split]].
+ exact I1.
+ exists canary. split; [exact HC| exact GU].
+ apply u8_of_cellz. assumption.
+ assumption.
- unfold PMST.loc_ok. intros iv Hin. cbn [pa_loc_foot PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; intros i Hi; apply I3; cbn [fst snd] in *; lia.
- unfold PMST.sys_ok. cbn [pa_syscat_guard PMA.AD ADDR_A]. intros i Hi. apply I3. lia.
- split.
+ cbn [pa_errcat_guard PMA.AD ADDR_A]. intros i Hi. apply I3. lia.
+ unfold PMSTA.atexit_stA, HAJ.atexit_cells. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 PMA.AD PMA.AAD ADDR_A AADDR_A].
split; [apply u8_of_cellz; assumption|]. repeat (split; [assumption|]). exact I.
Qed.
Theorem statics_frameA : ltac2:(TCodec.tc2 tcn__PmAStaticsTop ";&;&=v4%211vD&A&B&?&>%43321%:3761").
Proof.
unfold lib_statics_frameA, lib_statics_frame. intros g M M' OK FOOT RO INITC.
cbn [LibIface.ls_ok PMSTA.TopLSA] in *.
apply (PMSTA.ls_okA_frame RSEGS PMA.AD PMA.AAD PMA.addrs_wf_A M M'); [| | exact OK].
- intros a Ha [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
+ apply FOOT; [exact Ha|]. exists iv. cbn [lib_view ll_foot lla_foot PMHAS.Lay PMTAL.TopLayA_a PMTAL.foot_a PMTAL.ATEXIT_a].
unfold pm_foot in Hin. cbn in Hin. split; [cbn; tauto| exact Hr].
+ apply INITC; [exact Ha|]. left. exists (0x68edc0, 0x68edc8). cbn [lib_view ll_initc lla_initc PMHAS.Lay PMTAL.TopLayA_a]. cbn [pa_canary PMA.AD ADDR_A] in Hc.
split; [cbn; tauto| cbn; lia].
+ apply INITC; [exact Ha|]. left. unfold pm_initc in Hin. cbn in Hin.
cbn [lib_view ll_initc lla_initc PMHAS.Lay PMTAL.TopLayA_a].
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [exists (0x68f013, 0x68f014)| exists (0x68f0f0, 0x68f0f4)]; (split; [cbn; tauto| cbn; lia]).
- intros a Ha Hn. apply RO; [| exact Hn]. cbn [lib_view ll_rw_lo lla_rw_lo PMHAS.Lay PMTAL.TopLayA_a]. rewrite L5.unsigned_lit by (cbn [pa_rw_lo PMA.AD ADDR_A] in Ha; lia).
cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. lia.
Qed.
Theorem lsx_atexit : ltac2:(TCodec.tc2 tcn__PmAStaticsTop "N'6'@'GyR0%211'1y8%511%311p051&:&A&B&?&>%43321r2r1%83321'2'0&7r3%2216qQ<41%6251p081p<B1pQ>K1pQ:M1").
Proof.
intros ar0 g M (_ & _ & _ & (_ & AX)). exists (PMST.st_err g).
unfold PMSTA.atexit_stA, HAJ.atexit_cells in AX. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit pa_errcat_dtor pa_errcat_obj PMA.AD PMA.AAD ADDR_A AADDR_A] in AX.
unfold atexit_cellsA, AX_CELLS_A, AX_CELLS_B, ax_cell.
destruct (PMST.st_err g).
- destruct AX as (_ & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296 & C48 & C56 & C304 & C312).
repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
- destruct AX as (_ & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296 & _).
repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
Qed.
End T.
End PMSTT.
