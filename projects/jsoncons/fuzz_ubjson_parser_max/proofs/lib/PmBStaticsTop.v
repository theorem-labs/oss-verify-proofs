(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA LibIface LibIfaceAJ L5Defs L5Core L5DefsAB0 HeapIfaceAJx
PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmTopAL Jb0ExitCells.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBStaticsTop () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0ExitCells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIfaceAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTopAL.PMTAL."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "stdpp.bitvector.definitions."], [["0CREDIT"; "1bool"; "1option"; "2ex"; "3Z"; "0FRAMES"; "0L"; "0LEAK"; "0M"; "4asan_run"; "5atexit_cellsA"; "6u8_at"; "7cellz"; "7ls_ok"; "8lib_statics_frameA"; "8lib_statics_initA"]; ["9AADDR_B"; "9ADDR_B"; ":st"; ";TopLSA"; "<TopLayA_b"; "=loaded_segments"; "0STK"; "0a"; "0ar"; "0ax"; "0g"; ">bv"]]).
Module PMSTTB.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section T.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells).
Hypothesis LY : PMB.layout L C.
Let LYa := PMB.ly_as0 L C LY.
Variables (STK : Z) (FRAMES LEAK : Z -> Z) (CREDIT : Z -> credit).
Local Notation Lay := (PMTAL.TopLayA_b STK FRAMES LEAK CREDIT L).
Local Notation LSt := (PMSTA.TopLSA RSEGS PMB.AD PMB.AAD).
Lemma u8_of_cellz : ltac2:(TCodec.tc2 tcn__PmBStaticsTop "F'KyR0%211'2y8%511%311p051'4&<&Er2r1u1z%6554321&;r3%248174p041pQ@<1pB>1").
Proof. intros M a. unfold cellz, L5.u8_at. intros H. rewrite H. reflexivity. Qed.
Theorem statics_initA : ltac2:(TCodec.tc2 tcn__PmBStaticsTop "?&?&DvFv5v7v0v6%6554321vH&C&E&A&@%43321%>3761").
Proof.
unfold lib_statics_initA. intros av uid rnd tid canary hw M (IF & CELLS).
unfold lib_init_facts in IF. cbv zeta in IF.
cbn [lib_view heap_view ll_heap ll_init_img ll_guard HeapIface.hl_segs lla_L lla_init_img lla_guard PMTAL.TopLayA_b] in IF.
cbn [lla_L lla_init_cells PMTAL.TopLayA_b] in CELLS. unfold PMTAL.init_cells_b, PMTAL.ATEXIT_b in CELLS.
rewrite (L5A.aly_segs L C LYa) in IF, CELLS.
destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & _).
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end. clear CELLS.
cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in *.
assert (IC : forall lo hi, In (lo, hi) [(0x10000, 0x136000); (0x138ad8, 0x138b80); (0x66f091, 0x66f094); (0x66f095, 0x6709f0)] -> L5.img_clear M lo hi).
{ intros lo hi Hin i Hi. exact (IMG (lo, hi) i Hin Hi). }
pose proof (IC _ _ ltac:(left; reflexivity)) as I1. pose proof (IC _ _ ltac:(right; right; right; left; reflexivity)) as I3. clear IC IMG.
cbn [LibIface.ls_ok ls_g0 PMSTA.TopLSA]. unfold PMSTA.ls_okA, PMST.g0. cbn [PMST.st_loc PMST.st_sys PMST.st_err].
split; [|split; [|split]].
- split; [|split; [|split]].
+ exact I1.
+ exists canary. split; [exact HC| exact GU].
+ apply u8_of_cellz. assumption.
+ assumption.
- unfold PMST.loc_ok. intros iv Hin. cbn [pa_loc_foot PMB.AD ADDR_B] in Hin. destruct Hin as [<-|[<-|[]]]; intros i Hi; apply I3; cbn [fst snd] in *; lia.
- unfold PMST.sys_ok. cbn [pa_syscat_guard PMB.AD ADDR_B]. intros i Hi. apply I3. lia.
- split.
+ cbn [pa_errcat_guard PMB.AD ADDR_B]. intros i Hi. apply I3. lia.
+ unfold PMSTA.atexit_stA, HAJ.atexit_cells. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 PMB.AD PMB.AAD ADDR_B AADDR_B].
split; [apply u8_of_cellz; assumption|]. repeat (split; [assumption|]). exact I.
Qed.
Theorem statics_frameA : ltac2:(TCodec.tc2 tcn__PmBStaticsTop "?&>&DvFv5v7v0v6%6554321vH&C&E&A&@%43321%>3761").
Proof.
unfold lib_statics_frameA, lib_statics_frame. intros g M M' OK FOOT RO INITC.
cbn [LibIface.ls_ok PMSTA.TopLSA] in *.
apply (PMSTA.ls_okA_frame RSEGS PMB.AD PMB.AAD PMB.addrs_wf_A M M'); [| | exact OK].
- intros a Ha [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
+ apply FOOT; [exact Ha|]. exists iv. cbn [lib_view ll_foot lla_foot PMTAL.TopLayA_b PMTAL.foot_a PMTAL.ATEXIT_a].
unfold pm_foot in Hin. cbn in Hin. split; [cbn; tauto| exact Hr].
+ apply INITC; [exact Ha|]. left. exists (0x690b00, 0x690b08). cbn [lib_view ll_initc lla_initc PMTAL.TopLayA_b]. cbn [pa_canary PMB.AD ADDR_B] in Hc.
split; [cbn; tauto| cbn; lia].
+ apply INITC; [exact Ha|]. left. unfold pm_initc in Hin. cbn in Hin.
cbn [lib_view ll_initc lla_initc PMTAL.TopLayA_b].
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [exists (0x690d53, 0x690d54)| exists (0x690e30, 0x690e34)]; (split; [cbn; tauto| cbn; lia]).
- intros a Ha Hn. apply RO; [| exact Hn]. cbn [lib_view ll_rw_lo lla_rw_lo PMTAL.TopLayA_b]. rewrite L5.unsigned_lit by (cbn [pa_rw_lo PMB.AD ADDR_B] in Ha; lia).
cbn [pa_rw_lo PMB.AD ADDR_B] in Ha. lia.
Qed.
Theorem lsx_atexit : ltac2:(TCodec.tc2 tcn__PmBStaticsTop "N'9'B'KyR0%211'2y8%511%311p051&=&C&E&A&@%43321r2r1%83321'3'1&:r3%2216qQD41%6251p081pBB1pQFK1pQBM1").
Proof.
intros ar0 g M (_ & _ & _ & (_ & AX)). exists (PMST.st_err g).
unfold PMSTA.atexit_stA, HAJ.atexit_cells in AX. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit pa_errcat_dtor pa_errcat_obj PMB.AD PMB.AAD ADDR_B AADDR_B] in AX.
unfold atexit_cellsA, AX_CELLS_A, AX_CELLS_B, ax_cell.
destruct (PMST.st_err g).
- destruct AX as (_ & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296 & C48 & C56 & C304 & C312).
repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
- destruct AX as (_ & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296 & _).
repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
Qed.
End T.
End PMSTTB.
