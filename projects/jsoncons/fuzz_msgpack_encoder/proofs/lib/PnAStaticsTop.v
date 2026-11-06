(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.PnTopAL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.PnAHarnessStmts.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQSTT.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section T.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (RES : credit).
Hypothesis LY : PMA.layout L C.
Let LYa := PMA.ly_as0 L C LY.
Local Notation Lay := (PQHAS.LayA RES L).
Local Notation LSt := (PQSTA.TopLSA RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A).

Lemma u8_of_cellz (M : word -> option byte) a : cellz RSEGS M a 1 0 -> L5.u8_at RSEGS M a 0.
Proof. unfold cellz, L5.u8_at. intros H. rewrite H. reflexivity. Qed.

Theorem statics_initA : lib_statics_initA Lay ar LSt.
Proof.
  unfold lib_statics_initA. intros av uid rnd tid canary hw M (IF & CELLS).
  unfold lib_init_facts in IF. cbv zeta in IF.
  cbn [lib_view heap_view ll_heap ll_init_img ll_guard HeapIface.hl_segs lla_L lla_init_img lla_guard PQHAS.LayA PNTAL.TopLayA_a] in IF.
  cbn [lla_L lla_init_cells PQHAS.LayA PNTAL.TopLayA_a] in CELLS. unfold PNTAL.init_cells_a in CELLS.
  rewrite (L5A.aly_segs L C LYa) in IF, CELLS.
  destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & _).
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end. clear CELLS.
  cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in *.
  assert (IC : forall lo hi, In (lo, hi) [(0x10000, 0x158000); (0x15b4d0, 0x15b578); (0x6920d5, 0x693a30)] -> L5.img_clear M lo hi).
  { intros lo hi Hin i Hi. exact (IMG (lo, hi) i Hin Hi). }
  pose proof (IC _ _ ltac:(left; reflexivity)) as I1. pose proof (IC _ _ ltac:(right; right; left; reflexivity)) as I3. clear IC IMG.
  cbn [LibIface.ls_ok ls_g0 PQSTA.TopLSA]. unfold PQSTA.ls_okA, PMST.g0. cbn [PMST.st_loc PMST.st_sys PMST.st_err].
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + cbn [pa_rw_lo PMA.AD ADDR_A]. exact I1.
    + exists canary. split; [exact HC| exact GU].
    + apply u8_of_cellz. cbn [pa_need_locks PMA.AD ADDR_A]. assumption.
    + cbn [pa_locale_lock PMA.AD ADDR_A]. assumption.
  - unfold PMST.loc_ok. intros iv Hin. cbn [pa_loc_foot PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; intros i Hi; apply I3; cbn [fst snd] in *; lia.
  - unfold PMST.sys_ok. cbn [pa_syscat_guard PMA.AD ADDR_A]. intros i Hi. apply I3. lia.
  - split.
    + cbn [pa_errcat_guard PMA.AD ADDR_A]. intros i Hi. apply I3. lia.
    + unfold PQSTA.atexit_stA, HAJ.atexit_cells. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit qa_drv_call qa_drv_guard PQSTA.ax_list PMA.AD PMA.AAD ADDR_A AADDR_A PnLayoutQA.QADDR_A length Z.of_nat Z.mul Z.add].
      split; [apply u8_of_cellz; assumption|]. repeat (split; [assumption|]). intros i f a Hi. destruct i; discriminate.
Qed.

Theorem statics_frameA : lib_statics_frameA Lay ar LSt.
Proof.
  unfold lib_statics_frameA, lib_statics_frame. intros g M M' OK FOOT RO INITC.
  cbn [LibIface.ls_ok PQSTA.TopLSA] in *.
  apply (PQSTA.ls_okA_frame RSEGS PMA.AD PMA.AAD PnLayoutQA.QADDR_A PMA.addrs_wf_A M M'); [| | exact OK].
  - intros a Ha [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
    + apply FOOT; [exact Ha|]. exists iv. cbn [lib_view ll_foot lla_foot PQHAS.LayA PNTAL.TopLayA_a]. unfold PNTAL.foot_a. split; [exact Hin| exact Hr].
    + apply INITC; [exact Ha|]. left. exists (0x6b3b40, 0x6b3b48). cbn [lib_view ll_initc lla_initc PQHAS.LayA PNTAL.TopLayA_a]. cbn [pa_canary PMA.AD ADDR_A] in Hc.
      split; [cbn; tauto| cbn; lia].
    + apply INITC; [exact Ha|]. left. unfold pm_initc in Hin. cbn in Hin.
      cbn [lib_view ll_initc lla_initc PQHAS.LayA PNTAL.TopLayA_a].
      destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [exists (0x6b3d93, 0x6b3d94)| exists (0x6b3e70, 0x6b3e74)]; (split; [cbn; tauto| cbn; lia]).
  - intros a Ha Hn. apply RO; [| exact Hn]. cbn [lib_view ll_rw_lo lla_rw_lo PQHAS.LayA PNTAL.TopLayA_a]. rewrite L5.unsigned_lit by (cbn [pa_rw_lo PMA.AD ADDR_A] in Ha; lia).
    cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. lia.
Qed.
End T.
End PQSTT.
