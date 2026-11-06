(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic ACor4x6 ACorg10 AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopT.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACorg10 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section Top.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Theorem pop_core_ok : pop_core_stmt.
  Proof.
    unfold pop_core_stmt. intros until T1. intros PRE NP EMP SHORT K1.
    assert (TPE : tp = cl_tp LPA) by ((first [ dand12 PRE as _ _ _ _ _ _ _ _ _ _ X _ | destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _) ]); exact X). subst tp.   (* [comment removed for export] *)
    unfold alloc_entry_ms. cbn [cl_segs LPA].
    exact (pop_core_gen rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key PRE NP EMP SHORT T1 K1 t0 t1 t2 a6 a7 t3 t4 t5 t6).
  Qed.
End Top.
(* [comment removed for export] *)
