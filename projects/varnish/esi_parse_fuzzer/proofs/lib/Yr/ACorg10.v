(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section Arms.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition pop_core_stmt : Prop :=
    forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T1 : TSet),
      alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
      n <= kMaxPrimaryUser -> pk_chunks (a_cache A (class_of n)) = [] ->
      Z.of_nat (length (rg_free (a_reg A (class_of n)))) < refill_count (class_of n) ->
      alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1 ->
      srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T1.

  (* [comment removed for export] *)
  Definition a8_core_cps1_stmt : Prop :=
    forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T1 : TSet),
      alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
      524288 <= n ->
      alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1 ->
      srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T1.

End Arms.
