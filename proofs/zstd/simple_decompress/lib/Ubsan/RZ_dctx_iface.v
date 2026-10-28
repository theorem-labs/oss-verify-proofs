(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep ZdSepKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface RZ_block_iface RZ_dframe_iface.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma dctx_any_transport : forall DCTX W' m1 m2, dctx_any m1 DCTX -> munch W' m1 m2 -> wmono usegs m1 m2 ->
  disjoint_from W' DCTX 95992 -> dctx_any m2 DCTX.
Proof.
  intros DCTX W' m1 m2 (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                   PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]) MU WM DJ.
  assert (TR : forall A cs, rw_cells usegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells usegs m2 A cs).
  { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ | lia | lia]. }
  assert (TS : forall a b, stk usegs m1 a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk usegs m2 a b).
  { intros a b SK L1 L2 L3. eapply stk_transport_disjoint; [exact SK | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ | lia | lia]. }
  unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
  exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, ws, jhb, ovd, dcb, dce, trace.
  split; [apply TR; [exact PT | lia | cbn; lia]|].
  split; [apply TR; [exact H1 | lia | cbn; lia]|].
  split; [split; [apply TR; [exact FPC | lia | rewrite FPSZ; lia]| exact FPSZ]|].
  split; [apply TR; [exact H3 | lia | cbn; lia]|].
  split; [split; [apply TR; [exact XSC | lia | rewrite XSSZ; lia]| exact XSSZ]|].
  split; [split; [apply TR; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
  split; [exact H5OK|].
  split; [apply TR; [exact TX | lia | cbn; lia]|].
  split; apply TS; try assumption; lia.
Qed.

Definition zd_ddctx_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DCTX DST CAP SRC : Z) (src : list Z) (size : Z),
  dctx_any m DCTX -> 4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
  rw_cells usegs m PZD_GOT_TRACE [C8 wz0; C8 wz0] ->
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= size -> size <= zlen src -> size < 2^40 ->
  4096 <= SRC -> SRC + zlen src < 2^47 ->
  stk usegs m DST (DST + CAP) -> 0 <= CAP -> CAP < 2^40 -> (DST = 0 -> CAP = 0) -> (DST <> 0 -> 4096 <= DST) -> DST + CAP < 2^47 ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - DMF_STACK -> SPV < 2^47 -> SPV mod 16 = 0 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (DST + CAP <= lo \/ SPV <= DST) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (PZD_GOT_TRACE + 16 <= lo \/ SPV <= PZD_GOT_TRACE) ->
  (DST + CAP <= DCTX \/ DCTX + 95992 <= DST) -> (DST + CAP <= SRC \/ SRC + zlen src <= DST) ->
  (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC) ->
  (PZD_GOT_TRACE + 16 <= DCTX \/ DCTX + 95992 <= PZD_GOT_TRACE) -> (PZD_GOT_TRACE + 16 <= DST \/ DST + CAP <= PZD_GOT_TRACE) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 SRC -> a4 = Z_to_bv 64 size ->
  evt usegs (zd_dmf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP src size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DDCTX) fc None m (seg_rom usegs)).
