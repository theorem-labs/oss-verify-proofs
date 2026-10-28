(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_frame_iface AZ_block_iface AZ_dframe_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdSepKit.
Import ListNotations.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma dctx_any_transport : forall DCTX W' m1 m2, dctx_any m1 DCTX -> munch W' m1 m2 -> wmono bsegs m1 m2 ->
  disjoint_from W' DCTX 95992 -> dctx_any m2 DCTX.
Proof.
  intros DCTX W' m1 m2 (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                   PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]) MU WM DJ.
  assert (TR : forall A cs, rw_cells bsegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells bsegs m2 A cs).
  { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ | lia | lia]. }
  assert (TS : forall a b, stk bsegs m1 a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk bsegs m2 a b).
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition zd_ddctx_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo DCTX DST CAP SRC : Z) (src : list Z) (size : Z),
  dctx_any m DCTX -> 4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
  rw_cells bsegs m APZD_GOT_TRACE [C8 wz0; C8 wz0] ->
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= size -> size <= zlen src -> size < 2^40 ->
  4096 <= SRC -> SRC + zlen src < 2^47 ->
  stk bsegs m DST (DST + CAP) -> 0 <= CAP -> CAP < 2^40 -> (DST = 0 -> CAP = 0) -> (DST <> 0 -> 4096 <= DST) -> (CAP = 0 -> DST = 0) -> DST + CAP < 2^47 ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - DMF_STACK_A -> SPV < 2^47 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (DST + CAP <= lo \/ SPV <= DST) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (APZD_GOT_TRACE + 16 <= lo \/ SPV <= APZD_GOT_TRACE) ->
  (DST + CAP <= DCTX \/ DCTX + 95992 <= DST) -> (DST + CAP <= SRC \/ SRC + zlen src <= DST) ->
  (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC) ->
  (APZD_GOT_TRACE + 16 <= DCTX \/ DCTX + 95992 <= APZD_GOT_TRACE) -> (APZD_GOT_TRACE + 16 <= DST \/ DST + CAP <= APZD_GOT_TRACE) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV DMF_DEPTH -> tp = Z_to_bv 64 ATP ->
  azstk RNG m lo SPV ->
  aro_client RNG m ->
  areg RNG m SRC (zlen src) -> (0 < zlen src -> ainimg LB SRC (zlen src)) -> (0 < zlen src -> ahull RNG m SRC (zlen src)) -> DCTX mod 8 = 0 -> areg RNG m DCTX 95992 -> ahull RNG m DCTX 95992 -> ainblk LB DCTX 95992 ->
  (0 < CAP -> areg RNG m DST CAP /\ ahull RNG m DST CAP /\ ainblk LB DST CAP) ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 SRC -> a4 = Z_to_bv 64 size ->
  evtF bsegs RNG (zd_dmf_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP src size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_DDCTX) fc None m (seg_rom bsegs)).
End StmtsF.
End CANSEC1.
