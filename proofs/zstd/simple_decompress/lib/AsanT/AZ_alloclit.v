(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdLit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_frame_iface AZ_blk_iface AZ_blk_iface4 AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition zd_alloclit_stmtA2 : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DCTX DST CAP litSize ews : Z) (imm : bool) (h : frame_header) (ws : list word) (lo : Z),
  rw_cells bsegs m (DCTX + 29928) (zfh_cells h) -> 0 <= fh_bsmax h <= 131072 ->
  dctx_h5 bsegs m DCTX ws -> wnth ws H5_isFrameDecompression = Z_to_bv 64 1 ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 -> 0 <= DST -> 0 <= CAP -> DST + CAP < 2^47 ->
  (DST = 0 -> CAP = 0) ->
  0 <= litSize <= ews -> ews = Z.min (fh_bsmax h) CAP -> 0 <= SPV < 2^64 ->
  stk bsegs m lo SPV -> lo <= SPV - 16 -> SPV < 2^47 ->
  (* [comment removed for export] *)
  off_stack lo SPV DCTX 95992 ->
  DCTX mod 8 = 0 -> areg RNG m DCTX 95992 -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 litSize -> a4 = Z_to_bv 64 0 ->
  a5 = Z_to_bv 64 ews -> a6 = Z_to_bv 64 (if imm then 1 else 0) ->
  evtF bsegs RNG (zd_alloclit_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST ws (alloc_lit_buffer (fh_bsmax h) CAP litSize ews imm) lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_ALLOCLIT) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
  Local Ltac al_run DCTX SPV DST CAP litSize ews h dlo chi :=
  kx_autoFLAx [KAUnp DCTX 95992; KAApp (DCTX + 30352) 20; KAApp (SPV - 16) 16] [] 120%nat
    [KZRange SPV 0x10007fff8000 (2^47); KZRange DCTX 0x625000 (2^47 - 95992); KZRange DST dlo (2^47); KZRange CAP 0 chi;
     KZRange (DST + CAP) 0 (2^47 - 1); KZRange litSize 0 131072; KZRange ews 0 131072; KZRange (fh_bsmax h) 0 131072;
     KZAlign DCTX 8;
     KZWr (DCTX + 30352) 20; KZWr (SPV - 16) 16; KZDisj (DCTX + 30352) 20 (SPV - 16) 16;
     KZDisj (DCTX + 30096) 276 (SPV - 16) 16; KZDisj (DCTX + 29928) 48 (SPV - 16) 16]
    [(SPV - 16, 16); (DCTX + 29928, 48); (DCTX + 30096, 276)] [(SPV - 16, 16); (DCTX, 95992)].

Lemma zd_alloclit_proofA2 : zd_alloclit_stmtA2.
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DCTX DST CAP litSize ews imm h ws lo.
  intros FP BSM (H5 & L5) ISF DCL DCH DST0 CAP0 DSTH DZ LSZ EWS SPR ST LOS SPV47 OFS D8 ARD ART AST MI -> -> -> -> -> -> ->.
  unfold off_stack in OFS.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct (ARD ltac:(lia)) as (ABD & UD & RD & RDS). clear ARD.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (DA : DCTX + 95992 <= 0x7fff7000 \/ 0x10007fff8000 <= DCTX) by (unfold ablk, AIMG_HI, KLS in ABD; lia).
  assert (DAL : 0x625000 <= DCTX) by (unfold ablk, AIMG_HI, KLS in ABD; lia).
  assert (MU : munch [(DCTX + 30352, DCTX + 30352 + 20); (SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  unfold zfh_cells in FP.
  h5_open ws L5. lazymatch type of ISF with ?x = _ => subst x end.
  carve_frame 16%nat ST.
  unfold APZD_ALLOCLIT.
  (* [comment removed for export] *)
  destruct (Z.eq_dec DST 0) as [DZ0|DNZ];
    [pose proof (DZ DZ0) as CZ0; subst DST; subst CAP; assert (ews = 0) by lia; subst ews; assert (litSize = 0) by lia; subst litSize;
     destruct imm; al_run DCTX SPV 0 0 0 0 h 0 0
    | destruct imm; al_run DCTX SPV DST CAP litSize ews h 1 (2^47)].
  (* [comment removed for export] *)
  all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
  all: kx_mem.
  all: kx_abs.
  all: zstep.
  all: lazymatch goal with FRc : rw_cells _ ?mc (?S + -16) [_; C8 _], STc : stk _ ?mc ?l (?S + -16) |- _ => release_frame FRc STc S end.
  all: kx_mkR_fold.
  all: apply evtF_done; unfold zd_alloclit_postA.
  all: lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => do 15 eexists; exists mc end.
  all: split; [reflexivity|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: split; [|reflexivity].
  (* [comment removed for export] *)
  all: unfold alloc_lit_buffer, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE.
  all: match goal with |- context [?a <? ?c] =>
         first [ replace (a <? c) with true by (symmetry; apply Z.ltb_lt; lia)
               | replace (a <? c) with false by (symmetry; apply Z.ltb_ge; lia) ] end.
  all: try match goal with |- context [?a <=? 65536] =>
         first [ replace (a <=? 65536) with true by (symmetry; apply Z.leb_le; lia)
               | replace (a <=? 65536) with false by (symmetry; apply Z.leb_gt; lia) ] end.
  all: cbv [h5_placed h5_cells mk_wcells h5_sizes wupd lp_loc lp_base lp_buf lp_end lit_base_addr H5_litBuffer H5_litBufferEnd H5_litBufferLocation ZSTD_split ZSTD_in_dst ZSTD_not_in_dst DCTX_litExtraBuffer].
  all: lazymatch goal with H5c : rw_cells _ ?mc (?D + 30096) ?cs |- rw_cells _ ?mc (?D + 30096) ?cg => replace cg with cs; [exact H5c|] end.
  all: repeat (f_equal; try lia).
Qed.


(* [comment removed for export] *)
Theorem zd_alloclit_proofA : zd_alloclit_stmtA.
Proof. exact zd_alloclit_proofA2. Qed.

End CANSEC1.
