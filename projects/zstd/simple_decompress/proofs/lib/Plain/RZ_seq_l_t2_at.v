(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition t2_brk (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x11 x12 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  LEND < LP + llv ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 LP) (Z_to_bv 64 LEND) x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) (Z_to_bv 64 llv) (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (y_nbSeq P)) x25 x26 (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18d00) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition t2_sw0 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 < llv < 2^18 ->
  0 <= mlv < 2^18 ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) (Z_to_bv 64 llv) (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (y_nbSeq P)) x25 (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18ff4) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition t2_sw (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  0 < lft < llv ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 lft) x25 (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18fe4) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition t2_cpA (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft en cur src : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  en = OP + lft ->
  en <= OEND ->
  OP <= cur < en ->
  src = LP + (cur - OP) ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 src) x10 x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 lft) x25 (Z_to_bv 64 en) (Z_to_bv 64 cur) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18d9c) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition t2_cpB (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft en cur src rem : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x11 x12 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  en = OP + lft ->
  en <= OEND ->
  OP <= cur < en ->
  src = LP + (cur - OP) ->
  rem = en - cur ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 src) (Z_to_bv 64 rem) x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 lft) (Z_to_bv 64 cur) (Z_to_bv 64 en) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18fc8) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition t2_w1 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft en wend wlen : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  en = OP + lft ->
  en <= OEND ->
  wend = en - 32 ->
  OP <= wend ->
  wlen = wend - OP ->
  17 <= LP - OP ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 LP) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 wlen) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 lft) (Z_to_bv 64 wend) (Z_to_bv 64 en) (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18d50) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition t2_wl (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft en wend wlen cur srcp : Z) (idx cidx raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  en = OP + lft ->
  en <= OEND ->
  wend = en - 32 ->
  wlen = wend - OP ->
  17 <= wend - OP ->
  OP + 16 <= cur < wend ->
  srcp = LP + (cur - OP) + 16 ->
  17 <= LP - OP ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 cur) (Z_to_bv 64 LP) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 idx) (Z_to_bv 64 srcp) (Z_to_bv 64 wlen) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 lft) (Z_to_bv 64 wend) (Z_to_bv 64 en) (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18d60) (y_fc P) None m1 (seg_rom psegs)).

