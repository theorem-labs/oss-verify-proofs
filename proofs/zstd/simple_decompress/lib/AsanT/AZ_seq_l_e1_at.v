(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_xat.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition e1_exec (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c304 c352 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x25 x26 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) c304 (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) c352 (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  LP = LLO ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 raddr) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 LP) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) x25 x26 (Z_to_bv 64 llv) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b6f0) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_execb (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c304 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x25 x26 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) c304 (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ile = LP + llv ->
  ile <= LEND ->
  LP = LLO ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 raddr) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 LP) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) x25 x26 (Z_to_bv 64 llv) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b6f8) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_slow (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c304 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) c304 (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) x19 (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) x25 x26 (Z_to_bv 64 llv) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8bae4) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_lit1 (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 sl) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) x25 (Z_to_bv 64 ole) (Z_to_bv 64 llv) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b720) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_litloop (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 sl) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 src) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) (Z_to_bv 64 cur) (Z_to_bv 64 ole) (Z_to_bv 64 llv) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8bdb8) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_match (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 sl) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) x25 (Z_to_bv 64 ole) (Z_to_bv 64 llv) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b728) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_tail (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (r : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 r) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_PFX P)) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 x24 x25 x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b7fc) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_stail (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c304 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (r : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) c304 (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) x19 (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 x24 x25 x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8bb14) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_ltail (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (r : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 r) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) c376 (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 (l_DCTX P)) (Z_to_bv 64 (l_nbSeq P)) (Z_to_bv 64 (l_FF P)) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b80c) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_matloop (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (mtc : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 sl) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sql_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - l_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  mtc = ole - ofs ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) c376 (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 src) (Z_to_bv 64 ome) x25 (Z_to_bv 64 cur) x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b7b4) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_close (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (dpx : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 sl) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sql_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - l_PFX P ->
  mtc = ole - ofs ->
  dpx = ole - l_PFX P ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_PFX P)) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) (Z_to_bv 64 mtc) (Z_to_bv 64 ole) x27 (Z_to_bv 64 dpx) x29 x30 x31) (l_F P) (Z_to_bv 64 0x8c208) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_close_sel (sel : Z -> Prop) (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (dpx : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 sl) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sql_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - l_PFX P ->
  mtc = ole - ofs ->
  dpx = ole - l_PFX P ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  sel ofs ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_PFX P)) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) (Z_to_bv 64 mtc) (Z_to_bv 64 ole) x27 (Z_to_bv 64 dpx) x29 x30 x31) (l_F P) (Z_to_bv 64 0x8c208) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_close8 (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl rip8 : Z) (ofs dpx : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 sl) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sql_mfast P OEND OP ole mlv sl ->
  l_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  0 <= ofs <= ole - l_PFX P ->
  dpx = ole - l_PFX P ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_PFX P)) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) (Z_to_bv 64 rip8) (Z_to_bv 64 ole) x27 (Z_to_bv 64 dpx) x29 x30 x31) (l_F P) (Z_to_bv 64 0x8c724) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition e1_closeloop (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (j va0 va1 va4 vr8 sh5 sh6 : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x12 x17 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 (Z_to_bv 64 raddr) (Z_to_bv 64 sl) (Z_to_bv 64 dof) (Z_to_bv 64 dof) (Z_to_bv 64 sn) (Z_to_bv 64 139648) (Z_to_bv 64 OP) (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sql_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  l_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  va0 = ole + 8 ->
  va1 = rsrc - j ->
  va4 = ole ->
  vr8 = rsrc - j - 8 ->
  cur = ole + 8 + j ->
  sh5 = 2147450880 + cur / 8 ->
  sh6 = 2147450880 + rsrc / 8 ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 va0) (Z_to_bv 64 va1) x12 (Z_to_bv 64 j) (Z_to_bv 64 va4) (Z_to_bv 64 sh5) (Z_to_bv 64 sh6) x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 ome) (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 vr8) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8c76c) (l_fc P) None m1 (seg_rom bsegs)).

End CANSEC1.
