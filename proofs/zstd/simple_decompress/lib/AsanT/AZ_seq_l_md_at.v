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
Definition md_head (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c96 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z)  (sn : Z) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x27 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) c96 (Z_to_bv 64 ((l_DCTX P + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 c320 c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  sql_ring_ok 8 rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR (Z_to_bv 64 sn) (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) x20 (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 LEND) x27 x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8ae50) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition md_tbl (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML : Z) (sn : Z) (x10 x12 x24 x27 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 vML) (Z_to_bv 64 ((l_DCTX P + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 c320 c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  sql_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  sql_ring_ok 8 rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR (Z_to_bv 64 sn) (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) (Z_to_bv 64 bLL) (Z_to_bv 64 aML) (Z_to_bv 64 aOF) (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 bOF) x12 (Z_to_bv 64 nOF) (Z_to_bv 64 nML) (Z_to_bv 64 nLL) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 vLL) x24 (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 LEND) x27 (Z_to_bv 64 vOF) x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8afcc) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition md_tbl_sel (sel : Z -> Prop) (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML : Z) (sn : Z) (x10 x12 x24 x27 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 vML) (Z_to_bv 64 ((l_DCTX P + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 c320 c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  sql_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  sql_ring_ok 8 rl rm ro ->
  sel aOF ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR (Z_to_bv 64 sn) (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) (Z_to_bv 64 bLL) (Z_to_bv 64 aML) (Z_to_bv 64 aOF) (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 bOF) x12 (Z_to_bv 64 nOF) (Z_to_bv 64 nML) (Z_to_bv 64 nLL) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 vLL) x24 (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 LEND) x27 (Z_to_bv 64 vOF) x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8afcc) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition md_dec (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c264 c304 c312 c328 c336 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (ofs : word) (sn : Z) (x10 x12 x27 x28 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 mlv) (Z_to_bv 64 ((l_DCTX P + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 ofs c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  sql_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  sql_ring_ok 8 rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR (Z_to_bv 64 sn) (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) (Z_to_bv 64 bLL) (Z_to_bv 64 aML) (Z_to_bv 64 aOF) (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 bOF) x12 (Z_to_bv 64 nOF) (Z_to_bv 64 nML) (Z_to_bv 64 nLL) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 vLL) ofs (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 LEND) x27 x28 (Z_to_bv 64 139648) x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b038) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition md_rl1 (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c264 c304 c312 c328 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (ofs : word) (sn : Z) (x6 x7 x10 x12 x27 x28 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 mlv) (Z_to_bv 64 ((l_DCTX P + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 ofs c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  sql_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  sql_ring_ok 8 rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR (Z_to_bv 64 sn) (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) (Z_to_bv 64 bLL) x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 bOF) x12 (Z_to_bv 64 nOF) (Z_to_bv 64 nML) (Z_to_bv 64 nLL) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 vLL) ofs (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 LEND) x27 x28 (Z_to_bv 64 139648) x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b04c) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition md_upd (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c264 c304 c312 c328 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x27 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 mlv) (Z_to_bv 64 ((l_DCTX P + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 (Z_to_bv 64 ofs) c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  sql_ring_ok 8 rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR (Z_to_bv 64 sn) (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) x20 (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 llv) (Z_to_bv 64 ofs) (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 LEND) x27 x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b128) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition md_exec (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c248 c264 c304 c312 c328 c352 c368 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn : Z) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x27 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 mlv) (Z_to_bv 64 ((l_DCTX P + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 (Z_to_bv 64 ofs) c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  sql_ring_ok 8 rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR (Z_to_bv 64 sn) (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) x20 (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 llv) (Z_to_bv 64 ofs) (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 LEND) x27 x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8b288) (l_fc P) None m1 (seg_rom bsegs)).

End CANSEC1.
