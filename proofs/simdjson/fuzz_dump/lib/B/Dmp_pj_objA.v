(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_objwA Atp_objnA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA Dmp_pj_strA Dmp_pj_arrA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac clear_shrd := repeat match goal with H : ov_read_bytes _ _ _ 1 = Some [Z_to_bv 8 0] |- _ => clear H end.


Definition DMP_LIT_RBRC_A : Z := 0x235e0.   Definition DMP_LIT_QUOT_A : Z := 0x235a0.   Definition DMP_LIT_QCOL_A : Z := 0x235c0.
Definition DMP_PJ_OHEAD_A : Z := 0xaefb4.
Definition DMP_PJ_OTEST_A : Z := 0xaf8e0.

Definition pj_oframe (E : aenvA) (f e osp : Z) : list cell :=
  [C8 (Z_to_bv 64 DMP_LIT_RBRC_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 0x100000001);
   C8 (Z_to_bv 64 0x4020200); C8 (Z_to_bv 64 DMP_LIT_QCOL_A); C8 (Z_to_bv 64 DMP_LIT_QUOT_A); C8 (Z_to_bv 64 e);
   C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)].

Definition pjRO (E : aenvA) (q f kk : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s10 t0 t1 t2 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (2^56 - 1)) (Z_to_bv 64 (ae_DOC E + 8)) s4 (Z_to_bv 64 (shad (ae_DOC E + 8))) (Z_to_bv 64 kk) (Z_to_bv 64 (ae_DOC E))
      s8 (Z_to_bv 64 SHB) s10 (Z_to_bv 64 (shad f)) t3 t4 t5 t6.
