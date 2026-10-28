(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_cache_defs R_glue_defs R_quar_defs R_qrec_defs R_qput R_qdrain R_qmerge R_qrecycle R_qmerge3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Lemma qrec_A_spec_closed : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (CACHE STACK : word) (MIN SB lo : Z) (gl : list batch),
  qcache_rep m QG gl -> qwf SB gl -> (qbytes gl < 2^56)%Z -> (0 <= MIN < 2^63)%Z -> (0 < SB)%Z -> q_lock m 0 1 ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 96)%Z -> (r24 SB + 2^32 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qrec_E_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 CACHE STACK F fc
               ([(q_lockw, q_lockw + 4); (QG, QG + 32); (bv_unsigned sp - 96, bv_unsigned sp)] ++ bivs gl)%Z
               (rec_x gl MIN) (rec_r gl MIN) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qrecycle_entry) fc None m (seg_rom bsegs)).
Proof. intros. eapply qrec_A_spec; [exact merge_spec| eassumption ..]. Qed.
