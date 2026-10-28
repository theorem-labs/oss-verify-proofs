(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_new Sj_h_dtor Sj_h_alloc Atp_fzwA Atp_pidwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation PIREGT ra sp gp tp t0 t1 t2 RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6 :=
  (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1v
       a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) s6v s7v s8v (Z_to_bv 64 (P + 24))
       (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) (only parsing).

Lemma pi_walk4s : forall (RES P d len cap : Z) (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= len < 3 ->
  evt bsegs (eq (MS (PIREGT (Z_to_bv 64 0xafcd0) sp gp tp t0 t1 t2 RES P d len (Z_to_bv 64 3) (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7
                           s1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3 t4 t5 t6)
                    F (Z_to_bv 64 0xafa8c) fc None m (seg_rom bsegs)))
    (MS (PIREGT (Z_to_bv 64 0xafcd0) sp gp tp t0 t1 t2 RES P d len (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                s1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3 t4 t5 t6)
        F (Z_to_bv 64 0xafcd0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LEN.
  zstep. zstep. if_false.
  zstep. zstep. if_false.
  zstep. if_false.
  zstep. zstep. if_true.
  zstep. if_true.
  zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk4m : forall (RES P d len cap : Z) (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  3 <= len < 2^63 ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0xafa7c) sp gp tp t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 3)
                   (Z_to_bv 64 d) (Z_to_bv 64 0x235e0) (Z_to_bv 64 3) a3 a4 a5 a6 a7
                   (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc e_memcmp m))
    (MS (PIREGT (Z_to_bv 64 0xafcd0) sp gp tp t0 t1 t2 RES P d len (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                s1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3 t4 t5 t6)
        F (Z_to_bv 64 0xafcd0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LEN.
  unfold entry_st, e_memcmp in *.
  zstep. zstep. if_false.
  zstep. zstep. if_false.
  zstep. if_false.
  zstep. zstep. if_true.
  zstep. if_true.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pi_walk8c : forall (RES P len copy cap : Z) (r : word)
    (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  3 <= len < 2^63 -> 0 < copy -> copy + len < 2^63 ->
  evt bsegs (fun ms => exists BUF blen, ((BUF = copy /\ blen = len) \/ (BUF = copy + 3 /\ blen = len - 3)) /\
                ms = MS (PIREGT (Z_to_bv 64 0xafa7c) sp gp tp t0 t1 t2 RES P BUF blen r a1 a2 a3 a4 a5 a6 a7
                                (Z_to_bv 64 3) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3 t4 t5 t6)
                        F (Z_to_bv 64 0xafa8c) fc None m (seg_rom bsegs))
    (MS (PIREGT (Z_to_bv 64 0xafa7c) sp gp tp t0 t1 t2 RES P copy len r a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 3) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3 t4 t5 t6)
        F (Z_to_bv 64 0xafa7c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LEN C0 CH.
  zstep. if_cases K.
  - apply evt_done. exists copy, len. split; [left; split; reflexivity|]. cbv delta [mkR]. reflexivity.
  - zstep. zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. zstep.
    apply evt_done. exists (copy + 3), (len - 3). split; [right; split; reflexivity|]. cbv delta [mkR]. reflexivity.
Qed.
