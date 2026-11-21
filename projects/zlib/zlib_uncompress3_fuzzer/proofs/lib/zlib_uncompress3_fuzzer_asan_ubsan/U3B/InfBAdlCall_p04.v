(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface U2BCall InfBBase InfBKit AdlUBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BKit U2BKit_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Lemma seq_split_nth : forall (a k : nat), seq a (S k) = a :: seq (S a) k. Proof. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.

Lemma f8arr_sub_bytes : forall m A n f (a k : nat), f8arr bsegs m A n f -> (a + k <= n)%nat ->
  bytes_at bsegs m (A + Z.of_nat a) (map (Z_to_bv 8) (map (fun i => f (Z.of_nat i)) (seq a k))).
Proof.
  intros m A n f a k [(H0 & H1 & HB) _] Hk. rewrite length_map, length_seq in H1.
  split; [lia|]. split; [rewrite !length_map, length_seq; lia|].
  intros i Hi. rewrite !length_map, length_seq in Hi.
  replace (A + Z.of_nat a + Z.of_nat i) with (A + Z.of_nat (a + i)) by lia.
  rewrite (HB (a + i)%nat) by (rewrite length_map, length_seq; lia).
  rewrite !nth_error_map. rewrite !nth_error_seq.
  destruct (Nat.ltb_spec (a + i) n) as [X|X]; [| lia]. destruct (Nat.ltb_spec i k) as [Y|Y]; [| lia]. cbn. reflexivity.
Qed.

Definition adl_postz (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (res : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPV - 176, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV.

Lemma adler32_callz : adler32_stmtU ->
  forall (lo : Z) (bs : list Z) (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV adler A v : Z),
  0 <= SPV < 2^64 ->
  mem_inv bsegs m ->
  stk bsegs m lo SPV -> lo <= SPV - 176 -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  0 <= adler < 2^64 -> 1 <= A -> A + Z.of_nat (length bs) <= lo ->
  0 <= v < 2^64 -> v mod 2^32 = Z.of_nat (length bs) ->
  bytes_at bsegs m A (map (Z_to_bv 8) bs) -> Forall (fun b => 0 <= b < 256) bs ->
  unpoisoned m A (A + Z.of_nat (length bs)) ->
  rng RNG A (Z.of_nat (length bs)) ->
  (A < A + Z.of_nat (length bs) -> rng RNG (shad A) (shad (A + Z.of_nat (length bs) - 1) + 1 - shad A)) ->
  rng_aimg RNG -> rng RNG lo (SPV - lo) ->
  evtF bsegs RNG (adl_postz ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 adler) (Z_to_bv 64 A) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 A_ADLER32) fc None m (seg_rom bsegs)).
Proof.
  intros ADL. intros until v. intros RS. intros.
  eapply evtF_mono; [eapply (ADL RNG _ (Z_to_bv 64 SPV) _ _ _ _ _ _ _ (Z_to_bv 64 adler) (Z_to_bv 64 A) (Z_to_bv 64 v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo adler A v bs);
                     rewrite ?unsigned_lit by lia; try eassumption; reflexivity|].
  cbv beta. unfold adl_postU, adl_postz, ADL_STACK. rewrite !unsigned_lit by lia. intros ms' PO. exact PO.
Qed.

End CANSEC1.
