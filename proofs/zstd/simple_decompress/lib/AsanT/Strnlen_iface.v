(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition strnlen_i_entry : Z := 0x44518.
Definition STRNLEN_I_DEPTH : Z := 4400.

(* [comment removed for export] *)
Definition strnlen_rl (n : Z) (buf : list byte) : Z :=
  match find_byte 0 (firstn (Z.to_nat n) buf) with Some j => Z.of_nat j + 1 | None => n end.

Lemma strnlen_rl_res : forall n buf, 0 <= n -> strnlen_rl n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
  intros n buf Hn. unfold strnlen_rl, strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
  pose proof (find_byte_Some _ _ _ E) as [Hj _]. rewrite length_firstn in Hj. lia.
Qed.

(* [comment removed for export] *)
Lemma strnlen_rl_cstr : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> 0 <= n ->
  strnlen_rl n (str ++ Z_to_bv 8 0 :: slack) = Z.min (Z.of_nat (length str) + 1) n.
Proof.
  intros n str slack NONUL Hn. unfold strnlen_rl. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n).
  - rewrite (find_byte_cstr 0 n str slack NONUL) by lia. lia.
  - rewrite (find_byte_cstr_short 0 n str slack NONUL) by lia. lia.
Qed.

Definition strnlen_a_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - STRNLEN_I_DEPTH, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ bytes_at bsegs m' P buf.

Definition strnlen_a_stmt : Prop :=
  forall (RNG : footprint) (r : region)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n : Z) (buf : list byte) (lo : Z),
    a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 n -> 0 < P -> 0 <= n < 2^64 ->
    bytes_at bsegs m P buf -> memchr_ok P 0 n buf ->
    mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STRNLEN_I_DEPTH -> KHIGH <= lo ->
    (P + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= P) ->
    (* [comment removed for export] *)
    ashenv m -> rclean m r -> inreg r P (strnlen_rl n buf) -> strnlen_rl n buf <= 2^40 ->
    (* [comment removed for export] *)
    rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG P (Z.of_nat (length buf)) -> rrng RNG r ->
    evtF bsegs RNG (strnlen_a_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P n buf lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 strnlen_i_entry) fc None m (seg_rom bsegs)).
End CANSEC1.
