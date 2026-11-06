(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition strnlen_i_entry : Z := 0x42b80.
Definition STRNLEN_I_DEPTH : Z := 4400.
Definition strnlen_rl (n : Z) (buf : list byte) : Z :=
match find_byte 0 (firstn (Z.to_nat n) buf) with Some j => Z.of_nat j + 1 | None => n end.
#[using="Type"] Lemma strnlen_rl_res : forall n buf, 0 <= n -> strnlen_rl n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
intros n buf Hn. unfold strnlen_rl, strnlen_res.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=48608725705.562614946141.7000001005SS2Hj".
destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
pose proof (find_byte_Some _ _ _ E) as [Hj _]. rewrite length_firstn in Hj. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma strnlen_rl_cstr : forall n (str slack : list byte), ~ In (Z_to_bv 8 0) str -> 0 <= n ->
strnlen_rl n (str ++ Z_to_bv 8 0 :: slack) = Z.min (Z.of_nat (length str) + 1) n.
Proof.
intros n str slack NONUL Hn. unfold strnlen_rl. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n).
- Local Ltac2 Set LiaHints.tbl := fun () => "0040=16727155002.728169580680.732020963942.77261295007.7 00000300600900<S1HS1HS1HS1H".
rewrite (find_byte_cstr 0 n str slack NONUL) by lia. lia.
- rewrite (find_byte_cstr_short 0 n str slack NONUL) by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
ashenv m -> rclean m r -> inreg r P (strnlen_rl n buf) -> strnlen_rl n buf <= 2^40 ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG P (Z.of_nat (length buf)) -> rrng RNG r ->
evtF bsegs RNG (strnlen_a_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 strnlen_i_entry) fc None m (seg_rom bsegs)).
End CANSEC1.
