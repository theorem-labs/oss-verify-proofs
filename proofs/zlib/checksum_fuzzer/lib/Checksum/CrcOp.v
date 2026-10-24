(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Functional multiplication loop adapted from the pinned Varnish proof to
    the actual zlib checksum_fuzzer instruction layout and register allocation. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Img0 CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.transport_chunks segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.footprint_after_store segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.transport_after_call segs m m' MU WM ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.addr_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.mlia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require StepFast.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.step_core segs R F pc fc rv m ro ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.zstep ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Destzna.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_exs PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_exs PO.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_ands PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require WeqGuard TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.WeqGuard.weq_guard; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Stor0fe.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Dieta54.
Local Ltac lia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Dieta54.dlia.
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcWord CrcGen CrcOpInner.

Definition combine_op_model (c1 c2 op : Z) : Z := Z.lxor c2 (mm op c1).
Lemma combine_op_model_range : forall c1 c2 op,
  (0 <= c1 < 2^32)%Z -> (0 <= c2 < 2^32)%Z ->
  (0 <= combine_op_model c1 c2 op < 2^32)%Z.
Proof. intros c1 c2 op H1 H2. apply lxor_bound; try lia. apply mm_range; exact H1. Qed.
Opaque mm_loop.

Theorem crc32_combine_op_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  (bv_unsigned a0 < 2^32)%Z -> (bv_unsigned a1 < 2^32)%Z ->
  (0 < bv_unsigned a2 < 2^32)%Z ->
  evt rsegs (combine_gen_post (combine_op_model (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2))
     ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d6c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI H1 H2 HOP.
  pose proof (bv_unsigned_in_range _ a0) as R0.
  pose proof (bv_unsigned_in_range _ a1) as R1.
  pose proof (bv_unsigned_in_range _ a2) as R2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  remember (combine_op_model (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)) as answer eqn:Eanswer.
  do 5 zstep.
  rewrite <- (Z_to_bv_bv_unsigned a0).
  rewrite <- (Z_to_bv_bv_unsigned a2).
  replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (-306674912)) with (Z_to_bv 64 18446744073402876704) by (apply bv_eq; reflexivity).
  eapply op_inner with (k:=31%nat) (a:=bv_unsigned a2)
    (B:=bv_unsigned a0) (b:=bv_unsigned a0) (P:=0%Z) (p:=0%Z);
    [exact HOP|lia|rewrite Z.mod_small by lia; reflexivity|lia|lia|reflexivity|lia|lia|apply lowbits_nz_init; lia|].
  intros B' P' x14' x16' HP EP.
  do 4 zstep.
  assert (NARROW : (Z.lxor (bv_unsigned a1) P' mod 4294967296 = answer)%Z).
  { change 4294967296%Z with (2^32)%Z. rewrite low32_xor, EP.
    rewrite (Z.mod_small (bv_unsigned a1) (2^32)) by lia.
    unfold combine_op_model in Eanswer. symmetry. exact Eanswer. }
  rewrite NARROW. finish.
Qed.

(** The operator reads no memory: arbitrary overlay memories are preserved. *)
Theorem crc32_combine_op_any_memory_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (bv_unsigned a0 < 2^32)%Z -> (bv_unsigned a1 < 2^32)%Z ->
  (0 < bv_unsigned a2 < 2^32)%Z ->
  evt rsegs (crc_return_post (combine_op_model (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2))
     ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d6c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros H1 H2 HOP.
  pose proof (bv_unsigned_in_range _ a0) as R0.
  pose proof (bv_unsigned_in_range _ a1) as R1.
  pose proof (bv_unsigned_in_range _ a2) as R2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  remember (combine_op_model (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)) as answer eqn:Eanswer.
  do 5 zstep.
  rewrite <- (Z_to_bv_bv_unsigned a0).
  rewrite <- (Z_to_bv_bv_unsigned a2).
  replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (-306674912)) with (Z_to_bv 64 18446744073402876704) by (apply bv_eq; reflexivity).
  eapply op_inner with (k:=31%nat) (a:=bv_unsigned a2)
    (B:=bv_unsigned a0) (b:=bv_unsigned a0) (P:=0%Z) (p:=0%Z);
    [exact HOP|lia|rewrite Z.mod_small by lia; reflexivity|lia|lia|reflexivity|lia|lia|apply lowbits_nz_init; lia|].
  intros B' P' x14' x16' HP EP.
  do 4 zstep.
  assert (NARROW : (Z.lxor (bv_unsigned a1) P' mod 4294967296 = answer)%Z).
  { change 4294967296%Z with (2^32)%Z. rewrite low32_xor, EP.
    rewrite (Z.mod_small (bv_unsigned a1) (2^32)) by lia.
    unfold combine_op_model in Eanswer. symmetry. exact Eanswer. }
  rewrite NARROW. finish.
Qed.
