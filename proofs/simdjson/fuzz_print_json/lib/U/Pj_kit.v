(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2 Pj_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma rw_cells_CB_split2 : forall m A (n1 n2 : nat) (bs : list byte), rw_cells usegs m A [CB (n1 + n2) bs] ->
  rw_cells usegs m A [CB n1 (firstn n1 bs)] /\ rw_cells usegs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs H.
  assert (L : length bs = (n1 + n2)%nat) by (destruct H as [[[HL _] _] _]; exact HL).
  assert (H2 : rw_cells usegs m A ([CB n1 (firstn n1 bs)] ++ [CB n2 (skipn n1 bs)])).
  { eapply rw_cells_recast; [exact H| | |].
    - cbn. rewrite firstn_length, skipn_length. repeat split; lia.
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  apply (proj1 (Sj_stage1_kit.rw_cells_app usegs m A _ _)) in H2. cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma rw_cells_join : forall m A cs1 A' cs2, rw_cells usegs m A cs1 -> rw_cells usegs m A' cs2 -> A' = A + Z.of_nat (cells_size cs1) ->
  rw_cells usegs m A (cs1 ++ cs2).
Proof. intros m A cs1 A' cs2 H1 H2 ->. apply Sj_stage1_kit.rw_cells_app. split; assumption. Qed.

Lemma rw_cells_CB_join2 : forall m A (n1 n2 : nat) (b1 b2 : list byte) A',
  rw_cells usegs m A [CB n1 b1] -> rw_cells usegs m A' [CB n2 b2] -> A' = A + Z.of_nat n1 ->
  rw_cells usegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 A' H1 H2 E.
  assert (L1 : length b1 = n1) by (destruct H1 as [[[HL _] _] _]; exact HL).
  assert (L2 : length b2 = n2) by (destruct H2 as [[[HL _] _] _]; exact HL).
  pose proof (rw_cells_join m A [CB n1 b1] A' [CB n2 b2] H1 H2) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J.
  specialize (J E). eapply rw_cells_recast; [exact J| | |].
  - cbn. rewrite length_app. repeat split; lia.
  - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
Qed.

Lemma rw_cells_CB_at : forall m A (n : nat) (bs : list byte) (k : Z), rw_cells usegs m A [CB n bs] -> 0 <= k <= Z.of_nat n ->
  rw_cells usegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)] /\ rw_cells usegs m (A + k) [CB (n - Z.to_nat k) (skipn (Z.to_nat k) bs)].
Proof.
  intros m A n bs k H K. replace n with (Z.to_nat k + (n - Z.to_nat k))%nat in H by lia.
  apply rw_cells_CB_split2 in H. rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma memmove_far_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (1 <= N < 2^63)%Z -> (0 <= Src)%Z -> (Src + N < 2^63)%Z -> (0 <= Dst)%Z -> (Dst + N < 2^63)%Z -> mem_inv usegs m ->
  evt usegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMMOVE_T2) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HS2 HD HD2 MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memmove_far_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA| exact LEN| exact DC| exact SEP| lia| exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postZ in *. rewrite ED, ES, EN in P. exact P.
Qed.

End WithCeiling0.
