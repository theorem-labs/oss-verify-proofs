(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes ZBridge Tac InitMem SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AArr U2ABlob UwAKit U2cA_glue.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U3A Require Import U2AObj U2AIface InfABase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Out.
Variable segs : list Segment.

Lemma out_open : forall m OB osz fo k j,
  f8arr segs m OB (Z.to_nat osz) fo -> 0 <= k -> 0 <= j -> k + j <= osz ->
  exists b1 b2 b3, rw_cells segs m OB [CB (Z.to_nat k) b1] /\ rw_cells segs m (OB + k) [CB (Z.to_nat j) b2]
                   /\ rw_cells segs m (OB + k + j) [CB (Z.to_nat (osz - k - j)) b3].
Proof.
  intros m OB osz fo k j [HB HW] K0 J0 KJ. rewrite length_map, length_seq in HW.
  apply (blob_split3 segs m OB osz (map (fun i => Z_to_bv 8 (fo (Z.of_nat i))) (seq 0 (Z.to_nat osz))) k j); [| exact K0| exact J0| exact KJ].
  split; [split|].
  - cbn. split; [rewrite length_map, length_seq; reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma out_close : forall m OB osz k j b1 b2 b3,
  0 <= k -> 0 <= j -> k + j <= osz ->
  rw_cells segs m OB [CB (Z.to_nat k) b1] -> rw_cells segs m (OB + k) [CB (Z.to_nat j) b2] ->
  rw_cells segs m (OB + k + j) [CB (Z.to_nat (osz - k - j)) b3] ->
  exists fo', f8arr segs m OB (Z.to_nat osz) fo' /\ forall i, 0 <= fo' i < 256.
Proof.
  intros m OB osz k j b1 b2 b3 K0 J0 KJ H1 H2 H3.
  pose proof (blob_join3 segs m OB osz k j b1 b2 b3 K0 J0 KJ H1 H2 H3) as X.
  exact (f8arr_of_blob segs m OB (Z.to_nat osz) _ X).
Qed.

Lemma out_open1 : forall m OB osz fo k P,
  f8arr segs m OB (Z.to_nat osz) fo -> 0 <= k -> k + 1 <= osz -> P = OB + k ->
  exists b1 b b3, rw_cells segs m OB [CB (Z.to_nat k) b1] /\ rw_cells segs m P [C1 b]
                  /\ rw_cells segs m (P + 1) [CB (Z.to_nat (osz - k - 1)) b3].
Proof.
  intros m OB osz fo k P H K0 K1 ->. destruct (out_open m OB osz fo k 1 H K0 ltac:(lia) K1) as (b1 & b2 & b3 & H1 & H2 & H3).
  pose proof H2 as [[WF _] _]. cbn in WF. destruct WF as [HL _]. destruct b2 as [|b [|c b2]]; try discriminate HL.
  exists b1, b, b3. split; [exact H1|]. split; [| exact H3].
  eapply rw_cells_recast; [exact H2| cbn; split; exact I| reflexivity| reflexivity].
Qed.

Lemma out_close1 : forall m OB osz k P b1 b b3,
  0 <= k -> k + 1 <= osz -> P = OB + k ->
  rw_cells segs m OB [CB (Z.to_nat k) b1] -> rw_cells segs m P [C1 b] -> rw_cells segs m (P + 1) [CB (Z.to_nat (osz - k - 1)) b3] ->
  exists fo', f8arr segs m OB (Z.to_nat osz) fo' /\ forall i, 0 <= fo' i < 256.
Proof.
  intros m OB osz k P b1 b b3 K0 K1 -> H1 H2 H3.
  eapply (out_close m OB osz k 1 b1 [b] b3 K0 ltac:(lia) K1 H1); [| exact H3].
  eapply rw_cells_recast; [exact H2| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
Qed.

Lemma bytes_at_mid : forall m A bs k j, bytes_at segs m A bs -> (k + j <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn j (skipn k bs)) /\ length (firstn j (skipn k bs)) = j.
Proof.
  intros m A bs k j H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn j (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _].
  split; [exact H|]. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma out_write : forall m OB N fo i bs,
  f8arr segs m OB N fo -> 0 <= i < Z.of_nat N -> length bs = 1%nat ->
  exists fo', f8arr segs (write_to_mem m (wa (OB + i)) bs) OB N fo' /\ forall j, 0 <= fo' j < 256.
Proof.
  intros m OB N fo i bs H Hi HL. destruct bs as [|b [|c bs]]; try discriminate HL. unfold f8arr in H.
  pose proof (u8arr_write segs m OB _ i b H ltac:(rewrite length_map, length_seq; exact Hi)) as [HB HW].
  rewrite upd_length, length_map, length_seq in HW.
  apply (f8arr_of_blob segs _ OB N (upd (map (fun k => Z_to_bv 8 (fo (Z.of_nat k))) (seq 0 N)) (Z.to_nat i) b)).
  split; [split|].
  - cbn. split; [rewrite upd_length, length_map, length_seq; reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.
End Out.

Section CANSEC1. Context {rc : runConstT}.
Lemma pay_out_sep : forall cx ly AI RNG LB, inf_ctx cx ly AI RNG LB ->
  exists c : Z, 0 <= c <= 1 /\ c_q cx + c_n cx <= 6336512 + c * 2^48 /\ 6598656 <= c_q cx + (1 - c) * 2^48.
Proof.
  intros cx ly AI RNG LB CTX. unfold inf_ctx in CTX.
  destruct CTX as (_ & _ & (ps & _ & PD) & REST).
  assert (LBA : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)).
  { repeat (let X := fresh in destruct REST as [X REST]). exact REST. }
  atop_facts.
  destruct PD as [(pd & PDI & NP & _)|(N0 & DE)].
  - pose proof (ablk_lin _ _ (LBA _ PDI)) as (A1 & A2 & A3 & A4). cbn [ab_addr ab_size] in *. unfold AIMG_HI in A1. exists 1. lia.
  - exists 0. rewrite N0, DE. lia.
Qed.

Lemma blk_hull : forall (m : word -> option byte) RNG A n RLO RHI,
  ablk A (A + n) -> 0 <= n ->
  RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= A -> A + n + 64 <= RHI ->
  rng RNG (shad RLO) (shlen (RHI - RLO)) -> wr_at asegs m (shad RLO) (shlen (RHI - RLO)) ->
  let WLO := A / 64 * 64 in let WHI := (A + n + 63) / 64 * 64 in
  (WLO <= A /\ A + n <= WHI /\ WLO mod 64 = 0 /\ WHI mod 64 = 0 /\ 0 <= WLO /\ WHI <= KEND)
  /\ rng RNG (shad WLO) (shad WHI - shad WLO) /\ wr_at asegs m (shad WLO) (shad WHI - shad WLO).
Proof.
  intros m RNG A n RLO RHI WB N0 R1 R2 R3 R4 RR RW WLO WHI.
  pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1. atop_facts.
  assert (A1 : WLO <= A /\ A - 64 < WLO /\ WLO mod 64 = 0) by (subst WLO; Z.div_mod_to_equations; lia).
  assert (A2 : A + n <= WHI /\ WHI < A + n + 64 /\ WHI mod 64 = 0) by (subst WHI; Z.div_mod_to_equations; lia).
  split; [unfold KEND; lia|].
  unfold shlen in *. rewrite !shad_div. rewrite shad_div in RR, RW. rewrite Z.shiftr_div_pow2 in RR, RW by lia. change (2^3) with 8 in RR, RW.
  split.
  - eapply rng_sub'; [exact RR|]. Z.div_mod_to_equations. lia.
  - eapply wr_at_sub; [exact RW|..]; Z.div_mod_to_equations; lia.
Qed.
End CANSEC1.
