(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_recastK : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_cells_CB_joinK : forall m A n1 n2 (b1 b2 : list byte),
  rw_cells asegs m A [CB n1 b1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 b2] -> rw_cells asegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  destruct H1 as [[W1 B1] X1]. destruct H2 as [[W2 B2] X2]. cbn in W1, W2. destruct W1 as [L1 _]. destruct W2 as [L2 _].
  apply (rw_cells_recastK m A [CB n1 b1; CB n2 b2]).
  - apply (proj2 (rw_cells_app asegs m A [CB n1 b1] [CB n2 b2])). cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    split; [split; [split; [cbn; auto| exact B1]| exact X1] | split; [split; [cbn; auto| exact B2]| exact X2]].
  - cbn. rewrite length_app. repeat split; try lia; exact I.
  - cbn. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma rw_cells_CB_splitK : forall m A n (n1 : nat) (b : list byte),
  rw_cells asegs m A [CB n b] -> (n1 <= n)%nat ->
  rw_cells asegs m A [CB n1 (firstn n1 b)] /\ rw_cells asegs m (A + Z.of_nat n1) [CB (n - n1)%nat (skipn n1 b)].
Proof.
  intros m A n n1 b H Hn.
  destruct H as [[W B] X]. cbn in W. destruct W as [L _].
  assert (H' : rw_cells asegs m A [CB n1 (firstn n1 b); CB (n - n1)%nat (skipn n1 b)]).
  { apply (rw_cells_recastK m A [CB n b]).
    - split; [split; [cbn; auto| exact B]| exact X].
    - cbn. rewrite length_firstn, length_skipn. repeat split; try lia; exact I.
    - cbn. rewrite ?app_nil_r, firstn_skipn. reflexivity. }
  apply (proj1 (rw_cells_app asegs m A [CB n1 (firstn n1 b)] [CB (n - n1)%nat (skipn n1 b)])) in H'.
  cbn [cells_size csize Nat.add] in H'. rewrite Nat.add_0_r in H'. exact H'.
Qed.

Lemma align_frame_gen : forall m lo B q' (lowc rest : list cell) (K : nat),
  stk asegs m lo B -> lo + 16 <= B ->
  rw_cells asegs m B (lowc ++ rest) -> cells_size lowc = K -> (16 <= K)%nat ->
  (q' = B \/ q' = B - 16) ->
  stk asegs m lo q' /\ (exists jq, rw_cells asegs m q' [CB K jq]) /\ stk asegs m (q' + Z.of_nat K) (B + Z.of_nat K)
  /\ rw_cells asegs m (B + Z.of_nat K) rest.
Proof.
  intros m lo B q' lowc rest K ST LO FR EK K16 Hq.
  destruct (proj1 (rw_cells_app asegs m B lowc rest) FR) as [LOW REST]. rewrite EK in REST.
  destruct (rw_cells_forget asegs m B lowc LOW) as [jl LOWJ]. rewrite EK in LOWJ.
  pose proof (rw_cells_bound asegs _ _ _ LOWJ) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r in BB.
  destruct Hq as [-> | ->].
  - split; [exact ST|]. split; [exists jl; exact LOWJ|]. split; [apply stk_empty; lia| exact REST].
  - destruct (stk_carve asegs m lo B 16 ST ltac:(lia)) as [ST' [pj PAD]].
    change (Z.of_nat 16) with 16 in ST', PAD.
    destruct (rw_cells_CB_splitK m B K (K - 16)%nat jl LOWJ ltac:(lia)) as [LO1 LO2].
    replace (K - (K - 16))%nat with 16%nat in LO2 by lia.
    split; [exact ST'|]. split; [| split; [| exact REST]].
    + pose proof (rw_cells_CB_joinK m (B - 16) 16 (K - 16) pj _ PAD ltac:(replace (B - 16 + Z.of_nat 16) with B by lia; exact LO1)) as J.
      replace (16 + (K - 16))%nat with K in J by lia. eexists. exact J.
    + pose proof (stk_of_rw_cells asegs _ _ _ LO2) as G. cbn [cells_size csize Nat.add] in G.
      replace (B + Z.of_nat (K - 16) + Z.of_nat 16) with (B + Z.of_nat K) in G by lia.
      replace (B - 16 + Z.of_nat K) with (B + Z.of_nat (K - 16)) by lia. exact G.
Qed.

Lemma align32_cases : forall x, x mod 16 = 0 -> x - x mod 32 = x \/ x - x mod 32 = x - 16.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma fsb_app_iv {HC : HasCeiling} : forall FI : fs_if, app_iv (FSB FI, FSB FI + A0_FS_SIZE).
Proof.
  intros FI. destruct (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5). unfold app_iv, SH_HI. cbn [fst snd]. lia.
Qed.
