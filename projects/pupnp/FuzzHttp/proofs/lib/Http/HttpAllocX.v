(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame Arr Tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpAlloc.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.

Section A.
Context {HCEIL : HasCeiling}.
Variable segs : list Segment.
Variable AI : alloc_if segs.
Notation L := (ai_L segs AI).
Notation K := (ai_K segs AI).
Notation BL := (list (block K)).

Definition mbloc (LB : BL) (SP B MB n : Z) : Prop :=
  (SP <= MB /\ MB + n <= B) \/ (exists b, In b LB /\ blk_addr b <= MB /\ MB + n <= blk_addr b + blk_size b).

#[using="Type"] Lemma mbloc_stack : forall LB SP B MB n, SP <= MB -> MB + n <= B -> mbloc LB SP B MB n.
Proof. intros; left; lia. Qed.

#[using="Type"] Lemma mbloc_block : forall LB SP B MB n (b : block K),
  In b LB -> blk_addr b <= MB -> MB + n <= blk_addr b + blk_size b -> mbloc LB SP B MB n.
Proof. intros LB SP B MB n b H H1 H2. right. exists b. auto. Qed.

#[using="Type"] Lemma mbloc_weaken : forall LB LB' SP SP' B MB n,
  mbloc LB SP B MB n -> SP' <= SP -> (forall b, In b LB -> In b LB') -> mbloc LB' SP' B MB n.
Proof.
  intros LB LB' SP SP' B MB n [H|(b & Hb & H1 & H2)] HS SUB; [left; lia|]. right. exists b. split; [apply SUB; exact Hb| lia].
Qed.

#[using="Type"] Lemma mbloc_client : forall LB SP B MB n, mbloc LB SP B MB n -> client_range AI LB SP MB n.
Proof.
  intros LB SP B MB n [H|(b & Hb & H1 & H2)].
  - apply client_range_above. lia.
  - eapply client_range_block; [exact Hb| lia| lia].
Qed.

#[using="Type"] Lemma mbloc_lo : forall s LB0 LB SP B MB n m,
  RHEAP segs AI s LB0 m -> (forall b, In b LB -> In b LB0) -> mbloc LB SP B MB n ->
  MB + n <= alloc_ceiling \/ SP <= MB.
Proof.
  intros s LB0 LB SP B MB n m HR SUB [H|(b & Hb & H1 & H2)]; [right; lia|].
  destruct (ai_block_range segs AI _ _ _ _ HR (SUB b Hb)) as (_ & _ & _ & R4 & _). left. lia.
Qed.

#[using="Type"] Lemma mbloc_pos : forall s LB0 LB SP B MB n m,
  RHEAP segs AI s LB0 m -> (forall b, In b LB -> In b LB0) -> mbloc LB SP B MB n -> 0 < SP -> 0 < MB.
Proof.
  intros s LB0 LB SP B MB n m HR SUB [H|(b & Hb & H1 & H2)] HS; [lia|].
  destruct (ai_block_range segs AI _ _ _ _ HR (SUB b Hb)) as (R1 & _). lia.
Qed.

#[using="Type"] Lemma mbloc_hf : forall LB0 LB SP B MB n,
  mbloc LB SP B MB n -> alloc_ceiling <= SP -> (forall b, In b LB -> In b LB0) ->
  alloc_ceiling <= fst (MB, MB + n)
  \/ (exists lo hi, al_client_static L lo hi /\ lo <= fst (MB, MB + n) /\ snd (MB, MB + n) <= hi)
  \/ (al_errno L <= fst (MB, MB + n) /\ snd (MB, MB + n) <= al_errno L + 4)
  \/ (exists b, In b LB0 /\ blk_addr b <= fst (MB, MB + n) /\ snd (MB, MB + n) <= blk_addr b + blk_size b).
Proof.
  intros LB0 LB SP B MB n [H|(b & Hb & H1 & H2)] HC SUB; cbn.
  - left. lia.
  - right; right; right. exists b. split; [apply SUB; exact Hb| lia].
Qed.

#[using="Type"] Lemma mbloc_ef : forall LB0 LB SP B MB n,
  mbloc LB SP B MB n -> alloc_ceiling <= SP -> (forall b, In b LB -> In b LB0) ->
  (alloc_ceiling <= fst (MB, MB + n) /\ snd (MB, MB + n) <= B)
  \/ (exists lo hi, al_client_static L lo hi /\ lo <= fst (MB, MB + n) /\ snd (MB, MB + n) <= hi)
  \/ (al_errno L <= fst (MB, MB + n) /\ snd (MB, MB + n) <= al_errno L + 4)
  \/ (exists b, In b LB0 /\ blk_addr b <= fst (MB, MB + n) /\ snd (MB, MB + n) <= blk_addr b + blk_size b).
Proof.
  intros LB0 LB SP B MB n [H|(b & Hb & H1 & H2)] HC SUB; cbn.
  - left. lia.
  - right; right; right. exists b. split; [apply SUB; exact Hb| lia].
Qed.

#[using="Type"] Lemma mbloc_other_block : forall s LB0 LB SP B MB n m (b1 : block K),
  RHEAP segs AI s LB0 m -> (forall b, In b LB -> In b LB0 /\ b <> b1) -> In b1 LB0 ->
  mbloc LB SP B MB n -> alloc_ceiling <= SP ->
  MB + n <= blk_addr b1 \/ blk_addr b1 + blk_size b1 <= MB.
Proof.
  intros s LB0 LB SP B MB n m b1 HR SUB H1 [H|(b & Hb & Q1 & Q2)] HC.
  - destruct (ai_block_range segs AI _ _ _ _ HR H1) as (_ & _ & _ & R4 & _). right. lia.
  - destruct (SUB b Hb) as [Hb0 NE].
    destruct (ai_blocks_disjoint segs AI _ _ _ _ _ HR Hb0 H1 NE); lia.
Qed.

#[using="Type"] Lemma mbloc_errno : forall s LB0 LB SP B MB n m,
  layout_ok AI -> RHEAP segs AI s LB0 m -> (forall b, In b LB -> In b LB0) -> mbloc LB SP B MB n -> alloc_ceiling <= SP ->
  al_errno L + 4 <= MB \/ MB + n <= al_errno L.
Proof.
  intros s LB0 LB SP B MB n m LO HR SUB [H|(b & Hb & Q1 & Q2)] HC.
  - destruct (lo_errno_img segs AI LO) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling segs AI LO w Hw). left. lia.
  - destruct (fresh_block_disjoint_errno segs AI _ _ _ _ LO HR (SUB b Hb)); lia.
Qed.
End A.

Arguments mbloc {HCEIL segs} AI LB SP B MB n.

Section B.
Context {HCEIL : HasCeiling}.
Variable segs : list Segment.
Variable AI : alloc_if segs.
Notation K := (ai_K segs AI).

#[using="Type"] Lemma hpx_drop : forall W (LB LB' : list (block K)) SP SP' m m',
  hpx AI W LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) ->
  (forall a, 0 <= a < 2^64 -> client_addr AI LB' SP' a -> outside W a) -> hpx AI [] LB' SP' m m'.
Proof.
  intros W LB LB' SP SP' m m' H HS HL HO a Ha Hc _. apply H; [exact Ha| | apply HO; assumption].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.
End B.
