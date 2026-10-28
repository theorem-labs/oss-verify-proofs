(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a -> m' (wa a) = m (wa a).

Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m a _ _. reflexivity. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. rewrite (H2 a Ha HP). exact (H1 a Ha HP). Qed.
Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

(* [comment removed for export] *)
Lemma agree_on_D : forall P m m', agree_on P m m' -> D_kit.agree_on P m m'.
Proof.
  intros P m m' H a Ha. pose proof (bv_unsigned_in_range 64 a) as R. change (bv_modulus 64) with (2^64) in R.
  specialize (H (bv_unsigned a) R Ha). unfold wa in H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Lemma agree_on_of_D : forall P m m', D_kit.agree_on P m m' -> agree_on P m m'.
Proof. intros P m m' H a Ha HP. apply H. unfold wa. rewrite unsigned_lit by lia. exact HP. Qed.

Lemma agree_on_of_munch : forall W m m', munch W m m' -> wmono bsegs m m' -> agree_on (fun a => outside W a) m m'.
Proof. intros W m m' MU _ a Ha Ho. apply MU. unfold wa. rewrite unsigned_lit by lia. exact Ho. Qed.
Lemma agree_on_of_munch_nw : forall W m m', munch W m m' -> agree_on (fun a => outside W a) m m'.
Proof. intros W m m' MU a Ha Ho. apply MU. unfold wa. rewrite unsigned_lit by lia. exact Ho. Qed.

Lemma bytes_at_agree : forall P m m' A bs,
  agree_on P m m' -> bytes_at bsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at bsegs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  rewrite (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)). reflexivity.
Qed.

Lemma wr_at_agree : forall P m m' A n,
  agree_on P m m' -> wr_at bsegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at bsegs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_agree bsegs m m'); [exact (HW i Hi)|]. apply HP; [lia| apply HR; lia].
Qed.

Lemma rw_cells_agree : forall P m m' A cs,
  agree_on P m m' -> rw_cells bsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells bsegs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.

Lemma ro_cells_agree : forall P m m' A cs,
  agree_on P m m' -> ro_cells bsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  ro_cells bsegs m' A cs.
Proof.
  intros P m m' A cs HP [Hwf HB] HR. split; [exact Hwf|].
  eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
Qed.

Lemma u64arr_agree : forall P m m' A ws,
  agree_on P m m' -> u64arr bsegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) ->
  u64arr bsegs m' A ws.
Proof.
  intros P m m' A ws HP [HB HW] HR. split.
  - eapply bytes_at_agree; eauto. rewrite u64s_length. intros a Ha. apply HR. lia.
  - eapply wr_at_agree; eauto.
Qed.

Lemma u32arr_agree : forall P m m' A ws,
  agree_on P m m' -> u32arr bsegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) ->
  u32arr bsegs m' A ws.
Proof.
  intros P m m' A ws HP [HB HW] HR. split.
  - eapply bytes_at_agree; eauto. rewrite u32s_length. intros a Ha. apply HR. lia.
  - eapply wr_at_agree; eauto.
Qed.

Lemma stk_agree : forall P m m' lo hi,
  agree_on P m m' -> stk bsegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk bsegs m' lo hi.
Proof.
  intros P m m' lo hi HP ST HR. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (HP i ltac:(lia) ltac:(apply HR; lia)) as E. destruct (HW i Hi) as [W0 [b Hb]].
  split; [rewrite (wview_agree bsegs m m' _ E); exact W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma acc_agree : forall P m m' a n,
  agree_on P m m' -> A.Shadow.acc bsegs m a n -> (forall i, 0 <= i < n -> P (A.Shadow.shad (a + i))) -> A.Shadow.acc bsegs m' a n.
Proof.
  intros P m m' a n HP H HR i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [|exact Hok].
  eapply bytes_at_agree; [exact HP | exact Hb |]. intros x Hx. cbn [length] in Hx. replace x with (A.Shadow.shad (a + i)) by lia. apply HR. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition blk_an (b : block) : Z * Z := (blk_addr b, blk_size b).

(* [comment removed for export] *)
Definition aclient_addr (L : list block) (SP : Z) (a : Z) : Prop :=
  (SP <= a < USTACK_TOP) \/ client_static a \/ in_block L a.

Lemma in_live_blocks : forall (L : list block) a, in_live (map blk_an L) a <-> in_block L a.
Proof.
  intros L a. unfold in_live, in_block. split.
  - intros (p & n & Hin & Hr). apply in_map_iff in Hin as (b & E & Hb). unfold blk_an in E. injection E as <- <-. exists b. auto.
  - intros (b & Hb & Hr). exists (blk_addr b), (blk_size b). split; [|exact Hr]. apply in_map_iff. exists b. auto.
Qed.

Lemma aclient_of_addr : forall L SP a, aclient_addr L SP a -> aclient (map blk_an L) [] SP a.
Proof.
  intros L SP a [H|[H|H]]; [left; exact H | right; left; exact H | right; right; left; apply in_live_blocks; exact H].
Qed.

(* [comment removed for export] *)
Lemma aclient_of_addr_incl : forall live L SP a, (forall e, In e (map blk_an L) -> In e live) -> aclient_addr L SP a -> aclient live [] SP a.
Proof.
  intros live L SP a HI [H|[H|H]]; [left; exact H | right; left; exact H | right; right; left].
  apply in_live_blocks in H. destruct H as (p & n & Hin & Hr). exists p, n. split; [exact (HI _ Hin) | exact Hr].
Qed.

Lemma agree_of_rt_pres_incl : forall live L SP m m', (forall e, In e (map blk_an L) -> In e live) ->
  rt_pres live [] SP m m' -> agree_on (aclient_addr L SP) m m'.
Proof.
  intros live L SP m m' HI H a Ha Hc. apply H. unfold wa. rewrite unsigned_lit by lia. eapply aclient_of_addr_incl; eauto.
Qed.

Lemma agree_of_rt_pres_ex_incl : forall live L SP d n m m', (forall e, In e (map blk_an L) -> In e live) ->
  rt_pres_ex live [] SP d n m m' -> agree_on (fun a => aclient_addr L SP a /\ ~ (d <= a < d + n)) m m'.
Proof.
  intros live L SP d n m m' HI H a Ha [Hc Hd]. apply H; unfold wa; rewrite unsigned_lit by lia; [eapply aclient_of_addr_incl; eauto | exact Hd].
Qed.

Lemma agree_of_rt_pres_fp_incl : forall live L SP W m m', (forall e, In e (map blk_an L) -> In e live) ->
  rt_pres_fp live [] SP W m m' -> agree_on (fun a => aclient_addr L SP a /\ outside W a) m m'.
Proof.
  intros live L SP W m m' HI H a Ha [Hc Hd]. apply H; unfold wa; rewrite unsigned_lit by lia; [eapply aclient_of_addr_incl; eauto | exact Hd].
Qed.

Lemma agree_of_rt_pres : forall L SP m m', rt_pres (map blk_an L) [] SP m m' -> agree_on (aclient_addr L SP) m m'.
Proof.
  intros L SP m m' H a Ha Hc. apply H. unfold wa. rewrite unsigned_lit by lia. apply aclient_of_addr. exact Hc.
Qed.

Lemma agree_of_rt_pres_ex : forall L SP d n m m', rt_pres_ex (map blk_an L) [] SP d n m m' ->
  agree_on (fun a => aclient_addr L SP a /\ ~ (d <= a < d + n)) m m'.
Proof.
  intros L SP d n m m' H a Ha [Hc Hd]. apply H; unfold wa; rewrite unsigned_lit by lia; [apply aclient_of_addr; exact Hc | exact Hd].
Qed.

Lemma agree_of_rt_pres_fp : forall L SP W m m', rt_pres_fp (map blk_an L) [] SP W m m' ->
  agree_on (fun a => aclient_addr L SP a /\ outside W a) m m'.
Proof.
  intros L SP W m m' H a Ha [Hc Hd]. apply H; unfold wa; rewrite unsigned_lit by lia; [apply aclient_of_addr; exact Hc | exact Hd].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs',
  rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells bsegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
