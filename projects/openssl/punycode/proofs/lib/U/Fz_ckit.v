(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Image SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require LibKit KBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation mem := (word -> option byte) (only parsing).

(* [comment removed for export] *)
Lemma usegs_w_r : forallb (fun seg => negb (seg_writable seg) || seg_readable seg) usegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn in H; [discriminate|].
  destruct (_ && _); [injection H as <-; left; reflexivity| right; eapply IH; eassumption].
Qed.

Lemma wview_mrd_U : forall (m : mem) a, wview usegs m a <> None -> exists b, mrd usegs m a = Some b.
Proof.
  intros m a H. unfold wview, mrd in *. destruct (m a) as [b|]; [exists b; reflexivity|].
  unfold seg_rom, memory_read.
  destruct (find_segment usegs (bv_unsigned a) 1) as [seg|] eqn:FS; [| contradiction].
  change (Z.of_N 1) with 1. rewrite FS.
  pose proof (find_segment_in _ _ _ _ FS) as IN.
  pose proof usegs_w_r as W. rewrite forallb_forall in W. specialize (W seg IN).
  destruct (seg_writable seg) eqn:SW; [| contradiction]. cbn in W. rewrite W.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at _ _) as [b|]; [| contradiction]. exists b. reflexivity.
Qed.

Lemma wr_at_stk : forall (m : mem) d n, wr_at usegs m d n -> stk usegs m d (d + n).
Proof.
  intros m d n (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  assert (W : wview usegs m (wa a) <> None) by (replace a with (d + (a - d)) by lia; apply H; lia).
  split; [exact W| exact (wview_mrd_U m _ W)].
Qed.

Lemma wr_at_rw_CB : forall (m : mem) d n, wr_at usegs m d n -> 0 <= n -> exists junk, rw_cells usegs m d [CB (Z.to_nat n) junk].
Proof.
  intros m d n W N0. pose proof (wr_at_stk m d n W) as S.
  destruct (stk_carve usegs m d (d + n) (Z.to_nat n) S ltac:(lia)) as [_ (junk & FR)].
  exists junk. replace (d + n - Z.of_nat (Z.to_nat n)) with d in FR by lia. exact FR.
Qed.

Lemma wr_at_app : forall (m : mem) a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at usegs m a (n1 + n2) <-> wr_at usegs m a n1 /\ wr_at usegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall (m : mem) A cs1 cs2,
  rw_cells usegs m A (cs1 ++ cs2) <-> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_head : forall (m : mem) A c cs, rw_cells usegs m A (c :: cs) -> rw_cells usegs m A [c].
Proof. intros m A c cs H. exact (proj1 (proj1 (rw_cells_app m A [c] cs) H)). Qed.

Lemma rw_cells_tail : forall (m : mem) A c cs, rw_cells usegs m A (c :: cs) -> rw_cells usegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. pose proof (proj2 (proj1 (rw_cells_app m A [c] cs) H)) as H2. cbn [cells_size Nat.add] in H2.
  rewrite Nat.add_0_r in H2. exact H2. Qed.

Lemma wr_at_sub : forall (m : mem) a n a' n', wr_at usegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at usegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H1 H2 H3. split; [lia| split; [lia|]].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

Lemma rw_cells_recast : forall (m : mem) A cs cs', rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells usegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma wr_at_rw_C1 : forall (m : mem) a, wr_at usegs m a 1 -> exists b, rw_cells usegs m a [C1 b].
Proof.
  intros m a W. destruct (wr_at_rw_CB m a 1 W ltac:(lia)) as (junk & H).
  destruct H as [[W1 B] R]. cbn in W1. destruct junk as [|b [|? ?]]; cbn in W1; try (destruct W1; discriminate).
  exists b. split; [split; [cbn; split; [reflexivity| exact I]| exact B]| exact R].
Qed.

Lemma wview_of_wr_ok : forall (M : mem) a n (x : word), LibKit.wr_ok usegs M a n -> a <= bv_unsigned x < a + n ->
  wview usegs M x <> None.
Proof.
  intros M a n x Hw Hx. pose proof (Hw (bv_unsigned x) 1%nat ltac:(lia) ltac:(lia)) as Hs.
  rewrite Z_to_bv_bv_unsigned in Hs. cbn [store_ok] in Hs. destruct (wview usegs M x); [discriminate| discriminate].
Qed.

Lemma ro_C8_of_cell : forall (m : mem) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> LibKit.cell usegs m a 8 v -> ro_cells usegs m a [C8 v].
Proof.
  intros m a v Ha Hn H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  exact (KBridge.bytes_of_cell usegs m a 8 v Ha Hn H).
Qed.

Lemma rw_C8_of_cell : forall (m : mem) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> LibKit.cell usegs m a 8 v -> wr_at usegs m a 8 ->
  rw_cells usegs m a [C8 v].
Proof. intros m a v Ha Hn H Hw. split; [exact (ro_C8_of_cell m a v Ha Hn H)| exact Hw]. Qed.

Lemma rw_cells_join2 : forall (m : mem) a c1 c2, rw_cells usegs m a [c1] -> rw_cells usegs m (a + Z.of_nat (csize c1)) [c2] ->
  rw_cells usegs m a [c1; c2].
Proof.
  intros m a c1 c2 H1 H2. apply (proj2 (rw_cells_app m a [c1] [c2])). split; [exact H1|]. cbn [cells_size Nat.add].
  rewrite Nat.add_0_r. exact H2.
Qed.

Lemma rw_cells_skip : forall (m : mem) A cs1 cs2, rw_cells usegs m A (cs1 ++ cs2) -> rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. intros m A cs1 cs2 H. exact (proj2 (proj1 (rw_cells_app m A cs1 cs2) H)). Qed.

Lemma stk_wr_at : forall (m : mem) lo hi a n, stk usegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at usegs m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) Ha Hn H0. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (a + i) ltac:(lia))).
Qed.

Lemma stk_munch : forall W (m m' : mem) lo hi, stk usegs m lo hi -> munch W m m' -> wmono usegs m m' ->
  (forall x, lo <= x < hi -> outside W x) -> stk usegs m' lo hi.
Proof. intros W m m' lo hi H MU WM HO. eapply stk_transport; [exact H| exact MU| exact WM|]. intros x Hx. left. exact (HO x Hx). Qed.

Lemma bytes_at_sub : forall (m : mem) A bs k n, bytes_at usegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at usegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n (H0 & H1 & H) Hk. split; [lia|]. split; [rewrite firstn_length, skipn_length; lia|].
  intros i Hi. rewrite firstn_length, skipn_length in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia. rewrite (H (k + i)%nat) by lia.
  rewrite nth_error_firstn. rewrite nth_error_skipn.
  destruct (Nat.ltb_spec i n) as [L|L]; [reflexivity | lia].
Qed.

Lemma stk_wview : forall (m : mem) lo hi (x : word), stk usegs m lo hi -> lo <= bv_unsigned x < hi -> wview usegs m x <> None.
Proof.
  intros m lo hi x (S0 & S1 & S) Hx. pose proof (proj1 (S (bv_unsigned x) Hx)) as Wv.
  unfold wa in Wv. rewrite Z_to_bv_bv_unsigned in Wv. exact Wv.
Qed.

Lemma wr_at_wview : forall (m : mem) a n (x : word), wr_at usegs m a n -> a <= bv_unsigned x < a + n -> wview usegs m x <> None.
Proof.
  intros m a n x (S0 & S1 & S) Hx. pose proof (S (bv_unsigned x - a) ltac:(lia)) as Wv.
  replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Wv by lia. unfold wa in Wv. rewrite Z_to_bv_bv_unsigned in Wv. exact Wv.
Qed.
