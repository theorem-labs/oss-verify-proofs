(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StreamExec StreamSim StoreOk AllocSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Export ZStep ZMem ZTac TSet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.


Lemma mem_is_app_l : forall segs M a xs ys,
  mem_is segs M a (xs ++ ys) -> mem_is segs M a xs.
Proof.
  intros segs M a xs ys H.
  pose proof (mem_is_firstn segs M a (xs ++ ys) (length xs) H) as H1.
  rewrite length_app in H1. specialize (H1 ltac:(lia)).
  rewrite firstn_app, firstn_all, Nat.sub_diag in H1. cbn [firstn] in H1.
  rewrite app_nil_r in H1. exact H1.
Qed.

Lemma mem_is_app_r : forall segs M a xs ys,
  mem_is segs M a (xs ++ ys) -> mem_is segs M (a + Z.of_nat (length xs)) ys.
Proof.
  intros segs M a xs ys H.
  pose proof (mem_is_skip segs M a (xs ++ ys) (length xs) H) as H1.
  rewrite length_app in H1. specialize (H1 ltac:(lia)).
  rewrite skipn_app, skipn_all, Nat.sub_diag in H1. exact H1.
Qed.

Lemma mem_is_app_inv : forall segs M a xs ys,
  mem_is segs M a (xs ++ ys) ->
  mem_is segs M a xs /\ mem_is segs M (a + Z.of_nat (length xs)) ys.
Proof. intros. split; [eapply mem_is_app_l|eapply mem_is_app_r]; eassumption. Qed.

Lemma mem_is_of_rom : forall segs M a n bs,
  0 <= a -> a + Z.of_nat n <= two64 ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M x = None) ->
  rdn segs (fun _ => None) (w64 a) n = Some bs ->
  mem_is segs M a bs.
Proof.
  intros segs M a n bs Ha Hn Hnone H.
  unfold mem_is. rewrite (rdn_length _ _ _ _ _ H).
  destruct n as [|n]; [cbn in H |- *; congruence|].
  rewrite (rdn_ext segs (S n) M (fun _ => None) (w64 a)); [exact H| |].
  - rewrite w64_unsigned, mod_small_u64 by lia. rewrite <- two64_eq. lia.
  - intros x Hx. rewrite w64_unsigned, mod_small_u64 in Hx by lia. apply Hnone. lia.
Qed.

Definition range_writable_b (segs : list Segment) (lo : Z) (n : nat) : bool :=
  wseg_ok segs (w64 lo) n.

Lemma mem_wr_of_range_writable : forall segs lo n,
  range_writable_b segs lo n = true -> forall M, mem_wr segs M lo (Z.of_nat n).
Proof.
  intros segs lo n; revert lo; induction n as [|n IH]; intros lo H M i Hi; [lia|].
  unfold range_writable_b in H. cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned (w64 lo)) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec]. apply andb_true_iff in H as [Hw Hbyte].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r. unfold wview.
    destruct (M (w64 lo)); [discriminate|]. rewrite Hseg, Hw.
    destruct (segment_byte_at _ _); [discriminate|discriminate Hbyte].
  - replace (lo + i) with ((lo + 1) + (i - 1)) by lia.
    apply (IH (lo + 1)); [|lia].
    unfold range_writable_b. replace (w64 (lo + 1)) with (w64 lo + 1)%bv; [exact Hrec|].
    rewrite word1_nat, w64_add_nat. reflexivity.
Qed.

Lemma mem_wr_of_range_writable_Z : forall segs lo len M,
  0 <= len -> range_writable_b segs lo (Z.to_nat len) = true -> mem_wr segs M lo len.
Proof.
  intros segs lo len M Hlen H.
  rewrite <- (Z2Nat.id len) by lia. apply mem_wr_of_range_writable. exact H.
Qed.


Definition zzero (M : mem) (a n : Z) : mem := apply_zeros M [(w64 a, w64 n)].

Lemma zzero_pt : forall M a n (x : word), zzero M a n x = zmem M (w64 a) (w64 n) x.
Proof.
  intros M a n x. unfold zzero, apply_zeros, zeros_cover, zmem. cbn [existsb fst snd].
  rewrite orb_false_r. reflexivity.
Qed.

Section ZeroFrames.
Variable segs : list Segment.

Lemma rdn_zzero_zmem : forall M a n (x : word) k,
  bv_unsigned x + Z.of_nat k <= 2 ^ 64 ->
  rdn segs (zzero M a n) x k = rdn segs (zmem M (w64 a) (w64 n)) x k.
Proof. intros M a n x k Hnw. apply rdn_ext; [exact Hnw|]. intros y _. apply zzero_pt. Qed.

Lemma mem_zero_zzero : forall M a n, 0 <= a -> a + n <= two64 -> n < two64 -> mem_zero segs (zzero M a n) a n.
Proof.
  intros M a n H0 H1 H2 i Hi. unfold mem_zero.
  rewrite rdn_zzero_zmem by (rewrite w64_unsigned, mod_small_u64 by lia; cbn [Z.of_nat Pos.to_nat]; rewrite two64_eq in *; lia).
  apply rdn_zmem_in1.
  rewrite !w64_unsigned, !mod_small_u64 by lia. lia.
Qed.

Lemma mem_wr_zzero : forall M a n, 0 <= a -> a + n <= two64 -> n < two64 -> mem_wr segs (zzero M a n) a n.
Proof.
  intros M a n H0 H1 H2 i Hi. unfold wview. rewrite zzero_pt. unfold zmem.
  rewrite !w64_unsigned, !mod_small_u64 by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn. discriminate.
Qed.

Lemma mem_wr_zzero_mono : forall M a n a' len,
  mem_wr segs M a' len -> mem_wr segs (zzero M a n) a' len.
Proof.
  intros M a n a' len H i Hi. unfold wview. rewrite zzero_pt. unfold zmem. specialize (H i Hi). unfold wview in H.
  destruct (_ && _); [discriminate | exact H].
Qed.

Lemma rdn_zzero_frame : forall M a n a' (k : nat),
  zdisj a n a' (Z.of_nat k) -> 0 <= n < two64 ->
  rdn segs (zzero M a n) (w64 a') k = rdn segs M (w64 a') k.
Proof.
  intros M a n a' k (H1 & H2 & H3 & H4 & H5) Hn.
  pose proof (Nat2Z.is_nonneg k).
  rewrite rdn_zzero_zmem by (rewrite !w64_unsigned, !mod_small_u64; rewrite ?two64_eq in *; lia).
  apply rdn_zmem_out; rewrite !w64_unsigned, !mod_small_u64; lia.
Qed.

Lemma mem_is_zzero_frame : forall M a n a' bs,
  mem_is segs M a' bs -> zdisj a n a' (Z.of_nat (length bs)) -> 0 <= n < two64 -> mem_is segs (zzero M a n) a' bs.
Proof. intros. unfold mem_is. rewrite rdn_zzero_frame; assumption. Qed.

Lemma mem_zero_zzero_frame : forall M a n a' len,
  mem_zero segs M a' len -> zdisj a n a' len -> 0 <= n < two64 -> mem_zero segs (zzero M a n) a' len.
Proof.
  intros M a n a' len Hz (H1 & H2 & H3 & H4 & H5) Hn i Hi. rewrite rdn_zzero_frame; [apply Hz; lia| |exact Hn].
  unfold zdisj. cbn [Z.of_nat]. lia.
Qed.

Lemma mem_u64_zzero_frame : forall M a n a' e,
  mem_u64 segs M a' e -> zdisj a n a' 8 -> 0 <= n < two64 -> mem_u64 segs (zzero M a n) a' e.
Proof. intros. unfold mem_u64 in *. apply mem_is_zzero_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma mem_u32_zzero_frame : forall M a n a' e,
  mem_u32 segs M a' e -> zdisj a n a' 4 -> 0 <= n < two64 -> mem_u32 segs (zzero M a n) a' e.
Proof. intros. unfold mem_u32 in *. apply mem_is_zzero_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma mem_u16_zzero_frame : forall M a n a' e,
  mem_u16 segs M a' e -> zdisj a n a' 2 -> 0 <= n < two64 -> mem_u16 segs (zzero M a n) a' e.
Proof. intros. unfold mem_u16 in *. apply mem_is_zzero_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma mem_u8_zzero_frame : forall M a n a' e,
  mem_u8 segs M a' e -> zdisj a n a' 1 -> 0 <= n < two64 -> mem_u8 segs (zzero M a n) a' e.
Proof. intros. unfold mem_u8 in *. apply mem_is_zzero_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.

End ZeroFrames.


Definition zunmap (M : mem) (a n : Z) : mem := apply_unmaps M [(w64 a, w64 n)].

Lemma zunmap_out : forall M a n (x : word),
  (bv_unsigned x < bv_unsigned (w64 a) \/ bv_unsigned (w64 a) + bv_unsigned (w64 n) <= bv_unsigned x) ->
  zunmap M a n x = M x.
Proof.
  intros M a n x Hx. unfold zunmap, apply_unmaps, zeros_cover. cbn [existsb fst snd].
  rewrite orb_false_r.
  destruct ((bv_unsigned (w64 a) <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned (w64 a) + bv_unsigned (w64 n))) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. lia.
Qed.

Lemma rdn_zunmap_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned (w64 a)
   \/ bv_unsigned (w64 a) + bv_unsigned (w64 n) <= bv_unsigned x)%Z ->
  rdn segs (zunmap m a n) x k = rdn segs m x k.
Proof.
  intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros y Hy. apply zunmap_out. lia.
Qed.

Section UnmapFrames.
Variable segs : list Segment.

Lemma rdn_zunmap_frame : forall M a n a' (k : nat),
  zdisj a n a' (Z.of_nat k) -> 0 <= n < two64 ->
  rdn segs (zunmap M a n) (w64 a') k = rdn segs M (w64 a') k.
Proof.
  intros M a n a' k (H1 & H2 & H3 & H4 & H5) Hn.
  apply rdn_zunmap_out; rewrite !w64_unsigned, !mod_small_u64 by lia; [rewrite <- two64_eq; lia | lia].
Qed.

Lemma mem_is_zunmap_frame : forall M a n a' bs,
  mem_is segs M a' bs -> zdisj a n a' (Z.of_nat (length bs)) -> 0 <= n < two64 ->
  mem_is segs (zunmap M a n) a' bs.
Proof. intros. unfold mem_is. rewrite rdn_zunmap_frame; assumption. Qed.

Lemma mem_zero_zunmap_frame : forall M a n a' len,
  mem_zero segs M a' len -> zdisj a n a' len -> 0 <= n < two64 ->
  mem_zero segs (zunmap M a n) a' len.
Proof.
  intros M a n a' len Hz (H1 & H2 & H3 & H4 & H5) Hn i Hi. rewrite rdn_zunmap_frame; [apply Hz; lia| |exact Hn].
  unfold zdisj. cbn [Z.of_nat]. lia.
Qed.

Lemma mem_wr_zunmap_frame : forall M a n a' len,
  mem_wr segs M a' len -> zdisj a n a' len -> 0 <= n < two64 ->
  mem_wr segs (zunmap M a n) a' len.
Proof.
  intros M a n a' len Hw (H1 & H2 & H3 & H4 & H5) Hn i Hi. specialize (Hw i Hi).
  unfold wview in *. rewrite zunmap_out; [exact Hw|].
  rewrite !w64_unsigned, !mod_small_u64 by lia. lia.
Qed.

Lemma mem_u64_zunmap_frame : forall M a n a' e,
  mem_u64 segs M a' e -> zdisj a n a' 8 -> 0 <= n < two64 -> mem_u64 segs (zunmap M a n) a' e.
Proof. intros. unfold mem_u64 in *. apply mem_is_zunmap_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma mem_u32_zunmap_frame : forall M a n a' e,
  mem_u32 segs M a' e -> zdisj a n a' 4 -> 0 <= n < two64 -> mem_u32 segs (zunmap M a n) a' e.
Proof. intros. unfold mem_u32 in *. apply mem_is_zunmap_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma mem_u16_zunmap_frame : forall M a n a' e,
  mem_u16 segs M a' e -> zdisj a n a' 2 -> 0 <= n < two64 -> mem_u16 segs (zunmap M a n) a' e.
Proof. intros. unfold mem_u16 in *. apply mem_is_zunmap_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma mem_u8_zunmap_frame : forall M a n a' e,
  mem_u8 segs M a' e -> zdisj a n a' 1 -> 0 <= n < two64 -> mem_u8 segs (zunmap M a n) a' e.
Proof. intros. unfold mem_u8 in *. apply mem_is_zunmap_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.

End UnmapFrames.


End FXG.
Ltac zmem_transport_zero M a n :=
  repeat match goal with
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u64_zzero_frame segs M a n a' e) in H; [|zdisj_tac|lia] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u32_zzero_frame segs M a n a' e) in H; [|zdisj_tac|lia] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u16_zzero_frame segs M a n a' e) in H; [|zdisj_tac|lia] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u8_zzero_frame segs M a n a' e) in H; [|zdisj_tac|lia] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      first [ apply (mem_is_zzero_frame segs M a n a' bs') in H; [|zdisj_tac|lia] | clear H ]
  | H : mem_zero ?segs M ?a' ?len |- _ =>
      first [ apply (mem_zero_zzero_frame segs M a n a' len) in H; [|zdisj_tac|lia] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_zzero_mono segs M a n a' len) in H
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Ltac zmem_post_zero :=
  lazymatch goal with
  | |- realizes ?segs (zcfg _ ?pc ?R (zzero ?M ?a ?n) ?MD) ?T =>
      zmem_transport_zero M a n;
      first [ pose proof (mem_zero_zzero segs M a n ltac:(lia) ltac:(lia) ltac:(lia));
              pose proof (mem_wr_zzero segs M a n ltac:(lia) ltac:(lia) ltac:(lia))
            | idtac "zmem_post_zero: could not establish grant facts at" a ];
      let Mn := fresh "M" in
      set (Mn := zzero M a n) in *;
      clearbody Mn; try clear M
  end.
