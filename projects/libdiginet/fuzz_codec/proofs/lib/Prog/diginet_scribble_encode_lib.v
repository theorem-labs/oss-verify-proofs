(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 470 of its 484 lines of code are new or changed and 46 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Prog/codec_main_inv.v; 87 of its 135 lines of code are new or changed and 436 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** ---- cells at two bases ---- *)

Lemma sc_rw_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|].
    intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|].
    intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma sc_rw_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

(** One byte cell of n bytes cut at k into two cells at two bases. *)
Lemma sc_CB_cut : forall m A n k bs, (k <= n)%nat ->
  rw_cells rsegs m A [CB n bs] ->
  rw_cells rsegs m A [CB k (firstn k bs)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros m A n k bs Hk H.
  assert (H2 : rw_cells rsegs m A ([CB k (firstn k bs)] ++ [CB (n - k) (skipn k bs)])).
  { destruct H as [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
    split; [split|].
    - cbn [app cells_wf cell_wf]. rewrite length_firstn, length_skipn.
      split; [lia|]. split; [lia | exact I].
    - cbn [app cells_bytes cbytes] in *. rewrite !app_nil_r in *. rewrite firstn_skipn. exact Hb.
    - cbn [app cells_size csize] in *. replace (k + (n - k + 0))%nat with (n + 0)%nat by lia. exact Hw. }
  apply sc_rw_split in H2. destruct H2 as [H3 H4].
  cbn [cells_size csize] in H4. rewrite Nat.add_0_r in H4. split; assumption.
Qed.

Lemma sc_bytes_of_rw : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma sc_bytes_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n H. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

(** The 28 bytes before the key and the key written by one 4-byte store, as one cell. *)
Lemma sc_out_fin : forall m A X v Y,
  rw_cells rsegs m A [CB 28 X; C4 v] -> X ++ le4 v = Y -> rw_cells rsegs m A [CB 32 Y].
Proof.
  intros m A X v Y H E.
  pose proof (rw_cells_merge rsegs m A [] [CB 28 X; C4 v] [] H) as M.
  cbn [app cells_size csize cells_bytes cbytes Nat.add] in M. rewrite app_nil_r in M. rewrite E in M. exact M.
Qed.

(** ---- register and byte values ---- *)

Lemma sc_u32_small : forall r v, arg_u32 r v -> v < 2 ^ 31 -> bv_unsigned r = v.
Proof.
  intros r v [B ->] H. unfold s32. replace (v <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
  apply unsigned_lit. lia.
Qed.

Lemma sc_u32_big : forall r v, arg_u32 r v -> 2 ^ 31 <= v -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned r.
Proof.
  intros r v [B ->] H. unfold s32. replace (v <? 2 ^ 31) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite unsigned_lit_wrap. rewrite <- (Z_mod_plus_full (v - 2 ^ 32) 1).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sc_z8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma sc_b8_unsigned : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof. intros x Hx. unfold b8. rewrite sc_z8. apply Z.mod_small. exact Hx. Qed.

Lemma sc_zb_pl : forall (b1 b2 : byte) n cs addr,
  bv_unsigned b1 = u8 addr -> bv_unsigned b2 = 0 ->
  zb ([b1; b2] ++ firstn n cs) = [u8 addr; 0] ++ firstn n (zb cs).
Proof.
  intros b1 b2 n cs addr H1 H2. unfold zb. rewrite map_app, firstn_map. cbn [map app]. rewrite H1, H2. reflexivity.
Qed.

Lemma sc_key7 : forall addr x, 0 <= addr <= 127 -> x = addr ->
  Z_to_bv 64 (Z.lor x 458752) = Z_to_bv 64 (KEY 7 addr).
Proof.
  intros addr x H ->. unfold KEY.
  replace (Z.land addr 65535) with addr.
  2: { symmetry. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite (Z.lor_comm addr 458752). reflexivity.
Qed.

(** ---- the model ---- *)

(** sysex_encode either fails without a command or succeeds with key 0 and at most 24 bytes. *)
Lemma sc_sysex_shape : forall dev fn pl,
  (exists rc, sysex_spec dev fn pl = (rc, None) /\ -11 <= rc <= -1) \/
  (exists bs dp, sysex_spec dev fn pl = (0, Some (bs, 0, dp)) /\ (length bs <= 24)%nat).
Proof.
  intros dev fn pl. unfold sysex_spec.
  destruct (0x7f <? dev); [left; eexists; split; [reflexivity | unfold E_ARG; lia] |].
  destruct (fn =? 0x70); [left; eexists; split; [reflexivity | unfold E_REFUSED; lia] |].
  destruct (0x7f <? fn); [left; eexists; split; [reflexivity | unfold E_RANGE; lia] |].
  destruct (24 <? Z.of_nat (length pl) + 5) eqn:E4; [left; eexists; split; [reflexivity | unfold E_SPACE; lia] |].
  destruct (existsb (fun x => Z.testbit x 7) pl); [left; eexists; split; [reflexivity | unfold E_RANGE; lia] |].
  right. do 2 eexists. split; [reflexivity|].
  apply Z.ltb_ge in E4. rewrite !length_app. cbn [length]. lia.
Qed.

Lemma sc_with_key_none : forall rc k, with_key (rc, None) k = (rc, None).
Proof. intros [|p|p] k; reflexivity. Qed.

Lemma sc_scribble_some : forall d addr chars, 0 <= addr <= 0x7f ->
  scribble_spec (Some d) addr chars =
  with_key (sysex_spec (d_dev d) 0x40 ([u8 addr; 0] ++ firstn (Z.to_nat (d_chars d)) chars)) (KEY 7 addr).
Proof.
  intros d addr chars H. unfold scribble_spec.
  replace (0x7f <? addr) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma sc_scribble_big : forall d addr chars, 0x7f < addr -> scribble_spec (Some d) addr chars = (E_RANGE, None).
Proof.
  intros d addr chars H. unfold scribble_spec.
  replace (0x7f <? addr) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(** The command bytes with the key of a successful command replaced. *)
Lemma sc_cmd_out_key : forall before bs dp k0 k v,
  length before = 32%nat -> (length bs <= 24)%nat -> v = Z_to_bv 64 k ->
  firstn 28 (cmd_out before (Some (bs, k0, dp))) ++ le4 v = cmd_out before (Some (bs, k, dp)).
Proof.
  intros before bs dp k0 k v Lb Ls ->.
  assert (HP : forall P Q R : list byte, length P = 28%nat -> firstn 28 (P ++ Q) ++ R = P ++ R).
  { intros P Q R HL. rewrite firstn_app, HL, Nat.sub_diag. cbn [firstn app].
    rewrite app_nil_r, firstn_all2 by lia. reflexivity. }
  unfold cmd_out. rewrite !app_assoc. apply HP.
  unfold bz. rewrite ?length_app, ?length_map, ?length_skipn, ?length_firstn, ?length_skipn.
  rewrite Lb. cbn [length]. lia.
Qed.
