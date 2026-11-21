(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr Bytes.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zh_kit Z_kit Z_dview Z_dinit_kit Z_irep.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition ist_rawA (junk : list byte) : list cell :=
  [C8 (jw junk 0); C4 (wz (init_u32 (orc junk) 8 0)); C4 (wz (init_u32 (orc junk) 12 0)); C4 (wz (init_u32 (orc junk) 16 0)); C4 (wz (init_u32 (orc junk) 20 0));
   C8 (jw junk 24); C8 (jw junk 32); C8 (jw junk 40); C8 (jw junk 48);
   C4 (wz (init_u32 (orc junk) 56 0)); C4 (wz (init_u32 (orc junk) 60 0)); C8 (jw junk 64); C8 (jw junk 72);
   C8 (jw junk 80); C4 (wz (init_u32 (orc junk) 88 0)); C4 (wz (init_u32 (orc junk) 92 0)); C4 (wz (init_u32 (orc junk) 96 0)); C4 (wz (init_u32 (orc junk) 100 0));
   C8 (jw junk 104); C8 (jw junk 112);
   C4 (wz (init_u32 (orc junk) 120 0)); C4 (wz (init_u32 (orc junk) 124 0)); C4 (wz (init_u32 (orc junk) 128 0)); C4 (wz (init_u32 (orc junk) 132 0));
   C4 (wz (init_u32 (orc junk) 136 0)); C4 (wz (init_u32 (orc junk) 140 0)); C8 (jw junk 144)].

(* the 7176-byte state's tail is sane | back at 7160, was at 7168, pad at 7172 (the mover
   moved 7144 but not 7152 / 7156) *)
Definition ist_rawT (junk : list byte) : list cell :=
  [C8 (jw junk 7160); C4 (wz (init_u32 (orc junk) 7168 0)); CB 4 (jp junk 7172 4)].

Local Transparent zseq.
Lemma av32_orc : forall junk (a : arr) off n, 0 <= off -> 0 <= n -> off + 4 * n <= Z.of_nat (length junk) ->
  (forall i, 0 <= i < n -> arr_get a i = ole (orc junk) (off + 4 * i) 4) ->
  u32s (av32 a n) = sub junk (Z.to_nat off) (Z.to_nat (4 * n)).
Proof.
  intros junk a off n H0 Hn H Hf. unfold av32, zseq.
  rewrite (u32_map_seq junk (arr_get a) off (Z.to_nat n) 0); [f_equal; lia| exact H0| lia|].
  intros i Hi. rewrite Hf by lia. reflexivity.
Qed.
Local Opaque zseq.

Section Recast.
Variable m : mem.
Variable As : Z.
Variable junk : list byte.
Hypothesis H : rw_cells psegs m As [CB (Z.to_nat 7176) junk].
Local Notation g := (orc junk).

Lemma irecast_len : length junk = Z.to_nat 7176.
Proof. exact (proj1 (proj1 (proj1 H))). Qed.
Lemma irecast_lenZ : Z.of_nat (length junk) = 7176.
Proof. rewrite irecast_len. apply Z2Nat.id. lia. Qed.

Local Ltac prep GA off n :=
  pose proof irecast_len as LEN; pose proof irecast_lenZ as LENZ;
  pose proof H as H'; rewrite <- LEN in H';
  pose proof (cb_subZ m As junk off n H' ltac:(lia) ltac:(lia) ltac:(lia)) as GA; clear H' LEN.

Lemma irecast_A : rw_cells psegs m As (ist_rawA junk).
Proof.
  prep GA 0 152. rewrite Z.add_0_r in GA.
  eapply rw_cells_recast; [exact GA| |].
  - unfold ist_rawA. cbn [cells_wf cell_wf]. repeat split.
  - unfold ist_rawA, jw. cbn [cells_bytes cbytes].
    rewrite ?le8_orc, ?le4_orc by lia.
    rewrite (app_nil_r (sub junk (Z.to_nat 0) (Z.to_nat 152))).
    change (sub junk (Z.to_nat 0) (Z.to_nat 152)) with (sub junk (Z.to_nat 0) (sum_nat [8;4;4;4;4;8;8;8;8;4;4;8;8;8;4;4;4;4;8;8;4;4;4;4;4;4;8]%nat)).
    rewrite <- concat_subs_eq by lia. reflexivity.
Qed.

Lemma irecast_T : rw_cells psegs m (As + 7160) (ist_rawT junk).
Proof.
  prep GA 7160 16.
  eapply rw_cells_recast; [exact GA| |].
  - unfold ist_rawT, jp. cbn [cells_wf cell_wf]. repeat split. apply sub_length. lia.
  - unfold ist_rawT, jw, jp. cbn [cells_bytes cbytes].
    rewrite ?le8_orc, ?le4_orc by lia.
    rewrite (app_nil_r (sub junk (Z.to_nat 7160) (Z.to_nat 16))).
    change (sub junk (Z.to_nat 7160) (Z.to_nat 16)) with (sub junk (Z.to_nat 7160) (sum_nat [8;4;4]%nat)).
    rewrite <- concat_subs_eq by lia. reflexivity.
Qed.

Lemma irecast_lens : u16arr psegs m (As + 152) (av16 (iarr_u16_of g 152 320) 320).
Proof.
  prep GA 152 640. apply u8arr_of_rw_cells in GA. unfold u16arr.
  rewrite (av16_orc junk _ 152 320) by (try lia; intros i Hi; unfold iarr_u16_of; rewrite arr_get_init; apply (init_u16_ole _ (orc_range junk))). exact GA.
Qed.
Lemma irecast_work : u16arr psegs m (As + 792) (av16 (iarr_u16_of g 792 288) 288).
Proof.
  prep GA 792 576. apply u8arr_of_rw_cells in GA. unfold u16arr.
  rewrite (av16_orc junk _ 792 288) by (try lia; intros i Hi; unfold iarr_u16_of; rewrite arr_get_init; apply (init_u16_ole _ (orc_range junk))). exact GA.
Qed.
Lemma irecast_codes : u32arr psegs m (As + 1384) (av32 (iarr_u32_of g 1384 1444) 1444).
Proof.
  prep GA 1384 5776. apply u8arr_of_rw_cells in GA. unfold u32arr. destruct GA as [GB GW]. split.
  - rewrite (av32_orc junk _ 1384 1444) by (try lia; intros i Hi; unfold iarr_u32_of; rewrite arr_get_init; apply (init_u32_ole _ (orc_range junk))). exact GB.
  - rewrite av32_length. rewrite sub_length in GW by lia. exact GW.
Qed.
End Recast.
