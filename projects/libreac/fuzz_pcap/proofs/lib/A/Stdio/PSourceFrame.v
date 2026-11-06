(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written for libreac/fuzz_pcap -- frame (transport) lemmas for the read-stream predicates of
   PSource.v, so that a walk that changes only a few bytes can re-establish them. Each lemma says:
   if m' agrees with m (via mbyte) on the bytes a predicate reads, the predicate moves from m to m'.
   The val_mem and garr8 steps use the tree's own agreement lemmas, YE00.val_mem_frame and
   YI00.garr8_frame, not a hand unfolding of val_mem.

   The _mode variants serve a walk that rewrites the orientation word at f + 136 (musl __toread
   does): their FILE agreement holds only outside [f + 136, f + 140), and the new word is supplied
   as source_mode in the new memory. asource_at quantifies the orientation word existentially, so
   the walk need not keep the old value. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP09 YI04 YI00.
(* YE00 only for YE00.val_mem_frame. Not imported: its U32M1 / bytes would shadow PSource's. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YE00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section frame.
Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variable K : asource_syms.

(* The bytes asrc_stdio_env reads, as one predicate (the donor's YE00.aenv_addr shape): one
   premise `forall a, asrc_env_addr a -> mbyte segs m' a = mbyte segs m a` instead of six, and a
   caller discharges it with `unfold asrc_env_addr in *; lia` against its own write ranges. The
   ranges are exactly the env's reads: threaded (1), need_locks (1), ofl_lock (4), "rb\0" (3),
   "rwa\0" at as_rwa K (4), canary (8). The open-file-list head is NOT here: asource_at reads it separately,
   and the asource_at frames take it as its own premise. *)
Definition asrc_env_addr (a : Z) : Prop :=
  (as_threaded K <= a < as_threaded K + 1) \/
  (as_need_locks K <= a < as_need_locks K + 1) \/
  (as_ofl_lock K <= a < as_ofl_lock K + 4) \/
  (as_mode K <= a < as_mode K + 3) \/
  (as_rwa K <= a < as_rwa K + 4) \/
  (as_canary K <= a < as_canary K + 8).

(* ---- the FILE block, all but the orientation word ---- *)

Lemma source_static_frame_mode : forall (m m' : word -> option byte) f b n,
  (forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) -> mbyte segs m' a = mbyte segs m a) ->
  source_static segs K m f b n -> source_static segs K m' f b n.
Proof.
  intros m m' f b n Hfr Hs.
  assert (HFB : SRC_FILE_BLOCK = 1304) by reflexivity.
  assert (HCO : SRC_COOKIE_OFF = 232) by reflexivity.
  assert (HV : forall off (k : nat) v, 0 <= off -> off + Z.of_nat k <= SRC_FILE_BLOCK ->
                 (off + Z.of_nat k <= 136 \/ 140 <= off) ->
                 val_mem segs m (f + off) k v -> val_mem segs m' (f + off) k v).
  { intros off k v H0 H1 H2 Hv. apply (YE00.val_mem_frame segs m m'); [|exact Hv].
    intros x Hx. apply Hfr; lia. }
  unfold source_static in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    first [ assumption | (apply HV; [lia | lia | lia | assumption]) ].
Qed.

Lemma source_window_frame_mode : forall (m m' : word -> option byte) f Wl,
  (forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) -> mbyte segs m' a = mbyte segs m a) ->
  source_window segs m f Wl -> source_window segs m' f Wl.
Proof.
  intros m m' f Wl Hfr Hw.
  assert (HFB : SRC_FILE_BLOCK = 1304) by reflexivity.
  assert (HBO : SRC_BUF_OFF = 280) by reflexivity.
  assert (HBS : SRC_BUFSIZ = 1024) by reflexivity.
  assert (HV : forall off (k : nat) v, 0 <= off -> off + Z.of_nat k <= 136 ->
                 val_mem segs m (f + off) k v -> val_mem segs m' (f + off) k v).
  { intros off k v H0 H1 Hv. apply (YE00.val_mem_frame segs m m'); [|exact Hv].
    intros x Hx. apply Hfr; lia. }
  destruct Hw as [(HW & H1 & H2) | (i & Hi0 & Hi1 & H1 & H2 & HG)]; [left | right].
  - split; [exact HW|].
    split; (apply HV; [lia | lia | assumption]).
  - exists i. split; [exact Hi0|]. split; [exact Hi1|].
    split; [apply HV; [lia | lia | exact H1]|].
    split; [apply HV; [lia | lia | exact H2]|].
    apply (garr8_frame segs m m' _ _ HG). intros x Hx. apply Hfr; lia.
Qed.

(* 1. *)
Lemma source_static_frame : forall (m m' : word -> option byte) f b n,
  (forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  source_static segs K m f b n -> source_static segs K m' f b n.
Proof.
  intros m m' f b n Hfr. apply source_static_frame_mode. intros a Ha _. exact (Hfr a Ha).
Qed.

(* 2. *)
Lemma source_window_frame : forall (m m' : word -> option byte) f Wl,
  (forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  source_window segs m f Wl -> source_window segs m' f Wl.
Proof.
  intros m m' f Wl Hfr. apply source_window_frame_mode. intros a Ha _. exact (Hfr a Ha).
Qed.

(* 3. *)
Lemma source_flags_frame : forall (m m' : word -> option byte) f fl,
  (forall a, f <= a < f + 4 -> mbyte segs m' a = mbyte segs m a) ->
  source_flags segs m f fl -> source_flags segs m' f fl.
Proof.
  intros m m' f fl Hfr [Hv Hfl]. split; [|exact Hfl].
  apply (YE00.val_mem_frame segs m m'); [|exact Hv]. intros x Hx. apply Hfr. lia.
Qed.

Lemma source_mode_frame : forall (m m' : word -> option byte) f md,
  (forall a, f + 136 <= a < f + 140 -> mbyte segs m' a = mbyte segs m a) ->
  source_mode segs m f md -> source_mode segs m' f md.
Proof.
  intros m m' f md Hfr [Hv Hmd]. split; [|exact Hmd].
  apply (YE00.val_mem_frame segs m m'); [|exact Hv]. intros x Hx. apply Hfr. lia.
Qed.

(* 4. *)
Lemma asrc_stdio_env_frame : forall (m m' : word -> option byte),
  (forall a, asrc_env_addr a -> mbyte segs m' a = mbyte segs m a) ->
  asrc_stdio_env segs K m -> asrc_stdio_env segs K m'.
Proof.
  intros m m' Hfr (H1 & H2 & H3 & H4 & H5 & (cv & Hcv & H6)). unfold asrc_stdio_env.
  split; [apply (YE00.val_mem_frame segs m m'); [|exact H1]; intros x Hx; apply Hfr; unfold asrc_env_addr; lia|].
  split; [apply (YE00.val_mem_frame segs m m'); [|exact H2]; intros x Hx; apply Hfr; unfold asrc_env_addr; lia|].
  split; [apply (YE00.val_mem_frame segs m m'); [|exact H3]; intros x Hx; apply Hfr; unfold asrc_env_addr; lia|].
  split.
  { apply (garr8_frame segs m m' _ _ H4). intros x Hx. apply Hfr. unfold asrc_env_addr.
    change (Z.of_nat (length (src_mode_Z ++ [0]))) with 3 in Hx. lia. }
  split.
  { apply (garr8_frame segs m m' _ _ H5). intros x Hx. apply Hfr. unfold asrc_env_addr.
    change (Z.of_nat (length (src_modeset_Z ++ [0]))) with 4 in Hx. lia. }
  exists cv. split; [exact Hcv|].
  apply (YE00.val_mem_frame segs m m'); [|exact H6]. intros x Hx. apply Hfr. unfold asrc_env_addr. lia.
Qed.

(* 7. *)
Lemma asource_at_frame_mode : forall (m m' : word -> option byte) f b C p md',
  (forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) -> mbyte segs m' a = mbyte segs m a) ->
  source_mode segs m' f md' ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, asrc_env_addr a -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs m' a = mbyte segs m a) ->
  asource_at segs K m f b C p -> asource_at segs K m' f b C p.
Proof.
  intros m m' f b C p md' Hf Hmd Hb He Hh
    (W & cpos & fl & md & H0 & H1 & H2 & H3 & Hbw & H4 & H5 & Hok & HC & Hs & Hw & Hfl & Hfl24 & _ & Hcp & Henv & Hhd & Hf0).
  assert (HFB : SRC_FILE_BLOCK = 1304) by reflexivity.
  assert (HCO : SRC_COOKIE_OFF = 232) by reflexivity.
  exists W, cpos, fl, md'. cbv zeta.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact Hbw|].
  split; [exact H4|]. split; [exact H5|]. split; [exact Hok|].
  split; [exact (garr8_frame segs m m' b C HC Hb)|].
  split; [exact (source_static_frame_mode m m' f b _ Hf Hs)|].
  split; [exact (source_window_frame_mode m m' f W Hf Hw)|].
  split; [apply (source_flags_frame m m'); [intros x Hx; apply Hf; lia | exact Hfl]|].
  split; [exact Hfl24|]. split; [exact Hmd|].
  split; [apply (YE00.val_mem_frame segs m m'); [intros x Hx; apply Hf; lia | exact Hcp]|].
  split; [exact (asrc_stdio_env_frame m m' He Henv)|].
  split; [apply (YE00.val_mem_frame segs m m'); [intros x Hx; apply Hh; lia | exact Hhd]|].
  exact Hf0.
Qed.

(* 5. *)
Lemma asource_at_frame : forall (m m' : word -> option byte) f b C p,
  (forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, asrc_env_addr a -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs m' a = mbyte segs m a) ->
  asource_at segs K m f b C p -> asource_at segs K m' f b C p.
Proof.
  intros m m' f b C p Hf Hb He Hh Ha.
  assert (HFB : SRC_FILE_BLOCK = 1304) by reflexivity.
  pose proof Ha as (W & cpos & fl & md & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmd & _).
  apply (asource_at_frame_mode m m' f b C p md); [| | exact Hb | exact He | exact Hh | exact Ha].
  - intros a Ha1 _. exact (Hf a Ha1).
  - apply (source_mode_frame m m'); [|exact Hmd]. intros a Ha1. apply Hf. lia.
Qed.

(* 6. *)
Lemma asource_unbuffered_frame : forall (m m' : word -> option byte) f b C p,
  (forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, asrc_env_addr a -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs m' a = mbyte segs m a) ->
  asource_unbuffered segs K m f b C p -> asource_unbuffered segs K m' f b C p.
Proof.
  intros m m' f b C p Hf Hb He Hh [Ha Hw]. split.
  - exact (asource_at_frame m m' f b C p Hf Hb He Hh Ha).
  - exact (source_window_frame m m' f [] Hf Hw).
Qed.

(* 8. *)
Lemma asource_unbuffered_frame_mode : forall (m m' : word -> option byte) f b C p md',
  (forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) -> mbyte segs m' a = mbyte segs m a) ->
  source_mode segs m' f md' ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, asrc_env_addr a -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte segs m' a = mbyte segs m a) ->
  asource_unbuffered segs K m f b C p -> asource_unbuffered segs K m' f b C p.
Proof.
  intros m m' f b C p md' Hf Hmd Hb He Hh [Ha Hw]. split.
  - exact (asource_at_frame_mode m m' f b C p md' Hf Hmd Hb He Hh Ha).
  - exact (source_window_frame_mode m m' f [] Hf Hw).
Qed.

End frame.
