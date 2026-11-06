(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 479 of its 545 lines of code are new or changed and 448 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B_S1.v, with its module names changed; 21 of its 68 lines of code are new or changed and 498 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B_Link.v; 196 of its 235 lines of code are new or changed and 29 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B_Inst.v, with its module paths and module names changed; 14 of its 39 lines of code are new or changed and 210 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the IMAGE-FREE checkers of S1ImgA.v / S1ImgB.v, moved here so that a B' file can use them
   without Requiring lib/A/Prog/S1ImgA.v (which loads image A's PRH_Img / PAImg_prog instances: an unpinned implicit PA
   in a B' file could then resolve to PI_prog_A; a Theorem Labs lane 21:45Z, measured by a Theorem Labs lane). This file Requires no
   lib/A image file: only the Reusable model files and the kit's PRH_Base.
   wv_b / in_img_b / in_ro_b decide writability, image membership and read-only-ness of one byte over any segment list;
   pst_allb checks a predicate at every byte of a list of ranges; the soundness lemmas turn them into the Prop facts. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YP08 YL0b YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
Import ListNotations.
Local Open Scope Z_scope.

(* the byte a is writable whatever the memory holds: wview with the empty memory is already Some *)
Definition wv_b (segs : list Segment) (a : Z) : bool :=
  match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition in_img_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
Definition in_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
  || ((rlo <=? a) && (a <? rhi)).
(* f holds at every byte of every range of P *)
Definition pst_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.

Lemma pst_allb_sound : forall f P a, pst_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold pst_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.

(* the window of one byte at a (LENGTH 1) of YL0b's seg_win_check is wv_b at a *)
Lemma writable_of_wv_b : forall segs (m : word -> option byte) a, wv_b segs a = true -> writable_at segs m a.
Proof.
intros segs m a H. unfold writable_at. apply (seg_win_wview segs a 1 m a); [| lia | lia].
change (wv_b segs a && true = true). rewrite H. reflexivity.
Qed.

Lemma in_img_b_sound : forall segs a, in_img_b segs a = true -> in_img segs a.
Proof.
intros segs a H. apply existsb_exists in H as (s & Hs & H). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | lia].
Qed.

Lemma in_ro_b_complete : forall segs rlo rhi a, in_roP segs rlo rhi a -> in_ro_b segs rlo rhi a = true.
Proof.
intros segs rlo rhi a [(s & Hs & Hw & Hr) | Hr]; unfold in_ro_b; apply orb_true_intro; [left | right].
- apply existsb_exists. exists s. split; [exact Hs|]. rewrite Hw. cbn [negb andb].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
