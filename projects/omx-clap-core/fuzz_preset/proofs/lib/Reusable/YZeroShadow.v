(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: the image-B twin of lib/A/AZeroShadow.v, written for omx-clap-core/fuzz_preset's asan-ubsan build: the same zero-shadow lemmas over the generated Tfib_zero_shadow of lib/Reusable/YF0m.v, with the end of asan_globals taken by NAME from lib/Reusable/YImgCellsB.v (B_ASAN_GLOBALS_HI). lib/Reusable/YD1o.v keeps bss_zero_shadow and bss_shadow_facts as instances of the lemmas here. No literal of either image appears in this file, and it imports no walk file, so it builds on the generated tables alone. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgCellsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The shadow words that shadow_hull_vis reads for [p, p + n) (its 64-byte shadow hull) lie inside the shadow of the
   range r. Tfib_zero_shadow (A/AF0m.v, generated from the image's registered globals) is the image minus the holes
   (each registered global's guard bytes, and the descriptor table), so an interval whose 64-byte shadow hull misses
   every hole lies inside one gap, which is one range of the list. A user does not restate that geometry: it asks
   existsb over the generated list, decided by vm_compute. *)
Definition shadow_hull_in (p n : Z) (r : Z * Z) : bool :=
(shadow_addr (fst r) <=? shadow_addr p / 8 * 8) && (shadow_addr (p + n - 1) / 8 * 8 + 8 <=? shadow_addr (fst r + snd r)).
(* The zero-shadow ranges of the image's writable tail: the ranges of Tfib_zero_shadow that start at or above the end
   of asan_globals. The registered globals of .bss split that tail, so it is not one zero-shadow interval. *)
Definition TFIB_GLOBALS_END : Z := YImgCellsB.B_ASAN_GLOBALS_HI.
Definition Tfib_bss_zero_shadow : list (Z * Z) := List.filter (fun r => TFIB_GLOBALS_END <=? fst r) Tfib_zero_shadow.
Lemma tfib_zero_aligned : List.forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bss_hull_in_all : forall p n,
List.existsb (shadow_hull_in p n) Tfib_bss_zero_shadow = true -> List.existsb (shadow_hull_in p n) Tfib_zero_shadow = true.
Proof.
intros p n Hex. apply List.existsb_exists in Hex as (r & Hr & Hh). apply List.existsb_exists. exists r.
split; [exact (proj1 (proj1 (List.filter_In _ _ _) Hr)) | exact Hh].
Qed.
(* [p, p + n) inside [a, b): the hull of [p, p + n) lies inside the hull of [a, b). *)
Lemma shadow_hull_sub : forall L a b p n, a <= p -> p + n <= b ->
List.existsb (shadow_hull_in a (b - a)) L = true -> List.existsb (shadow_hull_in p n) L = true.
Proof.
intros L a b p n Ha Hb Hex. apply List.existsb_exists in Hex as (r & Hr & Hh). apply List.existsb_exists. exists r. split; [exact Hr|].
unfold shadow_hull_in in *. apply andb_prop in Hh as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply andb_true_intro. split; apply Z.leb_le; unfold shadow_addr in *.
- assert (L1 : a / 8 <= p / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (SHADOW_OFF + a / 8) / 8 <= (SHADOW_OFF + p / 8) / 8) by (apply Z.div_le_mono; lia). lia.
- assert (L1 : (p + n - 1) / 8 <= (a + (b - a) - 1) / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (SHADOW_OFF + (p + n - 1) / 8) / 8 <= (SHADOW_OFF + (a + (b - a) - 1) / 8) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma zero_range_hull : forall (rd : Z -> option Z) lo len p n, lo mod 8 = 0 -> len mod 8 = 0 -> zero_shadow rd SHADOW_OFF lo len ->
shadow_hull_in p n (lo, len) = true ->
range_addressable rd SHADOW_OFF p n /\ (forall s, shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> rd s = Some 0).
Proof.
intros rd lo len p n Ha1 Ha2 HZ Hh.
unfold shadow_hull_in in Hh. cbn [fst snd] in Hh. apply andb_prop in Hh as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold shadow_addr in H1, H2.
pose proof (Z.div_mod lo 8 ltac:(lia)) as Dlo. pose proof (Z.div_mod len 8 ltac:(lia)) as Dlen.
pose proof (Z.div_mod (lo + len) 8 ltac:(lia)) as Dll. pose proof (Z.mod_pos_bound (lo + len) 8 ltac:(lia)) as Bll.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Bp.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Bq.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as Ds1. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as Bs1.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as Ds2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as Bs2.
split.
- intros x Hx. apply (zero_shadow_range rd SHADOW_OFF lo len Ha1 Ha2 HZ x). lia.
- intros s Hs. unfold shadow_addr in Hs.
replace s with (shadow_of_addr SHADOW_OFF lo + (s - shadow_of_addr SHADOW_OFF lo)) by ring.
apply (HZ (s - shadow_of_addr SHADOW_OFF lo)). unfold shadow_of_addr. lia.
Qed.
Section w.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma tfib_zero_shadow_at : forall ly S W mem md r, AR tfibsegs B ly S W mem md -> In r Tfib_zero_shadow ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
Proof.
intros ly S W mem md r HAR Hr.
apply (al_zshadow _ _ LAWS ly S W mem md r HAR).
unfold zero_shadow_ranges. right. rewrite (ts_zsh B HB). exact Hr.
Qed.
Lemma tfib_zero_hull_facts : forall ly S W mem md p n, AR tfibsegs B ly S W mem md ->
List.existsb (shadow_hull_in p n) Tfib_zero_shadow = true ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n /\
(forall s, shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> aview tfibsegs (w_H W) mem s = Some 0).
Proof.
intros ly S W mem md p n HAR Hex. apply List.existsb_exists in Hex as ([lo len] & Hr & Hh).
pose proof (proj1 (List.forallb_forall _ _) tfib_zero_aligned (lo, len) Hr) as Ha. cbn [fst snd] in Ha.
apply andb_prop in Ha as [Ha1 Ha2]. apply Z.eqb_eq in Ha1. apply Z.eqb_eq in Ha2.
exact (zero_range_hull _ lo len p n Ha1 Ha2 (tfib_zero_shadow_at ly S W mem md (lo, len) HAR Hr) Hh).
Qed.
Lemma tfib_zero_shadow_facts : forall ly S W mem md p n, AR tfibsegs B ly S W mem md ->
List.existsb (shadow_hull_in p n) Tfib_zero_shadow = true ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Proof.
intros ly S W mem md p n HAR Hex. destruct (tfib_zero_hull_facts ly S W mem md p n HAR Hex) as [HRA HZ].
split; [exact HRA|]. intros s Hs. rewrite (HZ s Hs). discriminate.
Qed.
End w.
End z.
