(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths and module names changed; 571 of its 675 lines of code are new or changed and 468 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMW_rd_pre_k.v, with its module paths and module names changed; 56 of its 124 lines of code are new or changed and 607 lines of the source are left out. *)
(* G4.ExDecl, IMAGE B: what a caller keeps across a program call (FMW_ex_decl_d5.v, the call of plain): C strings
   with their homes, and the read-only view. B twin of lib/A/FMW_ex_decl_d5_kits.v (06d82004dc3), unchanged but for
   the Requires (lib.A AB1v -> lib.ReusableB YB1v; FMPstat, FMH_*, the kit from lib.B); A's file copies G5's kit
   (a Theorem Labs lane's lib/A/FMW_kitS.v:38-137: shadow_hull_vis_sub, word_end_mono, cstr_ok_kept_blk, cstr_ok_suffix,
   cstr_ok_kept, cstr_kept_kept; lib/A/FMW_K.v:397-414: roP_img, arodata_kept) under d5k_ names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP09 YI04 YI00 YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_decl_d5_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma d5k_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
lia.
Qed.
(* the 8-byte word end is monotone *)
Lemma d5k_word_end_mono : forall x y, x <= y -> x - x mod 8 + 8 <= y - y mod 8 + 8.
Proof.
intros x y H. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* the read-only bytes are image bytes *)
Lemma d5k_roP_img : forall a, in_roP tfibsegs FM_RLO FM_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FM_RLO) && (FM_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the read-only view rides through a journal whose footprint neither opens the sink nor touches read-only bytes *)
Lemma d5k_arodata_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> ~ YI16.sink_open_fp FP ->
  (forall a, in_roP tfibsegs FM_RLO FM_RHI a -> ~ inFP FP a) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hcl Hro HR a Ha Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (d5k_roP_img a Ha) Ho He (Hro a Ha) (fp_spares_closed FP a Hcl)). exact (HR a Ha Ho He).
Qed.

(* a string in a live block: cstr_ok carried over a journal that keeps the block and leaves the string's bytes out of
   its footprint *)
Lemma d5k_cstr_ok_kept_blk : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> ~ inFP FP a) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin Hin' Hb Hbm HnF
  ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin Hin'); [rewrite Hrq; lia | replace (b + (a - b)) with a by lia; apply HnF; lia]. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' b m p _ HAR' Hin' Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly' S' W' mem' md' b m HAR' Hin') as (_ & Hhv').
  apply (d5k_hull_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (d5k_block_word_tail_vis B LAWS ly' S' W' mem' md' b m HAR' Hin' Hm).
pose proof (d5k_word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.

(* a suffix of a C string is a C string with the same NUL *)
Lemma d5k_cstr_ok_suffix : forall (W : world tfibsegs) mem p0 l0 k, (k <= length l0)%nat ->
  cstr_ok tfibsegs W mem p0 l0 -> cstr_ok tfibsegs W mem (p0 + Z.of_nat k) (skipn k l0).
Proof.
intros W mem p0 l0 k Hk ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
assert (Hlen : Z.of_nat (length (skipn k l0)) = Z.of_nat (length l0) - Z.of_nat k) by (rewrite length_skipn; lia).
assert (Eend : p0 + Z.of_nat k + Z.of_nat (length (skipn k l0)) = p0 + Z.of_nat (length l0)) by lia.
split; [split|].
- rewrite <- (firstn_skipn k l0) in Hg. rewrite <- app_assoc in Hg. apply (garr8_app tfibsegs) in Hg as [_ Hg].
  rewrite length_firstn in Hg. replace (Nat.min k (length l0)) with k in Hg by lia. exact Hg.
- rewrite <- (firstn_skipn k l0) in Hnz. apply Forall_app in Hnz as [_ Hnz]. exact Hnz.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
  split; [intros x Hx; apply Hra; lia|].
  split; [apply (d5k_hull_sub _ p0 (Z.of_nat (length l0) + 1)); [exact Hhv | lia | lia | lia]|].
  intros a Ha. rewrite Eend in Ha. exact (Htl a Ha).
Qed.

(* a C string the caller keeps (FMH_Fn.v cstr_kept) after a program call: the block arm by d5k_cstr_ok_kept_blk (a
   footprint of image bytes misses every block), the read-only arms (suffixes of fm's listed strings) by fm_img_facts
   at the new state *)
Lemma d5k_cstr_ok_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l,
  fm_img_facts tfibsegs B ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  (forall a, inFP FP a -> in_img tfibsegs a) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem') ->
  cstr_kept B ly S p l -> cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l IMG HJ Hinc HFP HRO' Hk Hc.
pose proof HJ as (HAR' & _).
destruct Hk as [(b & m & Hin & Hb & Hbm) | (p0 & l0 & kk & Hsrc & Hkl & -> & ->)].
- apply (d5k_cstr_ok_kept_blk STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin (Hinc _ Hin) Hb Hbm);
    [|exact Hc].
  intros a Ha Hf. apply (blk_img tfibsegs B LAWS ly' S' W' mem' md' b m a HAR' (Hinc _ Hin)); [|exact (HFP a Hf)].
  assert (req_size m = m) as -> by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
- apply (d5k_cstr_ok_suffix W' mem' p0 l0 kk Hkl).
  destruct Hsrc as [Hro | (ps & Hf & ->)].
  + destruct (IMG ly' S' W' mem' md' HAR' HRO') as (_ & _ & _ & HS & _).
    exact (proj1 (proj1 (Forall_forall _ _) HS (p0, l0) Hro)).
  + destruct (IMG ly' S' W' mem' md' HAR' HRO') as (_ & _ & _ & _ & HF). exact (proj1 (HF p0 ps Hf)).
Qed.

(* the home itself: the block arm through a kept block, the read-only arms are constant *)
Lemma d5k_cstr_kept_kept : forall ly S ly' S' p l,
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  cstr_kept B ly S p l -> cstr_kept B ly' S' p l.
Proof.
intros ly S ly' S' p l Hinc [(b & m & Hin & H1 & H2) | Himg].
- left. exists b, m. split; [exact (Hinc _ Hin) | split; assumption].
- right. exact Himg.
Qed.
End s.
