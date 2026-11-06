(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfRealloc.v, with its module paths and module names changed; 63 of its 109 lines of code are new or changed and 93 lines of the source are left out. *)
(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YG0dcfR.v, sha256 b85371cd29aa65e96a9fcaefcb0e570d673920e99d4d6007b589368d877438c0 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree (lane W's AllocG / DeallocG / DMspec / DMiface / ImgBaseDG / DGif0, the F1 core's
   YGcfRehidePost / YGcfRecStep, and the per-image cf files of this carry) name lib/B; a sentence is split at a directory
   change, the module order kept.
*)
(* The cf call forms under the re-hide (F1 priming row R1, the layer source; TkSecLink, 2026-10-30).

   The free path can hide shadow pages again (the secondary recycle's madvise, F1 core YA0nH / YG0dH /
   YGcfRehidePost), so a caller that binds across a free needs the free contract in the primed form: the
   realization amreal' over the fixed re-hideable zone RZ_cf, and the call post acall_post_cf_rh (its world only
   grows outside dead_shadow, and its view frame excepts dead_shadow). This file states that twin,
   afree_realizes_cf_rh, beside YG0dcf.afree_realizes_cf, and proves that the released contract implies it
   (a free that re-hides nothing). The same for realloc of a live block, which binds across the free of the old
   block: arealloc_realizes_cf_rh beside YGcfRealloc.arealloc_realizes_cf. (realloc(NULL, n) is a malloc and
   binds across no free, so arealloc_null_realizes_cf has no twin.) It is a separate file because
   YGcfRehidePost.v, where acall_post_cf_rh is, Requires YG0dcf.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfPath ReallocP YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.
Local Notation code := (as_code B).

(* YG0dcf.free_leaf_cf with the call post acall_post_cf_rh. The raw-memory frame keeps its released shape: the
   re-hide step changes no memory (YGcfRehidePost, Section F). *)
Definition free_leaf_cf_rh (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf_rh segs B ASTACK ly S Hp W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
qtight (snd r) /\
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
 mem' x = mem x).

(* The primed cf free contract: YG0dcf.afree_realizes_cf with amreal' over RZ_cf and the leaf above. *)
Definition afree_realizes_cf_rh : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 code) regs ch) S ->
amreal' segs RZ_cf (free_cf p (call_trace ly (pc_free_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_free code) regs mem md)
(free_leaf_cf_rh ly S Hp W regs mem md p n).

Lemma free_leaf_cf_rh_of : forall ly S Hp W regs mem md p n r W' c',
free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' -> free_leaf_cf_rh ly S Hp W regs mem md p n r W' c'.
Proof.
intros ly S Hp W regs mem md p n r W' c' (ly' & regs' & mem' & md' & HC & HP & REST).
exists ly', regs', mem', md'. split; [exact HC|]. split; [|exact REST].
exact (acall_post_cf_rh_of segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.

(* A free that re-hides nothing: the released contract gives the primed one. *)
Theorem afree_realizes_cf_rh_of : afree_realizes_cf segs B -> afree_realizes_cf_rh.
Proof.
intros H ly S Hp W regs mem md p n ch PRE Hpn Hr Hh Htr.
eapply amreal'_mono; [| apply amreal_amreal'; exact (H ly S Hp W regs mem md p n ch PRE Hpn Hr Hh Htr)].
intros r W' c' HL. exact (free_leaf_cf_rh_of ly S Hp W regs mem md p n r W' c' HL).
Qed.
(* YGcfRealloc.realloc_leaf_cf with the call post acall_post_cf_rh; every other conjunct is the released one. *)
Definition realloc_leaf_cf_rh (ly : alayout) (S : astate) (Hp : list Z)
(W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_cf_rh segs B ASTACK ly S (realloc_hp_cf B ly p (fst r) Hp) W regs mem md
(fun a => (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
\/ (fst r <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old)
\/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(fst r <> PNull -> forall i, 0 <= i < Z.min n_old n ->
aview segs (w_H W') mem' (sptr_addr B ly' (fst r) + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
(fst r = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
xs_placed_cf ly' (snd r) /\
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ (fst r <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n_old)
    \/ Exists (in_zr (bv_unsigned x)) (xs_cf ly S ++ xs_cf ly' (snd r))) ->
 mem' x = mem x).

(* The primed realloc contract: YGcfRealloc.arealloc_realizes_cf with amreal' over RZ_cf and the leaf above. *)
Definition arealloc_realizes_cf_rh (Hp : list Z) (pc : Z) : Prop :=
forall ly S W regs mem md p n_old n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly cf_pc_realloc_ra0 regs ch) S ->
amreal' segs RZ_cf (realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => realloc_leaf_cf_rh ly S Hp W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> mt_refused malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S (snd r))).

Lemma realloc_leaf_cf_rh_of : forall ly S Hp W regs mem md p n_old n r W' c',
realloc_leaf_cf segs B ly S Hp W regs mem md p n_old n r W' c' ->
realloc_leaf_cf_rh ly S Hp W regs mem md p n_old n r W' c'.
Proof.
intros ly S Hp W regs mem md p n_old n r W' c' (ly' & regs' & mem' & md' & HC & HP & REST).
exists ly', regs', mem', md'. split; [exact HC|]. split; [|exact REST].
exact (acall_post_cf_rh_of segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.

(* A realloc that re-hides nothing: the released contract gives the primed one. *)
Theorem arealloc_realizes_cf_rh_of : forall Hp pc,
arealloc_realizes_cf segs B Hp pc -> arealloc_realizes_cf_rh Hp pc.
Proof.
intros Hp pc H ly S W regs mem md p n_old n ch PRE Hin Hr Hh Hn Hrange Hlive Htr.
eapply amreal'_mono;
[| apply amreal_amreal'; exact (H ly S W regs mem md p n_old n ch PRE Hin Hr Hh Hn Hrange Hlive Htr)].
intros r W' c' (HL & HR). split; [exact (realloc_leaf_cf_rh_of ly S Hp W regs mem md p n_old n r W' c' HL) | exact HR].
Qed.
End J.
End G.
