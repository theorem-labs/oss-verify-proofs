(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the APATH form of
   malloc_cf's post, for walks that hold a realized path (amreal / AllocG.alloc_leaf give
   `apath (malloc_cf n tr S) trc r /\ gflag trc = true`). It composes malloc_ok_cf (YG07cf.v, over
   atok_cf) with atok_cf_apath (YGcfTok.v). The post holds on EVERY path, so no gflag premise is
   needed here; gflag matters only for excluding PNull (YGcfPath.v). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG06bcf YG07cf YGcfPath.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section A. Context {ci : CfImg} {cp : CfParams}.

Theorem malloc_cf_apath_post : forall U s n tr trc r,
universe_ok U -> Wf_cf U s -> 0 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
Z.of_nat (length (st_sec_arr s)) < cf_sec_live_max -> ERRB_ROOM s -> batch_room_cf s ->
apath (malloc_cf n tr s) trc r ->
malloc_post_cf U s n true r.
Proof.
intros U s n tr trc r HU HW Hn HL Htr HS HE HB Hp.
destruct (atok_cf_apath (malloc_cf n tr s) true (malloc_post_cf U s n) trc r
(malloc_ok_cf U s n tr HU HW Hn HL Htr HS HE HB) Hp) as [ns H].
exact H.
Qed.

(* The success case unfolded, the facts h-pre-b1's driver binds. *)
Corollary malloc_cf_apath_success : forall U s n tr trc p s',
universe_ok U -> Wf_cf U s -> 0 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
Z.of_nat (length (st_sec_arr s)) < cf_sec_live_max -> ERRB_ROOM s -> batch_room_cf s ->
apath (malloc_cf n tr s) trc (p, s') -> p <> PNull ->
Wf_cf U s' /\ st_nev s + 1 <= st_nev s' /\ secs_ext_cf s s' /\ frames s' = frames s /\
blocks s' = blocks s ++ [(p, n)] /\ ~ In p (map fst (blocks s)) /\ (qtight s -> qtight s').
Proof.
intros U s n tr trc p s' HU HW Hn HL Htr HS HE HB Hp Hnn.
pose proof (malloc_cf_apath_post U s n tr trc (p, s') HU HW Hn HL Htr HS HE HB Hp) as H.
unfold malloc_post_cf in H. destruct H as (W' & N & X & F & B' & Q).
destruct p; try (exfalso; apply Hnn; reflexivity); destruct B' as [B1 B2];
exact (conj W' (conj N (conj X (conj F (conj B1 (conj B2 Q)))))).
Qed.

End A.

(* ---------------------------------------------------------------------------- *)
(* The REFUSED arm, for preset's allocator walks (S1, a Theorem Labs lane): from what the walk holds at *)
(* a NULL result (the leaf, the model path with every ask granted, and the wrapper's    *)
(* errno / OOM-byte writes), malloc_cf_null_post. gflag t = true is what excludes the   *)
(* refused-ask paths (amreal_SRr04, YG0d.v:185-207, and AllocG.alloc_leaf export it).   *)
Section N. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Theorem malloc_cf_null_post_of_leaf : forall segs B ly S Hp W regs mem md n ch tr t S' W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch ->
apath (malloc_cf n tr S) t (PNull, S') -> gflag t = true ->
malloc_leaf_cf segs B ly S Hp W regs mem md n (PNull, S') W' c' ->
malloc_cf_null_post segs B ly S Hp W regs mem md n (PNull, S') W' c'.
Proof.
intros segs B ly S Hp W regs mem md n ch tr t S' W' c' Hpre Hap Hg HL.
pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 Hpre))) as W0. unfold Wf_cf in W0.
pose proof (shape_cf_of_WfP_cf _ _ _ _ _ W0) as Hsh.
destruct (malloc_cf_null_path n tr S t S' Hsh Hap Hg) as (Hb & Hch & Hfp & Hex).
destruct HL as (ly' & regs' & mem' & md' & Hc & Hpost & Hr & Hq & Hx & _ & _ & HR).
destruct (Hx eq_refl) as [He Ho].
unfold malloc_cf_null_post. split; [reflexivity|].
exists ly', regs', mem', md'. split; [exact Hc|].
split.
{ unfold acall_post_cf in *. destruct Hpost as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))).
intros a Ha N1 N2 N3 N4. apply (A6 a Ha N1 N2 N3).
intros [[Hf _]|HX]; [apply Hf; reflexivity | exact (N4 HX)]. }
split; [exact Hr|]. split; [exact Hq|]. split; [exact Hb|]. split; [exact Hch|].
split; [exact He|]. split; [exact Ho|]. split; [exact Hfp|]. split; [exact Hex|].
intros x N1 N2 N3 N4. apply (HR x N1 N2 N3).
intros [[Hf _]|HX]; [apply Hf; reflexivity | exact (N4 HX)].
Qed.

End N.
