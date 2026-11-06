(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem
   statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc image A from
   proofs/libreac/fuzz_knock/lib/A/APgBase.v at origin/ossv/recipes 6ebe35ba632, with its module paths changed:
   lines 18-46 are taken as they stand (in_roP, arodata_okP, ro_below_ofl, ro_spares, arodata_ok_journalP);
   lines 47-63 (afobj and apost_base) are left out, because fuzz_qdisc's harness takes no fake-stack frame and
   hands its callees no object -- its two callees take their arguments in registers only (h-small-a3).
   rule 24 (reuse): no function is proved here; this file carries the image-independent read-only-data
   predicate the three qdisc contracts are stated over. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition in_roP (segs : list Segment) (rlo rhi : Z) (a : Z) : Prop :=
(exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (rlo <= a < rhi).
Definition arodata_okP (segs : list Segment) (rlo rhi : Z) (B : asyms) (rd : reader) : Prop :=
forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Class ro_below_ofl (segs : list Segment) (rlo rhi : Z) {SK : YI16.sink_head} : Prop :=
ro_below_ofl_at : forall a, in_roP segs rlo rhi a -> a < YI16.sk_ofl_head.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variables rlo rhi : Z.
Hypothesis relro_img : forall a, rlo <= a < rhi -> in_img segs a.
Context {RO : ro_below_ofl segs rlo rhi}.
Lemma ro_spares : forall FP a, in_roP segs rlo rhi a -> fp_spares FP a.
Proof. intros FP a Hro. apply fp_spares_below. exact (@ro_below_ofl_at segs rlo rhi SK RO a Hro). Qed.
Lemma arodata_ok_journalP : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (ro_spares FP a Hro)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (relro_img a Hgot).
Qed.
End e.
End d.
