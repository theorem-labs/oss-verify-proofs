(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfRhLift.v, with its module paths changed. *)
(* Theorem Labs, 2026-10-30: the shared lifting helper of the primed port.
   ra_rh_of_SRr is the lemma of lib/A/Prog/FuzzReallocAp.v:852-858 at commit 5e9d09d04d3a (the same text is
   at commit e4fc05dc07bf), with that Section's variables SEGS / RZ made explicit arguments; the proof is its
   five lines verbatim. GENERIC: no image, no unit, no address. It lifts a plain SRr segment whose continuation is
   already in the primed relation (YA0nH.SRr' at a zone RZ) to SRr', through YA0nH.SRr_SRr' and YA0nH.wle'_trans, so
   every owner of a walk that ends in a re-hide cites one lemma.
   RZ_cf_app: an application address (YG0f.app_addr, the predicate
   YGcfRehidePost.dead_shadow_new_app uses) is never in the re-hide zone YGcfRehidePost.RZ_cf. From the constants only,
   at every RunCeil: RZ_cf's low part is (shadow_addr 4096 - 4096, shadow_addr kLowShadowBeg + 4096) =
   (2147447296, 2415885824), above the low application range [4096, kLowShadowBeg = 2147446784); its high part is
   (shadow_addr kHighMemBeg - 4096, shadow_addr ASAN_CEIL + 4096), whose top is at most
   shadow_addr 0x7fffff800000 + 4096 = 17594332450816 (ASAN_CEIL_range), below kHighMemBeg = 17594333495296 where the
   high application range starts. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YA0n YM05 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.

Section rh. Context {fx : YK11.FPState}.

Lemma ra_rh_of_SRr : forall (segs : list Segment) (RZ : Z -> Prop) W c (Q : world segs -> config -> Prop),
  SRr segs W c (fun W' c' => YA0nH.SRr' segs RZ W' c' Q) -> YA0nH.SRr' segs RZ W c Q.
Proof.
intros segs RZ W c Q H. pose proof (YA0nH.SRr_SRr' segs RZ W c _ H) as H'.
unfold YA0nH.SRr', YA0nH.SRrG in *. intros HI T HK. apply (H' HI T). intros W' c' Hle HI' HQ.
apply (HQ HI' T). intros W'' c'' Hle' HI'' HQ'. exact (HK W'' c'' (YA0nH.wle'_trans segs RZ _ _ _ Hle Hle') HI'' HQ').
Qed.

End rh.

Section app. Context {rc : YM05.RunCeil}.

Lemma RZ_cf_app : forall a, app_addr a -> ~ YGcfRehidePost.RZ_cf a.
Proof.
intros a [H0 HA] HR. pose proof (proj1 (@ASAN_CEIL_range rc)) as [C1 C2].
assert (HR' : (2147447296 < a < 2415885824) \/ (2201439133696 < a < shadow_addr ASAN_CEIL + 4096)) by exact HR.
assert (E4 : shadow_addr ASAN_CEIL <= shadow_addr 0x7fffff800000) by (apply YGcfRehidePost.shadow_addr_mono; exact C2).
assert (E5 : shadow_addr 0x7fffff800000 = 17594332446720) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg in HA.
destruct HR' as [R|R]; destruct HA as [HL|[HH1 HH2]]; lia.
Qed.

End app.
