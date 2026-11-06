(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proves fuzz_state's U-form __asan_set_shadow_f5 contract at FSH_Base.PC_set_shadow_f5, the exact type of the FsRt field fr_set_shadow_f5 (lib/A/FSH_Rt.v), from the x form FCf5.set_shadow_f5_contract_x, through FCifaceWin.aset_shadow_realizes_xw_of_x and the bridge aset_shadow_realizesU_of_xw below; it proves no function of its own. It replaces the fs walk SetShadowU.set_shadow_f5_contractU (the FsRt switch to the x route). *)
(* JOIN of the two proved halves for set_shadow, as FSxU.v does for stack_malloc{0,1,3}: fuzz_state's U-form
   set_shadow contract (SetShadowDefU.aset_shadow_realizesU, the shared form whose frame clause exempts the callee's
   own stack window [sp - ESTACK, sp)), derived from fuzz_preset's AR-parametric x-form contract (lib/A/FCf5.v over
   the frame-area interface lib/Reusable/FCiface.v). The strict x form implies the window-exempt x form
   (lib/Reusable/FCifaceWin.v aset_shadow_realizes_xw_of_x); the window-exempt x form at ARx := FSifaceU.ARU_nohp U
   is the U form (aset_shadow_realizesU_of_xw): its pre is FSupoison.ecall_preU conjunct for conjunct (ARU in place
   of AR, and the stack window present on mem instead of on unpoison U mem; the stack is above the shadow, so the
   two readings agree there), and its post is SetShadowDefU.aset_shadow_realizesU's post verbatim (ARU_nohp U is
   FSupoison.ARU by definition). No Axiom, no Admitted. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/FSxSS.v at cb01f65c0f3: fuzz_state.asan-ubsan's U-form __asan_set_shadow_f5 contract at lib/B/FSH_Base.v PC_set_shadow_f5 (0x550a0), the type of lib/B/FSH_Rt.v's fr_set_shadow_f5 at segs := lib/B/YB1v.v tfibsegs, composed from lib/B/FCf5.v through lib/Reusable/FCifaceWin.v and lib/A/FSifaceU.v; it proves no function of its own; it replaces the fs walk lib/B/SetShadowU.v. Changes: module paths (lib.A -> lib.B: AB1v -> YB1v, AB1w -> YB1w, AE34 -> YE34, AF0l -> YF0l, AF0m -> YF0m, AF0x -> YF0x, AE2y -> YE2y, AE3d -> YE3d, and A's FCimg / FCxA / FCm<k>r / FCm<k>s / FCf5 / FSH_Base -> their lib/B twins; the image-generic lib/A FSupoison, FSupoisonU, FSifaceU, SetShadowDefU and FSuwalk stay), nothing else. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require FCiface FCifaceWin.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison SetShadowDefU FSifaceU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FCf5.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSuwalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (segs : list Segment) (B : asyms).

(* The window-exempt x form at ARU_nohp U, for every U, is the shared U form. *)
Lemma aset_shadow_realizesU_of_xw : forall pc v,
(forall U, FCifaceWin.aset_shadow_realizes_xw segs B (FSifaceU.ARU_nohp segs B U) pc v) ->
SetShadowDefU.aset_shadow_realizesU segs B pc v.
Proof.
intros pc v H ly S U W regs mem md cid pos q n HPRE Hin G10 G11 Hn Hq1 Hq2.
pose proof HPRE as ((HAR & Hra & Hal & Hlo & Hhi & HpresE & Hgp & Htp) & HOK & HPO).
assert (HU : FSupoison.ARU segs B ly S U W mem md) by exact (conj HAR (conj HOK HPO)).
pose proof (proj1 HAR) as M.
pose proof (lo_top _ (am_layout _ _ _ _ M)) as (_ & _ & _ & T4 & _ & _ & T7).
unfold kHighMemBeg, kHighMemEnd in T4, T7.
apply (H U ly S [] W regs mem md cid pos q n); [|exact Hin | exact G10 | exact G11 | exact Hn | exact Hq1 | exact Hq2].
split; [exact HU|]. split; [exact Hra|]. split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [|split; [exact Hgp | exact Htp]].
intros a Ha. apply (apresent_unp_off segs B ly S U W mem md (w_H W) a HU);
[change (2 ^ 64) with 18446744073709551616; unfold ESTACK in *; lia
|unfold off_shadow, kHighMemBeg, ESTACK in *; lia
|exact (HpresE a Ha)].
Qed.
End a.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The FsRt field fr_set_shadow_f5 (lib/B/FSH_Rt.v), discharged through the x route. *)
Theorem set_shadow_f5_contractU_x : forall (B : asyms), AR_laws tfibsegs B -> TfibSyms B -> SetShadowDefU.aset_shadow_realizesU tfibsegs B FSH_Base.PC_set_shadow_f5 0xf5.
Proof.
intros B LAWS TB.
apply (aset_shadow_realizesU_of_xw tfibsegs B FSH_Base.PC_set_shadow_f5 0xf5). intros U.
apply (FCifaceWin.aset_shadow_realizes_xw_of_x tfibsegs B (FSifaceU.ARU_nohp tfibsegs B U)).
exact (FCf5.set_shadow_f5_contract_x B (FSifaceU.ARU_nohp tfibsegs B U)
(FSifaceU.fs_iface_ARU tfibsegs B LAWS U) TB).
Qed.

End x.
