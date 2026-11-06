(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X047 X0jw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0ms X0mx X0n0 X0k2 X0m4 X0m6 X0li X0lh X0ll X0kj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X03o X03r X03n X03l X03m X03k
X0fy X0fg X0ed X0ef.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X002.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0v5 X1ab.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0up X0um X0uk X0ul X0uj X16j X161 X14y X150.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0r1.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0ms OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0mx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0n0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0k2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0m4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0m6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0li OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0lh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0ll OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0kj.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X03o.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0up OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0um OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ul OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X150.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r1.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hrt_fx : X0ms.FPState := X0ms.fx0.

Section StartRT.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : STARTF RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg bsegs R a_main FULL model).
Proof.
pose proof (hsa_argH_high ph sp rdraw argv envp uid hw Hsp Hva) as AH.
destruct (rt_init_glue A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hlim E ch R FULL model HC HTR)
as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
pose proof (hsa_sp0 A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E ch R FULL model HC) as Husp.
rewrite Husp in Hsp0, Hsig.
exact (hs_start A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok Hsegtop E ch R FULL model HC HT
RTA LIB Σ0 Hallow Hawf Hminv Hartm Hsp0 Hart Hsig HLIB).
Qed.

Theorem hs_hole_rt : forall T,
(forall c, STARTF RTA OUT_repA ERR_repA XENVA LIB argv fs c -> realizes bsegs c T) ->
srealizes bsegs (APS.cfg_of bsegs R a_main FULL model) T.
Proof.
intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start_rt.
Qed.

End StartRT.
End B_TWIN.

Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hrt_fx : X0ms.FPState := X0ms.fx0.

Section StartRT.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : STARTF RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg asegs R a_main FULL model).
Proof.
pose proof (hsa_argH_high ph sp rdraw argv envp uid hw Hsp Hva) as AH.
destruct (rt_init_glue A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hlim E ch R FULL model HC HTR)
as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
pose proof (hsa_sp0 A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E ch R FULL model HC) as Husp.
rewrite Husp in Hsp0, Hsig.
exact (hs_start A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok Hsegtop E ch R FULL model HC HT
RTA LIB Σ0 Hallow Hawf Hminv Hartm Hsp0 Hart Hsig HLIB).
Qed.

Theorem hs_hole_rt : forall T,
(forall c, STARTF RTA OUT_repA ERR_repA XENVA LIB argv fs c -> realizes asegs c T) ->
srealizes asegs (APS.cfg_of asegs R a_main FULL model) T.
Proof.
intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start_rt.
Qed.

End StartRT.
