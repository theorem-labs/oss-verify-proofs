(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC08 YC4z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis segs_low : forall a, in_img trasegs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env trasegs B.
Hypothesis ML : model_laws (as_universe B).
Lemma rg_aj_free_optD : afree_realizes trasegs B ->
forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n (o : Z) spw raw ch rest,
st_ok trasegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free (as_code B) -> ss_resv ss = None ->
ajournal trasegs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Permutation (ablocks B lyc Sc) (optb pa n ++ rest) ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
vev Sc < VEV_MAX ->
chain_pre lyc (aview trasegs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms) ch) (as_universe B) ->
(pa <> 0 -> In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr trasegs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved (ms_regs ms) regs2 /\
Permutation (ablocks B ly2 S2) rest /\
frames S2 = frames Sc /\
bud_le Sc S2 1 0 0 0 /\
acall_kept trasegs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <> 0 /\ pa <= a < pa + req_size n)).
Proof.
intros AFREE W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o spw raw ch rest
HS Hpc Hrv HJ HPerm Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch Htr HFP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) E ss ms HS Hrv), Hpc.
unfold optb in HPerm. destruct (Z.eqb_spec pa 0) as [-> | Hp].
-
eapply SRr_mono.
{ eapply (aj_free_null_atD trasegs B LAWS segs_low errno_low ML AFREE); eassumption. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPm & Hfr & HBD & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [eapply Permutation_trans; [exact HPm | exact HPerm]|]. split; [exact Hfr|]. split; [exact HBD|].
eapply rg_acall_kept_weaken; [|exact HK]. intros a [].
-
assert (Hin : In (pa, n) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity]).
eapply SRr_mono.
{ eapply (aj_free_atD trasegs B LAWS segs_low errno_low ML AFREE W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem md own lyc Sc mdc k pa n o raw ch);
try eassumption. intros Hin0. exact (HFP Hp Hin0). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfr & HBD & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split.
{ rewrite Ebl2. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (pa, n)). rewrite <- Ebl.
apply Permutation_sym. exact HPerm. }
split; [exact Hfr|]. split; [exact HBD|].
eapply rg_acall_kept_weaken; [|exact HK]. intros a Ha. split; [exact Hp | exact Ha].
Qed.
End c.
End b.
