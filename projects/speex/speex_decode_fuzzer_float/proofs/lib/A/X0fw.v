(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb
X0il X0gp X0h2 X0j4 X0hf X0j3 X0hi X0fy X0fg X0da X0g4 X0d8 X0fq X04b
X0d7 X0ff X0h3 X0gy X0gz X0h0 X0fv.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X173 X18c X17w X196 X17a X17n X19n X180 X19m X183 X16j X161 X13v X16p X13t X16b X0v9 X13s X160 X17o X17j X17k X17l X16g.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X160 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16g.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Theorem rta_stack_malloc_5 : stack_malloc_contract RTA 5.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size
FDO MST Hk -> _ Hlen Hcr ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
pose proof CALL as (ST & LOW & LOR & SPT & SPA).
destruct (sm_pre Σ m 5%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
& M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
assert (W1 : evt bsegs (sm5_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 5))
(fss_flags (fs_of Σ 5)) lo m)
(entry_st ra sp gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc (e_stack_malloc 5) m)).
{ unfold entry_st.
exact (stack_malloc_5_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(l_FSB (lay Σ)) (fss_hint (fs_of Σ 5)) (fss_flags (fs_of Σ 5)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold sm5_post in Hc1.
apply AST_exI in Hc1 as (jn & Hc2).
assert (PURE : (jn < 512)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 5) + Z.of_nat jn) mod 512)) (fss_flags (fs_of Σ 5)) 1 = 0).
{ destruct Hc2 as (_ & HP & _).
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
split; assumption. }
destruct PURE as (Hj & Hfree).
apply (sm_finish Σ PMc F fc ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 5%nat (Z.of_nat jn) lo _ c1 ART0 ltac:(lia)
ltac:(change (NF (Z.of_nat 5)) with 512; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
intros ms HP.
destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
& ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
split; [exact (rw_cells_last m' _ 24 junk1 sp 2008 junk2 _ (fsz (Z.of_nat 5)) eq_refl FR)|].
split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Theorem rta_stack_malloc_5 : stack_malloc_contract RTA 5.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size
FDO MST Hk -> _ Hlen Hcr ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
pose proof CALL as (ST & LOW & LOR & SPT & SPA).
destruct (sm_pre Σ m 5%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
& M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
assert (W1 : evt asegs (sm5_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 5))
(fss_flags (fs_of Σ 5)) lo m)
(entry_st ra sp gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc (e_stack_malloc 5) m)).
{ unfold entry_st.
exact (stack_malloc_5_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(l_FSB (lay Σ)) (fss_hint (fs_of Σ 5)) (fss_flags (fs_of Σ 5)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold sm5_post in Hc1.
apply AST_exI in Hc1 as (jn & Hc2).
assert (PURE : (jn < 512)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 5) + Z.of_nat jn) mod 512)) (fss_flags (fs_of Σ 5)) 1 = 0).
{ destruct Hc2 as (_ & HP & _).
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
split; assumption. }
destruct PURE as (Hj & Hfree).
apply (sm_finish Σ PMc F fc ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 5%nat (Z.of_nat jn) lo _ c1 ART0 ltac:(lia)
ltac:(change (NF (Z.of_nat 5)) with 512; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
intros ms HP.
destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
& ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
split; [exact (rw_cells_last m' _ 24 junk1 sp 2008 junk2 _ (fsz (Z.of_nat 5)) eq_refl FR)|].
split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.
