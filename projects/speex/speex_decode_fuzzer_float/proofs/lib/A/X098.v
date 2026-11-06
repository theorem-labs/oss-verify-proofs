(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X07z X05s X081 X05l X05m X09f X069 X08y X091 X08x X08u
X06h X0al X09g X0bi X085 X08f X09c X097 X09a X09b.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X05o X09e.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0ys X0x2 X0yt X0zq X0zp X0zl X0yw X0z7 X0yb X101 X0zw X0zz X100 X0x9 X116 X103 X125.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X091.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yw OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X101 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zw OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X100 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X116 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X103 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X125.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbEHtop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis MST : memset_icontract RT e_asan_memset.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis L2F : lsp_to_lpc_cpsF RT.
Hypothesis MC : multicomb_cps RT.
Hypothesis HP : highpass_cps RT.
Lemma nbEH_in_rows : forall mo r, smrec_at mo = Some r -> In r nb_smrecs.
Proof.
intros mo r SAT. unfold smrec_at in SAT. destruct (mo <? 1); [discriminate|]. exact (nth_error_In _ _ SAT).
Qed.

Lemma nbEH_ltp : forall mo r, smrec_at mo = Some r -> forall k, sm_ltp_unquant (smr_sm r) = Some k -> @ltp_unquant_cps RT bptr k.
Proof using AF MST.
intros mo r SAT k Ek. pose proof (nbEH_in_rows mo r SAT) as INR.
pose proof ltp_params_ok_all as LPA. rewrite Forall_forall in LPA.
unfold nb_smrecs in INR. cbn [In] in INR.
repeat (destruct INR as [<- | INR]; [vm_compute in Ek; injection Ek as <-;
first [exact (@forced_pitch_ltp RT AF bptr) | apply (@pitch3_ltp RT AF MST bptr); apply LPA; cbn [In]; repeat (first [left; reflexivity | right])] |]).
destruct INR.
Qed.

Lemma nbEH_innov : forall mo r, smrec_at mo = Some r -> forall k, sm_innovation_unquant (smr_sm r) = Some k -> @innov_unquant_cps RT bptr k.
Proof using AF APO AUN AF_LIB.
intros mo r SAT k Ek. pose proof (nbEH_in_rows mo r SAT) as INR.
pose proof scb_params_ok_all as SPA. rewrite Forall_forall in SPA.
unfold nb_smrecs in INR. cbn [In] in INR.
repeat (destruct INR as [<- | INR]; [vm_compute in Ek; injection Ek as <-;
first [exact (@noise_cb_innov RT AF bptr) | apply (@split_cb_innov RT bptr AF APO AUN AF_LIB); apply SPA; cbn [In]; repeat (first [left; reflexivity | right])] |]).
destruct INR.
Qed.

Theorem nbd_EH_ok : @nbd_EH_cps RT bptr.
Proof using AF MCP MST APO AUN AF_LIB L2F MC HP.
intros Σ PMc X fr0 PD ND fh kh r mo olp st b ms FDO MSTa TPX NXOK HE NSIG NACC ART0 FRMX CRD LTPN INNN.
destruct (subframes_pure 4 0 (smr_sm r) olp st b) as [[st' b']|] eqn:ESF; [|exact I].
assert (SAT : smrec_at mo = Some r)
by (destruct HE as (Fx & fc & m & xra & t0 & t1 & a0 & a1 & a2 & a3 & a4 & a5 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & E & FRM & CTX & SL & SM & _); exact SM).
pose proof (nbEH_ltp mo r SAT) as LTP. pose proof (nbEH_innov mo r SAT) as INN.
apply (cps_seq bsegs _ (at_ELc RT PMc X Σ (ms_mem ms) r mo olp 40 0 st b)).
-
intros T c Hc Hk. apply Hk. exists Σ. split; [| unfold nbEH_sig; repeat split; reflexivity].
eapply AST_conseq; [exact Hc | | intros mo0 Hmo; exact Hmo].
intros ms0 <-. split; [exact (at_EL_of_E X r mo olp st b ms HE)|].
split; [exact ART0|]. split; [exact NACC|]. split; [apply wmono_refl| apply pres_fp_refl].
- eapply cps_seq; [exact (nbE_loop RT AF MST AF_LIB PMc FDO MSTa X NXOK TPX Σ fr0 PD ND fh kh NSIG (ms_mem ms) r mo olp LTP INN 4 40 0 st b st' b' ltac:(lia) eq_refl ltac:(lia) ESF)|].
intros T c (bp' & BP' & HX) Hk.
apply (nbFGH RT AF MCP L2F PMc FDO MSTa X NXOK TPX Σ fr0 PD ND fh kh NSIG AF_LIB MC HP (ms_mem ms) r mo olp NACC bp' st' b' CRD FRMX T c HX).
intros c' (Σ' & H1 & LV' & FRS' & SP' & CR' & POI'). apply Hk. exists Σ'.
split; [| split; [exact LV'|]; split; [exact FRS'|]; split; [exact SP'|]; split; [exact CR'| exact POI']].
eapply AST_conseq; [exact H1 | | intros mo0 Hmo; exact Hmo].
intros ms' (HXA & ART' & NACC' & WM' & PF'). split; [exact HXA|]. split; [exact ART'|]. split; [exact NACC'|]. split; [exact WM'| exact PF'].
Qed.
End NbEHtop.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbEHtop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis MST : memset_icontract RT e_asan_memset.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis L2F : lsp_to_lpc_cpsF RT.
Hypothesis MC : multicomb_cps RT.

Lemma nbEH_in_rows : forall mo r, smrec_at mo = Some r -> In r nb_smrecs.
Proof.
intros mo r SAT. unfold smrec_at in SAT. destruct (mo <? 1); [discriminate|]. exact (nth_error_In _ _ SAT).
Qed.

Lemma nbEH_ltp : forall mo r, smrec_at mo = Some r -> forall k, sm_ltp_unquant (smr_sm r) = Some k -> @ltp_unquant_cps RT bptr k.
Proof using AF MST.
intros mo r SAT k Ek. pose proof (nbEH_in_rows mo r SAT) as INR.
pose proof ltp_params_ok_all as LPA. rewrite Forall_forall in LPA.
unfold nb_smrecs in INR. cbn [In] in INR.
repeat (destruct INR as [<- | INR]; [vm_compute in Ek; injection Ek as <-;
first [exact (@forced_pitch_ltp RT AF bptr) | apply (@pitch3_ltp RT AF MST bptr); apply LPA; cbn [In]; repeat (first [left; reflexivity | right])] |]).
destruct INR.
Qed.

Lemma nbEH_innov : forall mo r, smrec_at mo = Some r -> forall k, sm_innovation_unquant (smr_sm r) = Some k -> @innov_unquant_cps RT bptr k.
Proof using AF APO AUN AF_LIB.
intros mo r SAT k Ek. pose proof (nbEH_in_rows mo r SAT) as INR.
pose proof scb_params_ok_all as SPA. rewrite Forall_forall in SPA.
unfold nb_smrecs in INR. cbn [In] in INR.
repeat (destruct INR as [<- | INR]; [vm_compute in Ek; injection Ek as <-;
first [exact (@noise_cb_innov RT AF bptr) | apply (@split_cb_innov RT bptr AF APO AUN AF_LIB); apply SPA; cbn [In]; repeat (first [left; reflexivity | right])] |]).
destruct INR.
Qed.

Theorem nbd_EH_ok : @nbd_EH_cps RT bptr.
Proof using AF MCP MST APO AUN AF_LIB L2F MC.
intros Σ PMc X fr0 PD ND fh kh r mo olp st b ms FDO MSTa TPX NXOK HE NSIG NACC ART0 FRMX CRD LTPN INNN.
destruct (subframes_pure 4 0 (smr_sm r) olp st b) as [[st' b']|] eqn:ESF; [|exact I].
assert (SAT : smrec_at mo = Some r)
by (destruct HE as (Fx & fc & m & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff & E & FRM & CTX & SL & SM & _); exact SM).
pose proof (nbEH_ltp mo r SAT) as LTP. pose proof (nbEH_innov mo r SAT) as INN.
apply (cps_seq asegs _ (at_ELc RT PMc X Σ (ms_mem ms) r mo olp 40 0 st b)).
-
intros T c Hc Hk. apply Hk. exists Σ. split; [| unfold nbEH_sig; repeat split; reflexivity].
eapply AST_conseq; [exact Hc | | intros mo0 Hmo; exact Hmo].
intros ms0 <-. split; [exact (at_EL_of_E X r mo olp st b ms HE)|].
split; [exact ART0|]. split; [exact NACC|]. split; [apply wmono_refl| apply pres_fp_refl].
- eapply cps_seq; [exact (nbE_loop RT AF MST AF_LIB PMc FDO MSTa X NXOK TPX Σ fr0 PD ND fh kh NSIG (ms_mem ms) r mo olp LTP INN 4 40 0 st b st' b' ltac:(lia) eq_refl ltac:(lia) ESF)|].
intros T c (bp' & BP' & HX) Hk.
apply (nbFGH RT AF MCP L2F PMc FDO MSTa X NXOK TPX Σ fr0 PD ND fh kh NSIG AF_LIB MC (ms_mem ms) r mo olp NACC bp' st' b' CRD FRMX T c HX).
intros c' (Σ' & H1 & LV' & FRS' & SP' & CR' & POI'). apply Hk. exists Σ'.
split; [| split; [exact LV'|]; split; [exact FRS'|]; split; [exact SP'|]; split; [exact CR'| exact POI']].
eapply AST_conseq; [exact H1 | | intros mo0 Hmo; exact Hmo].
intros ms' (HXA & ART' & NACC' & WM' & PF'). split; [exact HXA|]. split; [exact ART'|]. split; [exact NACC'|]. split; [exact WM'| exact PF'].
Qed.
End NbEHtop.
