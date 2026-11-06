(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgMain.v of this library, for reac-pw/fuzz_pin's
   image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f; symbols of
   the unstripped twin 635d02c7e8fa2e1653012207b6ddd2f2c5dd3b8e578ee9607cdc35b94e5260bb). What differs: the imports
   are image B's lib/AU twins (the core's Y files, YE2k for the sink head, lib/AU/PPgSat.v, lib/AU/PPgLib.v,
   lib/AU/Rt/StrlenDef.v and MemchrDef.v, and image B's walk lib/AU/PPgMainCall .. PPgMain5.v; the shared texts
   lib/A/PPgBase.v and PPgCSpec.v are the same); the five program callees are taken at image B's entry addresses
   (.symtab st_value of the unstripped twin): fuzz_catalogue_row 0x80fb4 (called at 0x80a50), reac_box_pin_parse
   0x80ba4 (0x80934), check_known 0x80af8 (0x80940), check_row 0x80b24 (0x80950), check_label 0x80b48 (0x8095c);
   the top claim is PPgCSpec's text at lib/AU/YCfm.v's constants (A_EMPTY 0x5d3d60) and the read-only window of
   lib/AU/PPgMainSt.v (PM_RLO 0x97c20, PM_RHI 0x99e68), and pin_lib_x_A is lib/AU/PPgLib.v's form. The runtime's
   call sites of image B are frame_alloc_1 0x80724, the memchr wrapper 0x80830, malloc 0x80840, checked_memcpy
   0x8085c, the strlen wrapper 0x80884 and free 0x80964 (the runtime and the wrappers are at the same addresses in
   both images). The A file's comment below names image A's numbers; the statements are image B's. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin's ASan harness walk from
   proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632 (lines 126-243: the journal facts and
   the proof of the harness contract from the walk), with its module paths changed and pin's walk (lib/A/PPgMain0 ..
   PPgMain5.v) in place of knock's S0 .. S7; knock's links and closed form (lines 245-313) are left out, because
   pin's close is P5's. rule 24: this file closes the walk of LLVMFuzzerTestOneInput (0x806b4).

   THE TOP CLAIM. pin_lib_x_main proves lib/A/PPgCSpec.v's pin_lib_contract_x at image A's constants (tfibsegs,
   the ASan sink symbols tfib_K, A_LLVMF 0x806b4, RA_LLVMF, A_EMPTY, the harness's event budget 2, LIVE_LIB,
   LLVMF_STK, the read-only window [0x97b00, 0x99d48)), the meter ameter_triv (the meter the close instantiates)
   and any XL : Z -> Z with 0 <= XL n, which is lib/A/PPgLib.v's pin_lib_contract_x unfolded.

   THE CHAIN. pm_S0 (entry, ss_rt0 -> ss_H) and rt_H : rt_from .. (rt_post ..) ss_H (INV_0 .. 0), built as
   pm_S1 (ss_H -> ss_Q), pm_S2 (ss_Q -> ss_C or ss_D), pm_S3 (ss_C -> ss_D), pm_S4 (ss_D -> ss_X), pm_S5 (ss_X -> the
   return to RA_LLVMF with a0 = 0). The cut states and their invariants are lib/A/PPgMainSt.v's.

   SECTION HYPOTHESES (each discharged at the core's record by the close):
     the core's laws: TL : TfibLib B, LAWS : AR_laws, ML : model_laws, SMP, ASF, FFL, AIL : asink_img_laws, the
       read-only window below the sink head (ROB), knock's LEAF (LIBK pl fs K = K (LL 0 fs []));
     the runtime's offers at the harness's call sites (provenance/P4-WALKPLAN.md sections 5 and 6):
       ASM1 : astack_malloc_realizes tfibsegs B 1 (__asan_stack_malloc_1 at 0x80724),
       AMEMCHR : amemchr_realizes tfibsegs B 0x41928 (0x80800), AMALLOC : amalloc_realizes tfibsegs B (0x80824),
       AICPY : aintrin_realizes tfibsegs B OCpy 0x51a40 (__asan_memcpy, 0x80840),
       ASTRLEN : astrlen_realizes tfibsegs B 0x41908 (0x80860), AFREE : afree_realizes tfibsegs B (0x80930);
     the program's callees, at their contracts (lib/A/PPgCSpec.v) and addresses:
       TROW fuzz_catalogue_row 0x80eb4 (0x80a1c), TPARSE reac_box_pin_parse 0x80b44 (0x80900),
       TKNOWN check_known 0x80aa4 (0x8090c), TCROW check_row 0x80acc (0x8091c), TCLAB check_label 0x80aec (0x80928);
     the read-only objects' durable fact FCAT : pin_ro_law (PPgCSpec F-RO-LAW). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm YE2k.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgSat.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require PPgLib.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require Import StrlenDef MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgMainCall PPgMainRt PPgMainSt.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgMain0 PPgMain1 PPgMain2 PPgMain3 PPgMain4 PPgMain5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================== journal facts [knock A/APgLib.v:126-168] ============================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Lemma pm_ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply (fp_spares_closed (SK := SK)); intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
Lemma pm_ajournal_nil_io : forall STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
End e.
Section f.
Variable segs : list Segment.
Lemma pm_srz_enter : forall (W : world segs) (c : config) (T : TSet),
AI segs (w_H W) (w_A W) (cfg_model c) ->
SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) -> srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.
End f.
End d.

(* ============================== the walk and the top claim ============================== *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ROB : @YCeh.ro_tfa_below_ofl tfib_sink_head}.
Section h.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis AIL : asink_img_laws (SK := tfib_sink_head) tfibsegs B tfib_K.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy 0x51a40.
Hypothesis AMEMCHR : amemchr_realizes tfibsegs B 0x41928.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B 0x41908.
Hypothesis FCAT : pin_ro_law tfibsegs B PM_RLO PM_RHI PM_CAT PM_TP PM_DP PM_COLONP.
Hypothesis TROW : tpin_row_specX (SK := tfib_sink_head) tfibsegs B ameter_triv PM_RLO PM_RHI 0x80fb4 PM_CAT PM_TP PM_DP.
Hypothesis TPARSE : tpin_parse_specX (SK := tfib_sink_head) tfibsegs B ameter_triv PM_RLO PM_RHI 0x80ba4 PM_CAT PM_COLONP PM_TP PM_DP.
Hypothesis TKNOWN : tpin_check_known_specX (SK := tfib_sink_head) tfibsegs B ameter_triv 0x80af8.
Hypothesis TCROW : tpin_check_row_specX (SK := tfib_sink_head) tfibsegs B ameter_triv 0x80b24.
Hypothesis TCLAB : tpin_check_label_specX (SK := tfib_sink_head) tfibsegs B ameter_triv 0x80b48.
Variable XL : Z -> Z.
Hypothesis HXL : forall n, 0 <= XL n.
Hypothesis LEAF : forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs []).
Let errno_low := tl_env B TL.
(* malloc and free in the journal-threaded form the walk calls them, at the meter ameter_triv (lib/Reusable/YCbp.v) *)
Let AMALLOC4 : amalloc04_rule (SK := tfib_sink_head) tfibsegs B ameter_triv :=
amalloc04_rule_triv tfibsegs B tfib_segs_low errno_low LAWS ML AMALLOC.
Let AFREE4 : afree04_rule (SK := tfib_sink_head) tfibsegs B ameter_triv :=
afree04_rule_triv tfibsegs B tfib_segs_low errno_low LAWS ML AFREE.
(* the walk S1 .. S5 from ss_H *)
Lemma pm_rt_X : rt_from (SK := tfib_sink_head) B ameter_triv [] (rt_post (SK := tfib_sink_head) B ameter_triv []) ss_X (INV_X B ameter_triv).
Proof. eapply pm_S5; first [exact ameter_triv_laws | exact ameter_triv_fs_laws | eassumption]. Qed.
Lemma pm_rt_D : rt_from (SK := tfib_sink_head) B ameter_triv [] (rt_post (SK := tfib_sink_head) B ameter_triv []) ss_D (INV_D B ameter_triv).
Proof. eapply pm_S4; first [exact pm_rt_X | exact ameter_triv_laws | reflexivity | exact AFREE4 | eassumption]. Qed.
Lemma pm_rt_C : rt_from (SK := tfib_sink_head) B ameter_triv [] (rt_post (SK := tfib_sink_head) B ameter_triv []) ss_C (INV_C B ameter_triv).
Proof. eapply pm_S3; first [exact pm_rt_D | exact ameter_triv_laws | reflexivity | eassumption]. Qed.
Lemma pm_rt_Q : rt_from (SK := tfib_sink_head) B ameter_triv [] (rt_post (SK := tfib_sink_head) B ameter_triv []) ss_Q (INV_Q B ameter_triv).
Proof. eapply pm_S2; first [exact pm_rt_C | exact pm_rt_D | exact ameter_triv_laws | reflexivity | eassumption]. Qed.
Lemma pm_rt_H : rt_from (SK := tfib_sink_head) B ameter_triv [] (rt_post (SK := tfib_sink_head) B ameter_triv []) ss_H (INV_0 B ameter_triv 0).
Proof. eapply pm_S1; first [exact pm_rt_Q | exact ameter_triv_laws | reflexivity | exact AMALLOC4 | eassumption]. Qed.

(* the top claim [knock A/APgLib.v:195-241] *)
Theorem pin_lib_x_main :
PPgCSpec.pin_lib_contract_x (SK := tfib_sink_head) tfibsegs B ameter_triv tfib_K XL XL PM_RLO PM_RHI
A_LLVMF RA_LLVMF A_EMPTY RT_EV LIVE_LIB LLVMF_STK.
Proof.
unfold PPgCSpec.pin_lib_contract_x.
intros ly S W regs mem md p n pl M K HAI HPRE HK.
rewrite LEAF.
unfold PPgCSpec.pin_lib_pre_x in HPRE.
destruct HPRE as (HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK).
assert (HROD : arodata_ok B (aview tfibsegs (w_H W) mem)) by (intros a Ha; apply (HROS a); exact Ha).
apply (pm_srz_enter tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) _ HAI).
eapply SRr_mono.
{ exact (pm_S0 (SK := tfib_sink_head) B ameter_triv ameter_triv_laws TL LAWS ML ASM1 SMP FFL ameter_triv_fs_laws
[] (rt_post (SK := tfib_sink_head) B ameter_triv []) pm_rt_H
ly S W regs mem md p n pl (XL n) HPRE0 Hra Hp Hn Hpn Hnpl HPL Hfr0 Hev Hlive HROD HMOK
ltac:(unfold PIN_NEED; cbn [mo_malloc mo_free ameter_triv]; pose proof (HXL n); lia)). }
intros W' c' Hwle (fpos & sp1 & E0 & HPOST) HAI'.
unfold rt_post, rt_postP in HPOST.
destruct HPOST as (ly' & S' & regs' & mem' & md' & k' & -> & HJ & Hk & HPR & Ha0 & HPerm & HMLE & _).
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T] in HJ, HPR, HPerm, HMLE.
destruct (pm_ajournal_nil_io tfib_sink_head tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efds Efs].
apply (HK (LL 0 (m_fs md) []) W' _ Hwle HAI').
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold PPgCSpec.pin_lib_post_x. cbn [ll_fs ll_ret ll_out].
assert (HSNK' : asink_none tfibsegs tfib_K (mrestrict (w_H W') mem') md').
{ eapply (asink_none_kept (SK := tfib_sink_head) tfibsegs B tfib_K AIL); [exact HJ | intros Ho; exact (sink_closed_nil Ho) | exact HSNK]. }
split; [apply (pm_ajournal_fp_nil tfib_sink_head); exact HJ|]. split; [exact Hk|]. split; [exact HPR|]. split; [exact Ha0|].
split; [exact HPerm|].
split; [intros fd; rewrite Efds; reflexivity|].
split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
split; [exact HSNK'|].
split; [exact (ameta_inv_kept (SK := tfib_sink_head) tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM)|].
split; [exact I|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply inFP_nil.
Qed.
(* the same claim in lib/AU/PPgLib.v's form (its pin_lib_contract_x at RO_LO / RO_HI and PIN_EV_LIB, which are
   0x97c20 / 0x99e68 and 2 = PM_RLO / PM_RHI / RT_EV): by conversion *)
Theorem pin_lib_x_A : PPgLib.pin_lib_contract_x B ameter_triv XL XL PPgLib.RO_LO PPgLib.RO_HI.
Proof. exact pin_lib_x_main. Qed.
End h.
End g.

