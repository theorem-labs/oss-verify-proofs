(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Bi_topkit Po_topaux.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Bi_fktw CfY_pixdestroy_null CfY_pixdestroy_rc Cf_clone D_libiface ImageA LeptC_cmapdeser LeptC_cmapdestroy LeptC_cmapvalid LeptC_padbits LeptC_setcmap LeptF_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require LeptM_destroy Lept_create Lept_err Lept_gmax Lept_hdr Lept_iface Lept_stderr Lept_zero Pm_cmapcopy Pm_cmapvalid_stk Pm_copycmap Pm_iface2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Pm_strrepl Po_addb Po_casc Po_casc_defs Po_clearall Po_copycmap2 Po_copycmap2_defs Po_copyg Po_copyinf Po_copyn Po_copyr Po_copyres.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Po_copysame Po_copyspp Po_count Po_count_c16 Po_count_defs Po_create0 Po_creater Po_csc Po_csc_defs Po_csels Po_deser0 Po_dfd.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Po_dilate Po_dilate_defs Po_diln Po_erode Po_eron Po_fliplr Po_fliplr_defs Po_fliptb Po_fliptb_defs Po_fz_defs Po_hdr0 Po_hdr2r.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Po_hip Po_hip_defs Po_hmt Po_iface Po_mod Po_mod_defs Po_morph2_defs Po_msv Po_msv_defs Po_noinitr Po_null_defs Po_oc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Po_oc_defs Po_pixor Po_pma1 Po_pma1n Po_pmcs Po_pmcs_defs Po_rasterop1 Po_rb2 Po_rb2_defs Po_remb Po_rembn Po_resize.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Po_ropl_iface Po_rot180 Po_rot90 Po_rotorth Po_saadd Po_sacreate Po_sadestroy Po_saget Po_sasplit Po_sasplit_defs Po_scaleres Po_selcreate.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Po_seldestroy Po_selgp Po_selgp2 Po_selsetel Po_selstr Po_setall Po_sfmt Po_strnew Po_strrem Po_strtok Po_sure Po_template1.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Po_tmplr Po_topaux Po_udd Po_udd_defs RT23_iface RT23b_iface RT_fk_iface RT_gaps_iface RT_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_top () := "K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53A239Bi_topkitAex_lit_of_existsbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Po_oc_defs;A_OC_ERRMSGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=RT_gaps_iface9LEPT_LITSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53A23:Po_oc_defs9A_OC_PROCC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib2K53A239Bi_topkit@in_zz_of_existsbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_ropl_iface7A_RMASKC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A238RT_iface8ACC_LITSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_ropl_iface7A_LMASKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239Po_setall<A_MSG_SETALLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239Po_setall=A_PROC_SETALLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_rb2_defs>A_MSG_RB2_NULLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_rb2_defs<A_MSG_RB2_HSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_rb2_defs>A_MSG_RB2_PIXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_rb2_defs:A_PROC_RB2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_count_c16;A_MSG_COUNTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_count_c16<A_PROC_COUNTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A236Po_top3AFtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A236Po_topIT_pixDeserialize_res0_cpsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A236Po_topGT_pixOrientCorrect2_cpsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A236Po_topAT_pixDestroy_cpsFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A236Po_topFT_pixDestroy_null_cpsFC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Section Top.
Variable RT : RT_iface.rt_sig.
Hypothesis RC : RT_iface.rt_contracts RT.
Hypothesis GP : RT_gaps_iface.rt_gaps RT.
Hypothesis FKC : RT_fk_iface.rt_fk_contracts RT.
Hypothesis H_stack_malloc_x_contractF_3 : RT23_iface.stack_malloc_x_contractF RT 3.   (* [comment removed for export] *)
Hypothesis H_stack_malloc_x_contractF_4 : RT23_iface.stack_malloc_x_contractF RT 4.   (* [comment removed for export] *)
Hypothesis H_strchr_icontractF : RT23b_iface.strchr_icontractF RT.   (* [comment removed for export] *)
Hypothesis H_sscanf_dd_icontractF : RT23b_iface.sscanf_dd_icontractF RT.   (* [comment removed for export] *)
Hypothesis H_stack_malloc_7_contractF : RT23_iface.stack_malloc_7_contractF RT.   (* [comment removed for export] *)
Hypothesis H_stack_free_7_contractF : RT23_iface.stack_free_7_contractF RT.   (* [comment removed for export] *)
Definition AFt : RT_iface.art_facts RT := RT_iface.rc_facts RT RC.
Lemma L_lit_A_OC_ERRMSG : (exists l : Z, In (Po_oc_defs.A_OC_ERRMSG, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg003aR0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_lit_A_OC_PROC : (exists l : Z, In (Po_oc_defs.A_OC_PROC, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg007DR0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_acc_A_RMASK_132 : In (Po_ropl_iface.A_RMASK, 132) RT_iface.ACC_LITS.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;1p;4p;2p;3g008Dj10Tg008ij1<Tg009Nj15Tg009lj44Tg0000j2;Tg000Jj2:Tg000jj32Tg001Gj21Tg00:Lj33Tg00:ij26Tg001dj37Tg002@j38Tg00;Gj39Tg006fR0P0g00<Mg00=N#0#0#0#0#<#0#0#5C4R1g00>3R2g005fR3g006FR4';1:00R5f0R69200A2001'1A3006A3001'1'6X05;72=834d39o"). Qed.
Lemma L_acc_A_LMASK_132 : In (Po_ropl_iface.A_LMASK, 132) RT_iface.ACC_LITS.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;1p;4p;2p;3g008Dj10Tg008ij1<Tg009Nj15Tg009lj44Tg0000j2;Tg000Jj2:Tg000jj32Tg001Gj21Tg00:Lj33Tg00:ij26Tg001dj37Tg002@j38Tg00;Gj39Tg006fR0P0g00?0g00=N#0#0#0#0#<#0#0#5C4R1g00>3R2g005fR3g006FR4';1:00R5f0R69200A2001'1A3006A3001'1'6X05;72=834d39o"). Qed.
Lemma L_lit_A_MSG_SETALL : (exists l : Z, In (Po_setall.A_MSG_SETALL, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg00@1R0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_lit_A_PROC_SETALL : (exists l : Z, In (Po_setall.A_PROC_SETALL, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg00A3R0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_lit_A_MSG_RB2_NULL : (exists l : Z, In (Po_rb2_defs.A_MSG_RB2_NULL, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg00B6R0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_lit_A_MSG_RB2_HS : (exists l : Z, In (Po_rb2_defs.A_MSG_RB2_HS, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg00C<R0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_lit_A_MSG_RB2_PIXD : (exists l : Z, In (Po_rb2_defs.A_MSG_RB2_PIXD, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg00D@R0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_lit_A_PROC_RB2 : (exists l : Z, In (Po_rb2_defs.A_PROC_RB2, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg00EFR0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_lit_A_MSG_COUNT : (exists l : Z, In (Po_count_c16.A_MSG_COUNT, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg00FHR0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Lemma L_lit_A_PROC_COUNT : (exists l : Z, In (Po_count_c16.A_PROC_COUNT, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "h01pp;2p;3g0000j26Tg000Jj25Tg000jj30Tg001Gj21Tg001dj34Tg002@j32Tg002Zj33Tg00GLR0g004cR1g005fR2g006FR3'6g006fR4/54R5f09044/10X05;41=223d33o"). Qed.
Definition T_lept_stderr_cps : Lept_iface.lept_stderr_cps RT :=
  Lept_stderr.lept_stderr_ok RT AFt RC GP FKC.
Definition T_lept_stderr_cpsF : Bi_fktw.lept_stderr_cpsF RT :=
  Lept_stderr.lept_stderr_okF RT AFt RC GP FKC.
Definition T_returnError_cps_e_returnErrorPtr : Lept_iface.returnError_cps RT Lept_iface.e_returnErrorPtr :=
  Lept_err.returnError_ok RT AFt GP T_lept_stderr_cpsF Lept_iface.e_returnErrorPtr (or_intror eq_refl).
Definition T_returnError_cpsF_e_returnErrorPtr : Bi_fktw.returnError_cpsF RT Lept_iface.e_returnErrorPtr :=
  Lept_err.returnError_okF RT AFt GP T_lept_stderr_cpsF Lept_iface.e_returnErrorPtr (or_intror eq_refl).
Definition T_pixCreateHeader_cps : Lept_iface.pixCreateHeader_cps RT :=
  Lept_hdr.pixCreateHeader_ok RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCreateHeader_res0_cpsF : Po_iface.pixCreateHeader_res0_cpsF RT :=
  Po_hdr0.pixCreateHeader_res0_okF RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_returnError_cpsF_e_returnErrorInt : Bi_fktw.returnError_cpsF RT Lept_iface.e_returnErrorInt :=
  Lept_err.returnError_okF RT AFt GP T_lept_stderr_cpsF Lept_iface.e_returnErrorInt (or_introl eq_refl).
Definition T_pixSetPadBits_cpsF : Bi_fktw.pixSetPadBits_cpsF RT :=
  LeptC_padbits.pixSetPadBits_okF RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorInt.
Definition T_pixCreate_res0_cps : Po_iface.pixCreate_res0_cps RT :=
  Po_create0.pixCreate_res0_ok RT AFt RC GP FKC T_pixCreateHeader_res0_cpsF T_pixSetPadBits_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixcmapDestroy_cpsF : Bi_fktw.pixcmapDestroy_cpsF RT :=
  LeptC_cmapdestroy.pixcmapDestroy_okF RT AFt GP FKC.
Definition T_pixDestroy_cps : Lept_iface.pixDestroy_cps RT :=
  LeptM_destroy.pixDestroy_ok RT AFt GP FKC T_pixcmapDestroy_cpsF.
Definition T_pixcmapDeserialize_cps : Lept_iface.pixcmapDeserialize_cps RT :=
  LeptC_cmapdeser.pixcmapDeserialize_ok RT AFt GP.
Definition T_returnError_cps_e_returnErrorInt : Lept_iface.returnError_cps RT Lept_iface.e_returnErrorInt :=
  Lept_err.returnError_ok RT AFt GP T_lept_stderr_cpsF Lept_iface.e_returnErrorInt (or_introl eq_refl).
Definition T_pixZero_cpsF : LeptF_iface.pixZero_cpsF RT :=
  Lept_zero.pixZero_okF RT AFt GP.
Definition T_pixGetMaxColorIndex_cpsF : LeptF_iface.pixGetMaxColorIndex_cpsF RT :=
  Lept_gmax.pixGetMaxColorIndex_okF RT AFt GP FKC T_pixZero_cpsF.
Definition T_pixcmapIsValid_cps : Lept_iface.pixcmapIsValid_cps RT :=
  LeptC_cmapvalid.pixcmapIsValid_ok RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorInt T_pixGetMaxColorIndex_cpsF.
Definition T_pixSetColormap_cps : Lept_iface.pixSetColormap_cps RT :=
  LeptC_setcmap.pixSetColormap_ok RT AFt GP T_returnError_cps_e_returnErrorInt T_pixcmapIsValid_cps.
Definition T_pixDeserialize_res0_cps : Po_iface.pixDeserialize_res0_cps RT :=
  Po_deser0.pixDeserialize_res0_ok RT AFt RC GP T_lept_stderr_cps T_returnError_cps_e_returnErrorPtr T_pixCreateHeader_cps T_pixCreate_res0_cps T_pixDestroy_cps T_pixcmapDeserialize_cps T_pixSetColormap_cps T_pixcmapIsValid_cps.
Definition T_selCreate2_cps : Po_selcreate.selCreate2_cps RT :=
  Po_selcreate.selCreate_ok RT AFt GP FKC.
Definition T_selSetElement_cps : Po_iface.selSetElement_cps RT :=
  Po_selsetel.selSetElement_ok RT AFt GP.
Definition T_forall_k_Z_rts_RT_m_bv_64_option_bv_8_1_k_4_ART_m_acc_asegs_m_A_TSEL_k_31 : forall (k : Z) (Σ : RT_iface.rts RT) (m : definitions.bv 64 -> option (definitions.bv 8)), 1 <= k <= 4 -> RT_iface.ART RT Σ m -> Shadow.acc ImageA.asegs m (Po_iface.A_TSEL k) 31 :=
  Po_topaux.acctsel_ok RT AFt.
Definition T_selCreateFromString_cps : Po_iface.selCreateFromString_cps RT :=
  Po_selstr.selCreateFromString_ok RT AFt GP FKC T_selCreate2_cps T_selSetElement_cps T_forall_k_Z_rts_RT_m_bv_64_option_bv_8_1_k_4_ART_m_acc_asegs_m_A_TSEL_k_31.
Definition T_sarrayCreate02_cps : Po_sacreate.sarrayCreate02_cps RT :=
  Po_sacreate.sarrayCreate0_ok RT AFt GP FKC.
Definition T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_A_SEQ_TEXT_13 : forall (Σ : RT_iface.rts RT) (m : definitions.bv 64 -> option (definitions.bv 8)), RT_iface.ART RT Σ m -> Shadow.acc ImageA.asegs m Po_iface.A_SEQ_TEXT 13 :=
  Po_topaux.acc_seq_text_ok RT AFt.
Definition T_stringNew2_cps : Po_strnew.stringNew2_cps RT :=
  Po_strnew.stringNew_seq_ok RT AFt GP FKC T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_A_SEQ_TEXT_13.
Definition T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_A_SEPS_PLUS_2 : forall (Σ : RT_iface.rts RT) (m : definitions.bv 64 -> option (definitions.bv 8)), RT_iface.ART RT Σ m -> Shadow.acc ImageA.asegs m Po_iface.A_SEPS_PLUS 2 :=
  Po_topaux.acc_seps_plus_ok RT AFt.
Definition T_strtokSafe2_cps1 : Po_strtok.strtokSafe2_cps1 RT :=
  Po_strtok.strtokSafe_call1 RT AFt GP FKC H_strchr_icontractF T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_A_SEPS_PLUS_2.
Definition T_strtokSafe2_cps2 : Po_strtok.strtokSafe2_cps2 RT :=
  Po_strtok.strtokSafe_call2 RT AFt GP FKC H_strchr_icontractF T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_A_SEPS_PLUS_2.
Definition T_strtokSafe2_cps3 : Po_strtok.strtokSafe2_cps3 RT :=
  Po_strtok.strtokSafe_call3 RT AFt GP.
Definition T_sarrayAddString2_cps : Po_saadd.sarrayAddString2_cps RT :=
  Po_saadd.sarrayAddString_ok RT AFt GP.
Definition T_sarraySplitSeq2_cps : Po_sasplit_defs.sarraySplitSeq2_cps RT :=
  Po_sasplit.sarraySplitSeq2_ok RT AFt GP FKC T_stringNew2_cps T_strtokSafe2_cps1 T_strtokSafe2_cps2 T_strtokSafe2_cps3 T_sarrayAddString2_cps.
Definition T_sarrayGetCount_cps : Po_iface.sarrayGetCount_cps RT :=
  Po_saget.sarrayGetCount_ok RT AFt GP.
Definition T_sarrayGetString_cps : Po_iface.sarrayGetString_cps RT :=
  Po_saget.sarrayGetString_ok RT AFt GP.
Definition T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_A_SEPS_WS_4 : forall (Σ : RT_iface.rts RT) (m : definitions.bv 64 -> option (definitions.bv 8)), RT_iface.ART RT Σ m -> Shadow.acc ImageA.asegs m Po_iface.A_SEPS_WS 4 :=
  Po_topaux.acc_seps_ws_ok RT AFt.
Definition T_stringRemoveWS_cps : Po_iface.stringRemoveWS_cps RT :=
  Po_strrem.stringRemoveChars_ok RT AFt GP FKC H_strchr_icontractF T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_A_SEPS_WS_4.
Definition T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_SSCANF_FMT_6 : forall (Σ : RT_iface.rts RT) (m : definitions.bv 64 -> option (definitions.bv 8)), RT_iface.ART RT Σ m -> Shadow.acc ImageA.asegs m RT23b_iface.SSCANF_FMT 6 :=
  Po_topaux.acc_sscanf_fmt_ok RT AFt.
Definition T_morphSequenceVerify2_cps : Po_msv_defs.morphSequenceVerify2_cps RT :=
  Po_msv.morphSequenceVerify2_ok RT AFt GP FKC T_sarrayGetCount_cps T_sarrayGetString_cps T_stringRemoveWS_cps H_sscanf_dd_icontractF T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_SSCANF_FMT_6.
Definition T_pixCreateHeader_nn_res0_cpsF : Po_iface.pixCreateHeader_nn_res0_cpsF RT :=
  Po_hdr2r.pixCreateHeader_nn_res0_okF RT AFt GP FKC.
Definition T_pixCreateNoInit_nn_res0_cpsF_e_pixCreateNoInit_PM_NOINIT_MALLOC : Po_iface.pixCreateNoInit_nn_res0_cpsF RT Lept_iface.e_pixCreateNoInit Pm_iface2.PM_NOINIT_MALLOC :=
  Po_noinitr.pixCreateNoInit_res0_okF RT AFt GP FKC T_pixCreateHeader_nn_res0_cpsF T_pixSetPadBits_cpsF.
Definition T_pixcmapIsValid_cpsF : Bi_fktw.pixcmapIsValid_cpsF RT :=
  LeptC_cmapvalid.pixcmapIsValid_okF RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorInt T_pixGetMaxColorIndex_cpsF.
Definition T_pixcmapIsValid_stk_cpsF : Bi_fktw.pixcmapIsValid_stk_cpsF RT :=
  Pm_cmapvalid_stk.pixcmapIsValid_stk_okF RT AFt GP FKC.
Definition T_pixcmapCopy_cpsF : Bi_fktw.pixcmapCopy_cpsF RT :=
  Pm_cmapcopy.pixcmapCopy_okF RT AFt RC GP FKC T_pixcmapIsValid_stk_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCopyColormap_cpsF : Bi_fktw.pixCopyColormap_cpsF RT :=
  Pm_copycmap.pixCopyColormap_okF RT AFt GP FKC T_returnError_cpsF_e_returnErrorInt T_pixcmapIsValid_cpsF T_pixcmapCopy_cpsF.
Definition T_stringReplace_null_cpsF : Bi_fktw.stringReplace_null_cpsF RT :=
  Pm_strrepl.stringReplace_null_okF RT AFt GP.
Definition T_pixCreateTemplateNoInit_nn_res0_cpsF : Po_iface.pixCreateTemplateNoInit_nn_res0_cpsF RT :=
  Po_tmplr.pixCreateTemplateNoInit_res0_okF RT AFt GP T_pixCreateNoInit_nn_res0_cpsF_e_pixCreateNoInit_PM_NOINIT_MALLOC T_pixCopyColormap_cpsF T_stringReplace_null_cpsF T_pixSetPadBits_cpsF T_returnError_cpsF_e_returnErrorInt.
Definition T_pixCopy_nn_res0_cpsF : Po_iface.pixCopy_nn_res0_cpsF RT :=
  Po_copyr.pixCopy_res0_okF RT AFt RC GP FKC T_pixCreateTemplateNoInit_nn_res0_cpsF.
Definition T_pixCopyNew1_sure_cps : Po_iface.pixCopyNew1_sure_cps RT :=
  Po_sure.pixCopyNew1_sure_ok RT AFt T_pixCopy_nn_res0_cpsF.
Definition T_selectComposableSels_cps : Po_iface.selectComposableSels_cps RT :=
  Po_csels.selectComposableSels_ok RT AFt GP FKC H_stack_malloc_7_contractF H_stack_free_7_contractF.
Definition T_pixCreateHeader_cpsF : Bi_fktw.pixCreateHeader_cpsF RT :=
  Lept_hdr.pixCreateHeader_okF RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCreate_cpsF : Bi_fktw.pixCreate_cpsF RT :=
  Lept_create.pixCreate_okF RT AFt RC GP FKC T_pixCreateHeader_cpsF T_pixSetPadBits_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCreate_nn_res0_cpsF : Po_iface.pixCreate_nn_res0_cpsF RT :=
  Po_creater.pixCreate_nn_res0_ok RT AFt GP FKC T_pixCreateNoInit_nn_res0_cpsF_e_pixCreateNoInit_PM_NOINIT_MALLOC.
Definition T_pixCreate1_sure_cps : Po_iface.pixCreate1_sure_cps RT :=
  Po_sure.pixCreate1_sure_ok RT T_pixCreate_nn_res0_cpsF.
Definition T_pixCopyResolution_po_cps : Po_iface.pixCopyResolution_po_cps RT :=
  Po_copyres.pixCopyResolution_po_ok RT AFt GP.
Definition T_pixRasterop_po_cps : Po_iface.pixRasterop_po_cps RT :=
  Po_rasterop1.pixRasterop_po1_ok RT AFt GP FKC L_acc_A_RMASK_132 L_acc_A_LMASK_132.
Definition T_pixAddBorder32_rows_cps : Po_csc_defs.pixAddBorder32_rows_cps RT :=
  Po_addb.pixAddBorder32_rows_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorPtr T_pixCreate_cpsF T_pixCreate1_sure_cps T_pixCopyResolution_po_cps T_pixCopyColormap_cpsF T_pixRasterop_po_cps.
Definition T_selGetParameters_sxsy_cps : Po_iface.selGetParameters_sxsy_cps RT :=
  Po_selgp2.selGetParameters_sxsy_ok RT AFt GP.
Definition T_pixResizeImageData_same_cps : Po_iface.pixResizeImageData_same_cps RT :=
  Po_resize.pixResizeImageData_same_ok RT AFt GP.
Definition T_pixClone_cpsF : Bi_fktw.pixClone_cpsF RT :=
  Cf_clone.pixClone_okF RT AFt GP.
Definition T_pixCreateTemplate1_sure_cps : Po_iface.pixCreateTemplate1_sure_cps RT :=
  Po_template1.pixCreateTemplate1_sure_ok RT AFt GP FKC T_pixCreateTemplateNoInit_nn_res0_cpsF.
Definition T_processMorphArgs12_cps : Po_dilate_defs.processMorphArgs12_cps RT :=
  Po_pma1.processMorphArgs1_ok RT AFt GP FKC T_selGetParameters_sxsy_cps T_pixResizeImageData_same_cps T_pixClone_cpsF T_pixCreateTemplate1_sure_cps.
Definition T_selGetParameters_cps : Po_iface.selGetParameters_cps RT :=
  Po_selgp.selGetParameters_ok RT AFt GP.
Definition T_pixClearAll_cps : Po_iface.pixClearAll_cps RT :=
  Po_clearall.pixClearAll_ok RT AFt GP FKC.
Definition T_pixDestroy_rc_cpsF : Bi_fktw.pixDestroy_rc_cpsF RT :=
  CfY_pixdestroy_rc.pixDestroy_rc_okF RT AFt GP FKC.
Definition T_pixDilate2_cps : Po_dilate_defs.pixDilate2_cps RT :=
  Po_dilate.pixDilate2_ok RT AFt GP FKC T_processMorphArgs12_cps T_selGetParameters_cps T_pixClearAll_cps T_pixRasterop_po_cps T_pixDestroy_rc_cpsF.
Definition T_pixSetAll_cps : Po_iface.pixSetAll_cps RT :=
  Po_setall.pixSetAll_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorInt L_lit_A_MSG_SETALL L_lit_A_PROC_SETALL.
Definition T_selFindMaxTranslations_cps : Po_iface.selFindMaxTranslations_cps RT :=
  Po_sfmt.selFindMaxTranslations_ok RT AFt GP.
Definition T_pixErode_given2_cps : Po_morph2_defs.pixErode_given2_cps RT :=
  Po_erode.pixErode_given2_ok RT AFt GP FKC T_processMorphArgs12_cps T_selGetParameters_cps T_pixSetAll_cps T_selFindMaxTranslations_cps T_pixRasterop_po_cps T_pixDestroy_rc_cpsF.
Definition T_pixDestroy_cpsF : Bi_fktw.pixDestroy_cpsF RT :=
  LeptM_destroy.pixDestroy_okF RT AFt GP FKC T_pixcmapDestroy_cpsF.
Definition T_pixDestroy_null_cpsF : Bi_fktw.pixDestroy_null_cpsF RT :=
  CfY_pixdestroy_null.pixDestroy_null_okF RT AFt GP FKC.
Definition T_pixCopySpp_cps : Po_iface.pixCopySpp_cps RT :=
  Po_copyspp.pixCopySpp_ok RT AFt GP.
Definition T_pixRemoveBorder32_rows_cps : Po_csc_defs.pixRemoveBorder32_rows_cps RT :=
  Po_remb.pixRemoveBorder32_rows_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorPtr T_pixCreate1_sure_cps T_pixCopyResolution_po_cps T_pixCopySpp_cps T_pixCopyColormap_cpsF T_pixRasterop_po_cps.
Definition T_pixCopyColormap2_cpsF : Po_copycmap2_defs.pixCopyColormap2_cpsF RT :=
  Po_copycmap2.pixCopyColormap2_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorInt T_pixcmapIsValid_cpsF T_pixcmapCopy_cpsF.
Definition T_pixCopy_given_cps : Po_iface.pixCopy_given_cps RT :=
  Po_copyg.pixCopy_given_ok RT AFt GP FKC T_pixResizeImageData_same_cps T_pixCopyColormap2_cpsF T_stringReplace_null_cpsF.
Definition T_selDestroy_cps : Po_iface.selDestroy_cps RT :=
  Po_seldestroy.selDestroy_ok RT AFt GP FKC.
Definition T_pma1_null_cps : Po_null_defs.pma1_null_cps RT :=
  Po_pma1n.pma1_null_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixDilate_null0_cps : Po_null_defs.pixDilate_null0_cps RT :=
  Po_diln.pixDilate_null0_ok RT AFt GP FKC T_pma1_null_cps T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixErode_null0_cps : Po_null_defs.pixErode_null0_cps RT :=
  Po_eron.pixErode_null0_ok RT AFt GP FKC T_pma1_null_cps T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixRemoveBorder_null_cps : Po_null_defs.pixRemoveBorder_null_cps RT :=
  Po_rembn.pixRemoveBorder_null_ok RT AFt GP T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCopy_srcnull_cps : Po_null_defs.pixCopy_srcnull_cps RT :=
  Po_copyn.pixCopy_srcnull_ok RT AFt GP T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCloseSafeCompBrick3_cps : Po_pmcs_defs.pixCloseSafeCompBrick3_cps RT :=
  Po_csc.pixCloseSafeCompBrick3_ok RT AFt GP FKC T_selectComposableSels_cps T_pixAddBorder32_rows_cps T_pixDilate2_cps T_pixErode_given2_cps T_pixDestroy_cpsF T_pixDestroy_null_cpsF T_pixRemoveBorder32_rows_cps T_pixCopy_given_cps T_selDestroy_cps T_pixDilate_null0_cps T_pixErode_null0_cps T_pixRemoveBorder_null_cps T_pixCopy_srcnull_cps.
Definition T_sarrayDestroy2_cps : Po_sadestroy.sarrayDestroy2_cps RT :=
  Po_sadestroy.sarrayDestroy_ok RT AFt GP FKC.
Definition T_udd_pmcs_cps : Po_udd_defs.udd_pmcs_cps RT :=
  Po_pmcs.pixMorphCompSequence_ok RT AFt GP FKC H_stack_malloc_x_contractF_4 T_sarrayCreate02_cps T_sarraySplitSeq2_cps T_sarrayGetCount_cps T_sarrayGetString_cps T_morphSequenceVerify2_cps T_stringRemoveWS_cps H_sscanf_dd_icontractF T_pixCopyNew1_sure_cps T_pixCloseSafeCompBrick3_cps T_sarrayDestroy2_cps T_forall_rts_RT_m_bv_64_option_bv_8_ART_m_acc_asegs_m_SSCANF_FMT_6.
Definition T_udd_hmt_cps : Po_udd_defs.udd_hmt_cps RT :=
  Po_hmt.pixHMT2_ok RT AFt GP FKC T_processMorphArgs12_cps T_selGetParameters_cps T_pixClearAll_cps T_pixSetAll_cps T_selFindMaxTranslations_cps T_pixRasterop_po_cps T_pixDestroy_rc_cpsF.
Definition T_pixCopy_same_cps : Po_iface.pixCopy_same_cps RT :=
  Po_copysame.pixCopy_same_ok RT AFt GP.
Definition T_pixOr_cps : Po_iface.pixOr_cps RT :=
  Po_pixor.pixOr_ok RT AFt GP T_pixCopy_same_cps T_pixRasterop_po_cps.
Definition T_pixCreate_res0_cpsF : Po_iface.pixCreate_res0_cpsF RT :=
  Po_create0.pixCreate_res0_okF RT AFt RC GP FKC T_pixCreateHeader_res0_cpsF T_pixSetPadBits_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixScaleResolution_cps : Po_iface.pixScaleResolution_cps RT :=
  Po_scaleres.pixScaleResolution_ok RT AFt GP.
Definition T_pixReduceRankBinary22_cps : Po_rb2_defs.pixReduceRankBinary22_cps RT :=
  Po_rb2.pixReduceRankBinary2_ok RT AFt GP FKC T_pixSetPadBits_cpsF T_pixCreate_res0_cpsF T_pixCreate1_sure_cps T_pixCopyResolution_po_cps T_pixScaleResolution_cps T_returnError_cpsF_e_returnErrorPtr L_lit_A_MSG_RB2_NULL L_lit_A_MSG_RB2_HS L_lit_A_MSG_RB2_PIXD L_lit_A_PROC_RB2.
Definition T_pixReduceRankBinaryCascade2_cps : Po_casc_defs.pixReduceRankBinaryCascade2_cps RT :=
  Po_casc.pixReduceRankBinaryCascade_ok RT AFt GP FKC T_pixReduceRankBinary22_cps T_pixDestroy_cpsF T_pixDestroy_null_cpsF.
Definition T_pixCountPixels2_cps : Po_count_defs.pixCountPixels2_cps RT :=
  Po_count.pixCountPixels_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorInt L_lit_A_MSG_COUNT L_lit_A_PROC_COUNT.
Definition T_pixDebugFlipDetect_cps : Po_iface.pixDebugFlipDetect_cps RT :=
  Po_dfd.pixDebugFlipDetect_ok RT AFt GP FKC.
Definition T_pixUpDownDetect2_cps : Po_udd_defs.pixUpDownDetect2_cps RT :=
  Po_udd.pixUpDownDetect_ok RT AFt GP FKC H_stack_malloc_x_contractF_3 T_selCreateFromString_cps T_udd_pmcs_cps T_udd_hmt_cps T_pixOr_cps T_pixReduceRankBinaryCascade2_cps T_pixCountPixels2_cps T_pixDebugFlipDetect_cps T_pixDestroy_cpsF T_pixDestroy_null_cpsF T_selDestroy_cps.
Definition T_pixCopyInputFormat_cps : Po_iface.pixCopyInputFormat_cps RT :=
  Po_copyinf.pixCopyInputFormat_ok RT AFt GP.
Definition T_pixRotate90_cps : Po_iface.pixRotate90_cps RT :=
  Po_rot90.pixRotate90_ok RT AFt GP FKC T_pixCreate1_sure_cps T_pixCopyColormap_cpsF T_pixCopyResolution_po_cps T_pixCopyInputFormat_cps T_pixCopySpp_cps.
Definition T_makeOrientDecision2_cps : Po_mod_defs.makeOrientDecision2_cps RT :=
  Po_mod.makeOrientDecision_ok RT AFt GP FKC T_lept_stderr_cpsF.
Definition T_rasteropHipLow2_cps : Po_hip_defs.rasteropHipLow2_cps RT :=
  Po_hip.rasteropHipLow_ok RT AFt GP L_acc_A_LMASK_132.
Definition T_pixFlipLR2_cps : Po_fliplr_defs.pixFlipLR2_cps RT :=
  Po_fliplr.pixFlipLR_ok RT AFt GP FKC T_pixCopy_same_cps T_rasteropHipLow2_cps.
Definition T_pixFlipTB2_cps : Po_fliptb_defs.pixFlipTB2_cps RT :=
  Po_fliptb.pixFlipTB_ok RT AFt GP FKC T_pixCopy_same_cps.
Definition T_pixRotate180_cps : Po_iface.pixRotate180_cps RT :=
  Po_rot180.pixRotate180_ok RT AFt GP T_pixCopyNew1_sure_cps T_pixFlipLR2_cps T_pixFlipTB2_cps.
Definition T_pixRotateOrth_cps : Po_iface.pixRotateOrth_cps RT :=
  Po_rotorth.pixRotateOrth_ok RT AFt GP T_pixRotate90_cps T_pixRotate180_cps.
Definition T_pixOrientCorrect2_cps : Po_oc_defs.pixOrientCorrect2_cps RT :=
  Po_oc.pixOrientCorrect_ok RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorPtr L_lit_A_OC_ERRMSG L_lit_A_OC_PROC T_pixUpDownDetect2_cps T_pixRotate90_cps T_pixDestroy_cpsF T_makeOrientDecision2_cps T_pixRotateOrth_cps T_pixCopyNew1_sure_cps.

(* [comment removed for export] *)
Hypothesis FUZZ_OK : RT_iface.art_facts RT -> RT_gaps_iface.rt_gaps RT -> RT_fk_iface.rt_fk_contracts RT -> Po_iface.pixDeserialize_res0_cps RT -> Po_oc_defs.pixOrientCorrect2_cps RT -> Bi_fktw.pixDestroy_cpsF RT -> Bi_fktw.pixDestroy_null_cpsF RT -> Po_fz_defs.po_fuzz_one2_cps RT.
Hypothesis ADAPT : Po_fz_defs.po_fuzz_one2_cps RT -> D_libiface.fuzz_one_cps RT D_libiface.LIB_A.

Theorem po_cone_of_open : D_libiface.fuzz_one_cps RT D_libiface.LIB_A.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_top ()) ["Top"] "p,5ADAPTp,7FUZZ_OKg00HQp,2GPp,3FKCg00IGg00JSg00K]g00LaO7O1o"). Qed.
End Top.
