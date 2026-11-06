(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts RT_release R_fs_ok R_poison R_fs3 R_fs6 R_fs7 RT_stackmalloc.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_sec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_intalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_frame.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_trans.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_release.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_ok.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs3.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs6.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs7.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_stackmalloc.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Theorem rta_stack_malloc_3 : stack_malloc_contract RTA 3.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m size lo
    FDO MST Hk -> Ha0 Hsz Hsz8 Hlen Hcr ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 3%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  assert (W1 : evt bsegs (sm3_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 3))
                            (fss_flags (fs_of Σ 3)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6094d8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 3) m)).
  { unfold entry_st.
    exact (stack_malloc_3_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 3)) (fss_flags (fs_of Σ 3)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm3_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 2048)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 3) + Z.of_nat jn) mod 2048)) (fss_flags (fs_of Σ 3)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x6094d8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 3%nat (Z.of_nat jn) lo size _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 3)) with 2048; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 472 junk2 _ (fsz (Z.of_nat 3)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _))|]. split; [exact PFr|].
  apply (zero_shadow_prefix m' _ _ _ SH eq_refl). change (fs_size 3) with 512 in Hsz. cbn [cells_bytes cbytes length app le8].
  apply Nat2Z.inj_le. rewrite Z2Nat.id by (apply Z.div_pos; lia). pose proof (Z.div_le_upper_bound size 8 64 ltac:(lia) ltac:(lia)). cbn. lia.
Qed.

Theorem rta_stack_malloc_6 : stack_malloc_contract RTA 6.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m size lo
    FDO MST Hk -> Ha0 Hsz Hsz8 Hlen Hcr ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 6%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  assert (W1 : evt bsegs (sm6_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 6))
                            (fss_flags (fs_of Σ 6)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6094d8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 6) m)).
  { unfold entry_st.
    exact (stack_malloc_6_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 6)) (fss_flags (fs_of Σ 6)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm6_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 256)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 6) + Z.of_nat jn) mod 256)) (fss_flags (fs_of Σ 6)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x6094d8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 6%nat (Z.of_nat jn) lo size _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 6)) with 256; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 4056 junk2 _ (fsz (Z.of_nat 6)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _))|]. split; [exact PFr|].
  unfold ZERO64 in SH. apply (zero_shadow_prefix m' _ _ _ SH eq_refl). change (fs_size 6) with 4096 in Hsz. cbn [cells_bytes cbytes length app le8 repeat].
  apply Nat2Z.inj_le. rewrite Z2Nat.id by (apply Z.div_pos; lia). pose proof (Z.div_le_upper_bound size 8 512 ltac:(lia) ltac:(lia)). cbn. lia.
Qed.

Theorem rta_stack_malloc_7 : stack_malloc_contract RTA 7.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m size lo
    FDO MST Hk -> Ha0 Hsz Hsz8 Hlen Hcr ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *.
  assert (HLO7 : 0x7fff00000000 <= lo).
  { destruct CALL as (_ & LOW & _). pose proof (rta_sp0_win Σ m ART0) as SPW. cbn [rt_sp0 RTA] in LOW. unfold STACK_WIN in LOW. lia. }
  unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 7%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  pose proof (ART_consts Σ m ART0) as (_ & _ & _ & _ & PS & _).
  assert (W1 : evt bsegs (sm7_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 7))
                            (fss_flags (fs_of Σ 7)) lo size m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6094d8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 7) m)).
  { unfold entry_st.
    exact (stack_malloc_7_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 7)) (fss_flags (fs_of Σ 7)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo size tb te
      FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO7 FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0 Ha0 ltac:(change (fs_size 7) with 8192 in Hsz; lia) Hsz8 PS). }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm7_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 128)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 7) + Z.of_nat jn) mod 128)) (fss_flags (fs_of Σ 7)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x6094d8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 7%nat (Z.of_nat jn) lo size _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 7)) with 128; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FRW & FRL & SHW & SHZ & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact FRW|].
  split.
  { change (fsz (Z.of_nat 7)) with 8192.
    lazymatch goal with |- rw_cells _ _ (?X + 8192 - 8) _ => replace (X + 8192 - 8) with (X + 8184) by lia end. exact FRL. }
  split; [exact SHW|]. split; [exact PFr|].
  destruct SHZ as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_defs R_sizeclass R_cache_defs R_prim_defs R_glue_defs
  R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit
  RT_facts RT_release R_fs_ok R_poison R_fs3 R_fs6 R_fs7 RT_stackmalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Theorem rta_stack_malloc_3 : stack_malloc_contract RTA 3.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m size lo
    FDO MST Hk -> Ha0 Hsz Hsz8 Hlen Hcr ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 3%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  assert (W1 : evt asegs (sm3_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 3))
                            (fss_flags (fs_of Σ 3)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x5fc0d8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 3) m)).
  { unfold entry_st.
    exact (stack_malloc_3_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 3)) (fss_flags (fs_of Σ 3)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm3_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 2048)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 3) + Z.of_nat jn) mod 2048)) (fss_flags (fs_of Σ 3)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x5fc0d8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 3%nat (Z.of_nat jn) lo size _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 3)) with 2048; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 472 junk2 _ (fsz (Z.of_nat 3)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _))|]. split; [exact PFr|].
  apply (zero_shadow_prefix m' _ _ _ SH eq_refl). change (fs_size 3) with 512 in Hsz. cbn [cells_bytes cbytes length app le8].
  apply Nat2Z.inj_le. rewrite Z2Nat.id by (apply Z.div_pos; lia). pose proof (Z.div_le_upper_bound size 8 64 ltac:(lia) ltac:(lia)). cbn. lia.
Qed.

Theorem rta_stack_malloc_6 : stack_malloc_contract RTA 6.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m size lo
    FDO MST Hk -> Ha0 Hsz Hsz8 Hlen Hcr ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 6%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  assert (W1 : evt asegs (sm6_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 6))
                            (fss_flags (fs_of Σ 6)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x5fc0d8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 6) m)).
  { unfold entry_st.
    exact (stack_malloc_6_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 6)) (fss_flags (fs_of Σ 6)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm6_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 256)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 6) + Z.of_nat jn) mod 256)) (fss_flags (fs_of Σ 6)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x5fc0d8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 6%nat (Z.of_nat jn) lo size _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 6)) with 256; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 4056 junk2 _ (fsz (Z.of_nat 6)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _))|]. split; [exact PFr|].
  unfold ZERO64 in SH. apply (zero_shadow_prefix m' _ _ _ SH eq_refl). change (fs_size 6) with 4096 in Hsz. cbn [cells_bytes cbytes length app le8 repeat].
  apply Nat2Z.inj_le. rewrite Z2Nat.id by (apply Z.div_pos; lia). pose proof (Z.div_le_upper_bound size 8 512 ltac:(lia) ltac:(lia)). cbn. lia.
Qed.

Theorem rta_stack_malloc_7 : stack_malloc_contract RTA 7.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m size lo
    FDO MST Hk -> Ha0 Hsz Hsz8 Hlen Hcr ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *.
  assert (HLO7 : 0x7fff00000000 <= lo).
  { destruct CALL as (_ & LOW & _). pose proof (rta_sp0_win Σ m ART0) as SPW. cbn [rt_sp0 RTA] in LOW. unfold STACK_WIN in LOW. lia. }
  unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 7%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  pose proof (ART_consts Σ m ART0) as (_ & _ & _ & _ & PS & _).
  assert (W1 : evt asegs (sm7_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 7))
                            (fss_flags (fs_of Σ 7)) lo size m)
                 (entry_st ra sp gp (Z_to_bv 64 0x5fc0d8) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 7) m)).
  { unfold entry_st.
    exact (stack_malloc_7_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 7)) (fss_flags (fs_of Σ 7)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo size tb te
      FC FH FL OK ltac:(lia) HH FF TLS TGA TC TT M2S FSOK HLO7 FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0 Ha0 ltac:(change (fs_size 7) with 8192 in Hsz; lia) Hsz8 PS). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm7_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 128)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 7) + Z.of_nat jn) mod 128)) (fss_flags (fs_of Σ 7)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x5fc0d8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 7%nat (Z.of_nat jn) lo size _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 7)) with 128; lia) Hfree Hcr Hlen LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FRW & FRL & SHW & SHZ & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact FRW|].
  split.
  { change (fsz (Z.of_nat 7)) with 8192.
    lazymatch goal with |- rw_cells _ _ (?X + 8192 - 8) _ => replace (X + 8192 - 8) with (X + 8184) by lia end. exact FRL. }
  split; [exact SHW|]. split; [exact PFr|].
  destruct SHZ as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.
