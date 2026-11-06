(* LLVMFuzzerTestOneInput, segment 0x80ab0 .. 0x80ac8 (fuzz_manifest.c:318-320): a0 := u; check_round_trip (u);
   a0 := u; free (u); a0 := t; free (t); at 0x80ac8 (LF_R) both blocks are gone and the statics are at live with at
   most CNT_LIB more reader allocations. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YC85.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat AE2k ACfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_llvmfP FMW_llvmfD FMW_crtB FMW_crtX.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis UNIV : fm_univ B.
Hypothesis AFREE : afree04_rule tfibsegs B ameter_triv.
Hypothesis CRT : check_round_trip_spec tfibsegs B CTX_check_round_trip.

Lemma lf_seg7 : forall cx ly S W regs mem md k u t, lf_base B cx -> lf_P6 B cx ly S W regs mem md k u t ->
  (forall ly' S' W' regs' mem' md' k', lf_R B cx ly' S' W' regs' mem' md' k' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_R regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF_P6 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k u t HB HP6 KR.
pose proof HB as (HAP0 & _ & _ & _ & Hin0 & _ & _ & Hev0 & Hbb0 & HRO0 & _ & Hc0 & Hc1 & Hlv).
pose proof HAP0 as (HAR0 & _ & _ & Hgp & Htp & _ & _ & _ & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP0) as (Hal16 & Hceil & H47 & _).
destruct HP6 as ((HJ & HFR & Hsp & HKF & H21 & _ & HRO) & Hk & Hperm & HGl & Hu & H8 & H9 & H20).
unfold lf_J, lx_sp0 in HJ. unfold lf_glob6 in HGl.
assert (Hsp' : spZ regs = spZ (lx_regs cx) - 64) by exact Hsp.
pose proof (lx_ranges B cx HB) as (Rk & Rs6 & Rsk & Rn & _ & _ & _ & _ & Run & Rtn & Rlub).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_round_trip = 16784) by reflexivity.
assert (FE : EV_check_round_trip = 2040) by reflexivity.
assert (FL : EV_LLVMF = 2060) by reflexivity.
assert (FK : EV_check_no_overread + 2 + EV_names + EV_check_reject_clean_starved = 18) by reflexivity.
assert (FA : ASTACK = 16384) by reflexivity.
assert (FLS : LLVMF_STK = 32768) by reflexivity.
assert (Us0 : bv_unsigned (w64 (lx_un cx)) = lx_un cx) by (unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hperm' : Permutation (ablocks B ly S) ((u, lx_un cx + 1) :: (t, lx_tn cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)))
  by (eapply Permutation_trans; [exact Hperm | apply perm_swap]).
(* ======== 0x80ab0: a0 := s1; jal check_round_trip ======== *)
pose proof (fmw_resume_nr W regs [] mem LF_P6) as HS1.
unfold cfg_at. change (w64 LF_P6) with (Z_to_bv 64 LF_P6).
aj_run_to fmw_tbl_llvmf_ok HS1 HJ A_check_round_trip.
{ apply awr_ok_nil. }
lazymatch type of HS1 with context [restrict _ ?m] => rename m into ms1 end.
assert (SB1 : same_below mem (ms_mem ms1) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem (ms_mem ms1) |- _ => exact (frame_nil_same _ mem (ms_mem ms1) H) end).
clear HF HFr HG.
pose proof (fmw_reg_lit _ _ _ ms1 1%bv 0x80ab8 HS1 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fmw_reg_atom _ regs [] _ ms1 2%bv 2%bv 2 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R2.
pose proof (fmw_reg_atom _ regs [] _ ms1 3%bv 3%bv 3 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms1 4%bv 4%bv 4 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms1 8%bv 8%bv 8 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fmw_reg_atom _ regs [] _ ms1 9%bv 9%bv 9 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fmw_reg_atom _ regs [] _ ms1 10%bv 9%bv 9 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs [] _ ms1 20%bv 20%bv 20 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R20.
pose proof (fmw_reg_atom _ regs [] _ ms1 21%bv 21%bv 21 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R21.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
assert (SB1c : same_below mem (ms_mem ms1) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
pose proof (cstr_ok_below W mem (ms_mem ms1) u (lx_ub cx) SB1c Hu) as Hu1.
pose proof (fm_glob_below W mem (ms_mem ms1) _ _ _ _ SB1c HGl) as HG1.
pose proof (arodata_below B W mem (ms_mem ms1) SB1c HRO) as HRO1.
pose proof (lf_frame_below cx W mem (ms_mem ms1) SB1 ltac:(unfold lx_sp0, LF_FRAME; lia) ltac:(unfold lx_sp0; lia) HFR)
  as HFR1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS1 eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 A_check_round_trip) (ms_mem ms1) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs A_check_round_trip (ms_regs ms1) (ms_mem ms1) m).
  apply (CRT ly S W (ms_regs ms1) (ms_mem ms1) _ [] u (lx_ub cx) (lx_live cx)
    (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx))
    (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 4) SIZE_MAXZ).
  - split; [|exact HRO1].
    apply (afn_pre_at tfibsegs B LLVMF_STK (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx)
      (lx_md cx) [] ly S W (ms_mem ms1) _ k (ms_regs ms1) STK_check_round_trip (-64) [] HJ ltac:(lia)).
    all: first [ reflexivity | lia
               | (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
               | (unfold raZ; rewrite R1, unsigned_lit_small by lia; lia)
               | (rewrite R3, (kept_get _ _ _ 3%bv HKF ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp)
               | (rewrite R4, (kept_get _ _ _ 4%bv HKF ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp)
               | (apply achain_low; unfold s0Z; rewrite R8, H8, Us0; lia) ].
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. unfold CTX_check_round_trip. left. reflexivity.
  - rewrite R10. exact H9.
  - exact Hu1.
  - apply (lf_kept_blk B ly S u (lx_un cx + 1) _ (lx_ub cx) Hperm'). unfold lx_un. lia.
  - exact Rlub.
  - exact HG1.
  - unfold quiet. split; [reflexivity|]. unfold CNT_LIB in Hc1. destruct (length (lx_ub cx) =? 0)%nat; lia.
  - lia.
  - lia.
  - rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), !bsum_cons,
      <- (blocks_bytes_bsum B (lx_ly cx) (lx_S cx)).
    cbn [snd]. unfold LIVE_check_round_trip. unfold LIVE_LIB in Hbb0. lia. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & Hperm2 & HG2).
pose proof (ajournal_sub_incl B LLVMF_STK (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx)
  (lx_md cx) [] ly S W (ms_mem ms1) _ k STK_check_round_trip (spZ (ms_regs ms1)) FM_PSTAT_FP [] ly2 S2 W2 mem2 md2
  EV_check_round_trip HJ HJc ltac:(lia) ltac:(lia) (fun a Ha => Ha)) as HJ2.
cbn [app] in HJ2.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (HFR2 : lf_frame cx W2 mem2).
{ apply (lf_frame_kept cx W W2 (ms_mem ms1) mem2); [|exact HFR1].
  intros a Ha. unfold lx_sp0, LF_FRAME in Ha. apply F1c; lia. }
assert (E2_2 : getr regs2 2 = getr regs 2) by (rewrite (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)); exact R2).
assert (E8_2 : getr regs2 8 = getr regs 8) by (rewrite (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)); exact R8).
assert (E9_2 : getr regs2 9 = getr regs 9) by (rewrite (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)); exact R9).
assert (E20_2 : getr regs2 20 = getr regs 20) by (rewrite (fmw_pres _ _ 20%bv HP2 ltac:(fmw_cs_side)); exact R20).
assert (E21_2 : getr regs2 21 = getr regs 21) by (rewrite (fmw_pres _ _ 21%bv HP2 ltac:(fmw_cs_side)); exact R21).
pose proof (kept_step (w_H W) (lx_regs cx) regs [] _ ms1 regs2 lf_X HKF HS1 ltac:(vm_compute; reflexivity) HP2) as KF2.
assert (Hperm2' : Permutation (ablocks B ly2 S2)
  ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx))) by exact (Permutation_trans Hperm2 Hperm).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & Hnev2 & _).
(* the blocks are distinct: t and u are not entry blocks, and t is not u *)
assert (ND2 : List.NoDup (ablocks B ly2 S2)).
{ apply crt_nodup_pw.
  - apply Forall_forall. intros [p m] Hpm.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR2 Hpm) as (_ & _ & _ & _ & _ & _ & Hm).
    cbn [snd]. unfold req_size. destruct (Z.eqb_spec m 0); lia.
  - destruct (al_sep _ _ LAWS _ _ _ _ _ HAR2) as [Hp _]. apply pairwise_app_l in Hp as [Hp _]. exact Hp. }
pose proof (Permutation.Permutation_NoDup Hperm2' ND2) as ND.
apply List.NoDup_cons_iff in ND as [Nt ND]. apply List.NoDup_cons_iff in ND as [Nu _].
(* ======== 0x80ab8: a0 := s1; jal free ======== *)
rewrite R1.
pose proof (fmw_resume_nr W2 regs2 [] mem2 0x80ab8) as HS2.
aj_run_to fmw_tbl_llvmf_ok HS2 HJ2 0x52db8.
{ apply awr_ok_nil. }
lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
assert (SB2 : same_below mem2 (ms_mem ms2) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem2 (ms_mem ms2) |- _ => exact (frame_nil_same _ mem2 (ms_mem ms2) H) end).
clear HF HFr HG.
pose proof (fmw_reg_lit _ _ _ ms2 1%bv 0x80ac0 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1b.
pose proof (fmw_reg_atom _ regs2 [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R2b.
pose proof (fmw_reg_atom _ regs2 [] _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3b.
pose proof (fmw_reg_atom _ regs2 [] _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4b.
pose proof (fmw_reg_atom _ regs2 [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8b.
pose proof (fmw_reg_atom _ regs2 [] _ ms2 10%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10b.
pose proof (fmw_reg_atom _ regs2 [] _ ms2 20%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R20b.
pose proof (fmw_reg_atom _ regs2 [] _ ms2 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R21b.
assert (Hsp2 : spZ (ms_regs ms2) = spZ regs) by (unfold spZ; rewrite R2b, E2_2; reflexivity).
assert (SB2c : same_below mem2 (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB2); lia).
pose proof (fm_glob_below W2 mem2 (ms_mem ms2) _ _ _ _ SB2c HG2) as HG2'.
pose proof (lf_frame_below cx W2 mem2 (ms_mem ms2) SB2 ltac:(unfold lx_sp0, LF_FRAME; lia) ltac:(unfold lx_sp0; lia) HFR2)
  as HFR2'.
assert (Hch2 : chain_pre ly2 (aview tfibsegs (w_H W2) (ms_mem ms2)) (ms_regs ms2) []).
{ apply (achain_chain_pre ly2 _ (spZ (ms_regs ms2)) (s0Z (ms_regs ms2)) [] (ms_regs ms2)).
  - apply achain_low. unfold s0Z. rewrite R8b, E8_2, H8, Us0. lia.
  - lia.
  - reflexivity.
  - unfold raZ. rewrite R1b, unsigned_lit_small by lia. lia. }
assert (HU2 : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms2) []) (as_universe B)).
{ apply UNIV. rewrite call_trace_nil, (fb_code B FB).
  assert (RA : raZ (ms_regs ms2) = 0x80ac0) by (unfold raZ; rewrite R1b, unsigned_lit_small by lia; reflexivity).
  rewrite RA. apply memZL_In. vm_compute. reflexivity. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) _ _ ms2 HS2 eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 0x52db8) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite (fb_code B FB); reflexivity).
eapply SRr_bind.
{ apply (YC85.afree04_sub tfibsegs B LAWS HSL ameter_triv AFREE W2 (ms_regs ms2) (ms_mem ms2) LLVMF_STK
    (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) [] ly2 S2 _
    (k + EV_check_round_trip) u (lx_un cx + 1) (-64) (Z_to_bv 64 0x80ac0) []).
  - exact HJ2.
  - apply (Permutation_in _ (Permutation_sym Hperm2')). right. left. reflexivity.
  - rewrite R10b, E9_2. exact H9.
  - lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite R3b, (kept_get _ _ _ 3%bv KF2 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Hgp.
  - rewrite R4b, (kept_get _ _ _ 4%bv KF2 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Htp.
  - exact R1b.
  - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - lia.
  - exact Hch2.
  - exact HU2.
  - intros Hx. exfalso. exact (Nu Hx).
  - exact I. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & Hl1 & Hl2) & _ & HKu & _ & _).
destruct HKu as (KA1 & _ & KA3 & _).
assert (Hperm3 : Permutation (ablocks B ly3 S3) ((t, lx_tn cx + 1) :: ablocks B (lx_ly cx) (lx_S cx))).
{ rewrite Hl2. apply (Permutation_cons_inv (a := (u, lx_un cx + 1))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- Hl1.
  eapply Permutation_trans; [exact Hperm2'|]. apply perm_swap. }
assert (KI3 : forall a, inFP FM_PSTAT_FP a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) (ms_mem ms2) a).
{ intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KA3 a (pstat_img a Ha) N1 N2). }
pose proof (crt_glob_img W2 W3 (ms_mem ms2) mem3 _ _ _ _ KI3 HG2') as HG3.
assert (HFR3 : lf_frame cx W3 mem3).
{ apply (lf_frame_kept cx W2 W3 (ms_mem ms2) mem3); [|exact HFR2'].
  intros a Ha. unfold lx_sp0, LF_FRAME in Ha. apply KA1; lia. }
assert (E2_3 : getr regs3 2 = getr regs 2) by (rewrite (fmw_pres _ _ 2%bv HP3 ltac:(fmw_cs_side)), R2b; exact E2_2).
assert (E8_3 : getr regs3 8 = getr regs 8) by (rewrite (fmw_pres _ _ 8%bv HP3 ltac:(fmw_cs_side)), R8b; exact E8_2).
assert (E20_3 : getr regs3 20 = getr regs 20) by (rewrite (fmw_pres _ _ 20%bv HP3 ltac:(fmw_cs_side)), R20b; exact E20_2).
assert (E21_3 : getr regs3 21 = getr regs 21) by (rewrite (fmw_pres _ _ 21%bv HP3 ltac:(fmw_cs_side)), R21b; exact E21_2).
pose proof (kept_step (w_H W2) (lx_regs cx) regs2 [] _ ms2 regs3 lf_X KF2 HS2 ltac:(vm_compute; reflexivity) HP3) as KF3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
(* ======== 0x80ac0: a0 := s4; jal free ======== *)
pose proof (fmw_resume_nr W3 regs3 [] mem3 0x80ac0) as HS3.
aj_run_to fmw_tbl_llvmf_ok HS3 HJ3 0x52db8.
{ apply awr_ok_nil. }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms3 end.
assert (SB3 : same_below mem3 (ms_mem ms3) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem3 (ms_mem ms3) |- _ => exact (frame_nil_same _ mem3 (ms_mem ms3) H) end).
clear HF HFr HG.
pose proof (fmw_reg_lit _ _ _ ms3 1%bv 0x80ac8 HS3 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1c.
pose proof (fmw_reg_atom _ regs3 [] _ ms3 2%bv 2%bv 2 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R2c.
pose proof (fmw_reg_atom _ regs3 [] _ ms3 3%bv 3%bv 3 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R3c.
pose proof (fmw_reg_atom _ regs3 [] _ ms3 4%bv 4%bv 4 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R4c.
pose proof (fmw_reg_atom _ regs3 [] _ ms3 8%bv 8%bv 8 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R8c.
pose proof (fmw_reg_atom _ regs3 [] _ ms3 10%bv 20%bv 20 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R10c.
pose proof (fmw_reg_atom _ regs3 [] _ ms3 21%bv 21%bv 21 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R21c.
assert (Hsp3 : spZ (ms_regs ms3) = spZ regs) by (unfold spZ; rewrite R2c, E2_3; reflexivity).
assert (SB3c : same_below mem3 (ms_mem ms3) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB3); lia).
pose proof (fm_glob_below W3 mem3 (ms_mem ms3) _ _ _ _ SB3c HG3) as HG3'.
pose proof (lf_frame_below cx W3 mem3 (ms_mem ms3) SB3 ltac:(unfold lx_sp0, LF_FRAME; lia) ltac:(unfold lx_sp0; lia) HFR3)
  as HFR3'.
assert (Hch3 : chain_pre ly3 (aview tfibsegs (w_H W3) (ms_mem ms3)) (ms_regs ms3) []).
{ apply (achain_chain_pre ly3 _ (spZ (ms_regs ms3)) (s0Z (ms_regs ms3)) [] (ms_regs ms3)).
  - apply achain_low. unfold s0Z. rewrite R8c, E8_3, H8, Us0. lia.
  - lia.
  - reflexivity.
  - unfold raZ. rewrite R1c, unsigned_lit_small by lia. lia. }
assert (HU3 : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms3) []) (as_universe B)).
{ apply UNIV. rewrite call_trace_nil, (fb_code B FB).
  assert (RA : raZ (ms_regs ms3) = 0x80ac8) by (unfold raZ; rewrite R1c, unsigned_lit_small by lia; reflexivity).
  rewrite RA. apply memZL_In. vm_compute. reflexivity. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) _ _ ms3 HS3 eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 0x52db8) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite (fb_code B FB); reflexivity).
eapply SRr_bind.
{ apply (YC85.afree04_sub tfibsegs B LAWS HSL ameter_triv AFREE W3 (ms_regs ms3) (ms_mem ms3) LLVMF_STK
    (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) [] ly3 S3 _
    (k + EV_check_round_trip + 1) t (lx_tn cx + 1) (-64) (Z_to_bv 64 0x80ac8) []).
  - exact HJ3.
  - apply (Permutation_in _ (Permutation_sym Hperm3)). left. reflexivity.
  - rewrite R10c, E20_3. exact H20.
  - lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite R3c, (kept_get _ _ _ 3%bv KF3 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Hgp.
  - rewrite R4c, (kept_get _ _ _ 4%bv KF3 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Htp.
  - exact R1c.
  - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - lia.
  - exact Hch3.
  - exact HU3.
  - intros Hx. exfalso. apply Nt. right. exact Hx.
  - exact I. }
intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l3 & l4 & Hl3 & Hl4) & _ & HKt & _ & _).
destruct HKt as (KB1 & _ & KB3 & _).
assert (Hperm4 : Permutation (ablocks B ly4 S4) (ablocks B (lx_ly cx) (lx_S cx))).
{ rewrite Hl4. apply (Permutation_cons_inv (a := (t, lx_tn cx + 1))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- Hl3. exact Hperm3. }
assert (KI4 : forall a, inFP FM_PSTAT_FP a -> aview tfibsegs (w_H W4) mem4 a = aview tfibsegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KB3 a (pstat_img a Ha) N1 N2). }
pose proof (crt_glob_img W3 W4 (ms_mem ms3) mem4 _ _ _ _ KI4 HG3') as HG4.
assert (HFR4 : lf_frame cx W4 mem4).
{ apply (lf_frame_kept cx W3 W4 (ms_mem ms3) mem4); [|exact HFR3'].
  intros a Ha. unfold lx_sp0, LF_FRAME in Ha. apply KB1; lia. }
assert (E2_4 : getr regs4 2 = getr regs 2) by (rewrite (fmw_pres _ _ 2%bv HP4 ltac:(fmw_cs_side)), R2c; exact E2_3).
assert (E21_4 : getr regs4 21 = getr regs 21) by (rewrite (fmw_pres _ _ 21%bv HP4 ltac:(fmw_cs_side)), R21c; exact E21_3).
pose proof (kept_step (w_H W3) (lx_regs cx) regs3 [] _ ms3 regs4 lf_X KF3 HS3 ltac:(vm_compute; reflexivity) HP4) as KF4.
(* ======== 0x80ac8: lf_R ======== *)
change (mkCfg (mkst regs4 (Z_to_bv 64 0x80ac8) mem4 (seg_rom tfibsegs)) md4) with (cfg_at tfibsegs LF_R regs4 mem4 md4).
apply (KR ly4 S4 W4 regs4 mem4 md4 (k + EV_check_round_trip + 1 + 1)).
unfold lf_R, lf_core, lf_J.
split.
{ split; [exact HJ4|].
  split; [exact HFR4|].
  split; [unfold spZ at 1; rewrite E2_4; exact Hsp|].
  split; [exact KF4|].
  split; [rewrite E21_4; exact H21|].
  split.
  - intros i Hi.
    destruct Hin0 as [[Hn0 _] | [_ HinP]]; [lia|].
    assert (Rq : req_size (lx_n cx) = lx_n cx) by (unfold req_size; destruct (Z.eqb_spec (lx_n cx) 0); lia).
    pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    apply (F2 (lx_p cx) (lx_n cx) i HinP (Permutation_in _ (Permutation_sym Hperm4) HinP)); [lia|].
    intros Hf. exact (blk_img tfibsegs B LAWS (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) (lx_p cx) (lx_n cx)
      (lx_p cx + i) HAR0 HinP ltac:(lia) (pstat_img _ Hf)).
  - exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 pstat_closed pstat_not_roP HRO0). }
split; [lia|].
split; [exact Hperm4|].
eexists; eexists; split; [exact HG4|].
pose proof (rt_calls_le _ Rlub) as Hrc.
assert (Hrc0 : 0 <= rt_calls (lx_ub cx)) by (destruct (lx_ub cx); cbn [rt_calls]; lia).
unfold CNT_LIB. destruct (length (lx_ub cx) =? 0)%nat; lia.
Qed.
End X.
