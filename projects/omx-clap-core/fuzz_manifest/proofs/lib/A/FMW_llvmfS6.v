(* LLVMFuzzerTestOneInput 0x80a8c .. 0x80ab0 (fuzz_manifest.c:309-311): check_as_written (t, u, named),
   check_reject_clean (live), check_reject_clean_starved (t, u); back at 0x80ab0 (LF_P6). The three runs between the
   calls only move registers (a0..a2, ra), so every callee-saved register keeps its value at P5 (kept_from regs _ []). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat AE2k ACfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_llvmfP FMW_llvmfD.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a callee-saved register of a later register file that kept_from regs _ [] holds at its P5 value *)
Ltac s6_kr KR r := rewrite (kept_get _ _ [] r KR ltac:(fmw_cs_side) ltac:(intros [])).
(* the run's frame (no regions) as same_below (2 ^ 64); the run's other frame facts are dropped *)
Ltac s6_sb m ms SB :=
  match goal with H : frame_of _ _ m (ms_mem ms) |- _ =>
    assert (SB : same_below m (ms_mem ms) (2 ^ 64)) by exact (frame_nil_same _ m (ms_mem ms) H); clear H end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis CAW : check_as_written_spec tfibsegs B.
Hypothesis CRC : check_reject_clean_spec tfibsegs B.
Hypothesis STARVED : check_reject_clean_starved_spec tfibsegs B CTX_check_reject_clean_starved.

Lemma lf_seg6 : forall cx ly S W regs mem md k u t, lf_base B cx -> lf_P5 B cx ly S W regs mem md k u t ->
  (forall ly' S' W' regs' mem' md' k', lf_P6 B cx ly' S' W' regs' mem' md' k' u t ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P6 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF_P5 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k u t HB HP5 K6.
pose proof HB as (HAP & _ & _ & _ & Hin & _ & _ & Hev0 & Hbb0 & HRO0 & _ & Hc0 & Hc1 & Hlv0).
pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (_ & Hceil & H47 & _).
assert (Hsp0 : alloc_ceiling + LLVMF_STK <= lx_sp0 cx /\ lx_sp0 cx <= 2 ^ 47) by (unfold lx_sp0; lia).
pose proof (lx_ranges B cx HB) as (Rk & _ & _ & _ & _ & _ & _ & _ & Run & _ & Rub).
destruct HP5 as ((HJ & HFR & Hsp & HK & H21 & _ & _) & Hk & Hperm & GL5 & Htn & Hu & Ht & R8 & R9 & R18 & R19 & R20).
unfold lf_J in HJ. unfold lf_glob5 in GL5. unfold LF_FRAME in Hsp. unfold lx_tn in Htn.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof asan_consts as (C1 & _).
assert (FL : LLVMF_STK = 32768) by reflexivity.
assert (FW : STK_check_as_written = ltac:(let v := eval vm_compute in STK_check_as_written in exact v)) by reflexivity.
assert (FC : STK_check_reject_clean = ltac:(let v := eval vm_compute in STK_check_reject_clean in exact v)) by reflexivity.
assert (FS : STK_check_reject_clean_starved = ltac:(let v := eval vm_compute in STK_check_reject_clean_starved in exact v))
  by reflexivity.
assert (Egp : getr regs 3 = w64 (as_gp B)) by (rewrite (kept_get _ _ _ 3%bv HK ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp).
assert (Etp : getr regs 4 = w64 (as_tp B)) by (rewrite (kept_get _ _ _ 4%bv HK ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp).
assert (Uun : bv_unsigned (w64 (lx_un cx)) = lx_un cx) by (unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hkt0 : cstr_kept B ly S t (lx_tb cx)) by exact (lf_kept_blk B ly S t _ _ (lx_tb cx) Hperm ltac:(unfold lx_tn; lia)).
assert (Hku0 : cstr_kept B ly S u (lx_ub cx))
  by exact (lf_kept_blk B ly S u _ _ (lx_ub cx) (Permutation_trans Hperm (perm_swap _ _ _)) ltac:(unfold lx_un; lia)).
unfold cfg_at. change (w64 LF_P5) with (Z_to_bv 64 LF_P5).
(* ======== 0x80a8c: a0 := t, a1 := u, a2 := named; check_as_written ======== *)
pose proof (fmw_resume_nr W regs [] mem LF_P5) as HS.
aj_run_to fmw_tbl_llvmf_ok HS HJ A_check_as_written.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
s6_sb mem ms1 SB1.
assert (SB1c : same_below mem (ms_mem ms1) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
pose proof (fmw_reg_lit _ (Ereg regs []) _ ms1 1%bv 0x80a9c HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
pose proof (fmw_reg_atom _ regs [] _ ms1 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as Q2.
pose proof (fmw_reg_atom _ regs [] _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fmw_reg_atom _ regs [] _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fmw_reg_atom _ regs [] _ ms1 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fmw_reg_atom _ regs [] _ ms1 10%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as Q10.
pose proof (fmw_reg_atom _ regs [] _ ms1 11%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as Q11.
pose proof (fmw_reg_atom _ regs [] _ ms1 12%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as Q12.
assert (Hsp1 : spZ (ms_regs ms1) = lx_sp0 cx + -64) by (unfold spZ at 1; rewrite Q2; fold (spZ regs); lia).
assert (HROc1 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms1)))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ pstat_closed pstat_not_roP HRO0).
pose proof (cstr_ok_below W mem (ms_mem ms1) t _ SB1c Ht) as Htc1.
pose proof (cstr_ok_below W mem (ms_mem ms1) u _ SB1c Hu) as Huc1.
pose proof (lf_frame_below cx W mem (ms_mem ms1) SB1 ltac:(unfold LF_FRAME; lia) ltac:(lia) HFR) as HFRc1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (Ereg regs []) _ ms1 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 A_check_as_written) (ms_mem ms1) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs A_check_as_written (ms_regs ms1) (ms_mem ms1) m).
  apply (CAW ly S W (ms_regs ms1) (ms_mem ms1) _ [] t u (lx_tb cx) (lx_ub cx) (lx_live cx)
    (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx)) (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 3)
    SIZE_MAXZ).
  - split; [|exact HROc1].
    apply (afn_pre_at tfibsegs B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) []
      ly S W (ms_mem ms1) _ k (ms_regs ms1) STK_check_as_written (-64) [] HJ Hsp1).
    all: first [ reflexivity | lia
               | (rewrite Q1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
               | (unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
               | (rewrite Q3; exact Egp) | (rewrite Q4; exact Etp)
               | (apply achain_low; unfold s0Z; rewrite Q8, R8, Uun; lia) ].
  - exact (fm_glob_below W mem (ms_mem ms1) _ _ _ _ SB1c GL5).
  - rewrite Q10. exact R20.
  - rewrite Q11. exact R9.
  - rewrite Q12. exact R19.
  - exact Htc1.
  - exact Huc1.
  - exact Hkt0.
  - exact Hku0.
  - exact Rub.
  - exact Htn. }
intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJc1 & HP1 & Hbl1 & GL1).
pose proof (ajournal_sub_incl B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) []
  ly S W (ms_mem ms1) _ k STK_check_as_written (spZ (ms_regs ms1)) [] [] ly1 S1 W1 mem1 md1 0 HJ HJc1
  ltac:(rewrite Hsp1; lia) ltac:(rewrite Hsp1; lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ1.
cbn [app] in HJ1. rewrite Z.add_0_r in HJ1.
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 pstat_closed pstat_not_roP HRO0) as HROp1.
pose proof HJc1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c1 & _).
assert (HFR1 : lf_frame cx W1 mem1).
{ apply (lf_frame_kept cx W W1 (ms_mem ms1) mem1); [|exact HFRc1].
  intros a Ha. unfold LF_FRAME in Ha. apply F1c1; [lia | rewrite Hsp1; lia]. }
assert (Hinc1 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly1 S1)) by (rewrite Hbl1; auto).
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t _ IMG HJc1 Hinc1 nil_img HROp1 Hkt0 Htc1) as Ht1.
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u _ IMG HJc1 Hinc1 nil_img HROp1 Hku0 Huc1) as Hu1.
assert (Perm1 : Permutation (ablocks B ly1 S1) ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)))
  by (rewrite Hbl1; exact Hperm).
assert (Hkt1 : cstr_kept B ly1 S1 t (lx_tb cx))
  by exact (lf_kept_blk B ly1 S1 t _ _ (lx_tb cx) Perm1 ltac:(unfold lx_tn; lia)).
assert (Hku1 : cstr_kept B ly1 S1 u (lx_ub cx))
  by exact (lf_kept_blk B ly1 S1 u _ _ (lx_ub cx) (Permutation_trans Perm1 (perm_swap _ _ _)) ltac:(unfold lx_un; lia)).
pose proof (kept_step (w_H W) regs regs [] _ ms1 regs1 [] (kept_refl regs []) HS ltac:(vm_compute; reflexivity) HP1) as KR1.
rewrite Q1.
clear HS HJ HJc1 F1c1 HFRc1 Htc1 Huc1 HROc1 Hinc1 GL5 HFR Ht Hu Hkt0 Hku0 Q1 Q2 Q3 Q4 Q8 Q10 Q11 Q12.
(* ======== 0x80a9c: a0 := live; check_reject_clean ======== *)
pose proof (fmw_resume_nr W1 regs1 [] mem1 0x80a9c) as HS.
aj_run_to fmw_tbl_llvmf_ok HS HJ1 A_check_reject_clean.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
s6_sb mem1 ms2 SB2.
assert (SB2c : same_below mem1 (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB2); lia).
pose proof (fmw_reg_lit _ (Ereg regs1 []) _ ms2 1%bv 0x80aa4 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
pose proof (fmw_reg_atom _ regs1 [] _ ms2 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as Q2.
pose proof (fmw_reg_atom _ regs1 [] _ ms2 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fmw_reg_atom _ regs1 [] _ ms2 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fmw_reg_atom _ regs1 [] _ ms2 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fmw_reg_atom _ regs1 [] _ ms2 10%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as Q10.
assert (Hsp2 : spZ (ms_regs ms2) = lx_sp0 cx + -64)
  by (unfold spZ at 1; rewrite Q2; s6_kr KR1 (2%bv : bv 5); fold (spZ regs); lia).
assert (HROc2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W1) (ms_mem ms2)))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 pstat_closed pstat_not_roP HRO0).
pose proof (cstr_ok_below W1 mem1 (ms_mem ms2) t _ SB2c Ht1) as Htc2.
pose proof (cstr_ok_below W1 mem1 (ms_mem ms2) u _ SB2c Hu1) as Huc2.
pose proof (lf_frame_below cx W1 mem1 (ms_mem ms2) SB2 ltac:(unfold LF_FRAME; lia) ltac:(lia) HFR1) as HFRc2.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W1) (Ereg regs1 []) _ ms2 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 A_check_reject_clean) (ms_mem ms2) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs A_check_reject_clean (ms_regs ms2) (ms_mem ms2) m).
  apply (CRC ly1 S1 W1 (ms_regs ms2) (ms_mem ms2) _ [] (lx_live cx)
    (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx)) (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 3)
    SIZE_MAXZ).
  - split; [|exact HROc2].
    apply (afn_pre_at tfibsegs B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) []
      ly1 S1 W1 (ms_mem ms2) _ k (ms_regs ms2) STK_check_reject_clean (-64) [] HJ1 Hsp2).
    all: first [ reflexivity | lia
               | (rewrite Q1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
               | (unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
               | (rewrite Q3; s6_kr KR1 (3%bv : bv 5); exact Egp) | (rewrite Q4; s6_kr KR1 (4%bv : bv 5); exact Etp)
               | (apply achain_low; unfold s0Z; rewrite Q8; s6_kr KR1 (8%bv : bv 5); rewrite R8, Uun; lia) ].
  - exact (fm_glob_below W1 mem1 (ms_mem ms2) _ _ _ _ SB2c GL1).
  - rewrite Q10. s6_kr KR1 (18%bv : bv 5). exact R18. }
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc2 & HP2 & Hbl2 & GL2).
pose proof (ajournal_sub_incl B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) []
  ly1 S1 W1 (ms_mem ms2) _ k STK_check_reject_clean (spZ (ms_regs ms2)) [] [] ly2 S2 W2 mem2 md2 0 HJ1 HJc2
  ltac:(rewrite Hsp2; lia) ltac:(rewrite Hsp2; lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 pstat_closed pstat_not_roP HRO0) as HROp2.
pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c2 & _).
assert (HFR2 : lf_frame cx W2 mem2).
{ apply (lf_frame_kept cx W1 W2 (ms_mem ms2) mem2); [|exact HFRc2].
  intros a Ha. unfold LF_FRAME in Ha. apply F1c2; [lia | rewrite Hsp2; lia]. }
assert (Hinc2 : forall x, In x (ablocks B ly1 S1) -> In x (ablocks B ly2 S2)) by (rewrite Hbl2; auto).
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t _ IMG HJc2 Hinc2 nil_img HROp2 Hkt1 Htc2) as Ht2.
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u _ IMG HJc2 Hinc2 nil_img HROp2 Hku1 Huc2) as Hu2.
assert (Perm2 : Permutation (ablocks B ly2 S2) ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)))
  by (rewrite Hbl2; exact Perm1).
assert (Hkt2 : cstr_kept B ly2 S2 t (lx_tb cx))
  by exact (lf_kept_blk B ly2 S2 t _ _ (lx_tb cx) Perm2 ltac:(unfold lx_tn; lia)).
assert (Hku2 : cstr_kept B ly2 S2 u (lx_ub cx))
  by exact (lf_kept_blk B ly2 S2 u _ _ (lx_ub cx) (Permutation_trans Perm2 (perm_swap _ _ _)) ltac:(unfold lx_un; lia)).
pose proof (kept_step (w_H W1) regs regs1 [] _ ms2 regs2 [] KR1 HS ltac:(vm_compute; reflexivity) HP2) as KR2.
rewrite Q1.
clear HS HJ1 HJc2 F1c2 HFRc2 Htc2 Huc2 HROc2 HROp1 Hinc2 GL1 HFR1 Ht1 Hu1 Hkt1 Hku1 Perm1 Q1 Q2 Q3 Q4 Q8 Q10.
(* ======== 0x80aa4: a0 := t, a1 := u; check_reject_clean_starved ======== *)
pose proof (fmw_resume_nr W2 regs2 [] mem2 0x80aa4) as HS.
aj_run_to fmw_tbl_llvmf_ok HS HJ2 A_check_reject_clean_starved.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
s6_sb mem2 ms3 SB3.
assert (SB3c : same_below mem2 (ms_mem ms3) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB3); lia).
pose proof (fmw_reg_lit _ (Ereg regs2 []) _ ms3 1%bv 0x80ab0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
pose proof (fmw_reg_atom _ regs2 [] _ ms3 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as Q2.
pose proof (fmw_reg_atom _ regs2 [] _ ms3 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fmw_reg_atom _ regs2 [] _ ms3 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fmw_reg_atom _ regs2 [] _ ms3 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fmw_reg_atom _ regs2 [] _ ms3 10%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as Q10.
pose proof (fmw_reg_atom _ regs2 [] _ ms3 11%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as Q11.
assert (Hsp3 : spZ (ms_regs ms3) = lx_sp0 cx + -64)
  by (unfold spZ at 1; rewrite Q2; s6_kr KR2 (2%bv : bv 5); fold (spZ regs); lia).
assert (HROc3 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) (ms_mem ms3)))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 pstat_closed pstat_not_roP HRO0).
pose proof (cstr_ok_below W2 mem2 (ms_mem ms3) t _ SB3c Ht2) as Htc3.
pose proof (cstr_ok_below W2 mem2 (ms_mem ms3) u _ SB3c Hu2) as Huc3.
pose proof (lf_frame_below cx W2 mem2 (ms_mem ms3) SB3 ltac:(unfold LF_FRAME; lia) ltac:(lia) HFR2) as HFRc3.
assert (Hnev : st_nev S2 + EV_check_reject_clean_starved <= EV_MAX).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnv & _).
  unfold EV_LLVMF, EV_check_round_trip, EV_check_no_overread, EV_check_reject_clean_starved, EV_names in *. lia. }
assert (Hbb : blocks_bytes S2 + LIVE_names <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Perm2), !bsum_cons. cbn [snd].
  rewrite <- (blocks_bytes_bsum B (lx_ly cx) (lx_S cx)).
  unfold LIVE_LIB, LIVE_names, MANIFEST_MAX in *. unfold lx_tn. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) (Ereg regs2 []) _ ms3 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_check_reject_clean_starved) (ms_mem ms3) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs A_check_reject_clean_starved (ms_regs ms3) (ms_mem ms3) m).
  apply (STARVED ly2 S2 W2 (ms_regs ms3) (ms_mem ms3) _ [] t u (lx_tb cx) (lx_ub cx) (lx_live cx)
    (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx)) (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 3)
    SIZE_MAXZ).
  - split; [|exact HROc3].
    apply (afn_pre_at tfibsegs B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) []
      ly2 S2 W2 (ms_mem ms3) _ k (ms_regs ms3) STK_check_reject_clean_starved (-64) [] HJ2 Hsp3).
    all: first [ reflexivity | lia
               | (rewrite Q1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
               | (unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
               | (rewrite Q3; s6_kr KR2 (3%bv : bv 5); exact Egp) | (rewrite Q4; s6_kr KR2 (4%bv : bv 5); exact Etp)
               | (apply achain_low; unfold s0Z; rewrite Q8; s6_kr KR2 (8%bv : bv 5); rewrite R8, Uun; lia) ].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. cbn [spine map].
    unfold CTX_check_reject_clean_starved. left. reflexivity.
  - rewrite Q10. s6_kr KR2 (20%bv : bv 5). exact R20.
  - rewrite Q11. s6_kr KR2 (9%bv : bv 5). exact R9.
  - exact Htc3.
  - exact Huc3.
  - exact Hkt2.
  - exact Hku2.
  - exact Rub.
  - exact Htn.
  - exact (fm_glob_below W2 mem2 (ms_mem ms3) _ _ _ _ SB3c GL2).
  - unfold quiet, CNT_LIB in *. split; [reflexivity|]. destruct (length (lx_ub cx) =? 0)%nat; lia.
  - lia.
  - exact Hnev.
  - exact Hbb. }
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJc3 & HP3 & Hperm3 & GL3).
pose proof (ajournal_sub_incl B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) []
  ly2 S2 W2 (ms_mem ms3) _ k STK_check_reject_clean_starved (spZ (ms_regs ms3)) FM_PSTAT_FP [] ly3 S3 W3 mem3 md3
  EV_check_reject_clean_starved HJ2 HJc3 ltac:(rewrite Hsp3; lia) ltac:(rewrite Hsp3; lia) (fun a Ha => Ha)) as HJ3.
cbn [app] in HJ3.
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 pstat_closed pstat_not_roP HRO0) as HROp3.
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c3 & _).
assert (HFR3 : lf_frame cx W3 mem3).
{ apply (lf_frame_kept cx W2 W3 (ms_mem ms3) mem3); [|exact HFRc3].
  intros a Ha. unfold LF_FRAME in Ha. apply F1c3; [lia | rewrite Hsp3; lia]. }
assert (Hinc3 : forall x, In x (ablocks B ly2 S2) -> In x (ablocks B ly3 S3))
  by (intros x Hx; exact (Permutation_in x (Permutation_sym Hperm3) Hx)).
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u _ IMG HJc3 Hinc3 pstat_img HROp3 Hku2 Huc3) as Hu3.
pose proof (Permutation_trans Hperm3 Perm2) as Perm3.
pose proof (kept_step (w_H W2) regs regs2 [] _ ms3 regs3 [] KR2 HS ltac:(vm_compute; reflexivity) HP3) as KR3.
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
rewrite Q1.
change (mkCfg (mkst regs3 (Z_to_bv 64 0x80ab0) mem3 (seg_rom tfibsegs)) md3) with (cfg_at tfibsegs LF_P6 regs3 mem3 md3).
apply (K6 ly3 S3 W3 regs3 mem3 md3 (k + EV_check_reject_clean_starved)).
unfold lf_P6, lf_core, lf_J.
split; [|split; [|split; [exact Perm3 |]]].
- split; [exact HJ3|]. split; [exact HFR3|].
  split; [unfold LF_FRAME, spZ; s6_kr KR3 (2%bv : bv 5); fold (spZ regs); lia|].
  split; [intros r Hc Hn; rewrite (KR3 r Hc ltac:(intros [])); exact (HK r Hc Hn)|].
  split; [s6_kr KR3 (21%bv : bv 5); exact H21|].
  split; [|exact HROp3].
  intros i Hi.
  destruct Hin as [(Hn0 & _) | (Hnpos & Hinp)]; [lia|].
  assert (Hin3 : In (lx_p cx, lx_n cx) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Perm3)). right. right. exact Hinp. }
  assert (Hrq : req_size (lx_n cx) = lx_n cx) by (unfold req_size; destruct (Z.eqb_spec (lx_n cx) 0); lia).
  apply (G2 (lx_p cx) (lx_n cx) i Hinp Hin3 ltac:(rewrite Hrq; lia)).
  intros Hf. apply (blk_img tfibsegs B LAWS ly3 S3 W3 mem3 md3 (lx_p cx) (lx_n cx) (lx_p cx + i) HAR3 Hin3 ltac:(rewrite Hrq; lia)).
  exact (pstat_img _ Hf).
- unfold EV_check_reject_clean_starved, EV_names in *. lia.
- split.
  { unfold lf_glob6. revert GL3. destruct (length (lx_ub cx) =? 0)%nat; intros GL3; [exact GL3|].
    replace (lx_cnt cx + 4) with (lx_cnt cx + 3 + 1) by lia. exact GL3. }
  split; [exact Hu3|].
  split; [s6_kr KR3 (8%bv : bv 5); exact R8|].
  split; [s6_kr KR3 (9%bv : bv 5); exact R9|].
  s6_kr KR3 (20%bv : bv 5). exact R20.
Qed.
End X.
