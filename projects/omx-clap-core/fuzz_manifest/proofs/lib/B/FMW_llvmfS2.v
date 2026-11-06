(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_llvmfS2.v at a working branch 79d8c0f1b8f, relocated A->B:
   imports per a Theorem Labs lane's core rule (a working branch 305d8b1527f: lib.A AXxx -> lib.ReusableB YXxx when listed in its
   ReusableB list, other lib.A -> lib.B, FMupoison stays lib.A); every image numeral re-derived from B's listing
   (fuzz_manifest.objdump.txt / nm.txt of the asan-ubsan pin). *)
(* LLVMFuzzerTestOneInput 0x8097c, segment 0x80a50 .. 0x80a6c (fuzz_manifest.c:302-304): tn > 4 MiB returns 0 early
   (bltu to the epilogue at 0x80b74, LF_R); else check_no_overread (uri, un, text, tn), back at 0x80a6c (LF_P2). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YE2k YCfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_llvmfP FMW_llvmfD.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* every frame of a run with no regions in context as same_below (2 ^ 64), chained (FMW_crtB.v crt_sb_nil) *)
Ltac lf_sb_nil :=
  repeat match goal with
  | HF : frame_of ?E ?rs ?m1 ?m2 |- _ =>
      lazymatch m1 with mrestrict _ _ => fail | _ => idtac end;
      let H := fresh "SB" in
      assert (H : same_below m1 m2 (2 ^ 64)) by (apply (frame_nil_same E); exact HF); clear HF
  end;
  repeat match goal with
  | H1 : same_below ?a ?b (2 ^ 64), H2 : same_below ?b ?c (2 ^ 64) |- _ =>
      let H := fresh "SB" in pose proof (same_below_trans a b c (2 ^ 64) H1 H2) as H; clear H1 H2
  end.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis CNO : check_no_overread_spec tfibsegs B CTX_check_no_overread.

(* the input bytes ride through a step that leaves memory below lo as it was *)
Lemma lf_inkept_sb : forall cx (W : world tfibsegs) m m' lo, same_below m m' lo ->
  (0 < lx_n cx -> 0 <= lx_p cx /\ lx_p cx + lx_n cx <= lo) -> lf_inkept cx W m -> lf_inkept cx W m'.
Proof.
intros cx W m m' lo HS Hb HI i Hi. destruct (Hb ltac:(lia)) as [H0 H1].
rewrite (aview_below (w_H W) m m' lo _ HS) by lia. exact (HI i Hi).
Qed.

Lemma lf_seg2 : forall cx ly S W regs mem md k, lf_base B cx -> lf_P1 B cx ly S W regs mem md k ->
  (forall ly' S' W' regs' mem' md' k', lf_P2 B cx ly' S' W' regs' mem' md' k' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P2 regs' mem' md') (lf_post B cx)) ->
  (forall ly' S' W' regs' mem' md' k', lf_R B cx ly' S' W' regs' mem' md' k' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_R regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF_P1 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k HB HP1 K2 KR.
pose proof HB as (HAP & Hra0 & H10 & H11 & Hin0 & Hg0 & Hfr0 & Hev & Hbb & HRO0 & HG0 & Hc0 & Hcnt & Hlive).
destruct HP1 as ((HJ & HFR & Hsp & HK & H21 & HIN & HRO) & -> & Hperm & HG & H8 & H18 & H19 & H20).
unfold lf_J, lx_sp0 in HJ.
pose proof HAP as (HAR0 & _ & _ & Hgp & Htp & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (FC : STK_check_no_overread = 16752) by reflexivity.
assert (Hsp' : spZ regs = spZ (lx_regs cx) - 64) by (unfold lx_sp0, LF_FRAME in Hsp; exact Hsp).
pose proof (lx_ranges B cx HB) as (Rk & Rs6 & Rsk & Rn & Rn0 & Rn1 & Ruw & Rtw & Run & Rtn & Rub).
(* the input block at this state, and its bounds *)
assert (Hblk : 0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly S)).
{ intros Hn. destruct Hin0 as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (Permutation_in _ (Permutation_sym Hperm) Hin). }
assert (Hpb : 0 < lx_n cx -> 0 <= lx_p cx /\ lx_p cx + lx_n cx <= alloc_ceiling).
{ intros Hn. destruct Hin0 as [(Hn0 & _) | (_ & Hin)]; [lia|].
  destruct (lf_window B cx (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) 0 (lx_n cx) HB HAR0
    (fun i _ => eq_refl) (fun _ => Hin) ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & H4096 & Hend & _).
  lia. }
pose proof (fmw_resume_nr W regs [] mem LF_P1) as HS.
unfold cfg_at. change (w64 LF_P1) with (Z_to_bv 64 LF_P1).
assert (U19 : U (Ereg regs []) (SOff 19 0) = lx_tn cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact H19 | lia]).
assert (UL : U (Ereg regs []) (SLit 4194304) = 4194304) by (apply U_lit; lia).
(* 0x80a50: lui a0, 0x400 *)
aj_run fmw_tbl_llvmf_ok HS HJ.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
(* 0x80a54: bltu a0, s3 *)
eapply SRr_sym_branch with (c := BC_LTU) (a := SLit 4194304) (b := SOff 19 0); [exact HS | intros Hb HS2 | intros Hb HS2];
  rewrite branch_ltu_U, UL, U19 in Hb; clear HS.
- (* tn > 4 MiB: on to 0x80b74 *)
  apply Z.ltb_lt in Hb.
  aj_run_to fmw_tbl_llvmf_ok HS2 HJ LF_R.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  lf_sb_nil.
  match goal with H : same_below mem (ms_mem ms2) _ |- _ => rename H into SB end.
  assert (SBc : same_below mem (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
  pose proof (fmw_reg_atom _ regs [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs [] _ ms2 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q21.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms2 HS2 eq_refl). cbn [ss_pc].
  apply (KR ly S W (ms_regs ms2) (ms_mem ms2) _ 0).
  unfold lf_R, lf_core, lf_J.
  split.
  { split; [exact HJ|].
    split; [apply (lf_frame_below cx W mem (ms_mem ms2) SB); [unfold lx_sp0, LF_FRAME; lia | unfold lx_sp0; lia | exact HFR]|].
    split; [unfold spZ at 1; rewrite Q2; exact Hsp|].
    split; [exact (kept_step (w_H W) (lx_regs cx) regs [] _ ms2 (ms_regs ms2) lf_X HK HS2
                     ltac:(vm_compute; reflexivity) (fun r _ => eq_refl))|].
    split; [rewrite Q21; exact H21|].
    split; [exact (lf_inkept_sb cx W mem (ms_mem ms2) (2 ^ 64) SB ltac:(intros Hn; pose proof (Hpb Hn); lia) HIN)|].
    exact (arodata_below B W mem (ms_mem ms2) SBc HRO). }
  split; [unfold EV_LLVMF, EV_check_no_overread, EV_check_reject_clean_starved, EV_check_round_trip, EV_names; lia|].
  split; [exact Hperm|].
  exists (lx_peak cx), (lx_cnt cx). split; [exact (fm_glob_below W mem (ms_mem ms2) _ _ _ _ SBc HG)|].
  unfold CNT_LIB. lia.
- (* tn <= 4 MiB: check_no_overread (uri, un, text, tn) *)
  apply Z.ltb_ge in Hb.
  assert (Htn : lx_tn cx <= MANIFEST_MAX) by (unfold MANIFEST_MAX; lia).
  aj_run_to fmw_tbl_llvmf_ok HS2 HJ A_check_no_overread.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  lf_sb_nil.
  match goal with H : same_below mem (ms_mem ms2) _ |- _ => rename H into SB end.
  assert (SBc : same_below mem (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
  pose proof (fmw_reg_lit _ (Ereg regs []) _ ms2 1%bv LF_P2 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold LF_P2; lia)) as R1.
  pose proof (fmw_reg_atom _ regs [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R2.
  pose proof (fmw_reg_atom _ regs [] _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3.
  pose proof (fmw_reg_atom _ regs [] _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4.
  pose proof (fmw_reg_atom _ regs [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8.
  pose proof (fmw_reg_atom _ regs [] _ ms2 10%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10.
  pose proof (fmw_reg_atom _ regs [] _ ms2 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R11.
  pose proof (fmw_reg_atom _ regs [] _ ms2 12%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R12.
  pose proof (fmw_reg_atom _ regs [] _ ms2 13%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R13.
  pose proof (fmw_reg_atom _ regs [] _ ms2 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R18.
  pose proof (fmw_reg_atom _ regs [] _ ms2 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R19.
  pose proof (fmw_reg_atom _ regs [] _ ms2 20%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R20.
  pose proof (fmw_reg_atom _ regs [] _ ms2 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R21.
  assert (K3 : getr regs 3 = getr (lx_regs cx) 3) by fmw_kget HK (3%bv : bv 5).
  assert (K4 : getr regs 4 = getr (lx_regs cx) 4) by fmw_kget HK (4%bv : bv 5).
  assert (Hsp2 : spZ (ms_regs ms2) = spZ (lx_regs cx) + -64) by (unfold spZ at 1; rewrite R2; fold (spZ regs); lia).
  pose proof HJ as (HARc & _ & _ & _ & _ & _ & Hnev & _).
  assert (HINc : lf_inkept cx W (ms_mem ms2))
    by exact (lf_inkept_sb cx W mem (ms_mem ms2) (2 ^ 64) SB ltac:(intros Hn; pose proof (Hpb Hn); lia) HIN).
  destruct (lf_src_rd B cx ly S W (ms_mem ms2) _ HB HARc HINc Hblk) as (Hsu & Hst & Hnzu & Hnzt & Hwu & Hwt & _ & _).
  assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms2)))
    by exact (arodata_below B W mem (ms_mem ms2) SBc HRO).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms2 HS2 eq_refl). cbn [ss_pc].
  eapply SRr_bind.
  { change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 A_check_no_overread) (ms_mem ms2) (seg_rom tfibsegs)) ?m)
      with (cfg_at tfibsegs A_check_no_overread (ms_regs ms2) (ms_mem ms2) m).
    apply (CNO ly S W (ms_regs ms2) (ms_mem ms2) _ [] (lx_uri cx) (lx_text cx) (lx_ub cx) (lx_tb cx)
      (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ).
    - split; [|exact HRO2].
      apply (afn_pre_at tfibsegs B LLVMF_STK (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx)
        (lx_md cx) [] ly S W (ms_mem ms2) _ 0 (ms_regs ms2) STK_check_no_overread (-64) [] HJ Hsp2).
      all: first [ reflexivity | lia
                 | (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold LF_P2; lia); reflexivity)
                 | (unfold raZ; rewrite R1, unsigned_lit_small by (unfold LF_P2; lia); unfold LF_P2; lia)
                 | (rewrite R3, K3; exact Hgp) | (rewrite R4, K4; exact Htp)
                 | (apply achain_low; unfold s0Z; rewrite R8, H8; unfold w64;
                    rewrite unsigned_lit_small by lia; lia) ].
    - unfold raZ. rewrite R1, unsigned_lit_small by (unfold LF_P2; lia). cbn [spine map].
      unfold CTX_check_no_overread, LF_P2. left. reflexivity.
    - rewrite R10. exact H20.
    - rewrite R11. exact H8.
    - rewrite R12. exact H18.
    - rewrite R13. exact H19.
    - exact Hsu.
    - exact Hst.
    - exact Hnzu.
    - exact Hnzt.
    - exact Hwu.
    - exact Hwt.
    - exact Rub.
    - exact Htn.
    - exact (fm_glob_below W mem (ms_mem ms2) _ _ _ _ SBc HG).
    - split; [reflexivity|]. unfold CNT_LIB in Hcnt. lia.
    - lia.
    - unfold EV_LLVMF, EV_check_no_overread, EV_check_reject_clean_starved, EV_check_round_trip, EV_names in *. lia.
    - rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), <- (blocks_bytes_bsum B (lx_ly cx) (lx_S cx)).
      unfold LIVE_check_no_overread, LIVE_LIB in *. lia. }
  intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HP4 & Hperm4 & HG4).
  (* back at 0x80a6c *)
  pose proof (ajournal_sub_incl B LLVMF_STK (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx)
    (lx_md cx) [] ly S W (ms_mem ms2) _ 0 STK_check_no_overread (spZ (ms_regs ms2)) FM_PSTAT_FP [] ly4 S4 W4 mem4 md4
    EV_check_no_overread HJ HJc ltac:(rewrite Hsp2; lia) ltac:(rewrite Hsp2; lia) (fun a Ha => Ha)) as HJ4.
  cbn [app] in HJ4. replace (0 + EV_check_no_overread) with EV_check_no_overread in HJ4 by reflexivity.
  pose proof HJc as (HAR4 & _ & _ & _ & _ & _ & _ & _ & F1c & F2c & _).
  assert (HRO4 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W4) mem4))
    by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc pstat_closed pstat_not_roP HRO2).
  assert (HFR2 : lf_frame cx W (ms_mem ms2))
    by (apply (lf_frame_below cx W mem (ms_mem ms2) SB); [unfold lx_sp0, LF_FRAME; lia | unfold lx_sp0; lia | exact HFR]).
  assert (HFR4 : lf_frame cx W4 mem4).
  { apply (lf_frame_kept cx W W4 (ms_mem ms2) mem4); [|exact HFR2]. intros a Ha. unfold lx_sp0, LF_FRAME in Ha.
    apply F1c; [lia | rewrite Hsp2; lia]. }
  assert (HIN4 : lf_inkept cx W4 mem4).
  { intros i Hi. rewrite <- (HINc i Hi).
    assert (Hn : 0 < lx_n cx) by lia.
    pose proof (Hblk Hn) as Hb1.
    assert (Hb4 : In (lx_p cx, lx_n cx) (ablocks B ly4 S4)) by exact (Permutation_in _ (Permutation_sym Hperm4) Hb1).
    assert (Hrq : req_size (lx_n cx) = lx_n cx) by (unfold req_size; destruct (Z.eqb_spec (lx_n cx) 0); lia).
    apply (F2c (lx_p cx) (lx_n cx) i Hb1 Hb4); [rewrite Hrq; lia|].
    intros Hf. apply (blk_img tfibsegs B LAWS ly S W (ms_mem ms2) _ (lx_p cx) (lx_n cx) (lx_p cx + i) HARc Hb1);
      [rewrite Hrq; lia | exact (pstat_img _ Hf)]. }
  assert (HK4 : kept_from (lx_regs cx) regs4 lf_X)
    by exact (kept_step (w_H W) (lx_regs cx) regs [] _ ms2 regs4 lf_X HK HS2 ltac:(vm_compute; reflexivity) HP4).
  assert (P2 : getr regs4 2 = getr (ms_regs ms2) 2) by exact (fmw_pres _ _ 2%bv HP4 ltac:(fmw_cs_side)).
  assert (P8 : getr regs4 8 = getr (ms_regs ms2) 8) by exact (fmw_pres _ _ 8%bv HP4 ltac:(fmw_cs_side)).
  assert (P18 : getr regs4 18 = getr (ms_regs ms2) 18) by exact (fmw_pres _ _ 18%bv HP4 ltac:(fmw_cs_side)).
  assert (P19 : getr regs4 19 = getr (ms_regs ms2) 19) by exact (fmw_pres _ _ 19%bv HP4 ltac:(fmw_cs_side)).
  assert (P20 : getr regs4 20 = getr (ms_regs ms2) 20) by exact (fmw_pres _ _ 20%bv HP4 ltac:(fmw_cs_side)).
  assert (P21 : getr regs4 21 = getr (ms_regs ms2) 21) by exact (fmw_pres _ _ 21%bv HP4 ltac:(fmw_cs_side)).
  rewrite R1.
  change (mkCfg (mkst regs4 (Z_to_bv 64 LF_P2) mem4 (seg_rom tfibsegs)) md4) with (cfg_at tfibsegs LF_P2 regs4 mem4 md4).
  apply (K2 ly4 S4 W4 regs4 mem4 md4 EV_check_no_overread).
  unfold lf_P2, lf_core, lf_J.
  split.
  { split; [exact HJ4|]. split; [exact HFR4|].
    split; [unfold spZ at 1; rewrite P2, R2; exact Hsp|].
    split; [exact HK4|]. split; [rewrite P21, R21; exact H21|]. split; [exact HIN4|]. exact HRO4. }
  split; [unfold EV_check_no_overread, EV_names; lia|].
  split; [exact (Permutation_trans Hperm4 Hperm)|].
  split; [exact HG4|].
  split; [exact Htn|].
  split; [rewrite P8, R8; exact H8|]. split; [rewrite P18, R18; exact H18|].
  split; [rewrite P19, R19; exact H19|]. rewrite P20, R20. exact H20.
Qed.
End X.
