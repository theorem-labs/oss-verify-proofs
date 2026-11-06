(* check_round_trip, first stretch: the prologue (13 registers saved, s10 := the shadow base), n := strlen (uri),
   names ("", uri), back at 0x80f00 (fuzz_manifest.c:258-262). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_crt0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Ltac cs_tac := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.

Lemma crt_segA : forall cx (Q : world tfibsegs -> config -> Prop),
  crt_base B cx ->
  (forall ly' S' W' regs' mem' md' k, crt_P2 B cx ly' S' W' regs' mem' md' k ->
     SRr tfibsegs W' (cfg_at tfibsegs CRT_P2 regs' mem' md') Q) ->
  SRr tfibsegs (cx_W cx) (cfg_at tfibsegs A_check_round_trip (cx_regs cx) (cx_mem cx) (cx_md cx)) Q.
Proof.
intros [ly S W regs mem md ch u ub live peak cnt] Q
  (HPRE & HCTX & H10 & Hu & Hku & Hlu & HG & HQ & Hlive & Hev & Hbb) K2.
unfold cx_n in *. cbn [cx_ly cx_S cx_W cx_regs cx_mem cx_md cx_ch cx_u cx_ub cx_live cx_peak cx_cnt] in *.
destruct HPRE as [HAP HRO].
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fmw_sp B _ ly S W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_round_trip = 16784) by reflexivity.
pose proof (fmw_entry_sb B FB W ly S regs mem md STK_check_round_trip A_check_round_trip 112 HAR Hstk
  ltac:(lia) Hpres ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_check_round_trip FM_PSTAT_FP ly S W regs mem md ch HAP) as HJ.
set (E := Ereg regs [Z_to_bv 64 FMW_SB]) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_check_round_trip) with (Z_to_bv 64 A_check_round_trip).
unfold fmw_entry_ss in HS.
(* ---- the prologue, up to the strlen call at 0x80ee8 ---- *)
aj_run_to fmw_tbl_crt_ok HS HJ PC_strlen.
{ awr_ok_tac. exact Usp. }
pose proof (fmw_reg_lit _ E _ ms 1%bv CRT_P1 HS ltac:(vm_compute; reflexivity) ltac:(unfold CRT_P1; lia)) as R1.
pose proof (fmw_reg_off _ E _ ms 2%bv 2 (-112) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fmw_reg_atom _ regs _ _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs _ _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs _ _ ms 8%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fmw_reg_atom _ regs _ _ ms 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_extra _ regs _ _ ms 26%bv 0 HS ltac:(vm_compute; reflexivity)) as R26. cbn [nth] in R26.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -112) by (unfold spZ at 1; rewrite R2; lia).
pose proof (fmw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (HFR1 : crt_frame (mkCX ly S W regs mem md ch u ub live peak cnt) W (ms_mem ms)).
{ eapply (crt_frame_of_chunks (mkCX ly S W regs mem md ch u ub live peak cnt) W (ms_mem ms) _ _ _ _ _ _ HR0).
  intros j o r Ho Hr.
  do 13 (destruct j as [|j]; [cbn in Ho, Hr; injection Ho as <-; injection Hr as <-; cbn;
    repeat (first [left; reflexivity | right]) |]).
  destruct j; cbn in Ho; discriminate Ho. }
clear HR0.
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ apply (same_below_frame E _ mem (ms_mem ms) alloc_ceiling HF); [|lia].
  cbn [ss_mem]. unfold fmw_stack_region, fmw_got_region, fmw_bcell_region.
  apply Forall_cons; [right; cbn [YP09.r_base YP09.r_wlo base_val]; rewrite Usp; lia|].
  apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
pose proof HJ as (HAR1 & _).
pose proof (arodata_below B W mem (ms_mem ms) SB1 HRO) as HRO1.
destruct (IMG ly S W (ms_mem ms) _ HAR1 HRO1) as (HROM1 & _ & _ & _).
pose proof (cstr_ok_below W mem (ms_mem ms) u ub SB1 Hu) as Hu1.
pose proof (fm_glob_below W mem (ms_mem ms) live peak cnt SIZE_MAXZ SB1 HG) as HG1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
clear HF HFr.
(* ---- strlen (uri) ---- *)
eapply SRr_bind.
{ change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_strlen) (ms_mem ms) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs PC_strlen (ms_regs ms) (ms_mem ms) m).
  eapply (fmw_aj_rt_ro B W (ms_regs ms) (ms_mem ms) _ PC_strlen _ _ _ ly S W mem md ly S 0 STK_RT_STR _ (-112) HJ Hsp1);
    [lia | unfold STK_RT_STR, ESTACK; lia | unfold STK_RT_STR, ESTACK; lia |].
  apply (STRLEN ly S W (ms_regs ms) (ms_mem ms) _ u ub).
  - apply (fmw_ecall_pre_k B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-112) HJ Hsp1).
    all: first [ reflexivity | (cbv [STK_RT_STR ESTACK]; lia)
               | (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold CRT_P1; lia); reflexivity)
               | (rewrite R3; exact Hgp) | (rewrite R4; exact Htp) ].
  - exact HROM1.
  - rewrite R10. exact H10.
  - exact Hu1. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10' & Hv & Hvl & Hfr2).
subst v. rewrite R1.
(* ---- 0x80eec: s3 := n; a0 := ""; a1 := uri; names ---- *)
pose proof (fmw_resume_nr W regs2 [] mem2 CRT_P1) as HS2.
assert (LS2 : low_same W W (ms_mem ms) mem2).
{ apply (low_same_of_win W (ms_mem ms) mem2 (spZ (ms_regs ms) - STK_RT_STR) (spZ (ms_regs ms)) Hfr2).
  rewrite Hsp1. unfold STK_RT_STR, ESTACK. lia. }
assert (HFR2 : crt_frame (mkCX ly S W regs mem md ch u ub live peak cnt) W mem2).
{ apply (crt_frame_kept _ W W (ms_mem ms) mem2); [|exact HFR1]. intros a Ha.
  unfold cx_sp0 in Ha. cbn [cx_regs] in Ha. unfold CRT_FRAME in Ha. pose proof (proj1 alloc_ceiling_val).
  apply Hfr2; [lia | rewrite Hsp1; lia]. }
aj_run_to fmw_tbl_crt_ok HS2 HJ2 A_names.
{ apply awr_ok_nil. }
lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms3 end.
set (E2 := Ereg regs2 []) in HS2.
pose proof (fmw_reg_lit _ E2 _ ms3 1%bv CRT_P2 HS2 ltac:(vm_compute; reflexivity) ltac:(unfold CRT_P2; lia)) as Q1.
pose proof (fmw_reg_atom _ regs2 _ _ ms3 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
pose proof (fmw_reg_atom _ regs2 _ _ ms3 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fmw_reg_atom _ regs2 _ _ ms3 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fmw_reg_atom _ regs2 _ _ ms3 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fmw_reg_lit _ E2 _ ms3 10%bv STR_empty HS2 ltac:(vm_compute; reflexivity) ltac:(unfold STR_empty; lia)) as Q10.
pose proof (fmw_reg_atom _ regs2 _ _ ms3 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
pose proof (fmw_reg_atom _ regs2 _ _ ms3 19%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
pose proof (fmw_reg_atom _ regs2 _ _ ms3 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q26.
(* the callee-saved values regs2 holds (strlen kept them) *)
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (fmw_pres _ _ 2%bv HP2 ltac:(cs_tac)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (fmw_pres _ _ 3%bv HP2 ltac:(cs_tac)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (fmw_pres _ _ 4%bv HP2 ltac:(cs_tac)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (fmw_pres _ _ 8%bv HP2 ltac:(cs_tac)).
assert (P26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (fmw_pres _ _ 26%bv HP2 ltac:(cs_tac)).
assert (Hsp3 : spZ (ms_regs ms3) = spZ regs + -112) by (unfold spZ at 1; rewrite Q2, P2; exact Hsp1).
assert (SB3 : same_below mem2 (ms_mem ms3) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem2 (ms_mem ms3) |- _ => exact (frame_nil_same _ mem2 (ms_mem ms3) H) end).
pose proof HJ2 as (HAR3 & _).
assert (SB3c : same_below mem2 (ms_mem ms3) alloc_ceiling)
  by (apply (same_below_mono _ _ _ _ SB3); pose proof (proj1 alloc_ceiling_val); lia).
assert (HRO3 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms3))).
{ apply (arodata_below B W mem2 (ms_mem ms3) SB3c).
  exact (arodata_low B W W (ms_mem ms) mem2 LS2 HRO1). }
assert (Hu3 : cstr_ok tfibsegs W (ms_mem ms3) u ub).
{ apply (cstr_ok_below W mem2 (ms_mem ms3) u ub SB3c).
  exact (cstr_ok_low W W (ms_mem ms) mem2 u ub LS2 Hu1). }
assert (HG3 : fm_glob tfibsegs W (ms_mem ms3) live peak cnt SIZE_MAXZ).
{ apply (fm_glob_below W mem2 (ms_mem ms3) live peak cnt SIZE_MAXZ SB3c).
  exact (fm_glob_low W W (ms_mem ms) mem2 live peak cnt SIZE_MAXZ LS2 HG1). }
assert (HFR3 : crt_frame (mkCX ly S W regs mem md ch u ub live peak cnt) W (ms_mem ms3)).
{ apply (crt_frame_below _ W mem2 (ms_mem ms3) SB3); unfold cx_sp0; cbn [cx_regs]; [unfold CRT_FRAME; lia | lia | exact HFR2]. }
destruct (IMG ly S W (ms_mem ms3) _ HAR3 HRO3) as (_ & _ & _ & HSTRS3 & _).
pose proof (proj1 (proj1 (Forall_forall _ _) HSTRS3 (STR_empty, []) ltac:(left; reflexivity))) as He3.
cbn [fst snd] in He3.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ ms3 HS2 eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 A_names) (ms_mem ms3) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs A_names (ms_regs ms3) (ms_mem ms3) m).
  apply (NAMES ly S W (ms_regs ms3) (ms_mem ms3) _ [] STR_empty u [] ub live peak cnt SIZE_MAXZ).
  - split; [|exact HRO3].
    assert (FN : STK_names = 16640) by reflexivity.
    apply (afn_pre_at tfibsegs B STK_check_round_trip (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W (ms_mem ms3) _ 0
      (ms_regs ms3) STK_names (-112) [] HJ2 Hsp3).
    all: first [ reflexivity | lia
               | (rewrite Q1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold CRT_P2; lia); reflexivity)
               | (unfold raZ; rewrite Q1, unsigned_lit_small by (unfold CRT_P2; lia); unfold CRT_P2; lia)
               | (rewrite Q3, P3, R3; exact Hgp) | (rewrite Q4, P4, R4; exact Htp)
               | (apply achain_low; unfold s0Z; rewrite Q8, P8, R8, H10; unfold w64;
                  destruct Hu as (_ & H4096 & Hc & _); pose proof (proj1 alloc_ceiling_val);
                  rewrite unsigned_lit_small by lia; lia) ].
  - unfold raZ. rewrite Q1, unsigned_lit_small by (unfold CRT_P2; lia). cbn [spine].
    unfold CTX_lv2_locate_manifest_names, CRT_P2. repeat (first [left; reflexivity | right]).
  - rewrite Q10. reflexivity.
  - rewrite Q11, P8, R8. exact H10.
  - exact He3.
  - exact Hu3.
  - right. exists STR_empty, [], 0%nat. split; [left; left; reflexivity | split; [lia | split; [cbn; lia | reflexivity]]].
  - exact Hku.
  - exact Hlu.
  - cbn. unfold MANIFEST_MAX. lia.
  - exact HG3.
  - exact Hlive.
  - destruct HQ as (_ & H0 & H1). lia.
  - unfold EV_check_round_trip, EV_names in Hev |- *. lia.
  - unfold LIVE_check_round_trip, LIVE_names in Hbb |- *. lia. }
intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HP4 & res & H10r & Hperm4 & HNR).
destruct (names_res_quiet W4 mem4 [] ub live peak cnt SIZE_MAXZ res HNR ltac:(destruct HQ as (_ & H0 & H1); split; [reflexivity | lia]))
  as [Hres HG4].
rewrite ManifestModel.rt_empty in Hres. subst res.
pose proof (ajournal_sub_incl B STK_check_round_trip (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W (ms_mem ms3) _ 0
  STK_names (spZ (ms_regs ms3)) FM_PSTAT_FP [] ly4 S4 W4 mem4 md4 EV_names HJ2 HJc ltac:(rewrite Hsp3; assert (STK_names = 16640) by reflexivity; lia)
  ltac:(rewrite Hsp3; lia) (fun a Ha => Ha)) as HJ4.
cbn [app] in HJ4. replace (0 + EV_names) with EV_names in HJ4 by reflexivity.
assert (Hinc4 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly4 S4)).
{ intros x Hx. apply (Permutation_in x (Permutation_sym Hperm4) Hx). }
pose proof HJc as (HAR4 & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (HRO4 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W4) mem4))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc pstat_closed pstat_not_roP HRO3).
assert (R'2 : getr regs4 2 = getr (ms_regs ms3) 2) by exact (fmw_pres _ _ 2%bv HP4 ltac:(cs_tac)).
rewrite Q1.
change (mkCfg (mkst regs4 (Z_to_bv 64 CRT_P2) mem4 (seg_rom tfibsegs)) md4) with (cfg_at tfibsegs CRT_P2 regs4 mem4 md4).
apply (K2 ly4 S4 W4 regs4 mem4 md4 EV_names).
unfold crt_P2, crt_core, crt_glob, crt_J, cx_n, cx_sp0. cbn [cx_ly cx_S cx_W cx_regs cx_mem cx_md cx_ch cx_u cx_ub cx_live cx_peak cx_cnt].
split; [split; [exact HJ4|] |].
2:{ split; [unfold EV_names; lia|].
    split; [exact H10r|].
    split.
    { rewrite (fmw_pres _ _ 19%bv HP4 ltac:(cs_tac)), Q19. exact H10'. }
    split; [exact Hperm4|].
    destruct ub as [|c ub']; cbn [length Z.of_nat Z.eqb] in HG4 |- *.
    - rewrite Z.add_0_r. exact HG4.
    - exact HG4. }
split.
{ apply (crt_frame_kept _ W W4 (ms_mem ms3) mem4); [|exact HFR3]. intros a Ha. unfold cx_sp0 in Ha. cbn [cx_regs] in Ha.
  apply F1c; [pose proof (proj1 alloc_ceiling_val); unfold CRT_FRAME in Ha; lia | rewrite Hsp3; unfold CRT_FRAME in Ha; lia]. }
split; [unfold spZ at 1; rewrite R'2, Q2, P2; unfold CRT_FRAME; lia|].
split; [rewrite (fmw_pres _ _ 3%bv HP4 ltac:(cs_tac)), Q3, P3, R3; reflexivity|].
split; [rewrite (fmw_pres _ _ 4%bv HP4 ltac:(cs_tac)), Q4, P4, R4; reflexivity|].
split; [rewrite (fmw_pres _ _ 8%bv HP4 ltac:(cs_tac)), Q8, P8, R8; exact H10|].
split; [rewrite (fmw_pres _ _ 26%bv HP4 ltac:(cs_tac)), Q26, P26, R26; reflexivity|].
split.
{ exact (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IMG HJc Hinc4 pstat_img HRO4 Hku Hu3). }
split; [exact (cstr_kept_kept B ly S ly4 S4 u ub Hinc4 Hku)|].
exact HRO4.
Qed.
End A.
