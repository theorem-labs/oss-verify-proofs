(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pre_e.v (a working branch e2e59892bef),
   re-walked on B (0x81e94 .. 0x81f00 = A's same stretch shifted by 0x290, registers renamed). *)
(* lv2_locate_manifest_readings, PRE entry piece (0x81e94 .. RD_C2 and the exits uri_len = 0 / NULL; B-readings.lst
   lines 1-28): prologue (13 saves), s0 = rp, s2 = uri, s11 = the shadow base loaded through GOT 0x99c98, s6 = text;
   strlen (uri);
     uri_len = 0 -> RD_R0 0x82370 (s9 = 0) -> RD_R (names_res: no URI);
     whole = fuzz_malloc (uri_len + 3), called with s0 = rp = the entry sp, so its frame chain is one record (readings'
     saved ra / s0, rdp_chain_rp) and its trace [0x81f00; 0x81e88] is B's CTX_fuzz_malloc;
     NULL (the allocation set to fail) -> RD_R0 -> RD_R; else RD_C2 (FMW_rd_pre_c2.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_pre_k FMW_rd_pre_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the entry state: the frame below sp (writable), the GOT slot of __asan_shadow_memory_dynamic_address and the
   cell (atom 32 = the shadow base), fm-fn-measure.md 2 ---- *)
Definition RD_GOT : Z := 0x99c98.
Definition RD_CELL : Z := 0xa2078.
Definition rdp_ss0 : sstate :=
  mkSS A_readings sr_atoms
    [YP09.mkRegion (Some 2%nat) (-208) 0 (-208) 0 [];
     YP09.mkRegion None RD_GOT (RD_GOT + 8) 0 0 [YP09.mkChunk RD_GOT (CVal 8 (SLit RD_CELL))];
     YP09.mkRegion None RD_CELL (RD_CELL + 8) 0 0 [YP09.mkChunk RD_CELL (CVal 8 (SOff 32 0))]]
    None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 0x7fff8000 0x7fff8000 0)] [] []).


Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis CELLS : g3_cells B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis MALLOC : fuzz_malloc_spec tfibsegs B CTX_fuzz_malloc.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation rdJ cx := (ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
  (cx_W cx) (cx_mem cx) (cx_md cx) []).


(* the entry state *)
Lemma rdp_entry : forall cx, rd_base B CTX cx ->
  st_ok tfibsegs (Ereg (cx_regs cx) [Z_to_bv 64 SHADOW_OFF]) rdp_ss0
    (restrict (w_H (cx_W cx)) (mkst (cx_regs cx) (Z_to_bv 64 A_readings) (cx_mem cx) (seg_rom tfibsegs))).
Proof.
intros cx HB. destruct HB as (HAN & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct CELLS as [HBgot HBcell].
destruct (al_const _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg (cx_regs cx) [Z_to_bv 64 SHADOW_OFF]).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra _ _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ (cx_regs cx)) by (subst E; rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl); reflexivity).
assert (HSTK : STK_readings = 16624) by reflexivity.
unfold rdp_ss0. apply (entry_st_ok_full tfibsegs); change (Ereg (cx_regs cx) [Z_to_bv 64 SHADOW_OFF]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
  + cbn [base_val]. unfold RD_GOT. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l 0x99c98) at 1.
    apply (chunk_ok_val tfibsegs E _ 0 0x99c98 8 (SLit RD_CELL) RD_CELL); [reflexivity | unfold RD_CELL; zside | zside |].
    exact (val_mem_of_rdword tfibsegs (w_H (cx_W cx)) (cx_mem cx) _ _ Kgot).
  + cbn [base_val]. unfold RD_CELL. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa2078) at 1.
    apply (chunk_ok_val tfibsegs E _ 0 0xa2078 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword tfibsegs (w_H (cx_W cx)) (cx_mem cx) _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp. unfold RD_GOT, RD_CELL.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil Hstk0 C1. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hstk0 C1 Hal16. clear. unfold SHADOW_OFF. intros. repeat split; lia.
Qed.

(* ======== the entry segment ======== *)
Theorem rdp_E_holds : rdp_seg_C2 B CTX -> rd_seg_E B CTX.
Proof.
intros HC2 cx HB.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof HB as (HAN & HCX & HRO & H10 & H11 & H12 & Hpr16 & Htop16 & Hv & Hv63 & Ct & Cu & Kt & Ku & Hub255 & Htb & HG0 &
  Hlv & Hcnt & Hev & Hlb & HraN & HchN).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Cu as (_ & Hu4 & Hucl & _). pose proof Ct as (_ & Ht4 & Htcl & _).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (Esp : cx_sp cx = spZ (cx_regs cx)) by reflexivity. assert (EF : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (Hulen : cx_ulen cx = Z.of_nat (length (cx_ub cx))) by reflexivity.
pose proof (rdp_jinit B CTX cx HB) as HJ.
pose proof (rdp_entry cx HB) as HS.
set (E0 := Ereg (cx_regs cx) [Z_to_bv 64 SHADOW_OFF]) in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr (cx_regs cx) r)
  by (intros n r Hn; subst E0; apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = cx_sp cx + 16 + -16) by (rewrite (EE 2%nat 2%bv eq_refl); unfold cx_sp, spZ; lia).
unfold cfg_at. change (w64 A_readings) with (Z_to_bv 64 A_readings).
change (cx_mem cx) with (ms_mem (mkst (cx_regs cx) (Z_to_bv 64 A_readings) (cx_mem cx) (seg_rom tfibsegs))) in HJ at 2.
(* ---- the prologue to strlen (uri) ---- *)
aj_run rd_tbl_ok HS HJ.
{ rdp_awr (-16) Usp. }
rdp_name HS ms1.
set (m1 := ms_mem ms1) in *.
assert (KE0 : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_sp cx - 208 <= a < cx_sp cx) ->
  aview tfibsegs (w_H (cx_W cx)) m1 a = aview tfibsegs (w_H (cx_W cx)) (cx_mem cx) a).
{ intros a Ha Hn. apply (g3_aview_frame E0 _ (w_H (cx_W cx)) (cx_mem cx) m1 HFr a Ha).
  intros (r & Hin & Hr). cbv [rdp_ss0 ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite Usp in Hr | |]; lia. }
assert (LK1 : g3_low_kept (cx_W cx) (cx_W cx) (cx_mem cx) m1) by (intros a Ha; apply KE0; lia).
assert (HPRO : rdp_pro cx m1).
{ split; [|intros a Ha; apply KE0; lia].
  assert (Hb : bv_unsigned (ew E0 2) = cx_sp cx) by lia.
  unfold rd_saved_ok, RD_SAVED. cbn [fst snd].
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth_error (ss_mem ssx) 0) in
    lazymatch r with Some (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      lazymatch goal with |- val_mem _ _ (cx_F cx + ?o) _ _ =>
        replace (cx_F cx + o) with (cx_sp cx + (o - 208)) by (unfold cx_F; lia) end;
      (eapply (rdp_slot Ex ssx (cx_W cx) msx lo hi wlo whi cs);
        [exact HS | reflexivity | vm_compute; reflexivity | exact Hb | | apply u64_range])
    end end.
  all: rewrite rdp_SOff0, Z_to_bv_bv_unsigned; subst E0; apply ew_Ereg_nat; vm_compute; reflexivity. }
clear HF HFr HG.
rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10.
assert (HR1 : rdp_regs cx (ms_regs ms1)).
{ rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (27%bv : bv 5) Q27.
  rreg HS (8%bv : bv 5) Q8. rreg HS (18%bv : bv 5) Q18. rreg HS (22%bv : bv 5) Q22.
  unfold rdp_regs. rewrite Q2, Q3, Q4, Q27, Q8, Q18, Q22.
  rewrite (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 12%nat 12%bv eq_refl), (EE 11%nat 11%bv eq_refl),
    (EE 10%nat 10%bv eq_refl), H12, H11, H10.
  assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF) by (subst E0; exact (ew_Ereg_extra _ _ 0)).
  rewrite E32. split; [|repeat split; reflexivity].
  unfold w64, cx_F. f_equal; rewrite ?Usp; lia. }
pose proof HR1 as (S2 & S3 & S4 & S27 & S8 & S18 & S22).
rewrite (EE 11%nat 11%bv eq_refl), H11 in Q10.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
assert (Hsp1 : spZ (ms_regs ms1) = cx_sp cx + 16 + -224) by (unfold spZ; rewrite S2; unfold w64, cx_F; rewrite unsigned_lit_small by lia; lia).
assert (HRO1 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H (cx_W cx)) m1)) by exact (g3_arodata_kept B _ _ _ _ HRO LK1).
eapply SRr_bind.
{ apply (g3_aj_ro_at B LAWS PC_strlen STK_RT_STR (fun v => v = Z.of_nat (length (cx_ub cx))) (cx_W cx) (ms_regs ms1) m1
    (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) [] (cx_ly cx)
    (cx_S cx) _ 0 (-224) (Z_to_bv 64 532204) HJ Hsp1 eq_refl ltac:(lia) ltac:(unfold STK_RT_STR, ESTACK; lia)
    ltac:(unfold STK_RT_STR, ESTACK; lia) ltac:(rewrite S3; exact Hgp) ltac:(rewrite S4; exact Htp) Q1
    ltac:(vm_compute; reflexivity)).
  intros HPK. apply (STRLEN (cx_ly cx) (cx_S cx) (cx_W cx) (ms_regs ms1) m1 _ (cx_u cx) (cx_ub cx) HPK).
  - exact (proj1 (IMG _ _ _ _ _ (proj1 HJ) HRO1)).
  - exact Q10.
  - exact (g3_cstr_ok_kept _ _ _ _ _ _ Cu LK1). }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10v & Hv64 & Hvl & Hfr2 & Hpres2).
assert (KE2 : rdp_ke cx m1 (cx_W cx) mem2) by (intros a Ha; rewrite Hfr2 by lia; reflexivity).
assert (HSTR : STK_RT_STR = 8192) by reflexivity.
assert (LK2 : g3_low_kept (cx_W cx) (cx_W cx) (cx_mem cx) mem2) by (intros a Ha; rewrite Hfr2 by lia; apply LK1; exact Ha).
pose proof (rdp_regs_pres cx _ _ HP2 HR1) as HR2.
(* ---- 0x81eec: beqz a0 (uri_len = 0) ---- *)
change (Z_to_bv 64 532204) with (Z_to_bv 64 RD_C1).
clear HS. pose proof (rdp_ssn_ok (cx_W cx) regs2 [] mem2 RD_C1) as HS.
assert (E10 : ew (Ereg regs2 []) 10 = Z_to_bv 64 v) by (rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl); exact H10v).
srr_branch_with rd_tbl_ok HS.
- (* uri_len = 0: s9 = 0 (RD_R0), return 0 *)
  rewrite branch_eq_U, (U_atom _ 10 v E10 Hv64), U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
  assert (Hub0 : cx_ub cx = []) by (destruct (cx_ub cx); [reflexivity | cbn in Hvl; lia]).
  srr_run_to_with rd_tbl_ok HS RD_R.
  rdp_name HS ms3.
  assert (Hm3 : ms_mem ms3 = mem2) by (lazymatch type of HF with frame_of _ ?rs _ _ =>
    exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) end).
  clear HF HFr.
  pose proof (rdp_regs4_run cx _ regs2 _ ms3 HS ltac:(vm_compute; reflexivity) HR2) as (Q2 & Q3 & Q4 & Q27).
  rreg HS (25%bv : bv 5) Q25.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. rewrite Hm3. rdp_cfg RD_R.
  apply (rd_ret_holds B CTX cx 0 (cx_ly cx) (cx_S cx) (cx_W cx) (ms_regs ms3) mem2 _ 0 HB).
  + apply (rdp_com_of B CTX IMG cx 0 (cx_ly cx) (cx_S cx) (cx_W cx) (ms_regs ms3) mem2 _ m1 HB); [| cbv [EV_names]; lia | exact Q2 | exact Q3
      | exact Q4 | exact Q27 | exact HPRO | exact KE2 | intros x Hx; exact Hx].
    exact (ajournal_materialize tfibsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2).
  + rewrite Q25. reflexivity.
  + lia.
  + split; [apply Permutation_refl|]. split.
    * left. split; [exact Hub0|]. split; [reflexivity|]. exact (g3_fm_glob_kept _ _ _ _ _ _ _ _ HG0 LK2).
    * rewrite Hub0. cbn [length Nat.eqb orb]. exact (rdp_rp B CTX cx m1 (cx_W cx) mem2 HB HPRO KE2).
- (* uri_len <> 0: s1 = uri_len, s5 = uri_len + 3; fuzz_malloc (uri_len + 3) *)
  rewrite branch_eq_U, (U_atom _ 10 v E10 Hv64), U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
  assert (Hub : cx_ub cx <> []) by (intros E; rewrite E in Hvl; cbn in Hvl; lia).
  assert (Hub1 : (1 <= length (cx_ub cx))%nat) by (destruct (cx_ub cx); [contradiction | cbn; lia]).
  srr_run_with rd_tbl_ok HS.
  rdp_name HS msC.
  assert (HmC : ms_mem msC = mem2) by (lazymatch type of HF with frame_of _ ?rs _ _ =>
    exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) end).
  clear HF HFr.
  pose proof (rdp_regs_run cx _ regs2 _ msC HS ltac:(vm_compute; reflexivity) HR2) as HRC.
  pose proof HRC as (C2' & C3' & C4' & C27' & C8' & _).
  rreg HS (1%bv : bv 5) P1. rreg HS (10%bv : bv 5) P10. rreg HS (21%bv : bv 5) P21. rreg HS (9%bv : bv 5) P9.
  rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl), H10v in P10, P21, P9.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. rewrite HmC. rdp_cfg A_fuzz_malloc.
  lazymatch goal with |- context [with_vm_backing _ ?mm _] =>
    assert (HJ2s := ajournal_materialize tfibsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm HJ2) end.
  assert (Hsp2 : spZ (ms_regs msC) = cx_sp cx + 16 + -224) by (unfold spZ; rewrite C2'; unfold w64, cx_F; rewrite unsigned_lit_small by lia; lia).
  assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H (cx_W cx)) mem2)) by exact (g3_arodata_kept B _ _ _ _ HRO LK2).
  set (n := cx_ulen cx + 3) in *.
  assert (Pn : getr (ms_regs msC) 10 = w64 n).
  { rewrite P10. unfold w64. rewrite unsigned_lit_small by lia. unfold n. rewrite Hvl, Hulen. reflexivity. }
  eapply SRr_bind.
  { apply (MALLOC (cx_ly cx) (cx_S cx) (cx_W cx) (ms_regs msC) mem2 _ [(cx_sp cx, RD_NAMES_RA, bv_unsigned (getr (cx_regs cx) 8))]
      n (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx)).
    - split; [|exact HRO2].
      apply (afn_pre_at tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
        (cx_mem cx) (cx_md cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) mem2 _ 0 (ms_regs msC) STK_fuzz_malloc (-224)
        [(cx_sp cx, RD_NAMES_RA, bv_unsigned (getr (cx_regs cx) 8))] HJ2s).
      + exact Hsp2.
      + reflexivity.
      + lia.
      + unfold STK_fuzz_malloc, ASTACK, STK_RT_POISON. lia.
      + unfold STK_fuzz_malloc, ASTACK, STK_RT_POISON. lia.
      + rewrite P1. vm_compute. reflexivity.
      + unfold raZ. rewrite P1, unsigned_lit_small by lia. lia.
      + rewrite C3'. exact Hgp.
      + rewrite C4'. exact Htp.
      + apply (rdp_chain_rp B CTX cx m1 (cx_ly cx) (cx_S cx) (cx_W cx) mem2 _ 0 (ms_regs msC) HB HJ2s HPRO KE2).
        * rewrite Hsp2. unfold cx_F. lia.
        * unfold s0Z. rewrite C8'. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - unfold raZ. rewrite P1, unsigned_lit_small by lia. cbn [spine map fst snd]. left. reflexivity.
    - exact Pn.
    - unfold n, cx_ulen. lia.
    - unfold n, cx_ulen, HEAD, MALLOC_MAX. lia.
    - exact (g3_fm_glob_kept _ _ _ _ _ _ _ _ HG0 LK2).
    - unfold n. lia.
    - exact Hcnt.
    - unfold EV_names in Hev. lia.
    - unfold n, cx_ulen, HEAD, LIVE_names in *. lia. }
  intros W3 c3 _ [(Hcf & HFP) | (Hcf & res & HFU)].
  + (* the allocation set to fail: NULL, return 0 *)
    destruct HFP as (ly3 & Sz3 & regs3 & mem3 & md3 & -> & HJc & HP3 & (H10f & Hbl3 & HG3)).
    pose proof (g3_ajsub_img_ok B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
      (cx_md cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) mem2 _ 0 STK_fuzz_malloc (spZ (ms_regs msC)) FM_PSTAT_FP []
      ly3 Sz3 W3 mem3 md3 0 HJ2s HJc) as HJ3.
    specialize (HJ3 ltac:(rewrite Hsp2; unfold STK_fuzz_malloc, ASTACK, STK_RT_POISON; lia) ltac:(lia)
      ltac:(intros a Ha; right; right; split; [exact Ha | exact (g3_pstat_img a Ha)])).
    cbn [app] in HJ3.
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & Fc1 & _).
    assert (KE3 : rdp_ke cx m1 W3 mem3).
    { intros a Ha. rewrite (Fc1 a ltac:(lia) ltac:(rewrite Hsp2; unfold STK_fuzz_malloc, ASTACK, STK_RT_POISON; lia)).
      exact (KE2 a Ha). }
    pose proof (rdp_regs_pres cx _ _ HP3 HRC) as HR3.
    rewrite P1. change (Z_to_bv 64 532224) with (Z_to_bv 64 RD_C2).
    clear HS. pose proof (rdp_ssn_ok W3 regs3 [] mem3 RD_C2) as HS.
    assert (E10f : ew (Ereg regs3 []) 10 = Z_to_bv 64 0) by (rewrite (ew_Ereg_nat regs3 [] 10 10%bv eq_refl); exact H10f).
    srr_branch_with rd_tbl_ok HS.
    * srr_run_to_with rd_tbl_ok HS RD_R.
      rdp_name HS ms4.
      assert (Hm4 : ms_mem ms4 = mem3) by (lazymatch type of HF with frame_of _ ?rs _ _ =>
    exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) end).
      clear HF HFr.
      pose proof (rdp_regs4_run cx _ regs3 _ ms4 HS ltac:(vm_compute; reflexivity) HR3) as (Q2 & Q3 & Q4 & Q27).
      rreg HS (25%bv : bv 5) Q25.
      rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. rewrite Hm4. rdp_cfg RD_R.
      apply (rd_ret_holds B CTX cx 0 ly3 Sz3 W3 (ms_regs ms4) mem3 _ 0 HB).
      -- apply (rdp_com_of B CTX IMG cx 0 ly3 Sz3 W3 (ms_regs ms4) mem3 _ m1 HB); [| cbv [EV_names]; lia | exact Q2 | exact Q3
           | exact Q4 | exact Q27 | exact HPRO | exact KE3 | intros x Hx; rewrite Hbl3; exact Hx].
         exact (ajournal_materialize tfibsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3).
      -- rewrite Q25. reflexivity.
      -- lia.
      -- split; [rewrite Hbl3; apply Permutation_refl|]. split.
         ++ right. left. split; [exact Hub|]. split; [exact Hcf|]. split; [reflexivity | exact HG3].
         ++ rewrite (proj2 (Z.eqb_eq _ _) Hcf), Bool.orb_true_r. exact (rdp_rp B CTX cx m1 W3 mem3 HB HPRO KE3).
    * (* Hc is RD_C1's v <> 0, so srr_branch_with named this branch's hypothesis Hc0 *)
      rewrite branch_eq_U, (U_atom _ 10 0 E10f ltac:(lia)), U_SLit in Hc0. change (zcanon 0) with 0 in Hc0.
      rewrite Z.eqb_refl in Hc0. discriminate Hc0.
  + (* whole = fuzz_malloc's block, its head poisoned *)
    destruct HFU as (lyM & SM & regsM & memM & mdM & -> & HJc & HokM & HpoM & HPM & (H10M & HresM & EabM & HrbM & HRAM &
      HhvM & HGM)).
    rename W3 into WM.
    pose proof (g3_ajsub_img_ok B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
      (cx_md cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (unpoison [] mem2) _ 0 STK_fuzz_malloc (spZ (ms_regs msC)) FM_PSTAT_FP []
      lyM SM WM (unpoison [(res - HEAD, HEAD)] memM) mdM 1 HJ2s HJc) as HJ3.
    specialize (HJ3 ltac:(rewrite Hsp2; unfold STK_fuzz_malloc, ASTACK, STK_RT_POISON; lia) ltac:(lia)
      ltac:(intros a Ha; right; right; split; [exact Ha | exact (g3_pstat_img a Ha)])).
    cbn [app] in HJ3. rewrite Z.add_0_l in HJ3.
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & Fc1 & _).
    unfold HEAD in *.
    assert (HM16 : 0 <= res - 16 /\ res - 16 + 16 <= kHighMemEnd).
    { pose proof (proj1 HJ3) as HARM.
      assert (Hb : In (res - 16, n + 16) (ablocks B lyM SM)) by (rewrite EabM; apply in_or_app; right; left; reflexivity).
      pose proof (rdp_blk_slack B _ _ _ _ _ _ _ HARM Hb ltac:(unfold n, cx_ulen in *; lia)) as [_ Hs]. lia. }
    assert (KEM : rdp_ke cx m1 WM memM).
    { intros a Ha. rewrite <- (rdp_aview_unp_hi (w_H WM) [(res - 16, 16)] memM a
        ltac:(right; exists (res - 16); split; [reflexivity | lia]) ltac:(lia)).
      rewrite (Fc1 a ltac:(lia) ltac:(rewrite Hsp2; unfold STK_fuzz_malloc, ASTACK, STK_RT_POISON; lia)).
      exact (KE2 a Ha). }
    rewrite P1. change (Z_to_bv 64 532224) with (Z_to_bv 64 RD_C2).
    apply (HC2 cx m1 lyM SM WM regsM memM mdM res HB HJ3).
    * exact (rdp_regs_pres cx _ _ HPM HRC).
    * rewrite (rdp_pres _ _ 9%bv HPM ltac:(rdp_cs)), P9.
      unfold w64. rewrite ?unsigned_lit_small by lia. rewrite Hvl, Hulen. reflexivity.
    * rewrite (rdp_pres _ _ 21%bv HPM ltac:(rdp_cs)), P21.
      unfold w64. rewrite ?unsigned_lit_small by lia. rewrite Hvl, Hulen. reflexivity.
    * exact H10M.
    * exact HPRO.
    * exact KEM.
    * exact HokM.
    * exact HpoM.
    * exact HresM.
    * exact EabM.
    * exact HrbM.
    * exact HRAM.
    * exact (HhvM ltac:(unfold n, cx_ulen in *; lia)).
    * exact HGM.
    * exact Hcf.
    * exact Hub.
Qed.
End c.
