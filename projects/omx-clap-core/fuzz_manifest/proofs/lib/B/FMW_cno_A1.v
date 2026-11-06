(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_cno_A1.v at a working branch 31d1eb57a40.
   check_no_overread 0x80bd4, entry segment: the prologue (frame 112, ra s0..s11 saved; s1 := tn, s2 := tp, s4 := un,
   s6 := up, s8 := the shadow base, s5 := un + 18 + (un + 18 == 0) = un + 18), malloc (un + 18) at 0x80c38, back at
   0x80c3c (cno_P1). No overflow check lies in this range (B 0x80bd4 .. 0x80c38). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20 YC85.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YCbp YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YF0m YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_cno0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.                                   (* lib/B/FMW_seg.v:37: code addresses, GOT/cell values, statics not owned *)
Hypothesis HB : TfibSyms B.                              (* ReusableB/YF0m.v:658 *)
Hypothesis IMG : fm_img_facts tfibsegs B.                (* lib/B/FMH_Fn.v:61 *)
Hypothesis UNIV : fm_univ B.                             (* lib/B/FMH_Fn.v:71: incl Tfib_universe (as_universe B) *)
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv.   (* YC5d.v:57; ameter_triv YCbp.v:17, mo_ok = True *)
Hypothesis AFREE4 : afree04_rule tfibsegs B ameter_triv.       (* YC5d.v:76 *)
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy PC_memcpy.  (* YG0d.v:318 *)
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet PC_memset.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.   (* lib/B/FMH_Fn.v:241 *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).

(* a register the run left as a computed value v, U E v = z *)
Lemma cnoA1_reg_U : forall H E ss ms (r : bv 5) v z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> U E v = z -> getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r v z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. unfold w64. rewrite <- Hz.
unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* s5 = (a1 + 18) + (a1 + 18 == 0) with a1 = un (B 0x80c28 .. 0x80c30): un + 18, never 0 *)
Lemma cnoA1_U_s5 : forall E n, ew E 11 = Z_to_bv 64 n -> 0 <= n <= 255 ->
  U E (SAlu ALU_ADD (SOff 11 18) (SAlu ALU_SLTU (SOff 11 18) (SLit 1))) = n + 18.
Proof.
intros E n H Hn. rewrite !U_SAlu. rewrite (U_atom_off E 11 n 18 H) by lia. rewrite (U_lit E 1) by lia.
cbn [zalu_raw]. replace (n + 18 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.
(* fm's statics ride through any step that keeps their bytes *)
Lemma cnoA1_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FM_PSTAT_FP a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fm_glob tfibsegs W m live peak cnt fail -> fm_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail HK (G1 & G2 & G3 & G4 & R).
assert (VK : forall g v, In (g, g + 8) FM_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv. eapply (val_mem_kept tfibsegs); [|exact Hv]. intros k Hk. apply HK.
  apply (inFP_FM_PSTAT_FP g Hg). cbn in Hk. lia. }
unfold fm_glob, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G1]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G2]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G3]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G4]|].
exact R.
Qed.
(* a source window homed in a block live at the entry keeps its bytes over a journal that keeps the block (block bytes
   are not image bytes, so not fm's statics) *)
Lemma cnoA1_bytes_kept : forall STK sp0 k ly S (W : world tfibsegs) mem md ly2 S2 W2 mem2 md2 p l,
  ajournal tfibsegs B STK sp0 FM_PSTAT_FP ly S W mem md [] ly2 S2 W2 mem2 md2 k ->
  AR tfibsegs B ly S W mem md ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  cno_home B ly S p l -> bytes_at tfibsegs W mem p l -> bytes_at tfibsegs W2 mem2 p l.
Proof.
intros STK sp0 k ly S W mem md ly2 S2 W2 mem2 md2 p l HJ HAR Hinc Hh Hb.
destruct Hh as [-> | (b & m & Hin & Hlo & Hhi)]; [apply garr8_nil|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
unfold bytes_at in *. apply (garr8_frame tfibsegs _ _ p l Hb). intros a Ha.
apply mbyte_of_aview.
assert (Hi : 0 <= a - b < req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
replace a with (b + (a - b)) by lia.
apply (F2 b m (a - b)); [exact Hin | exact (Hinc _ Hin) | exact Hi |].
intros Hfp. apply (blk_img tfibsegs B LAWS ly S W mem md b m (b + (a - b)) HAR Hin ltac:(lia)).
exact (pstat_img _ Hfp).
Qed.

Lemma cno_seg_0 : forall cx, cno_base B cx ->
  (forall ly' S' W' regs' mem' md' u1, cno_P1 B cx ly' S' W' regs' mem' md' u1 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_P1 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs (nx_W cx) (cfg_at tfibsegs A_check_no_overread (nx_regs cx) (nx_mem cx) (nx_md cx)) (cno_post B cx).
Proof.
intros [ly S W regs mem md up tp ub tb live peak cnt] HBX K1.
pose proof HBX as (HPRE & Hra0 & H10 & H11 & H12 & H13 & Hsu & Hst & Hnzu & Hnzt & Hhu & Hht & Hlu & Htn & HG & HQ
  & Hlive & Hev & Hbb).
unfold nx_un, nx_tn in *.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt] in *.
destruct HPRE as [HAP HRO].
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (_ & _ & _ & _ & _ & Hs6 & _ & Hs8 & Hs9).
pose proof (fmw_sp B _ ly S W regs mem md [] HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_no_overread = 16752) by reflexivity.
assert (Hun : 0 <= Z.of_nat (length ub) <= 255) by lia.
pose proof (fmw_entry_sb B FB W ly S regs mem md STK_check_no_overread A_check_no_overread 112 HAR Hstk
  ltac:(lia) Hpres ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_check_no_overread FM_PSTAT_FP ly S W regs mem md [] HAP) as HJ.
set (E := Ereg regs [Z_to_bv 64 FMW_SB]) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (length ub)))
  by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
unfold cfg_at. change (w64 A_check_no_overread) with (Z_to_bv 64 A_check_no_overread).
unfold fmw_entry_ss in HS.
(* ---- the prologue, up to the malloc call at 0x80c38 ---- *)
aj_run_to fmw_tbl_cno_ok HS HJ 0x52e1c.
{ awr_ok_tac. exact Usp. }
pose proof (fmw_reg_lit _ E _ ms 1%bv CNO_P1 HS ltac:(vm_compute; reflexivity) ltac:(unfold CNO_P1; lia)) as R1.
pose proof (fmw_reg_off _ E _ ms 2%bv 2 (-112) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fmw_reg_atom _ regs _ _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs _ _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs _ _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fmw_reg_atom _ regs _ _ ms 9%bv 13%bv 13 HS ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fmw_reg_atom _ regs _ _ ms 18%bv 12%bv 12 HS ltac:(vm_compute; reflexivity) eq_refl) as R18.
pose proof (fmw_reg_atom _ regs _ _ ms 20%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R20.
pose proof (fmw_reg_atom _ regs _ _ ms 22%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R22.
pose proof (fmw_reg_extra _ regs _ _ ms 24%bv 0 HS ltac:(vm_compute; reflexivity)) as R24. cbn [nth] in R24.
assert (U5 : U E (SAlu ALU_ADD (SOff 11 18) (SAlu ALU_SLTU (SOff 11 18) (SLit 1))) = Z.of_nat (length ub) + 18)
  by exact (cnoA1_U_s5 E _ E11 Hun).
assert (U10 : U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 18) (SAlu ALU_SLTU (SOff 11 18) (SLit 1))) (SLit 0))
  = Z.of_nat (length ub) + 18).
{ rewrite U_SAlu, U5, (U_lit E 0) by lia. cbn [zalu_raw]. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
pose proof (cnoA1_reg_U _ _ _ ms 10%bv _ _ HS ltac:(vm_compute; reflexivity) U10) as R10.
pose proof (cnoA1_reg_U _ _ _ ms 21%bv _ _ HS ltac:(vm_compute; reflexivity) U5) as R21.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -112) by (unfold spZ at 1; rewrite R2; lia).
(* the saved registers in the frame (B 0x80bd8 .. 0x80c08: ra, s0 .. s11 at sp + 104 .. sp + 8) *)
pose proof (fmw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (HFR1 : cno_frame (mkNX ly S W regs mem md up tp ub tb live peak cnt) W (ms_mem ms)).
{ eapply (cno_frame_of_chunks (mkNX ly S W regs mem md up tp ub tb live peak cnt) W (ms_mem ms) _ _ _ _ _ _ HR0).
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
pose proof (fm_glob_below W mem (ms_mem ms) live peak cnt SIZE_MAXZ SB1 HG) as HG1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
(* the caller's frame chain (memory at and above sp0 is the entry's) *)
assert (CH : chain_pre ly (aview tfibsegs (w_H W) (ms_mem ms)) (ms_regs ms) []).
{ apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) [] (ms_regs ms)).
  - apply (achain_kept ly (aview tfibsegs (w_H W) mem) _ _ _ [] (spZ regs) Hch); [lia | lia |].
    intros a Ha. apply F1; lia.
  - rewrite Hsp1. lia.
  - unfold s0Z. rewrite R8. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by (unfold CNO_P1; lia). unfold CNO_P1. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 0x52e1c) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite (fb_code B FB); reflexivity).
clear HF HFr.
(* ---- malloc (un + 18) ---- *)
eapply SRr_bind.
{ apply (amalloc04_sub tfibsegs B LAWS HSL ameter_triv AMALLOC4 W (ms_regs ms) (ms_mem ms) STK_check_no_overread
    (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S _ 0 (Z.of_nat (length ub) + 18) (-112) (Z_to_bv 64 CNO_P1) []).
  - exact HJ.
  - exact R10.
  - unfold MALLOC_MAX. lia.
  - unfold LIVE_check_no_overread in Hbb. lia.
  - exact Hsp1.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_even. rewrite unsigned_lit_small by (unfold CNO_P1; lia). reflexivity.
  - unfold EV_check_no_overread, EV_names in Hev. lia.
  - exact CH.
  - apply UNIV. rewrite call_trace_nil, (fb_code B FB).
    assert (RA : raZ (ms_regs ms) = 0x80c3c) by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold CNO_P1; lia).
    rewrite RA. apply memZL_In. vm_compute. reflexivity.
  - exact I. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & H10r & _ & Hr4 & Hbl & HK & _ & HJs).
(* ---- back at 0x80c3c ---- *)
destruct HK as (KK1 & _ & KK3 & _).
assert (Hinc : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; rewrite Hbl; apply in_or_app; left; exact Hx).
assert (HFR2 : cno_frame (mkNX ly S W regs mem md up tp ub tb live peak cnt) W2 mem2).
{ apply (cno_frame_kept _ W W2 (ms_mem ms) mem2); [|exact HFR1]. intros a Ha.
  unfold nx_sp0, CNO_FRAME in Ha. cbn [nx_regs] in Ha. apply KK1; [lia | unfold ASTACK; lia]. }
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 pstat_closed pstat_not_roP HRO).
assert (HG2 : fm_glob tfibsegs W2 mem2 live peak cnt SIZE_MAXZ).
{ apply (cnoA1_glob_img W W2 (ms_mem ms) mem2); [|exact HG1].
  intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KK3 a (pstat_img a Ha) N1 N2). }
assert (Hbu : bytes_at tfibsegs W2 mem2 up ub)
  by exact (cnoA1_bytes_kept _ _ _ ly S W mem md ly2 S2 W2 mem2 md2 up ub HJ2 HAR Hinc Hhu (proj1 Hsu)).
assert (Hbt : bytes_at tfibsegs W2 mem2 tp tb)
  by exact (cnoA1_bytes_kept _ _ _ ly S W mem md ly2 S2 W2 mem2 md2 tp tb HJ2 HAR Hinc Hht (proj1 Hst)).
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (fmw_pres _ _ 3%bv HP2 ltac:(fmw_cs_side)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (fmw_pres _ _ 4%bv HP2 ltac:(fmw_cs_side)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)).
assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (fmw_pres _ _ 18%bv HP2 ltac:(fmw_cs_side)).
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (fmw_pres _ _ 20%bv HP2 ltac:(fmw_cs_side)).
assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (fmw_pres _ _ 21%bv HP2 ltac:(fmw_cs_side)).
assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (fmw_pres _ _ 22%bv HP2 ltac:(fmw_cs_side)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (fmw_pres _ _ 24%bv HP2 ltac:(fmw_cs_side)).
assert (Hsp2 : spZ regs2 = spZ regs - CNO_FRAME) by (unfold spZ at 1; rewrite P2, R2; unfold CNO_FRAME; lia).
assert (G3 : getr regs2 3 = getr regs 3) by (rewrite P3, R3; reflexivity).
assert (G4 : getr regs2 4 = getr regs 4) by (rewrite P4, R4; reflexivity).
assert (G24 : getr regs2 24 = w64 FMW_SB) by (rewrite P24, R24; reflexivity).
assert (G9 : getr regs2 9 = w64 (Z.of_nat (length tb))) by (rewrite P9, R9; exact H13).
assert (G18 : getr regs2 18 = w64 tp) by (rewrite P18, R18; exact H12).
assert (G20 : getr regs2 20 = w64 (Z.of_nat (length ub))) by (rewrite P20, R20; exact H11).
assert (G21 : getr regs2 21 = w64 (Z.of_nat (length ub) + 18)) by (rewrite P21; exact R21).
assert (G22 : getr regs2 22 = w64 up) by (rewrite P22, R22; exact H10).
change (mkCfg (mkst regs2 (Z_to_bv 64 CNO_P1) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs CNO_P1 regs2 mem2 md2).
apply (K1 ly2 S2 W2 regs2 mem2 md2 res).
unfold cno_P1, cno_cp, cno_core, cno_J, nx_sp0, nx_un, nx_tn.
cbn [nx_ly nx_S nx_W nx_regs nx_mem nx_md nx_up nx_tp nx_ub nx_tb nx_live nx_peak nx_cnt].
exact (conj (conj (conj HJ2 (conj HFR2 (conj Hsp2 (conj G3 (conj G4 (conj G24 HRO2))))))
  (conj Hbl (conj Hbu (conj Hbt HG2))))
  (conj Hr4 (conj H10r (conj G9 (conj G18 (conj G20 (conj G21 G22))))))).
Qed.
End S.
