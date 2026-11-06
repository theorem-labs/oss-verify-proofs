(* check_no_overread 0x80b20, segments N2 -> F1 -> F2 -> F3: at N2 (0x80d08) `bne s1, a0, abort` is dead (both hold
   ManifestModel.names tb ub), then free (u1) back at F1 (0x80d14); free (t1) back at F2 (0x80d1c); free (u2) back at
   F3 (0x80d24). Each free goes through cnoE1_free (afree04_sub over the walk's journal). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l AF0m ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_cno0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.                                   (* FMW_seg.v:32: code addresses, GOT/cell values, statics not owned *)
Hypothesis HB : TfibSyms B.                              (* AF0m.v:564 *)
Hypothesis IMG : fm_img_facts tfibsegs B.                (* FMH_Fn.v:56 *)
Hypothesis UNIV : fm_univ B.                             (* FMH_Fn.v:70: incl Tfib_universe (as_universe B) *)
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv.   (* YC5d.v:57; ameter_triv YCbp.v:17, mo_ok = True *)
Hypothesis AFREE4 : afree04_rule tfibsegs B ameter_triv.       (* YC5d.v:76 *)
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy PC_memcpy.  (* YG0d.v:318 *)
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet PC_memset.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.   (* FMH_Fn.v:234 *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).

(* fm's statics ride through any step that keeps their bytes *)
Lemma cnoE1_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
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

(* a block the walk made is not one of the entry's: AR separates the blocks of a state, so no block is listed twice *)
Lemma cnoE1_not_entry : forall ly S (W : world tfibsegs) mem md (entry left : list (Z * Z)) x,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (entry ++ x :: left) -> ~ In x entry.
Proof.
intros ly S W mem md entry left x HAR HP Hin. apply in_split in Hin as (e1 & e2 & ->).
assert (HP2 : Permutation (ablocks B ly S) (x :: x :: e1 ++ e2 ++ left)).
{ eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym.
  apply Permutation_cons_app. rewrite (app_assoc e1 e2 (x :: left)), (app_assoc e1 e2 left).
  apply Permutation_cons_app. reflexivity. }
pose proof (sep_blocks_perm tfibsegs B LAWS ly S W mem md x x _ HAR HP2) as Hd.
assert (Hx : In x (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP2)); left; reflexivity).
destruct x as [p n].
pose proof (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hx) as (_ & _ & _ & _ & _ & _ & Hn & _).
unfold zdisjoint, block_rng, req_size in Hd. cbn [fst snd] in Hd.
revert Hd. destruct (Z.eqb_spec n 0); cbv beta iota; intros Hd; lia.
Qed.

(* free (pa) at 0x52db8 with ra = the next resume point: the post holds if it holds from every state the free can
   return in (one event more, the block gone, the statics and the frame kept, the callee-saved registers kept) *)
Lemma cnoE1_free : forall cx ly S W regs mem md k pa n left (ra : Z) Q,
  cno_base B cx ->
  cno_core B cx ly S W regs mem md k ->
  Permutation (ablocks B ly S) (ablocks B (nx_ly cx) (nx_S cx) ++ (pa, n) :: left) ->
  cno_glob cx W mem 2 ->
  getr regs 10 = w64 pa -> getr regs 1 = Z_to_bv 64 ra -> 4096 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  s0Z regs < alloc_ceiling -> 0 <= k < EV_check_no_overread ->
  memZL (pc_free_ra0 Tfib_code :: (if ra =? pc_free_ra0 Tfib_code then [] else [ra])) Tfib_universe = true ->
  (forall ly2 S2 W2 regs2 mem2 md2,
     cno_core B cx ly2 S2 W2 regs2 mem2 md2 (k + 1) ->
     Permutation (ablocks B ly2 S2) (ablocks B (nx_ly cx) (nx_S cx) ++ left) ->
     cno_glob cx W2 mem2 2 -> aregs_preserved regs regs2 ->
     SRr tfibsegs W2 (cfg_at tfibsegs ra regs2 mem2 md2) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 PC_free) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros cx ly S W regs mem md k pa n left ra Q HBX HC HP HG H10 H1 Hra Hra2 Hs0 Hk HU K.
pose proof HBX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal & _ & HSlo & HSlo2 & HShi & HShi47 & _).
pose proof HC as (HJ & HFR & Hsp & G3 & G4 & G24 & HROc & G26 & G27).
unfold cno_J, nx_sp0, CNO_FRAME in *.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof fm_segs_low as HSL.
assert (FS : STK_check_no_overread = 16736) by reflexivity.
assert (FA : ASTACK = 16384) by reflexivity.
assert (Hin : In (pa, n) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
assert (CH : chain_pre ly (aview tfibsegs (w_H W) mem) regs []).
{ apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) [] regs).
  - apply achain_low. exact Hs0.
  - rewrite Hsp. lia.
  - reflexivity.
  - unfold raZ. rewrite H1, unsigned_lit_small by lia. lia. }
replace (Z_to_bv 64 PC_free) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite (fb_code B FB); reflexivity).
eapply SRr_bind.
{ apply (afree04_sub tfibsegs B LAWS HSL ameter_triv AFREE4 W regs mem STK_check_no_overread
    (spZ (nx_regs cx)) FM_PSTAT_FP (nx_ly cx) (nx_S cx) (nx_W cx) (nx_mem cx) (nx_md cx) [] ly S md k pa n (-96)
    (Z_to_bv 64 ra) []).
  - exact HJ.
  - exact Hin.
  - exact H10.
  - rewrite Hsp. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - exact H1.
  - apply ret_ok_even. rewrite unsigned_lit_small by lia. exact Hra2.
  - unfold EV_check_no_overread, EV_names in *. lia.
  - exact CH.
  - apply UNIV. rewrite call_trace_nil, (fb_code B FB).
    replace (raZ regs) with ra by (unfold raZ; rewrite H1; symmetry; apply unsigned_lit_small; lia).
    apply memZL_In. exact HU.
  - intros Hin0. exfalso. exact (cnoE1_not_entry ly S W mem md _ left (pa, n) HAR HP Hin0).
  - exact I. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl1 & Ebl2) & _ & HK & _ & _).
destruct HK as (KK1 & _ & KK3 & _).
change (mkCfg (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs ra regs2 mem2 md2).
apply (K ly2 S2 W2 regs2 mem2 md2); [| | |exact HP2].
- unfold cno_core, cno_J, nx_sp0, CNO_FRAME.
  split; [exact HJ2|].
  split.
  { apply (cno_frame_kept _ W W2 mem mem2); [|exact HFR]. intros a Ha.
    unfold nx_sp0, CNO_FRAME in Ha. apply KK1; lia. }
  split; [unfold spZ at 1; rewrite (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)); exact Hsp|].
  split; [rewrite (fmw_pres _ _ 3%bv HP2 ltac:(fmw_cs_side)); exact G3|].
  split; [rewrite (fmw_pres _ _ 4%bv HP2 ltac:(fmw_cs_side)); exact G4|].
  split; [rewrite (fmw_pres _ _ 24%bv HP2 ltac:(fmw_cs_side)); exact G24|].
  split; [exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 pstat_closed pstat_not_roP HRO)|].
  split; [rewrite (fmw_pres _ _ 26%bv HP2 ltac:(fmw_cs_side)); exact G26|].
  rewrite (fmw_pres _ _ 27%bv HP2 ltac:(fmw_cs_side)); exact G27.
- rewrite Ebl2. apply (Permutation_app_inv l1 l2 _ left (pa, n)). rewrite <- Ebl1. exact HP.
- unfold cno_glob in *. apply (cnoE1_glob_img W W2 mem mem2); [|exact HG].
  intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KK3 a (pstat_img a Ha) N1 N2).
Qed.

(* a stretch that writes no memory (fss_nr) keeps cno_core if it keeps sp, gp, tp, s8, s10 and s11 *)
Lemma cnoE1_core_step : forall cx ly S W regs mem md k regs' mem' md',
  cno_base B cx -> cno_core B cx ly S W regs mem md k ->
  cno_J B cx ly S W mem' md' k -> same_below mem mem' (2 ^ 64) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 24 = getr regs 24 -> getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
  cno_core B cx ly S W regs' mem' md' k.
Proof.
intros cx ly S W regs mem md k regs' mem' md' HBX HC HJ SB R2 R3 R4 R24 R26 R27.
pose proof HBX as (HPRE & _). destruct HPRE as [HAP _].
pose proof HAP as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & HSlo & HSlo2 & HShi & HShi47 & _).
assert (FS : STK_check_no_overread = 16736) by reflexivity.
pose proof (proj1 alloc_ceiling_val) as AC.
pose proof HC as (_ & HFR & Hsp & G3 & G4 & G24 & HROc & G26 & G27).
split; [exact HJ|].
split; [apply (cno_frame_below cx W mem mem' SB); [unfold nx_sp0, CNO_FRAME; lia | unfold nx_sp0; lia | exact HFR]|].
split; [unfold spZ at 1; rewrite R2; exact Hsp|].
split; [rewrite R3; exact G3|].
split; [rewrite R4; exact G4|].
split; [rewrite R24; exact G24|].
split; [exact (arodata_below B W mem mem' (same_below_mono _ _ _ alloc_ceiling SB ltac:(pose proof alloc_ceiling_lt; lia)) HROc)|].
split; [rewrite R26; exact G26 | rewrite R27; exact G27].
Qed.
(* a block's address is below alloc_ceiling *)
Lemma cnoE1_blk_low : forall ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 4096 <= p < alloc_ceiling.
Proof.
intros ly S W mem md p n HAR Hin.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn & _).
unfold req_size in Hc. revert Hc. destruct (Z.eqb_spec n 0); cbv beta iota; intros Hc; lia.
Qed.

Lemma cno_seg_N2 : forall cx ly S W regs mem md u1 t1 u2 t2,
  cno_base B cx -> cno_N2 B cx ly S W regs mem md u1 t1 u2 t2 ->
  (forall ly' S' W' regs' mem' md', cno_F1 B cx ly' S' W' regs' mem' md' t1 u2 t2 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_F1 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_N2 regs mem md) (cno_post B cx).
Proof.
intros cx ly S W regs mem md u1 t1 u2 t2 HBX HN K.
destruct HN as ((HC & HP & Hu1 & Ht1 & Hu2 & Ht2 & G20 & G23 & G19 & G8) & G10 & G9 & HGl).
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof HC as (HJ & HFR & Hsp & G3 & G4 & G24 & HROc & G26 & G27).
unfold cno_J in HJ.
pose proof HBX as (HPRE & _).
pose proof (fmw_resume_nr W regs [] mem CNO_N2) as HS.
set (E := Ereg regs []) in HS.
unfold cfg_at. change (w64 CNO_N2) with (Z_to_bv 64 CNO_N2).
assert (Hn : 0 <= ManifestModel.names (nx_tb cx) (nx_ub cx) < 2 ^ 64)
  by (destruct (names_01 (nx_tb cx) (nx_ub cx)) as [-> | ->]; lia).
assert (E9 : ew E 9 = Z_to_bv 64 (ManifestModel.names (nx_tb cx) (nx_ub cx)))
  by (subst E; rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); exact G9).
assert (E10 : ew E 10 = Z_to_bv 64 (ManifestModel.names (nx_tb cx) (nx_ub cx)))
  by (subst E; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact G10).
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 9 0) (b := SOff 10 0); [exact HS | |].
- intros Hb _. exfalso. rewrite branch_ne_U in Hb.
  rewrite (U_atom _ 9 _ E9 Hn), (U_atom _ 10 _ E10 Hn), Z.eqb_refl in Hb. discriminate Hb.
- intros _ HS1. clear HS.
  aj_run_to fmw_tbl_cno_ok HS1 HJ 0x52db8.
  { awr_ok_tac. }
  pose proof (frame_nil_same E mem (ms_mem ms) HF) as SB.
  pose proof (fmw_reg_lit _ E _ ms 1%bv CNO_F1 HS1 ltac:(vm_compute; reflexivity) ltac:(unfold CNO_F1; lia)) as R1.
  pose proof (fmw_reg_atom _ regs [] _ ms 10%bv 8%bv 8 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R10.
  pose proof (fmw_reg_atom _ regs [] _ ms 2%bv 2%bv 2 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R2.
  pose proof (fmw_reg_atom _ regs [] _ ms 3%bv 3%bv 3 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R3.
  pose proof (fmw_reg_atom _ regs [] _ ms 4%bv 4%bv 4 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R4.
  pose proof (fmw_reg_atom _ regs [] _ ms 8%bv 8%bv 8 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R8.
  pose proof (fmw_reg_atom _ regs [] _ ms 19%bv 19%bv 19 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R19.
  pose proof (fmw_reg_atom _ regs [] _ ms 20%bv 20%bv 20 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R20.
  pose proof (fmw_reg_atom _ regs [] _ ms 23%bv 23%bv 23 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R23.
  pose proof (fmw_reg_atom _ regs [] _ ms 24%bv 24%bv 24 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R24.
  pose proof (fmw_reg_atom _ regs [] _ ms 26%bv 26%bv 26 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R26.
  pose proof (fmw_reg_atom _ regs [] _ ms 27%bv 27%bv 27 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R27.
  pose proof HJ as (HAR & _).
  assert (Hin1 : In (u1, nx_un cx + 18) (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; left; reflexivity).
  pose proof (cnoE1_blk_low ly S W _ _ _ _ HAR Hin1) as Hu1c.
  pose proof alloc_ceiling_lt as ACl.
  assert (Hs0 : s0Z (ms_regs ms) < alloc_ceiling).
  { unfold s0Z. rewrite R8, G8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  pose proof (cnoE1_core_step cx ly S W regs mem md _ (ms_regs ms) (ms_mem ms) _ HBX HC HJ SB R2 R3 R4 R24 R26 R27) as HC1.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS1 eq_refl). cbn [ss_pc].
  apply (cnoE1_free cx ly S W (ms_regs ms) (ms_mem ms) _ (4 + 2 * EV_names) u1 (nx_un cx + 18)
    [(t1, nx_tn cx + 18); (u2, nx_un cx + 18); (t2, nx_tn cx + 18)] CNO_F1 (cno_post B cx) HBX HC1 HP).
  + unfold cno_glob in *. exact (fm_glob_below W mem (ms_mem ms) _ _ _ _ (same_below_mono _ _ _ alloc_ceiling SB ltac:(lia)) HGl).
  + rewrite R10. exact G8.
  + exact R1.
  + unfold CNO_F1. lia.
  + reflexivity.
  + exact Hs0.
  + unfold EV_check_no_overread, EV_names. lia.
  + vm_compute. reflexivity.
  + intros ly2 S2 W2 regs2 mem2 md2 HC2 HP2 HG2 HPr.
    apply (K ly2 S2 W2 regs2 mem2 md2).
    unfold cno_F1, cno_fr.
    replace (5 + 2 * EV_names) with (4 + 2 * EV_names + 1) by reflexivity.
    split; [split; [exact HC2 | split; [exact HP2 | exact HG2]]|].
    split; [rewrite (fmw_pres _ _ 20%bv HPr ltac:(fmw_cs_side)), R20; exact G20|].
    split; [rewrite (fmw_pres _ _ 23%bv HPr ltac:(fmw_cs_side)), R23; exact G23|].
    split; [rewrite (fmw_pres _ _ 19%bv HPr ltac:(fmw_cs_side)), R19; exact G19|].
    unfold s0Z. rewrite (fmw_pres _ _ 8%bv HPr ltac:(fmw_cs_side)). exact Hs0.
Qed.

Lemma cno_seg_F1 : forall cx ly S W regs mem md t1 u2 t2,
  cno_base B cx -> cno_F1 B cx ly S W regs mem md t1 u2 t2 ->
  (forall ly' S' W' regs' mem' md', cno_F2 B cx ly' S' W' regs' mem' md' u2 t2 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_F2 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_F1 regs mem md) (cno_post B cx).
Proof.
intros cx ly S W regs mem md t1 u2 t2 HBX HF1 K.
destruct HF1 as ((HC & HP & HGl) & G20 & G23 & G19 & Hs0).
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof HC as (HJ & _).
unfold cno_J in HJ.
pose proof (fmw_resume_nr W regs [] mem CNO_F1) as HS.
set (E := Ereg regs []) in HS.
unfold cfg_at. change (w64 CNO_F1) with (Z_to_bv 64 CNO_F1).
aj_run_to fmw_tbl_cno_ok HS HJ 0x52db8.
{ awr_ok_tac. }
pose proof (frame_nil_same E mem (ms_mem ms) HF) as SB.
pose proof (fmw_reg_lit _ E _ ms 1%bv CNO_F2 HS ltac:(vm_compute; reflexivity) ltac:(unfold CNO_F2; lia)) as R1.
pose proof (fmw_reg_atom _ regs [] _ ms 10%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs [] _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as R2.
pose proof (fmw_reg_atom _ regs [] _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fmw_reg_atom _ regs [] _ ms 20%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as R20.
pose proof (fmw_reg_atom _ regs [] _ ms 23%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl) as R23.
pose proof (fmw_reg_atom _ regs [] _ ms 24%bv 24%bv 24 HS ltac:(vm_compute; reflexivity) eq_refl) as R24.
pose proof (fmw_reg_atom _ regs [] _ ms 26%bv 26%bv 26 HS ltac:(vm_compute; reflexivity) eq_refl) as R26.
pose proof (fmw_reg_atom _ regs [] _ ms 27%bv 27%bv 27 HS ltac:(vm_compute; reflexivity) eq_refl) as R27.
pose proof alloc_ceiling_lt as ACl.
assert (Hs0c : s0Z (ms_regs ms) < alloc_ceiling) by (unfold s0Z in *; rewrite R8; exact Hs0).
pose proof (cnoE1_core_step cx ly S W regs mem md _ (ms_regs ms) (ms_mem ms) _ HBX HC HJ SB R2 R3 R4 R24 R26 R27) as HC1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
apply (cnoE1_free cx ly S W (ms_regs ms) (ms_mem ms) _ (5 + 2 * EV_names) t1 (nx_tn cx + 18)
  [(u2, nx_un cx + 18); (t2, nx_tn cx + 18)] CNO_F2 (cno_post B cx) HBX HC1 HP).
- unfold cno_glob in *. exact (fm_glob_below W mem (ms_mem ms) _ _ _ _ (same_below_mono _ _ _ alloc_ceiling SB ltac:(lia)) HGl).
- rewrite R10. exact G19.
- exact R1.
- unfold CNO_F2. lia.
- reflexivity.
- exact Hs0c.
- unfold EV_check_no_overread, EV_names. lia.
- vm_compute. reflexivity.
- intros ly2 S2 W2 regs2 mem2 md2 HC2 HP2 HG2 HPr.
  apply (K ly2 S2 W2 regs2 mem2 md2).
  unfold cno_F2, cno_fr.
  replace (6 + 2 * EV_names) with (5 + 2 * EV_names + 1) by reflexivity.
  split; [split; [exact HC2 | split; [exact HP2 | exact HG2]]|].
  split; [rewrite (fmw_pres _ _ 20%bv HPr ltac:(fmw_cs_side)), R20; exact G20|].
  split; [rewrite (fmw_pres _ _ 23%bv HPr ltac:(fmw_cs_side)), R23; exact G23|].
  unfold s0Z. rewrite (fmw_pres _ _ 8%bv HPr ltac:(fmw_cs_side)). exact Hs0c.
Qed.

Lemma cno_seg_F2 : forall cx ly S W regs mem md u2 t2,
  cno_base B cx -> cno_F2 B cx ly S W regs mem md u2 t2 ->
  (forall ly' S' W' regs' mem' md', cno_F3 B cx ly' S' W' regs' mem' md' t2 ->
     SRr tfibsegs W' (cfg_at tfibsegs CNO_F3 regs' mem' md') (cno_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_F2 regs mem md) (cno_post B cx).
Proof.
intros cx ly S W regs mem md u2 t2 HBX HF2 K.
destruct HF2 as ((HC & HP & HGl) & G20 & G23 & Hs0).
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof HC as (HJ & _).
unfold cno_J in HJ.
pose proof (fmw_resume_nr W regs [] mem CNO_F2) as HS.
set (E := Ereg regs []) in HS.
unfold cfg_at. change (w64 CNO_F2) with (Z_to_bv 64 CNO_F2).
aj_run_to fmw_tbl_cno_ok HS HJ 0x52db8.
{ awr_ok_tac. }
pose proof (frame_nil_same E mem (ms_mem ms) HF) as SB.
pose proof (fmw_reg_lit _ E _ ms 1%bv CNO_F3 HS ltac:(vm_compute; reflexivity) ltac:(unfold CNO_F3; lia)) as R1.
pose proof (fmw_reg_atom _ regs [] _ ms 10%bv 23%bv 23 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs [] _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as R2.
pose proof (fmw_reg_atom _ regs [] _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fmw_reg_atom _ regs [] _ ms 20%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as R20.
pose proof (fmw_reg_atom _ regs [] _ ms 24%bv 24%bv 24 HS ltac:(vm_compute; reflexivity) eq_refl) as R24.
pose proof (fmw_reg_atom _ regs [] _ ms 26%bv 26%bv 26 HS ltac:(vm_compute; reflexivity) eq_refl) as R26.
pose proof (fmw_reg_atom _ regs [] _ ms 27%bv 27%bv 27 HS ltac:(vm_compute; reflexivity) eq_refl) as R27.
pose proof alloc_ceiling_lt as ACl.
assert (Hs0c : s0Z (ms_regs ms) < alloc_ceiling) by (unfold s0Z in *; rewrite R8; exact Hs0).
pose proof (cnoE1_core_step cx ly S W regs mem md _ (ms_regs ms) (ms_mem ms) _ HBX HC HJ SB R2 R3 R4 R24 R26 R27) as HC1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
apply (cnoE1_free cx ly S W (ms_regs ms) (ms_mem ms) _ (6 + 2 * EV_names) u2 (nx_un cx + 18)
  [(t2, nx_tn cx + 18)] CNO_F3 (cno_post B cx) HBX HC1 HP).
- unfold cno_glob in *. exact (fm_glob_below W mem (ms_mem ms) _ _ _ _ (same_below_mono _ _ _ alloc_ceiling SB ltac:(lia)) HGl).
- rewrite R10. exact G23.
- exact R1.
- unfold CNO_F3. lia.
- reflexivity.
- exact Hs0c.
- unfold EV_check_no_overread, EV_names. lia.
- vm_compute. reflexivity.
- intros ly2 S2 W2 regs2 mem2 md2 HC2 HP2 HG2 HPr.
  apply (K ly2 S2 W2 regs2 mem2 md2).
  unfold cno_F3, cno_fr.
  replace (7 + 2 * EV_names) with (6 + 2 * EV_names + 1) by reflexivity.
  split; [split; [exact HC2 | split; [exact HP2 | exact HG2]]|].
  rewrite (fmw_pres _ _ 20%bv HPr ltac:(fmw_cs_side)), R20; exact G20.
Qed.

End S.
