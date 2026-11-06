(* check_no_overread 0x80b20, last segment F3 (0x80d24, fuzz_manifest.c:189): a0 := s4 (t2), the epilogue (ra, s0..s9
   back from their slots, sp back up by 96), and the tail call `j free` (0x80d58 -> 0x52db8) with ra = the caller's
   0x809e0: free (t2) returns straight to the caller. *)
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

(* ---- the epilogue's symbolic state at 0x80d24: every register its own atom, atom 32 the shadow base, atoms 33..43 the
   11 slot values (cno_saved_regs order), the frame [sp, sp + 96) writable ---- *)
Definition cnoE2_vals (cx : cnx) : list Z := map (fun r => bv_unsigned (getr (nx_regs cx) (Z_to_bv 5 r))) cno_saved_regs.
Definition cnoE2_epi_ss (pc : Z) : sstate :=
  mkSS pc sr_atoms [fmw_frame_region CNO_FRAME cno_saved_offs] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
(* the callee-saved registers after the epilogue: sp back up by the frame, s0 s1 s2..s9 the slot atoms, s10 s11 kept *)
Definition cnoE2_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 CNO_FRAME
  | 8 => SOff 34 0
  | 9 => SOff 35 0
  | z => if (18 <=? z) && (z <=? 25) then SOff (Z.to_nat (z + 18)) 0 else SOff (Z.to_nat z) 0
  end.

Lemma cnoE2_slot : forall cx regs' j (r : bv 5), nth_error cno_saved_regs j = Some (bv_unsigned r) ->
  sv_denot (fmw_env regs' (cnoE2_vals cx)) (SOff (33 + j) 0) = getr (nx_regs cx) r.
Proof.
intros cx regs' j r Hr. rewrite fmw_SOff0, fmw_env_extra.
- assert (Ev : nth j (cnoE2_vals cx) 0 = bv_unsigned (getr (nx_regs cx) r)).
  { apply nth_error_nth. unfold cnoE2_vals. rewrite (map_nth_error _ j _ Hr). cbv beta.
    rewrite Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Ev. apply Z_to_bv_bv_unsigned.
- unfold cnoE2_vals. rewrite length_map. apply nth_error_Some. rewrite Hr. discriminate.
Qed.
Lemma cnoE2_reg_slot : forall H regs' cx ss ms (q r : bv 5) j,
  st_ok tfibsegs (fmw_env regs' (cnoE2_vals cx)) ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff (33 + j) 0 ->
  nth_error cno_saved_regs j = Some (bv_unsigned r) -> getr (ms_regs ms) q = getr (nx_regs cx) r.
Proof.
intros H regs' cx ss ms q r j HS Hq Hr. rewrite (st_ok_restrict_reg tfibsegs H _ ss ms q HS), Hq.
exact (cnoE2_slot cx regs' j r Hr).
Qed.

(* fm's statics ride through any step that keeps their bytes *)
Lemma cnoE2_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
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

(* blocks with disjoint extents are distinct *)
Lemma cnoE2_nodup_pw : forall l : list (Z * Z), Forall (fun b => 0 < req_size (snd b)) l ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x t IH]; intros HF HP; constructor.
- intros Hin. cbn [map pairwise] in HP. destruct HP as [F _].
  pose proof (proj1 (Forall_forall _ _) F _ (in_map (fun b => (fst b, req_size (snd b))) t x Hin)) as Hd.
  apply Forall_inv in HF. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply Forall_inv_tail in HF. cbn [map pairwise] in HP. exact (IH HF (proj2 HP)).
Qed.

(* the epilogue's symbolic state holds at any resume point after the prologue *)
Lemma cnoE2_epi_st : forall cx ly' S' W' regs' mem' md' k pc,
  cno_base B cx -> cno_core B cx ly' S' W' regs' mem' md' k ->
  st_ok tfibsegs (fmw_env regs' (cnoE2_vals cx)) (cnoE2_epi_ss pc)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 pc) mem' (seg_rom tfibsegs))).
Proof.
intros cx ly' S' W' regs' mem' md' k pc ((HAP & HRO) & _) (HJ & HFR & Hsp & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_no_overread = 16736) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
unfold nx_sp0, CNO_FRAME in *.
unfold cnoE2_epi_ss, CNO_FRAME. apply fmw_mid_entry.
- lia.
- lia.
- intros a Ha. apply Hpres. lia.
- unfold cnoE2_vals. rewrite length_map. reflexivity.
- intros j o Ho. destruct (nth_error cno_saved_regs j) as [r|] eqn:Er.
  + assert (Ev : nth j (cnoE2_vals cx) 0 = bv_unsigned (getr (nx_regs cx) (Z_to_bv 5 r))).
    { apply nth_error_nth. unfold cnoE2_vals. rewrite (map_nth_error _ j _ Er). reflexivity. }
    rewrite Ev. split; [|apply u64_range]. rewrite Hsp. exact (HFR j o r Ho Er).
  + exfalso. apply nth_error_None in Er.
    assert (Hj : (j < length cno_saved_offs)%nat) by (apply nth_error_Some; rewrite Ho; discriminate).
    cbn in Er, Hj. lia.
- vm_compute. reflexivity.
- constructor.
- cbn. tauto.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (fmw_env_reg regs' (cnoE2_vals cx) 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs').
  rewrite Hsp. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. reflexivity.
Qed.

(* the per-register goals of fmw_preserved after the epilogue (cnoE2_expect) *)
Ltac cnoE2_cs_cases cx regs' E2s H3 H4 H26 H27 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv [CALLEE_SAVED In] in Hr;
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (cnoE2_expect ?q) = _ =>
    let e := eval vm_compute in (cnoE2_expect q) in change (cnoE2_expect q) with e end;
  first
  [ eapply fmw_sp_back; exact E2s
  | rewrite fmw_SOff0, (fmw_env_reg regs' (cnoE2_vals cx) 3 3%bv eq_refl); exact H3
  | rewrite fmw_SOff0, (fmw_env_reg regs' (cnoE2_vals cx) 4 4%bv eq_refl); exact H4
  | rewrite fmw_SOff0, (fmw_env_reg regs' (cnoE2_vals cx) 26 26%bv eq_refl); exact H26
  | rewrite fmw_SOff0, (fmw_env_reg regs' (cnoE2_vals cx) 27 27%bv eq_refl); exact H27
  | lazymatch goal with |- sv_denot _ (SOff ?n 0) = getr _ ?q =>
      let j := eval vm_compute in (n - 33)%nat in
      exact (cnoE2_slot cx regs' j q ltac:(vm_compute; reflexivity)) end ].

(* ---- 0x80d24: a0 := t2, the epilogue, `j free`: free (t2) returns to the caller ---- *)
Lemma cno_seg_F3 : forall cx ly S W regs mem md t2,
  cno_base B cx -> cno_F3 B cx ly S W regs mem md t2 ->
  SRr tfibsegs W (cfg_at tfibsegs CNO_F3 regs mem md) (cno_post B cx).
Proof.
intros cx ly S W regs mem md t2 HBX HF3.
destruct HF3 as ((HC & Hperm & HGl) & HF3r).
pose proof (cnoE2_epi_st cx ly S W regs mem md _ CNO_F3 HBX HC) as HS.
destruct HC as (HJ & HFR & Hsp & H3 & H4 & H24 & HROc & H26 & H27).
rename HF3r into H20.
pose proof HBX as (HPRE & Hra0 & H10 & H11 & H12 & H13 & Hsu & Hst & Hnzu & Hnzt & Hhu & Hht & Hlu & Htn & HG & HQ
  & Hlive & Hev & Hbb).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
unfold cno_J, nx_sp0, CNO_FRAME in *.
pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_no_overread = 16736) by reflexivity.
assert (FE : EV_check_no_overread = 12) by reflexivity.
assert (FN : EV_names = 2) by reflexivity.
assert (E2s : bv_unsigned (ew (fmw_env regs (cnoE2_vals cx)) 2) = spZ (nx_regs cx) - 96).
{ rewrite (fmw_env_reg regs _ 2 2%bv eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs). exact Hsp. }
assert (E2 : bv_unsigned (ew (fmw_env regs (cnoE2_vals cx)) 2) = spZ (nx_regs cx) + -96) by lia.
(* 0x80d24 .. 0x80d58: a0 := s4, the epilogue, j free *)
unfold cfg_at. change (w64 CNO_F3) with (Z_to_bv 64 CNO_F3).
aj_run_to fmw_tbl_cno_ok HS HJ 0x52db8.
{ unfold cnoE2_epi_ss; cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
    [reflexivity | exact E2 | cbn [fmw_frame_region YP09.r_wlo YP09.r_whi]; unfold CNO_FRAME; lia
    | cbn [fmw_frame_region YP09.r_wlo YP09.r_whi]; unfold CNO_FRAME; lia | apply awr_ok_nil]. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
pose proof (cnoE2_reg_slot _ regs cx _ ms1 1%bv 1%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as R1.
pose proof (cnoE2_reg_slot _ regs cx _ ms1 8%bv 8%bv 1 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as R8.
pose proof (fmw_reg_off _ _ _ ms1 2%bv 2 96 (spZ (nx_regs cx) - 96) HS ltac:(vm_compute; reflexivity) E2s ltac:(lia)) as R2.
pose proof (fmw_reg_atom _ regs _ _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs _ _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs _ _ ms1 10%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
assert (Hsp1 : spZ (ms_regs ms1) = spZ (nx_regs cx)) by (unfold spZ at 1; rewrite R2; lia).
assert (SB : same_below mem (ms_mem ms1) alloc_ceiling).
{ unfold cnoE2_epi_ss in HF; cbn [ss_mem] in HF.
  apply (same_below_frame1 _ _ mem (ms_mem ms1) alloc_ceiling HF); [|lia].
  cbn [fmw_frame_region YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & _ & Hnev & _ & F1 & _).
(* t2's block is live now and was not at the entry *)
assert (Hin : In (t2, nx_tn cx + 18) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
assert (Hnot : ~ In (t2, nx_tn cx + 18) (ablocks B (nx_ly cx) (nx_S cx))).
{ assert (ND : List.NoDup (ablocks B ly S)).
  { apply cnoE2_nodup_pw.
    - apply Forall_forall. intros [p m] Hpm.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR1 Hpm) as (_ & _ & _ & _ & _ & _ & Hm).
      cbn [snd]. unfold req_size. destruct (Z.eqb_spec m 0); lia.
    - destruct (al_sep _ _ LAWS _ _ _ _ _ HAR1) as [Hp _]. apply pairwise_app_l in Hp as [Hp _]. exact Hp. }
  pose proof (Permutation_NoDup Hperm ND) as ND2.
  pose proof (NoDup_remove_2 _ [] _ ND2) as ND3. rewrite app_nil_r in ND3. exact ND3. }
(* the entry frame chain, read through the journal (memory at and above sp0 is the entry's) *)
assert (Hchain : chain_pre ly (aview tfibsegs (w_H W) (ms_mem ms1)) (ms_regs ms1) []).
{ apply (achain_chain_pre ly _ (spZ (nx_regs cx)) (s0Z (nx_regs cx)) [] (ms_regs ms1)).
  - destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
    apply (achain_ly_top (nx_ly cx) ly _ _ _ _ Etop).
    pose proof Hstk as (_ & _ & _ & _ & _ & Hs6 & _ & Hs8 & Hs9).
    apply (achain_kept (nx_ly cx) (aview tfibsegs (w_H (nx_W cx)) (nx_mem cx)) _ _ _ [] (spZ (nx_regs cx)) Hch);
      [lia | lia |].
    intros a Ha. apply F1; lia.
  - rewrite Hsp1. lia.
  - unfold s0Z. rewrite R8. reflexivity.
  - unfold raZ. rewrite R1. exact Hra4. }
assert (HU : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms1) []) (as_universe B)).
{ apply UNIV. rewrite call_trace_nil, (fb_code B FB).
  assert (RA : raZ (ms_regs ms1) = 0x809e0) by (unfold raZ; rewrite R1; exact Hra0).
  rewrite RA. apply memZL_In. vm_compute. reflexivity. }
(* free (t2): returns to the caller *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 0x52db8) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite (fb_code B FB); reflexivity).
eapply SRr_mono.
{ apply (afree04_sub tfibsegs B LAWS HSL ameter_triv AFREE4 W (ms_regs ms1) (ms_mem ms1) STK_check_no_overread
    (spZ (nx_regs cx)) FM_PSTAT_FP (nx_ly cx) (nx_S cx) (nx_W cx) (nx_mem cx) (nx_md cx) [] ly S _
    (7 + 2 * EV_names) t2 (nx_tn cx + 18) 0 (getr (nx_regs cx) 1) []).
  - exact HJ.
  - exact Hin.
  - rewrite R10. exact H20.
  - rewrite Hsp1. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - rewrite R3, H3. exact Hgp.
  - rewrite R4, H4. exact Htp.
  - exact R1.
  - exact Hra.
  - lia.
  - exact Hchain.
  - exact HU.
  - intros Hx. exfalso. exact (Hnot Hx).
  - exact I. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Hl1 & Hl2) & _ & HK & _ & _).
unfold cno_post, fpost, apost_base.
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split.
{ eapply (ajournal_mono_k tfibsegs B); [exact HJ2 | lia]. }
split.
{ apply (aregs_preserved_trans _ (ms_regs ms1)); [|exact HP2].
  apply (fmw_preserved _ _ _ ms1 (nx_regs cx) cnoE2_expect HS); [vm_compute; reflexivity|].
  cnoE2_cs_cases cx regs E2s H3 H4 H26 H27. }
cbv beta. split.
{ rewrite Hl2. apply (Permutation_cons_inv (a := (t2, nx_tn cx + 18))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- Hl1.
  eapply Permutation_trans; [exact Hperm|]. apply Permutation_sym, Permutation_cons_append. }
destruct HK as (_ & _ & KK3 & _).
apply (cnoE2_glob_img W W2 (ms_mem ms1) mem2).
{ intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KK3 a (pstat_img a Ha) N1 N2). }
apply (fm_glob_below W mem (ms_mem ms1) _ _ _ _ SB).
exact HGl.
Qed.
End S.
