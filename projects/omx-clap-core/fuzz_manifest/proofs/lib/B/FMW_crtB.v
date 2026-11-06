(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_crtB.v, relocated by b_reloc.py (crt): every image
   numeral re-derived by symbol / section / string content, revcheck report (internal path). *)
(* check_round_trip after names ("", uri) (fuzz_manifest.c:262-266) and its n = 0 exit (fuzz_manifest.c:263, the
   epilogue at 0x8122c). crt_segB: from 0x81058 (a0 = 0: `bnez a0` is dead), `beqz s3`: n = 0 goes to 0x8122c; n >= 1:
   s1 := 3 n + 64, malloc (s1), `beqz a0` (dead: t >= 4096), s2 := t, at 0x8107c (crt_P3). crt_segX0: the epilogue at
   0x8122c (13 registers back from their slots, sp back up) and ret. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YC85.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_crt0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the epilogue's symbolic state (0x811ec, 0x8122c): every register its own atom, atom 32 the shadow base, atoms
   33..45 the 13 slot values (crt_saved_regs order), the frame [sp, sp + 112) writable ---- *)
Definition crt_vals (cx : crtx) : list Z := map (fun r => bv_unsigned (getr (cx_regs cx) (Z_to_bv 5 r))) crt_saved_regs.
Definition crt_epi_ss (pc : Z) : sstate :=
  mkSS pc sr_atoms [fmw_frame_region CRT_FRAME crt_saved_offs] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
(* the callee-saved registers after the epilogue: sp back up by the frame, ra s0 s1 s2..s11 the slot atoms *)
Definition crt_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 CRT_FRAME
  | 8 => SOff 34 0
  | 9 => SOff 35 0
  | z => if (18 <=? z) && (z <=? 27) then SOff (Z.to_nat (z + 18)) 0 else SOff (Z.to_nat z) 0
  end.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma crt_slot : forall cx regs' j (r : bv 5), nth_error crt_saved_regs j = Some (bv_unsigned r) ->
  sv_denot (fmw_env regs' (crt_vals cx)) (SOff (33 + j) 0) = getr (cx_regs cx) r.
Proof.
intros cx regs' j r Hr. rewrite fmw_SOff0, fmw_env_extra.
- assert (Ev : nth j (crt_vals cx) 0 = bv_unsigned (getr (cx_regs cx) r)).
  { apply nth_error_nth. unfold crt_vals. rewrite (map_nth_error _ j _ Hr). cbv beta.
    rewrite Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Ev. apply Z_to_bv_bv_unsigned.
- unfold crt_vals. rewrite length_map. apply nth_error_Some. rewrite Hr. discriminate.
Qed.
Lemma crt_reg_slot : forall H regs' cx ss ms (q r : bv 5) j,
  st_ok tfibsegs (fmw_env regs' (crt_vals cx)) ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff (33 + j) 0 ->
  nth_error crt_saved_regs j = Some (bv_unsigned r) -> getr (ms_regs ms) q = getr (cx_regs cx) r.
Proof.
intros H regs' cx ss ms q r j HS Hq Hr. rewrite (st_ok_restrict_reg tfibsegs H _ ss ms q HS), Hq.
exact (crt_slot cx regs' j r Hr).
Qed.
(* a register the run left as a computed value v, U E v = z *)
Lemma crt_reg_U : forall H E ss ms (r : bv 5) v z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> U E v = z -> getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r v z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. unfold w64. rewrite <- Hz.
unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* fm's statics ride through any step that keeps their bytes *)
Lemma crt_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
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

Lemma nil_closed : ~ YI16.sink_open_fp [].
Proof. intros (r & Hr & _). destruct Hr. Qed.
End h.

(* every frame of a run with no regions in context as same_below (2 ^ 64), chained *)
Ltac crt_sb_nil :=
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

(* the per-register goals of fmw_preserved after the epilogue (crt_expect) *)
Ltac crt_cs_cases cx regs' E2s H3 H4 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv [CALLEE_SAVED In] in Hr;
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (crt_expect ?q) = _ =>
    let e := eval vm_compute in (crt_expect q) in change (crt_expect q) with e end;
  first
  [ eapply fmw_sp_back; exact E2s
  | rewrite fmw_SOff0, (fmw_env_reg regs' (crt_vals cx) 3 3%bv eq_refl); exact H3
  | rewrite fmw_SOff0, (fmw_env_reg regs' (crt_vals cx) 4 4%bv eq_refl); exact H4
  | lazymatch goal with |- sv_denot _ (SOff ?n 0) = getr _ ?q =>
      let j := eval vm_compute in (n - 33)%nat in
      exact (crt_slot cx regs' j q ltac:(vm_compute; reflexivity)) end ].

Section B. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis UNIV : fm_univ B.
Hypothesis AMALLOC : amalloc04_rule tfibsegs B ameter_triv.

(* the epilogue's symbolic state holds at any resume point after the prologue *)
Lemma crt_epi_st : forall cx ly' S' W' regs' mem' md' k pc,
  crt_base B cx -> crt_core B cx ly' S' W' regs' mem' md' k ->
  st_ok tfibsegs (fmw_env regs' (crt_vals cx)) (crt_epi_ss pc)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 pc) mem' (seg_rom tfibsegs))).
Proof.
intros cx ly' S' W' regs' mem' md' k pc ((HAP & HRO) & _) (HJ & HFR & Hsp & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_round_trip = 16784) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
unfold cx_sp0, CRT_FRAME in *.
unfold crt_epi_ss, CRT_FRAME. apply fmw_mid_entry.
- lia.
- lia.
- intros a Ha. apply Hpres. lia.
- unfold crt_vals. rewrite length_map. reflexivity.
- intros j o Ho. destruct (nth_error crt_saved_regs j) as [r|] eqn:Er.
  + assert (Ev : nth j (crt_vals cx) 0 = bv_unsigned (getr (cx_regs cx) (Z_to_bv 5 r))).
    { apply nth_error_nth. unfold crt_vals. rewrite (map_nth_error _ j _ Er). reflexivity. }
    rewrite Ev. split; [|apply u64_range]. rewrite Hsp. exact (HFR j o r Ho Er).
  + exfalso. apply nth_error_None in Er.
    assert (Hj : (j < length crt_saved_offs)%nat) by (apply nth_error_Some; rewrite Ho; discriminate).
    cbn in Er, Hj. lia.
- vm_compute. reflexivity.
- constructor.
- cbn. tauto.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (fmw_env_reg regs' (crt_vals cx) 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs').
  rewrite Hsp. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. reflexivity.
Qed.

(* ---- 0x8122c, n = 0: the epilogue and ret ---- *)
Lemma crt_segX0 : forall cx ly' S' W' regs' mem' md' k,
  crt_base B cx -> crt_X0 B cx ly' S' W' regs' mem' md' k ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_X0 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly' S' W' regs' mem' md' k HB HX.
destruct HX as (HC & Hk & Hn0 & Hperm & HGl).
pose proof (crt_epi_st cx ly' S' W' regs' mem' md' k CRT_X0 HB HC) as HS.
pose proof HB as (HPRE & HCTX & H10 & Hu & Hku & Hlu & HG & HQ & Hlive & Hev & Hbb).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct HC as (HJ & HFR & Hsp & H3 & H4 & H8 & H26 & Hu' & Hku' & HRO').
unfold crt_J, cx_sp0, CRT_FRAME in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_round_trip = 16784) by reflexivity.
assert (E2s : bv_unsigned (ew (fmw_env regs' (crt_vals cx)) 2) = spZ (cx_regs cx) - 112).
{ rewrite (fmw_env_reg regs' _ 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs'). exact Hsp. }
assert (E2 : bv_unsigned (ew (fmw_env regs' (crt_vals cx)) 2) = spZ (cx_regs cx) + -112) by lia.
unfold cfg_at. change (w64 CRT_X0) with (Z_to_bv 64 CRT_X0).
aj_run fmw_tbl_crt_ok HS HJ.
{ unfold crt_epi_ss; cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -112);
    [reflexivity | exact E2 | cbn [fmw_frame_region YP09.r_wlo YP09.r_whi]; unfold CRT_FRAME; lia
    | cbn [fmw_frame_region YP09.r_wlo YP09.r_whi]; unfold CRT_FRAME; lia | apply awr_ok_nil]. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
pose proof (crt_reg_slot _ regs' cx _ ms1 1%bv 1%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as R1.
assert (SB : same_below mem' (ms_mem ms1) alloc_ceiling).
{ unfold crt_epi_ss in HF; cbn [ss_mem] in HF.
  apply (same_below_frame1 _ _ mem' (ms_mem ms1) alloc_ceiling HF); [|lia].
  cbn [fmw_frame_region YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
eapply (SRr_ret_at tfibsegs _ fmw_tbl_crt_ok fm_wx); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat2.
assert (Hpc : v_jalr (getr (ms_regs ms1) 1) 0 = getr (cx_regs cx) 1) by (rewrite R1; exact Hra).
rewrite Hpc. unfold crt_post, fpost, apost_base.
do 5 eexists. split; [reflexivity|].
split.
{ apply (ajournal_materialize tfibsegs B LAWS HSL).
  eapply (ajournal_mono_k tfibsegs B); [exact HJ | unfold EV_check_round_trip, EV_names in *; lia]. }
split.
{ apply (fmw_preserved _ _ _ ms1 (cx_regs cx) crt_expect HS); [vm_compute; reflexivity|].
  crt_cs_cases cx regs' E2s H3 H4. }
split; [exact Hperm|].
unfold crt_glob in HGl. unfold cx_n in Hn0.
replace (if 0 =? 0 then cx_peak cx else rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx)) with (cx_peak cx) in HGl
  by reflexivity.
destruct (cx_ub cx) as [|c ub'] eqn:Eub; [|cbn in Hn0; lia].
cbn [rt_peak rt_calls].
exact (fm_glob_below W' mem' (ms_mem ms1) _ _ _ _ SB HGl).
Qed.

(* ---- 0x81058 .. 0x8107c ---- *)
Lemma crt_segB : forall cx ly' S' W' regs' mem' md' k,
  crt_base B cx -> crt_P2 B cx ly' S' W' regs' mem' md' k ->
  (forall ly2 S2 W2 regs2 mem2 md2 k2, crt_X0 B cx ly2 S2 W2 regs2 mem2 md2 k2 ->
     SRr tfibsegs W2 (cfg_at tfibsegs CRT_X0 regs2 mem2 md2) (crt_post B cx)) ->
  (forall ly2 S2 W2 regs2 mem2 md2 k2 t, crt_P3 B cx ly2 S2 W2 regs2 mem2 md2 k2 t ->
     SRr tfibsegs W2 (cfg_at tfibsegs CRT_P3 regs2 mem2 md2) (crt_post B cx)) ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_P2 regs' mem' md') (crt_post B cx).
Proof.
intros cx ly' S' W' regs' mem' md' k HB HP2 K0 K3.
pose proof HB as (HPRE & HCTX & H10 & Hu & Hku & Hlu & HG & HQ & Hlive & Hev & Hbb).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct HP2 as ((HJ & HFR & Hsp & H3 & H4 & H8 & H26 & Hu' & Hku' & HRO') & Hk & Ha0 & Hn & Hperm & HGl).
unfold crt_J, cx_sp0, CRT_FRAME in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_round_trip = 16784) by reflexivity.
assert (Hn255 : 0 <= cx_n cx <= 255) by (unfold cx_n; lia).
pose proof (fmw_resume_nr W' regs' [] mem' CRT_P2) as HS.
unfold cfg_at. change (w64 CRT_P2) with (Z_to_bv 64 CRT_P2).
assert (U10 : U (Ereg regs' []) (SOff 10 0) = 0)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs' [] 10 10%bv eq_refl); exact Ha0 | lia]).
assert (U19 : U (Ereg regs' []) (SOff 19 0) = cx_n cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs' [] 19 19%bv eq_refl); exact Hn | lia]).
assert (UZ : U (Ereg regs' []) (SLit 0) = 0) by (apply U_lit; lia).
(* 0x81058: bnez a0 (a0 = 0) *)
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 10 0) (b := SLit 0); [exact HS | intros Hb _ | intros _ HS1].
{ exfalso. rewrite branch_ne_U, U10, UZ in Hb. discriminate Hb. }
clear HS.
aj_run fmw_tbl_crt_ok HS1 HJ.
{ apply awr_ok_nil. }
(* 0x8105c: beqz s3 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 19 0) (b := SLit 0); [exact HS1 | intros Hb HS2 | intros Hb HS2];
  rewrite branch_eq_U, U19, UZ in Hb; clear HS1.
- (* n = 0: on to 0x8122c *)
  apply Z.eqb_eq in Hb.
  aj_run_to fmw_tbl_crt_ok HS2 HJ CRT_X0.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  crt_sb_nil.
  match goal with H : same_below mem' (ms_mem ms2) _ |- _ => rename H into SB1 end.
  assert (SB1c : same_below mem' (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
  pose proof (fmw_reg_atom _ regs' [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q26.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W') _ _ ms2 HS2 eq_refl). cbn [ss_pc].
  apply (K0 ly' S' W' (ms_regs ms2) (ms_mem ms2) _ k).
  rewrite Hb in HGl. change (if 0 =? 0 then 0 else 1) with 0 in HGl.
  unfold crt_X0, crt_core, crt_J, crt_glob in *.
  split; [|split; [exact Hk | split; [exact Hb | split; [exact Hperm | exact (fm_glob_below W' mem' (ms_mem ms2) _ _ _ _ SB1c HGl)]]]].
  split; [exact HJ|].
  split; [apply (crt_frame_below cx W' mem' (ms_mem ms2) SB1); [unfold cx_sp0, CRT_FRAME; lia | unfold cx_sp0; lia | exact HFR]|].
  split; [unfold cx_sp0, CRT_FRAME; unfold spZ at 1; rewrite Q2; exact Hsp|].
  split; [rewrite Q3; exact H3|]. split; [rewrite Q4; exact H4|]. split; [rewrite Q8; exact H8|].
  split; [rewrite Q26; exact H26|].
  split; [exact (cstr_ok_below W' mem' (ms_mem ms2) _ _ SB1c Hu')|].
  split; [exact Hku'|].
  exact (arodata_below B W' mem' (ms_mem ms2) SB1c HRO').
- (* n >= 1: s1 := 3 n + 64, malloc (s1) *)
  apply Z.eqb_neq in Hb.
  assert (Hn1 : 1 <= cx_n cx) by lia.
  aj_run_to fmw_tbl_crt_ok HS2 HJ 0x52e1c.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  crt_sb_nil.
  match goal with H : same_below mem' (ms_mem ms2) _ |- _ => rename H into SB1 end.
  assert (SB1c : same_below mem' (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
  pose proof (fmw_reg_lit _ (Ereg regs' []) _ ms2 1%bv 0x81074 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
  pose proof (fmw_reg_atom _ regs' [] _ ms2 26%bv 26%bv 26 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q26.
  assert (U9 : U (Ereg regs' []) (SAlu ALU_ADD (SMd M_MUL (SOff 19 0) (SLit 3)) (SLit 64)) = crt_tsz (cx_n cx)).
  { rewrite U_SAlu, U_SMd, U19, !U_lit by lia. cbn [zalu_raw zmd_raw].
    rewrite (zcanon_id (cx_n cx * 3)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). unfold crt_tsz. lia. }
  pose proof (crt_reg_U _ _ _ ms2 9%bv _ _ HS2 ltac:(vm_compute; reflexivity) U9) as Q9.
  pose proof (crt_reg_U _ _ _ ms2 10%bv _ _ HS2 ltac:(vm_compute; reflexivity) U9) as Q10.
  assert (Hsp2 : spZ (ms_regs ms2) = spZ (cx_regs cx) + -112) by (unfold spZ at 1; rewrite Q2; fold (spZ regs'); lia).
  pose proof Hu as (_ & Hu4096 & Hucl & _).
  assert (FL : LIVE_check_round_trip = 2048) by reflexivity.
  assert (FE : EV_check_round_trip = 2040) by reflexivity.
  assert (FN : EV_names = 2) by reflexivity.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W') _ _ ms2 HS2 eq_refl). cbn [ss_pc].
  replace (Z_to_bv 64 0x52e1c) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite (fb_code B FB); reflexivity).
  eapply SRr_bind.
  { apply (amalloc04_sub tfibsegs B LAWS HSL ameter_triv AMALLOC W' (ms_regs ms2) (ms_mem ms2) STK_check_round_trip
      (spZ (cx_regs cx)) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) [] ly' S' _ k
      (crt_tsz (cx_n cx)) (-112) (Z_to_bv 64 0x81074) []).
    - exact HJ.
    - exact Q10.
    - unfold crt_tsz, MALLOC_MAX. lia.
    - rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ Hperm), <- (blocks_bytes_bsum B (cx_ly cx) (cx_S cx)).
      unfold crt_tsz. lia.
    - exact Hsp2.
    - reflexivity.
    - lia.
    - unfold ASTACK. lia.
    - rewrite Q3, H3. exact Hgp.
    - rewrite Q4, H4. exact Htp.
    - exact Q1.
    - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
    - lia.
    - apply (achain_chain_pre ly' _ (spZ (ms_regs ms2)) (cx_u cx) [] (ms_regs ms2)).
      + apply achain_low. lia.
      + lia.
      + unfold s0Z. rewrite Q8, H8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
    - apply UNIV. rewrite call_trace_nil, (fb_code B FB).
      assert (RA : raZ (ms_regs ms2) = 0x81074) by (unfold raZ; rewrite Q1; apply unsigned_lit_small; lia).
      rewrite RA. apply memZL_In. vm_compute. reflexivity.
    - exact I. }
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & H10r & _ & Hr4 & Hbl & HK & _ & HJs).
  (* back at 0x81074 *)
  assert (Hinc : forall x, In x (ablocks B ly' S') -> In x (ablocks B ly2 S2))
    by (intros x Hx; rewrite Hbl; apply in_or_app; left; exact Hx).
  pose proof HJ2 as (HAR2 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res (crt_tsz (cx_n cx)) HAR2 ltac:(rewrite Hbl; apply in_or_app; right; left; reflexivity))
    as (_ & _ & Hres & _).
  assert (Hrq : req_size (crt_tsz (cx_n cx)) = crt_tsz (cx_n cx)) by (unfold req_size, crt_tsz; destruct (Z.eqb_spec (3 * cx_n cx + 64) 0); lia).
  rewrite Hrq in Hres. unfold crt_tsz in Hres.
  destruct HK as (KK1 & _ & KK3 & _).
  assert (HROm : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') (ms_mem ms2)))
    by exact (arodata_below B W' mem' (ms_mem ms2) SB1c HRO').
  assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) mem2))
    by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJs nil_closed nil_not_roP HROm).
  assert (Hu2 : cstr_ok tfibsegs W2 mem2 (cx_u cx) (cx_ub cx))
    by exact (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IMG HJs Hinc nil_img HRO2 Hku'
                (cstr_ok_below W' mem' (ms_mem ms2) _ _ SB1c Hu')).
  assert (HFR2 : crt_frame cx W2 mem2).
  { apply (crt_frame_kept cx W' W2 (ms_mem ms2) mem2).
    - intros a Ha. unfold cx_sp0, CRT_FRAME in Ha. apply KK1; [lia | unfold ASTACK; lia].
    - apply (crt_frame_below cx W' mem' (ms_mem ms2) SB1); [unfold cx_sp0, CRT_FRAME; lia | unfold cx_sp0; lia | exact HFR]. }
  assert (HG2 : crt_glob cx W2 mem2 1).
  { rewrite (proj2 (Z.eqb_neq _ _) Hb) in HGl. change (if false then 0 else 1) with 1 in HGl.
    unfold crt_glob in *. apply (crt_glob_img W' W2 (ms_mem ms2) mem2).
    - intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KK3 a (pstat_img a Ha) N1 N2).
    - exact (fm_glob_below W' mem' (ms_mem ms2) _ _ _ _ SB1c HGl). }
  assert (P2 : getr regs2 2 = getr (ms_regs ms2) 2) by exact (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)).
  assert (P3 : getr regs2 3 = getr (ms_regs ms2) 3) by exact (fmw_pres _ _ 3%bv HP2 ltac:(fmw_cs_side)).
  assert (P4 : getr regs2 4 = getr (ms_regs ms2) 4) by exact (fmw_pres _ _ 4%bv HP2 ltac:(fmw_cs_side)).
  assert (P8 : getr regs2 8 = getr (ms_regs ms2) 8) by exact (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)).
  assert (P9 : getr regs2 9 = getr (ms_regs ms2) 9) by exact (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)).
  assert (P19 : getr regs2 19 = getr (ms_regs ms2) 19) by exact (fmw_pres _ _ 19%bv HP2 ltac:(fmw_cs_side)).
  assert (P26 : getr regs2 26 = getr (ms_regs ms2) 26) by exact (fmw_pres _ _ 26%bv HP2 ltac:(fmw_cs_side)).
  clear HS2.
  pose proof (fmw_resume_nr W2 regs2 [] mem2 0x81074) as HS3.
  assert (U10r : U (Ereg regs2 []) (SOff 10 0) = res)
    by (apply U_atom; [rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl); exact H10r | lia]).
  assert (UZ2 : U (Ereg regs2 []) (SLit 0) = 0) by (apply U_lit; lia).
  (* 0x81074: beqz a0 (t >= 4096) *)
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS3 | intros Hb3 _ | intros _ HS4].
  { exfalso. rewrite branch_eq_U, U10r, UZ2 in Hb3. apply Z.eqb_eq in Hb3. lia. }
  clear HS3.
  aj_run_to fmw_tbl_crt_ok HS4 HJ2 CRT_P3.
  { apply awr_ok_nil. }
  lazymatch type of HS4 with context [restrict _ ?m] => rename m into ms3 end.
  crt_sb_nil.
  match goal with H : same_below mem2 (ms_mem ms3) _ |- _ => rename H into SB3 end.
  assert (SB3c : same_below mem2 (ms_mem ms3) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB3); lia).
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 2%bv 2%bv 2 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S2r.
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 3%bv 3%bv 3 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S3r.
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 4%bv 4%bv 4 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S4r.
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 8%bv 8%bv 8 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S8r.
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 9%bv 9%bv 9 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S9r.
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 10%bv 10%bv 10 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S10r.
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 18%bv 10%bv 10 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S18r.
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 19%bv 19%bv 19 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S19r.
  pose proof (fmw_reg_atom _ regs2 [] _ ms3 26%bv 26%bv 26 HS4 ltac:(vm_compute; reflexivity) eq_refl) as S26r.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) _ _ ms3 HS4 eq_refl). cbn [ss_pc].
  apply (K3 ly2 S2 W2 (ms_regs ms3) (ms_mem ms3) _ (k + 1) res).
  unfold crt_P3, crt_tcore, crt_core, crt_J.
  split; [|split; [rewrite S10r; exact H10r | rewrite S19r, P19, Q19; exact Hn]].
  split.
  2:{ split; [lia|]. split; [exact Hn1|]. split; [rewrite S9r, P9; exact Q9|]. split; [rewrite S18r; exact H10r|].
      split; [exact Hr4|].
      split.
      - rewrite Hbl. eapply Permutation_trans; [apply Permutation_sym, Permutation_cons_append|]. apply perm_skip. exact Hperm.
      - unfold crt_glob in *. exact (fm_glob_below W2 mem2 (ms_mem ms3) _ _ _ _ SB3c HG2). }
  split; [exact HJ2|].
  split; [apply (crt_frame_below cx W2 mem2 (ms_mem ms3) SB3); [unfold cx_sp0, CRT_FRAME; lia | unfold cx_sp0; lia | exact HFR2]|].
  split; [unfold cx_sp0, CRT_FRAME; unfold spZ at 1; rewrite S2r, P2; fold (spZ (ms_regs ms2)); lia|].
  split; [rewrite S3r, P3, Q3; exact H3|]. split; [rewrite S4r, P4, Q4; exact H4|].
  split; [rewrite S8r, P8, Q8; exact H8|]. split; [rewrite S26r, P26, Q26; exact H26|].
  split; [exact (cstr_ok_below W2 mem2 (ms_mem ms3) _ _ SB3c Hu2)|].
  split; [exact (cstr_kept_kept B ly' S' ly2 S2 _ _ Hinc Hku')|].
  exact (arodata_below B W2 mem2 (ms_mem ms3) SB3c HRO2).
Qed.
End B.
