(* LLVMFuzzerTestOneInput 0x8091c, segment 0 (fuzz_manifest.c:295): the prologue (ra, s0..s6 saved, s1 := size,
   s5 := the shadow base) and k := size ? min (data[0], size - 1) : 0, up to 0x8097c (FMW_llvmfP.v LF_P0). The shadow
   check of data[0] at 0x80954 takes the fast path: data[0] is in the input block (shent_ok_of_block). *)
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

(* ---- 0x80954 (size > 0): data[0] (atom 32) at a0, s5 = the shadow base; the shadow entry says data[0] is
   addressable ---- *)
Definition lf_byte : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_lfB : sstate :=
  mkSS 0x80954 sr_atoms [lf_byte] None
    (mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 16) 0); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] []).
Definition LF_SH : list shent := [mkSHE 10 0 1].

(* the saved registers from the frame region (region 0) of a symbolic state *)
Ltac lf_frame_tac HS :=
  let HR := fresh "HR" in
  pose proof (fmw_region_nth _ _ _ 0 _ HS eq_refl) as HR; cbn [ms_mem restrict] in HR;
  eapply lf_frame_of_chunks; [exact HR|];
  let j := fresh "j" in let o := fresh "o" in let r := fresh "r" in let Ho := fresh "Ho" in let Hr := fresh "Hr" in
  intros j o r Ho Hr;
  do 8 (destruct j as [|j]; [cbn in Ho, Hr; injection Ho as <-; injection Hr as <-; cbn;
    repeat (first [left; reflexivity | right]) |]);
  destruct j; cbn in Ho; discriminate Ho.
(* every region of a run's start state is read-only or a stack window above alloc_ceiling *)
Ltac lf_rs_tac Usp :=
  cbn [ss_mem add_cond ss_lfB lf_byte];
  repeat (apply Forall_cons; [first [left; cbn; lia | right; cbn [YP09.r_base YP09.r_wlo base_val]; rewrite Usp; lia] |]);
  apply Forall_nil.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis FB : FmB B.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Lemma lf_reg_ew : forall (H : word -> bool) E ss ms (r : bv 5) n v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = v -> getr (ms_regs ms) r = v.
Proof. intros H E ss ms r n v HS Hr Hv. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr, fmw_SOff0. exact Hv. Qed.

(* the callee-saved registers outside X, through a run whose environment agrees with Ereg regsA below 32 *)
Lemma lf_kept_env : forall (H : word -> bool) E ss ms regs0 regsA extra X,
  kept_from regs0 regsA X -> st_ok tfibsegs E ss (restrict H ms) -> atoms_kept ss X = true ->
  (forall n, (n < 32)%nat -> ew E n = ew (Ereg regsA extra) n) -> kept_from regs0 (ms_regs ms) X.
Proof.
intros H E ss ms regs0 regsA extra X HK HS HA AG r Hc HX.
destruct (acs_bv r Hc) as [Eu _].
assert (Hr : 0 <= r < 32) by (unfold acallee_saved in Hc; lia).
rewrite (st_ok_restrict_reg tfibsegs H _ ss ms _ HS), (atoms_kept_get ss X r HA Hc HX), fmw_SOff0.
rewrite (AG (Z.to_nat r) ltac:(lia)).
rewrite (ew_Ereg_nat regsA extra (Z.to_nat r) (Z_to_bv 5 r) ltac:(rewrite Eu; lia)). exact (HK r Hc HX).
Qed.

Lemma lfB_entry : forall (W : world tfibsegs) mem regs p c,
  getr regs 10 = w64 p -> getr regs 21 = w64 FMW_SB -> 4096 <= p <= 2 ^ 47 - 16 -> 0 <= c < 256 ->
  val_mem tfibsegs (rdW W mem) p 1 c ->
  st_ok tfibsegs (Ereg regs [Z_to_bv 64 c]) ss_lfB (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80954) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs p c R10 R21 Hp Hc Vc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs [Z_to_bv 64 c]).
assert (U10 : bv_unsigned (ew E 10) = p)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl), R21; unfold w64; rewrite unsigned_lit_small;
      unfold FMW_SB, SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
unfold ss_lfB. apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 c]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lf_byte. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ p 0 1 (SOff 32 0) c);
    [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Vc.
- apply pairwise_disjoint_of_extents. unfold lf_byte, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U21, E32, unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* lf_P0 from the facts a run leaves: the journal, the frame, memory below alloc_ceiling as at entry, the registers *)
Lemma lf_P0_mk : forall cx regs' mem' md', lf_base B cx ->
  lf_J B cx (lx_ly cx) (lx_S cx) (lx_W cx) mem' md' 0 -> lf_frame cx (lx_W cx) mem' ->
  same_below (lx_mem cx) mem' alloc_ceiling -> spZ regs' = lx_sp0 cx - LF_FRAME ->
  kept_from (lx_regs cx) regs' lf_X -> getr regs' 21 = w64 FMW_SB ->
  getr regs' 9 = w64 (lx_n cx) -> getr regs' 10 = w64 (lx_p cx) -> getr regs' 19 = w64 (lx_k cx) ->
  lf_P0 B cx (lx_ly cx) (lx_S cx) (lx_W cx) regs' mem' md' 0.
Proof.
intros cx regs' mem' md' HB HJ HFR SB Hsp HK H21 H9 H10 H19.
pose proof HB as (HAP & _ & _ & _ & Hcase & _ & _ & _ & _ & HRO & HG & _).
pose proof HAP as (HAR & _).
assert (Hn0 : 0 <= lx_n cx) by (unfold lx_n; lia).
assert (HIN0 : 0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B (lx_ly cx) (lx_S cx)))
  by (intros Hp; destruct Hcase as [[Hz _]|[_ Hin]]; [lia | exact Hin]).
destruct (lf_window B cx _ _ _ _ _ 0 (lx_n cx) HB HAR (fun i _ => eq_refl) HIN0 ltac:(lia) Hn0 ltac:(lia))
  as (_ & Hp4096 & Hpcl & _).
unfold lf_P0, lf_core.
split; [|split; [reflexivity|]].
- split; [exact HJ|]. split; [exact HFR|]. split; [exact Hsp|]. split; [exact HK|]. split; [exact H21|].
  split.
  + intros i Hi. apply (aview_below (w_H (lx_W cx)) (lx_mem cx) mem' alloc_ceiling (lx_p cx + i) SB). lia.
  + exact (arodata_below B (lx_W cx) (lx_mem cx) mem' SB HRO).
- split; [apply Permutation_refl|]. split; [exact (fm_glob_below (lx_W cx) (lx_mem cx) mem' _ _ _ _ SB HG)|].
  split; [exact H9|]. split; [exact H10 | exact H19].
Qed.

Lemma lf_seg0 : forall cx, lf_base B cx ->
  (forall ly' S' W' regs' mem' md' k, lf_P0 B cx ly' S' W' regs' mem' md' k ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P0 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs (lx_W cx) (cfg_at tfibsegs A_LLVMF (lx_regs cx) (lx_mem cx) (lx_md cx)) (lf_post B cx).
Proof.
intros cx HB K0.
pose proof HB as (HAP & Hra & H10 & H11 & Hcase & Hgarr & Hfrs & Hev & Hbb & HRO & HG & Hc0 & Hc1 & Hlv).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof HAP as (HAR & Hra' & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (Hn0 : 0 <= lx_n cx) by (unfold lx_n; lia).
assert (Hn26 : lx_n cx < 2 ^ 26) by (destruct Hcase as [[Hz _]|[[_ Hlt] _]]; lia).
assert (HIN0 : 0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B (lx_ly cx) (lx_S cx)))
  by (intros Hp; destruct Hcase as [[Hz _]|[_ Hin]]; [lia | exact Hin]).
destruct (lf_window B cx _ _ _ _ _ 0 (lx_n cx) HB HAR (fun i _ => eq_refl) HIN0 ltac:(lia) Hn0 ltac:(lia))
  as (_ & Hp4096 & Hpcl & _).
assert (Hsp0 : 0 <= lx_sp0 cx - LF_FRAME /\ lx_sp0 cx <= 2 ^ 47) by (unfold lx_sp0, LF_FRAME; lia).
(* ---- the prologue, up to beqz s1 at 0x80950 ---- *)
pose proof (fmw_entry_sb B FB (lx_W cx) (lx_ly cx) (lx_S cx) (lx_regs cx) (lx_mem cx) (lx_md cx) LLVMF_STK A_LLVMF 64 HAR Hstk
  ltac:(lia) Hpres ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B LLVMF_STK FM_PSTAT_FP _ _ _ _ _ _ _ HAP) as HJ.
set (E := Ereg (lx_regs cx) [Z_to_bv 64 FMW_SB]) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ (lx_regs cx))
  by (subst E; rewrite (ew_Ereg_nat (lx_regs cx) _ 2 2%bv eq_refl); reflexivity).
assert (EZ10 : ew E 10 = w64 (lx_p cx)) by (subst E; rewrite (ew_Ereg_nat (lx_regs cx) _ 10 10%bv eq_refl); exact H10).
assert (EZ11 : ew E 11 = w64 (lx_n cx)) by (subst E; rewrite (ew_Ereg_nat (lx_regs cx) _ 11 11%bv eq_refl); exact H11).
assert (EZ32 : ew E 32 = w64 FMW_SB) by (subst E; exact (ew_Ereg_extra (lx_regs cx) _ 0)).
unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 A_LLVMF).
unfold fmw_entry_ss in HS.
aj_run fmw_tbl_llvmf_ok HS HJ.
{ awr_ok_tac. exact Usp. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (SB1 : same_below (lx_mem cx) (ms_mem ms1) alloc_ceiling).
{ apply (same_below_frame E _ (lx_mem cx) (ms_mem ms1) alloc_ceiling HF); [|lia].
  cbn [ss_mem]. unfold fmw_stack_region, fmw_got_region, fmw_bcell_region.
  apply Forall_cons; [right; cbn [YP09.r_base YP09.r_wlo base_val]; rewrite Usp; lia|].
  apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
clear HF HFr HG.
assert (U11 : U E (SOff 11 0) = lx_n cx) by (apply U_atom; [exact EZ11 | lia]).
assert (UZ : U E (SLit 0) = 0) by (apply U_lit; lia).
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 11 0) (b := SLit 0); [exact HS | intros Hbr HS2 | intros Hbr HS2];
  rewrite ?branch_eq_U, U11, UZ in Hbr; clear HS.
- (* size = 0: 0x80978 s3 := 0 *)
  apply Z.eqb_eq in Hbr.
  aj_run_to fmw_tbl_llvmf_ok HS2 HJ LF_P0.
  { awr_ok_tac. all: exact Usp. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (SB2 : same_below (ms_mem ms1) (ms_mem ms2) alloc_ceiling).
  { match goal with H : frame_of _ ?rs (ms_mem ms1) (ms_mem ms2) |- _ =>
      apply (same_below_frame E rs (ms_mem ms1) (ms_mem ms2) alloc_ceiling H); [|lia] end.
    lf_rs_tac Usp. }
  assert (HFR : lf_frame cx (lx_W cx) (ms_mem ms2)) by lf_frame_tac HS2.
  pose proof (fmw_reg_off _ E _ ms2 2%bv 2 (-64) _ HS2 ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
  pose proof (lf_reg_ew _ _ _ ms2 9%bv 11 _ HS2 ltac:(vm_compute; reflexivity) EZ11) as R9.
  pose proof (lf_reg_ew _ _ _ ms2 10%bv 10 _ HS2 ltac:(vm_compute; reflexivity) EZ10) as R10.
  pose proof (lf_reg_ew _ _ _ ms2 21%bv 32 _ HS2 ltac:(vm_compute; reflexivity) EZ32) as R21.
  pose proof (fmw_reg_lit _ E _ ms2 19%bv 0 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R19.
  pose proof (lf_kept_env _ E _ ms2 (lx_regs cx) (lx_regs cx) [Z_to_bv 64 FMW_SB] lf_X (kept_refl _ _) HS2
    ltac:(vm_compute; reflexivity) (fun n _ => eq_refl)) as KF.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H (lx_W cx)) E _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 LF_P0) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs LF_P0 (ms_regs ms2) (ms_mem ms2) mm).
  apply (K0 (lx_ly cx) (lx_S cx) _ _ _ _ 0).
  apply (lf_P0_mk cx (ms_regs ms2) (ms_mem ms2) _ HB HJ HFR (same_below_trans _ _ _ _ SB1 SB2)).
  + unfold spZ at 1. rewrite R2. unfold lx_sp0, LF_FRAME. lia.
  + exact KF.
  + exact R21.
  + exact R9.
  + exact R10.
  + rewrite R19. unfold lx_k. rewrite Hbr. reflexivity.
- (* size > 0: the shadow check of data[0], k := min (data[0], size - 1) *)
  apply Z.eqb_neq in Hbr.
  assert (Hnp : 0 < lx_n cx) by lia.
  pose proof (HIN0 Hnp) as Hin.
  aj_run_to fmw_tbl_llvmf_ok HS2 HJ 0x80954.
  { awr_ok_tac. all: exact Usp. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  assert (SB2 : same_below (ms_mem ms1) (ms_mem ms2) alloc_ceiling).
  { match goal with H : frame_of _ ?rs (ms_mem ms1) (ms_mem ms2) |- _ =>
      apply (same_below_frame E rs (ms_mem ms1) (ms_mem ms2) alloc_ceiling H); [|lia] end.
    lf_rs_tac Usp. }
  assert (HFR2 : lf_frame cx (lx_W cx) (ms_mem ms2)) by lf_frame_tac HS2.
  pose proof (fmw_reg_off _ E _ ms2 2%bv 2 (-64) _ HS2 ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as P2.
  pose proof (lf_reg_ew _ _ _ ms2 9%bv 11 _ HS2 ltac:(vm_compute; reflexivity) EZ11) as P9.
  pose proof (lf_reg_ew _ _ _ ms2 10%bv 10 _ HS2 ltac:(vm_compute; reflexivity) EZ10) as P10.
  pose proof (lf_reg_ew _ _ _ ms2 21%bv 32 _ HS2 ltac:(vm_compute; reflexivity) EZ32) as P21.
  pose proof (lf_kept_env _ E _ ms2 (lx_regs cx) (lx_regs cx) [Z_to_bv 64 FMW_SB] lf_X (kept_refl _ _) HS2
    ltac:(vm_compute; reflexivity) (fun n _ => eq_refl)) as KB.
  pose proof (same_below_trans _ _ _ _ SB1 SB2) as SBB.
  pose proof HJ as (HAR2 & _).
  (* data[0] *)
  assert (Hlen : (0 < length (lx_dl cx))%nat) by (unfold lx_dl; rewrite length_map; unfold lx_n in Hnp; lia).
  destruct (Hgarr 0%nat Hlen) as (Vd & Hdr).
  rewrite Z.add_0_r in Vd.
  set (d0 := nth 0 (lx_dl cx) 0) in *.
  pose proof (val_mem_below (w_H (lx_W cx)) (lx_mem cx) (ms_mem ms2) alloc_ceiling (lx_p cx) 1 d0 SBB
    ltac:(lia) ltac:(cbn; lia) Vd) as Vd2.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H (lx_W cx)) E _ ms2 HS2 eq_refl). cbn [ss_pc].
  clear HS2.
  pose proof (lfB_entry (lx_W cx) (ms_mem ms2) (ms_regs ms2) (lx_p cx) d0 P10 P21 ltac:(lia) Hdr Vd2) as HS.
  set (EB := Ereg (ms_regs ms2) [Z_to_bv 64 d0]) in HS.
  assert (SHOK : sh_ok tfibsegs (SOff 21 0) LF_SH EB
      (rdW (lx_W cx) (ms_mem (mkst (ms_regs ms2) (Z_to_bv 64 0x80954) (ms_mem ms2) (seg_rom tfibsegs))))).
  { constructor; [|constructor]. cbn [ms_mem].
    apply (shent_ok_of_block tfibsegs B LAWS _ _ _ _ _ EB (SOff 21 0) 10 (lx_p cx) (lx_n cx) 0 1 HAR2 Hin).
    - apply U_atom; [unfold EB; rewrite (ew_Ereg_nat _ _ 21 21%bv eq_refl); exact P21 | unfold SHADOW_OFF; lia].
    - apply U_atom; [unfold EB; rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact P10 | lia].
    - lia.
    - unfold req_size. destruct (lx_n cx =? 0); lia. }
  change (ms_mem ms2) with (ms_mem (mkst (ms_regs ms2) (Z_to_bv 64 0x80954) (ms_mem ms2) (seg_rom tfibsegs))) in HJ.
  aj_run_to_tok fmw_tbl_llvmf_ok HS HJ SHOK fmw_Bspan LF_P0.
  { awr_ok_tac. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
  lazymatch type of HS with st_ok _ ?Ex _ _ => set (E1 := Ex) in HS, SHOK end.
  assert (AG : forall n, (n < 33)%nat -> ew E1 n = ew EB n)
    by (intros n0 Hn33; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
  assert (AGr : forall (r : bv 5) n, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E1 n = getr (ms_regs ms2) r)
    by (intros r n0 Hn0' Hr; rewrite (AG n0 ltac:(lia)); unfold EB; exact (ew_Ereg_nat _ _ n0 r Hr)).
  assert (SB3 : same_below (ms_mem ms2) (ms_mem ms3) (2 ^ 64)).
  { match goal with H : frame_of _ ?rs (ms_mem ms2) (ms_mem ms3) |- _ =>
      apply (same_below_frame EB rs (ms_mem ms2) (ms_mem ms3) (2 ^ 64) H); [|lia] end.
    lf_rs_tac Usp. }
  assert (EZ9' : ew E1 9 = w64 (lx_n cx)) by (rewrite (AGr 9%bv 9%nat ltac:(lia) eq_refl); exact P9).
  assert (EZd : ew E1 32 = Z_to_bv 64 d0) by (rewrite (AG 32%nat ltac:(lia)); unfold EB; exact (ew_Ereg_extra _ _ 0)).
  assert (U9 : U E1 (SOff 9 (-1)) = lx_n cx - 1)
    by (rewrite (U_atom_off E1 9 (lx_n cx) (-1) EZ9' ltac:(lia) ltac:(lia)); lia).
  assert (Ud : U E1 (SOff 32 0) = d0) by (apply U_atom; [exact EZd | lia]).
  assert (Hk : lx_k cx = Z.min d0 (lx_n cx - 1)) by (unfold lx_k; rewrite (proj2 (Z.eqb_neq _ _) Hbr); reflexivity).
  eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 9 (-1)) (b := SOff 32 0); [exact HS | intros Hb2 HS4 | intros Hb2 HS4];
    rewrite ?branch_ltu_U, U9, Ud in Hb2; clear HS.
  + (* size - 1 < data[0]: k = size - 1 *)
    apply Z.ltb_lt in Hb2.
    aj_run_to fmw_tbl_llvmf_ok HS4 HJ LF_P0.
    { awr_ok_tac. }
    lazymatch type of HS4 with context [restrict _ ?m] => rename m into ms4 end.
    assert (SB4 : same_below (ms_mem ms3) (ms_mem ms4) (2 ^ 64)).
    { match goal with H : frame_of _ ?rs (ms_mem ms3) (ms_mem ms4) |- _ =>
        apply (same_below_frame E1 rs (ms_mem ms3) (ms_mem ms4) (2 ^ 64) H); [|lia] end.
      lf_rs_tac Usp. }
    pose proof (same_below_trans _ _ _ _ SB3 SB4) as SB24.
    pose proof (lf_reg_ew _ _ _ ms4 2%bv 2 _ HS4 ltac:(vm_compute; reflexivity) (AGr 2%bv 2%nat ltac:(lia) eq_refl)) as Q2.
    pose proof (lf_reg_ew _ _ _ ms4 9%bv 9 _ HS4 ltac:(vm_compute; reflexivity) EZ9') as Q9.
    pose proof (lf_reg_ew _ _ _ ms4 10%bv 10 _ HS4 ltac:(vm_compute; reflexivity)
      (eq_trans (AGr 10%bv 10%nat ltac:(lia) eq_refl) P10)) as Q10.
    pose proof (lf_reg_ew _ _ _ ms4 21%bv 21 _ HS4 ltac:(vm_compute; reflexivity)
      (eq_trans (AGr 21%bv 21%nat ltac:(lia) eq_refl) P21)) as Q21.
    pose proof (fmw_reg_off _ E1 _ ms4 19%bv 9 (-1) (lx_n cx) HS4 ltac:(vm_compute; reflexivity)
      ltac:(rewrite EZ9'; unfold w64; apply unsigned_lit_small; lia) ltac:(lia)) as Q19.
    pose proof (lf_kept_env _ E1 _ ms4 (lx_regs cx) (ms_regs ms2) [Z_to_bv 64 d0] lf_X KB HS4
      ltac:(vm_compute; reflexivity) (fun n Hn => AG n ltac:(lia))) as KF.
    rewrite (st_ok_restrict_mkst tfibsegs (w_H (lx_W cx)) E1 _ ms4 HS4 eq_refl). cbn [ss_pc].
    change (mkCfg (mkst (ms_regs ms4) (Z_to_bv 64 LF_P0) (ms_mem ms4) (seg_rom tfibsegs)) ?mm)
      with (cfg_at tfibsegs LF_P0 (ms_regs ms4) (ms_mem ms4) mm).
    apply (K0 (lx_ly cx) (lx_S cx) _ _ _ _ 0).
    apply (lf_P0_mk cx (ms_regs ms4) (ms_mem ms4) _ HB HJ
      (lf_frame_below cx _ _ _ SB24 (proj1 Hsp0) (proj2 Hsp0) HFR2)
      (same_below_trans _ _ _ _ SBB (same_below_mono _ _ (2 ^ 64) alloc_ceiling SB24 ltac:(lia)))).
    * unfold spZ at 1. rewrite Q2, P2. unfold lx_sp0, LF_FRAME. lia.
    * exact KF.
    * exact Q21.
    * exact Q9.
    * exact Q10.
    * apply bv_eq. rewrite Q19, Hk. unfold w64. rewrite unsigned_lit_small by lia. lia.
  + (* data[0] <= size - 1: k = data[0] *)
    apply Z.ltb_ge in Hb2.
    aj_run_to fmw_tbl_llvmf_ok HS4 HJ LF_P0.
    { awr_ok_tac. }
    lazymatch type of HS4 with context [restrict _ ?m] => rename m into ms4 end.
    assert (SB4 : same_below (ms_mem ms3) (ms_mem ms4) (2 ^ 64)).
    { match goal with H : frame_of _ ?rs (ms_mem ms3) (ms_mem ms4) |- _ =>
        apply (same_below_frame E1 rs (ms_mem ms3) (ms_mem ms4) (2 ^ 64) H); [|lia] end.
      lf_rs_tac Usp. }
    pose proof (same_below_trans _ _ _ _ SB3 SB4) as SB24.
    pose proof (lf_reg_ew _ _ _ ms4 2%bv 2 _ HS4 ltac:(vm_compute; reflexivity) (AGr 2%bv 2%nat ltac:(lia) eq_refl)) as Q2.
    pose proof (lf_reg_ew _ _ _ ms4 9%bv 9 _ HS4 ltac:(vm_compute; reflexivity) EZ9') as Q9.
    pose proof (lf_reg_ew _ _ _ ms4 10%bv 10 _ HS4 ltac:(vm_compute; reflexivity)
      (eq_trans (AGr 10%bv 10%nat ltac:(lia) eq_refl) P10)) as Q10.
    pose proof (lf_reg_ew _ _ _ ms4 21%bv 21 _ HS4 ltac:(vm_compute; reflexivity)
      (eq_trans (AGr 21%bv 21%nat ltac:(lia) eq_refl) P21)) as Q21.
    pose proof (lf_reg_ew _ _ _ ms4 19%bv 32 _ HS4 ltac:(vm_compute; reflexivity) EZd) as Q19.
    pose proof (lf_kept_env _ E1 _ ms4 (lx_regs cx) (ms_regs ms2) [Z_to_bv 64 d0] lf_X KB HS4
      ltac:(vm_compute; reflexivity) (fun n Hn => AG n ltac:(lia))) as KF.
    rewrite (st_ok_restrict_mkst tfibsegs (w_H (lx_W cx)) E1 _ ms4 HS4 eq_refl). cbn [ss_pc].
    change (mkCfg (mkst (ms_regs ms4) (Z_to_bv 64 LF_P0) (ms_mem ms4) (seg_rom tfibsegs)) ?mm)
      with (cfg_at tfibsegs LF_P0 (ms_regs ms4) (ms_mem ms4) mm).
    apply (K0 (lx_ly cx) (lx_S cx) _ _ _ _ 0).
    apply (lf_P0_mk cx (ms_regs ms4) (ms_mem ms4) _ HB HJ
      (lf_frame_below cx _ _ _ SB24 (proj1 Hsp0) (proj2 Hsp0) HFR2)
      (same_below_trans _ _ _ _ SBB (same_below_mono _ _ (2 ^ 64) alloc_ceiling SB24 ltac:(lia)))).
    * unfold spZ at 1. rewrite Q2, P2. unfold lx_sp0, LF_FRAME. lia.
    * exact KF.
    * exact Q21.
    * exact Q9.
    * exact Q10.
    * rewrite Q19, Hk. unfold w64. f_equal. lia.
Qed.
End X.
