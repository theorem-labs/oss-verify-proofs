(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_llvmfSR.v at a working branch 79d8c0f1b8f, relocated A->B:
   imports per a Theorem Labs lane's core rule (a working branch 305d8b1527f: lib.A AXxx -> lib.ReusableB YXxx when listed in its
   ReusableB list, other lib.A -> lib.B, FMupoison stays lib.A); every image numeral re-derived from B's listing
   (fuzz_manifest.objdump.txt / nm.txt of the asan-ubsan pin). *)
(* LLVMFuzzerTestOneInput 0x8097c, segment R (fuzz_manifest.c:320): from 0x80b74 (lf_R), `mv a0, zero`, the epilogue
   (ra, s0..s6 back from their slots, sp back up by 64) and `ret` to RA_LLVMF; the walk's post (llvmf_post). *)
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

(* ---- the epilogue's symbolic state (0x80b74): every register its own atom, atom 32 the shadow base, atoms 33..40 the
   8 slot values (lf_saved_regs order: ra, s0..s6), the frame [sp, sp + 64) writable ---- *)
Definition lf_vals (cx : lfx) : list Z := map (fun r => bv_unsigned (getr (lx_regs cx) (Z_to_bv 5 r))) lf_saved_regs.
Definition lf_epi_ss (pc : Z) : sstate :=
  mkSS pc sr_atoms [fmw_frame_region LF_FRAME lf_saved_offs] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
(* the callee-saved registers after the epilogue: sp back up by the frame, s0 s1 s2..s6 the slot atoms, the rest (gp, tp,
   s7..s11) their own atoms *)
Definition lf_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 LF_FRAME
  | 8 => SOff 34 0
  | 9 => SOff 35 0
  | z => if (18 <=? z) && (z <=? 22) then SOff (Z.to_nat (z + 18)) 0 else SOff (Z.to_nat z) 0
  end.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.

Lemma lf_slot : forall cx regs' j (r : bv 5), nth_error lf_saved_regs j = Some (bv_unsigned r) ->
  sv_denot (fmw_env regs' (lf_vals cx)) (SOff (33 + j) 0) = getr (lx_regs cx) r.
Proof.
intros cx regs' j r Hr. rewrite fmw_SOff0, fmw_env_extra.
- assert (Ev : nth j (lf_vals cx) 0 = bv_unsigned (getr (lx_regs cx) r)).
  { apply nth_error_nth. unfold lf_vals. rewrite (map_nth_error _ j _ Hr). cbv beta.
    rewrite Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Ev. apply Z_to_bv_bv_unsigned.
- unfold lf_vals. rewrite length_map. apply nth_error_Some. rewrite Hr. discriminate.
Qed.
Lemma lf_reg_slot : forall H regs' cx ss ms (q r : bv 5) j,
  st_ok tfibsegs (fmw_env regs' (lf_vals cx)) ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff (33 + j) 0 ->
  nth_error lf_saved_regs j = Some (bv_unsigned r) -> getr (ms_regs ms) q = getr (lx_regs cx) r.
Proof.
intros H regs' cx ss ms q r j HS Hq Hr. rewrite (st_ok_restrict_reg tfibsegs H _ ss ms q HS), Hq.
exact (lf_slot cx regs' j r Hr).
Qed.

(* the epilogue's symbolic state holds at any resume point after the prologue *)
Lemma lf_epi_st : forall cx ly' S' W' regs' mem' md' k pc,
  lf_base B cx -> lf_core B cx ly' S' W' regs' mem' md' k ->
  st_ok tfibsegs (fmw_env regs' (lf_vals cx)) (lf_epi_ss pc)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 pc) mem' (seg_rom tfibsegs))).
Proof.
intros cx ly' S' W' regs' mem' md' k pc (HAP & _) (HJ & HFR & Hsp & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : LLVMF_STK = 32768) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
unfold lx_sp0, LF_FRAME in *.
unfold lf_epi_ss, LF_FRAME. apply fmw_mid_entry.
- lia.
- lia.
- intros a Ha. apply Hpres. lia.
- unfold lf_vals. rewrite length_map. reflexivity.
- intros j o Ho. destruct (nth_error lf_saved_regs j) as [r|] eqn:Er.
  + assert (Ev : nth j (lf_vals cx) 0 = bv_unsigned (getr (lx_regs cx) (Z_to_bv 5 r))).
    { apply nth_error_nth. unfold lf_vals. rewrite (map_nth_error _ j _ Er). reflexivity. }
    rewrite Ev. split; [|apply u64_range]. rewrite Hsp. exact (HFR j o r Ho Er).
  + exfalso. apply nth_error_None in Er.
    assert (Hj : (j < length lf_saved_offs)%nat) by (apply nth_error_Some; rewrite Ho; discriminate).
    cbn in Er, Hj. lia.
- vm_compute. reflexivity.
- constructor.
- cbn. tauto.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (fmw_env_reg regs' (lf_vals cx) 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs').
  rewrite Hsp. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. reflexivity.
Qed.
End X.

(* the per-register goals of fmw_preserved after the epilogue (lf_expect): sp back up (E2s), a slot atom (lf_slot),
   or a register outside lf_X kept from the entry (HK : kept_from) *)
Ltac lf_cs_cases cx regs' E2s HK :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv [CALLEE_SAVED In] in Hr;
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (lf_expect ?q) = _ =>
    let e := eval vm_compute in (lf_expect q) in change (lf_expect q) with e end;
  first
  [ eapply fmw_sp_back; exact E2s
  | lazymatch goal with |- sv_denot _ (SOff ?n 0) = getr _ ?q =>
      let j := eval vm_compute in (n - 33)%nat in
      exact (lf_slot cx regs' j q ltac:(vm_compute; reflexivity)) end
  | unfold fmw_env; eapply fmw_kept_atom; [exact HK | vm_compute; reflexivity | fmw_cs_side | fmw_notin] ].

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.

(* ---- 0x80b74: a0 := 0, the epilogue, ret ---- *)
Lemma lf_segR : forall cx ly S W regs mem md k, lf_base B cx -> lf_R B cx ly S W regs mem md k ->
  SRr tfibsegs W (cfg_at tfibsegs LF_R regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k HB HR.
destruct HR as (HC & Hk & Hperm & peak' & cnt' & HG & Hcnt).
pose proof (lf_epi_st B cx ly S W regs mem md k LF_R HB HC) as HS.
pose proof HB as (HAP & Hra' & H10 & H11 & Hin & Hga & Hfrs & Hnev & Hbb & HRO & HG0 & Hc0 & Hc1 & Hl0).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct HC as (HJ & HFR & Hsp & HK & H21 & HIN & HRO').
unfold lf_J, lx_sp0, LF_FRAME in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (E2s : bv_unsigned (ew (fmw_env regs (lf_vals cx)) 2) = spZ (lx_regs cx) - 64).
{ rewrite (fmw_env_reg regs _ 2 2%bv eq_refl). change (bv_unsigned (getr regs 2)) with (spZ regs). exact Hsp. }
assert (E2 : bv_unsigned (ew (fmw_env regs (lf_vals cx)) 2) = spZ (lx_regs cx) + -64) by lia.
unfold cfg_at. change (w64 LF_R) with (Z_to_bv 64 LF_R).
aj_run fmw_tbl_llvmf_ok HS HJ.
{ unfold lf_epi_ss; cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64);
    [reflexivity | exact E2 | cbn [fmw_frame_region YP09.r_wlo YP09.r_whi]; unfold LF_FRAME; lia
    | cbn [fmw_frame_region YP09.r_wlo YP09.r_whi]; unfold LF_FRAME; lia | apply awr_ok_nil]. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
pose proof (lf_reg_slot _ regs cx _ ms1 1%bv 1%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as R1.
pose proof (fmw_reg_lit _ _ _ ms1 10%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R10.
assert (SB : same_below mem (ms_mem ms1) alloc_ceiling).
{ unfold lf_epi_ss in HF; cbn [ss_mem] in HF.
  apply (same_below_frame1 _ _ mem (ms_mem ms1) alloc_ceiling HF); [|lia].
  cbn [fmw_frame_region YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
eapply (SRr_ret_at tfibsegs _ fmw_tbl_llvmf_ok fm_wx); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat2.
assert (Hpc : v_jalr (getr (ms_regs ms1) 1) 0 = w64 RA_LLVMF).
{ rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. unfold w64. rewrite <- Hra'. unfold raZ.
  symmetry. apply Z_to_bv_bv_unsigned. }
rewrite Hpc. unfold lf_post, llvmf_post.
eexists ly, S, (ms_regs ms1), (ms_mem ms1), _, k, cnt'.
split; [reflexivity|].
split; [apply (ajournal_materialize tfibsegs B LAWS HSL); exact HJ|].
split; [lia|].
split.
{ apply (fmw_preserved _ _ _ ms1 (lx_regs cx) lf_expect HS); [vm_compute; reflexivity|].
  lf_cs_cases cx regs E2s HK. }
split; [exact R10|].
split; [exact Hperm|].
split.
{ intros i Hi.
  destruct Hin as [(Hn0 & _) | (_ & Hin0)]; [lia|].
  assert (Hin1 : In (lx_p cx, lx_n cx) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin0).
  assert (Hrq : lx_n cx <= req_size (lx_n cx)) by (unfold req_size; destruct (Z.eqb_spec (lx_n cx) 0); lia).
  apply (F2 (lx_p cx) (lx_n cx) i Hin0 Hin1); [lia|].
  intros Hf. apply (blk_img tfibsegs B LAWS _ _ _ _ _ (lx_p cx) (lx_n cx) (lx_p cx + i) HAR Hin0); [lia|].
  exact (pstat_img _ Hf). }
split; [exists peak'; exact (fm_glob_below W mem (ms_mem ms1) _ _ _ _ SB HG)|].
exact Hcnt.
Qed.
End R.
