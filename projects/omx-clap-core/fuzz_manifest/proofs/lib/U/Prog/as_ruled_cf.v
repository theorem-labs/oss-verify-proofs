From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import AgCf names_c_cf as_ruled_c_cf.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem expected_c KindB.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB names_c as_ruled_c KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import as_ruled.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free (agreement) twin of as_ruled_holds (as_ruled.v): the same proof in SRcf form, with names taken
   through names_contract_cf. *)
Section Pcf.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis ERR : errno_low B.
Hypothesis GS : guard_syms B.

Theorem as_ruled_cf_holds : (forall fx', @names_contract_cf fx' rc B API) -> expected_contract -> as_ruled_contract_cf B API.
Proof.
  intros NAMES EXP. unfold as_ruled_contract_cf.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail SEG PRE INIT TS FRM RA GC CT CU HT HU T4 U4 LT LU IMG DT DU
    OT OU LG QT RES CAP BY0 BYQ.
  pose proof CT as (_ & _ & CTa). pose proof CU as (_ & _ & CUa).
  pose proof alloc_ceiling_val as Hacv.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  assert (EK : AS_RULED_K = 8464%Z) by reflexivity. rewrite EK in *.
  assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  pose proof (zr_word (reg_get regs 2)) as Rsp. unfold inr64 in Rsp. rewrite SP in Rsp.
  assert (STK : stk rsegs mem (spZ regs - 8464) (spZ regs)).
  { apply stk_of_writable; [lia | unfold spZ in *; lia |].
    intros a Ha. rewrite <- SEG. apply HWS. exact Ha. }
  eapply (evt_SRcf_canon B); [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (as_ruled_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (spZ regs - 8464)).
    - exact STK.
    - rewrite SP. lia. }
  intros ms1 (can & (m1 & Ecan & FR & MU1 & WM1) & EQV). subst can.
  apply eqv_shape in EQV as [Ems1 XR1]. rewrite Ems1.
  set (regs1 := ms_regs ms1) in *.
  rewrite SP in MU1, FR.
  assert (RA1 : ro_agree rsegs m1).
  { apply (ro_agree_munch _ mem m1 RA MU1). intros x Hx. apply outside_one. lia. }
  assert (GC1 : guard_cells B m1).
  { apply (guard_cells_munch B mem m1 _ GS GC MU1). intros x Hx. apply outside_one. lia. }
  assert (R1 : getr regs1 1 = Z_to_bv 64 0x13c28) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (S32 : bv_unsigned (getr regs1 2) = spZ regs - 32).
  { rewrite <- (getr_eqv _ _ XR1).
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -32)) = spZ regs - 32).
    rewrite SP. rewrite (inr64_unsigned_lit _) by (unfold inr64; lia). lia. }
  assert (R10 : getr regs1 10 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R11 : getr regs1 11 = getr regs 11) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R4 : getr regs1 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  unfold off_stack in DT, DU.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in DT, DU.
  assert (HM1 : aa_MR API L A m1 md).
  { apply (MR_high B API L A mem m1 md _ HM MU1). intros x Hx. apply outside_one. lia. }
  replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
  eapply SRcf_bind.
  { apply (NAMES fx L A regs1 m1 md b tb ts ub us Lam peak cnt fail).
    - exact SEG.
    - unfold call_pre_k. unfold spZ at 1 2 3 4 5. rewrite S32.
      split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite R1; apply ret_ok_even; vm_compute; reflexivity|].
      split; [Z.div_mod_to_equations; lia|].
      split; [unfold NAMES_K, READINGS_KB, ALLOC_STACK; lia|].
      split; [lia|].
      split.
      { intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG. apply HWS.
        unfold NAMES_K, READINGS_KB, ALLOC_STACK in Ha. lia. }
      split; [rewrite R4; exact HTP|].
      split.
      { intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG. apply HER. exact Ha. }
      intros H. rewrite INIT in H. discriminate.
    - exact INIT.
    - rewrite S32. change (bv_unsigned (getr regs 2)) with (spZ regs) in TS. lia.
    - exact FRM.
    - exact RA1.
    - exact GC1.
    - rewrite R10. eapply cstr_munch; [exact CT | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I].
    - rewrite R11. eapply cstr_munch; [exact CU | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I].
    - rewrite R10. exact HT.
    - rewrite R11. exact HU.
    - rewrite R10. exact T4.
    - rewrite R11. exact U4.
    - exact LT.
    - exact LU.
    - exact (img_strings_keep mem m1 RA RA1 IMG).
    - unfold off_stack. rewrite S32, R10. unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - unfold off_stack. rewrite S32, R11. unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - unfold off_stack. rewrite S32. unfold NAMES_K, READINGS_KB, ALLOC_STACK, PREFIX_LC_STR. left. lia.
    - unfold off_stack. rewrite S32. unfold NAMES_K, READINGS_KB, ALLOC_STACK, PREFIX_UC_STR. left. lia.
    - unfold off_stack. rewrite S32. unfold NAMES_K, READINGS_KB, ALLOC_STACK, FMT_WHOLE_STR. left. lia.
    - rewrite R10. exact OT.
    - rewrite R11. exact OU.
    - apply (ledger_munch B API L A mem md m1 _ Lam peak cnt fail HM LG MU1). intros x Hx. apply outside_one. lia.
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' POST.
  destruct POST as (fx2 & L' & A' & regs2 & mem2 & md' & res & -> & FRM2 & INIT2 & BP & RES10 & (ts2 & CT2) &
    (us2 & CU2) & ARMS & SLOTS).
  pose proof BP as (HM2 & HWF2 & HBD2 & RP2 & HMD & HBL & HBB & HFR & HSC & RA2 & GK2).
  rewrite SEG in HFR, HSC, RA2.
  destruct (mr_model _ _ (aa_laws API) L' A' mem2 md' HM2) as (Hh2 & Hl2 & _).
  destruct QT as (QF & QC0 & QC1).
  assert (RV : res = names (ManifestMem.zbytes tb) (ManifestMem.zbytes ub)).
  { destruct ARMS as [(Eub & Er & _) | [(_ & Ecf & _) | (_ & _ & Er & _)]].
    - subst ub res. reflexivity.
    - lia.
    - exact Er. }
  assert (CS : forall k, callee_saved k -> getr regs2 (Z_to_bv 5 k) = getr regs1 (Z_to_bv 5 k)) by exact RP2.
  assert (S2 : bv_unsigned (reg_get regs2 2) = spZ regs - 32).
  { change (bv_unsigned (getr regs2 (Z_to_bv 5 2)) = spZ regs - 32).
    rewrite (CS 2 ltac:(unfold callee_saved; lia)). exact S32. }
  assert (Q9 : reg_get regs2 9 = getr regs 10).
  { change (getr regs2 (Z_to_bv 5 9) = getr regs 10). rewrite (CS 9 ltac:(unfold callee_saved; lia)).
    rewrite <- (getr_eqv _ _ XR1). reflexivity. }
  assert (Q8 : reg_get regs2 8 = getr regs 11).
  { change (getr regs2 (Z_to_bv 5 8) = getr regs 11). rewrite (CS 8 ltac:(unfold callee_saved; lia)).
    rewrite <- (getr_eqv _ _ XR1). reflexivity. }
  assert (Q10 : reg_get regs2 10 = Z_to_bv 64 (names (ManifestMem.zbytes tb) (ManifestMem.zbytes ub))).
  { rewrite <- RV. exact RES10. }
  rewrite R10 in CT2. rewrite R11 in CU2.
  destruct (cstr_trim _ _ _ _ CT2) as (sl & CT2' & Lsl). destruct (cstr_trim _ _ _ _ CU2) as (slu & CU2' & Lslu).
  rewrite R1.
  eapply (evt_SRcf_canon B); [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (as_ruled_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2
              (spZ regs - 32 - NAMES_K) tb sl ub slu (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)).
    - rewrite S2. replace (spZ regs - 32) with (spZ regs + -32) by lia.
      apply (rw_cells_keep m1 mem2 _ _ FR). intros a Ha. cbn in Ha.
      apply HFR.
      + left. lia.
      + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho). lia.
      + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
      + unfold scratch_k, spZ. rewrite S32. unfold errno_low in ERR. lia.
      + unfold stat_writes, G_LIVE, G_COUNT, G_FAIL. lia.
    - rewrite Q9. exact CT2'.
    - rewrite Q8. exact CU2'.
    - rewrite Q9. exact T4.
    - rewrite Q8. exact U4.
    - exact LT.
    - lia.
    - exact (prefix_exp_bytes mem2 RA2).
    - exact RA2.
    - rewrite S2. apply stk_of_writable; [unfold NAMES_K, READINGS_KB, ALLOC_STACK; lia | lia |].
      intros a Ha. apply HSC. left. unfold spZ. rewrite S32. lia.
    - rewrite S2. unfold NAMES_K, READINGS_KB, ALLOC_STACK, EXPECTED_K. lia.
    - unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - rewrite S2. lia.
    - unfold off_stack. rewrite S2, Q9. unfold NAMES_K, READINGS_KB, ALLOC_STACK, EXPECTED_K. lia.
    - unfold off_stack. rewrite S2, Q8. unfold NAMES_K, READINGS_KB, ALLOC_STACK, EXPECTED_K. lia.
    - unfold off_stack. rewrite S2. unfold EXPECTED_K, expected_c.PREFIX_LC_STR. left. lia.
    - exact Q10.
    - exact EXP. }
  intros ms3 (can & (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
    Ecan & MU3 & WM3 & RA3 & CT3 & CU3) & EQV).
  subst can. apply eqv_shape in EQV as [Ems3 XR3]. rewrite Ems3.
  apply SRcf_ret. unfold as_ruled_post.
  exists fx2, L', A', (ms_regs ms3), m3, md'.
  split; [rewrite (ret_pc_ok _ HRA); rewrite SEG; reflexivity|].
  split; [exact FRM2|]. split; [exact INIT2|].
  split.
  { eapply (bpost_sandwich B API 8464 NAMES_K stat_writes L A regs mem md m1 regs1 L' A' regs2 mem2 md' m3
      (ms_regs ms3)).
    - exact HM.
    - exact HWS.
    - exact HAC.
    - exact H63.
    - unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - exact S32.
    - intros a Ha. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Ha. lia.
    - exact (in_img_low B SEG).
    - replace (spZ regs - 32) with (spZ regs + -32) by lia. exact MU1.
    - rewrite SEG. exact WM1.
    - exact BP.
    - exact MU3.
    - rewrite SEG. exact WM3.
    - rewrite S2. unfold EXPECTED_K. lia.
    - rewrite S2. lia.
    - exact GS.
    - rewrite SEG. exact RA3.
    - intros r Hr. rewrite <- (getr_eqv _ _ XR3 (Z_to_bv 5 r)). unfold callee_saved in Hr.
      assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                   r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | HC]]]]]].
      + change (Z_to_bv 64 (bv_unsigned (reg_get regs2 2) + 32) = getr regs (Z_to_bv 5 2)).
        rewrite S2. replace (spZ regs - 32 + 32) with (spZ regs) by lia. unfold spZ.
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      + transitivity (getr regs2 (Z_to_bv 5 3)); [reflexivity|].
        rewrite (CS 3 ltac:(unfold callee_saved; lia)). rewrite <- (getr_eqv _ _ XR1). reflexivity.
      + transitivity (getr regs2 (Z_to_bv 5 4)); [reflexivity|].
        rewrite (CS 4 ltac:(unfold callee_saved; lia)). rewrite <- (getr_eqv _ _ XR1). reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + assert (HR : 19 <= r <= 27) by lia.
        transitivity (getr regs2 (Z_to_bv 5 r)).
        { destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; reflexivity. }
        rewrite (CS r ltac:(unfold callee_saved; lia)). rewrite <- (getr_eqv _ _ XR1).
        destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; reflexivity. }
  split; [exists sl; rewrite <- Q9; exact CT3|].
  split; [exists slu; rewrite <- Q8; exact CU3|].
  split; [|exact SLOTS].
  destruct ARMS as [(Eub & Er & AW2) | [(_ & Ecf & _) | (Nub & Ncf & Er & AW2)]].
  - left. split; [exact Eub|]. rewrite QF in AW2.
    apply (ledger_munch B API L' A' mem2 md' m3 _ _ _ _ _ HM2 AW2 MU3). intros x Hx. apply outside_one. rewrite S2.
    unfold EXPECTED_K. lia.
  - lia.
  - right. split; [exact Nub|]. rewrite QF in AW2. rewrite (Z.mod_small (cnt + 1) (2 ^ 64)) in AW2 by lia.
    apply (ledger_munch B API L' A' mem2 md' m3 _ _ _ _ _ HM2 AW2 MU3). intros x Hx. apply outside_one. rewrite S2.
    unfold EXPECTED_K. lia.
Qed.

End Pcf.
