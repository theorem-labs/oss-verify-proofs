From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import AgCf readings_c_cf names_c_cf.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB names_c readings_c KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import names.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free (agreement) twin of names_holds (names.v): the same proof in SRcf form, with readings taken
   through readings_contract_cf. *)
Section Pcf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis ERR : errno_low B.
Let MR := aa_MR API.

Theorem names_cf_holds : (forall fx', @readings_contract_cf fx' rc B API) -> names_contract_cf B API.
Proof.
  intros READ. unfold names_contract_cf.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail SEG PRE INIT TS FRM MI GC CT CU HT HU T4 U4 LT LU IMG DT DU
    DP1 DP2 DP3 OT OU LED RES CAP BY0 BYQ.
  pose proof alloc_ceiling_val as Hacv.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  assert (EK : NAMES_K = 8432) by reflexivity. rewrite EK in *.
  assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  pose proof (zr_word (reg_get regs 2)) as Rsp. unfold inr64 in Rsp. rewrite SP in Rsp.
  assert (STK : stk rsegs mem (spZ regs - 8432) (spZ regs)).
  { apply stk_of_writable; [lia | unfold spZ in *; lia |].
    intros a Ha. rewrite <- SEG. apply HWS. exact Ha. }
  eapply (evt_SRcf_canon B); [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (nm_pro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (spZ regs - 8432)).
    - exact STK.
    - rewrite SP. lia. }
  intros ms1 (can & (m1 & Ecan & FR & MU1 & WM1) & EQV). subst can.
  apply eqv_shape in EQV as [Ems1 XR1]. rewrite Ems1.
  set (regs1 := ms_regs ms1) in *.
  rewrite SP in MU1, FR.
  assert (R1 : getr regs1 1 = Z_to_bv 64 0x13e24) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (S16 : bv_unsigned (getr regs1 2) = spZ regs - 16).
  { rewrite <- (getr_eqv _ _ XR1).
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -16)) = spZ regs - 16).
    rewrite SP. rewrite (inr64_unsigned_lit _) by (unfold inr64; lia). lia. }
  assert (R12 : bv_unsigned (getr regs1 12) = spZ regs - 16).
  { rewrite <- (getr_eqv _ _ XR1).
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -16)) = spZ regs - 16).
    rewrite SP. rewrite (inr64_unsigned_lit _) by (unfold inr64; lia). lia. }
  assert (R10 : getr regs1 10 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R11 : getr regs1 11 = getr regs 11) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  assert (R4 : getr regs1 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
  unfold off_stack in DT, DU.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in DT, DU.
  assert (HM1 : aa_MR API L A m1 md).
  { apply (MR_high B API L A mem m1 md _ HM MU1). intros x Hx. apply outside_one. lia. }
  destruct (rw_cells_head8 m1 _ _ _ FR) as [RPB RPW].
  replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
  eapply SRcf_bind.
  { apply (READ fx L A regs1 m1 md b tb ts ub us Lam peak cnt fail (Z_to_bv 64 0)).
    - exact SEG.
    - unfold call_pre_k. unfold spZ at 1 2 3 4 5. rewrite S16.
      split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite R1; apply ret_ok_even; vm_compute; reflexivity|].
      split; [Z.div_mod_to_equations; lia|].
      split; [unfold READINGS_KB, ALLOC_STACK; lia|].
      split; [lia|].
      split.
      { intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG. apply HWS.
        unfold READINGS_KB, ALLOC_STACK in Ha. lia. }
      split; [rewrite R4; exact HTP|].
      split.
      { intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG. apply HER. exact Ha. }
      intros H. rewrite INIT in H. discriminate.
    - exact INIT.
    - rewrite R12. change (bv_unsigned (getr regs 2)) with (spZ regs) in TS. lia.
    - exact FRM.
    - apply (ro_agree_munch _ mem m1 MI MU1). intros x Hx. apply outside_one. lia.
    - apply (guard_cells_munch B API L A mem md m1 _ HM GC MU1). intros x Hx. apply outside_one. lia.
    - rewrite R10. eapply cstr_munch; [exact CT | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I].
    - rewrite R11. eapply cstr_munch; [exact CU | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I].
    - rewrite R10. exact HT.
    - rewrite R11. exact HU.
    - rewrite R10. exact T4.
    - rewrite R11. exact U4.
    - exact LT.
    - exact LU.
    - apply (img_strings_keep mem m1 MI); [|exact IMG].
      apply (ro_agree_munch _ mem m1 MI MU1). intros x Hx. apply outside_one. lia.
    - unfold off_stack. rewrite S16, R10. unfold READINGS_KB, ALLOC_STACK. lia.
    - unfold off_stack. rewrite S16, R11. unfold READINGS_KB, ALLOC_STACK. lia.
    - rewrite R12. replace (spZ regs - 16) with (spZ regs + -16) by lia. exact RPB.
    - rewrite R12. replace (spZ regs - 16) with (spZ regs + -16) by lia. exact RPW.
    - rewrite S16, R12. lia.
    - rewrite R10, R11, R12. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - eapply ledger_munch; [exact HM | exact LED | exact MU1 | intros x Hx; apply outside_one; lia].
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' POST.
  destruct POST as (fx2 & L' & A' & regs2 & mem2 & md' & res & -> & FRM2 & INIT2 & BP & WR2 & RES10 & CT2 & CU2 &
    ARMS & SLOTS).
  rewrite R12 in BP, WR2.
  pose proof BP as (HM2 & HWF2 & HBD2 & RP2 & HMD & HBL & HBB & HFR & HSC & RA2 & GK2).
  destruct (mr_model _ _ (aa_laws API) L' A' mem2 md' HM2) as (Hh2 & Hl2 & _).
  assert (CS : forall k, callee_saved k -> getr regs2 (Z_to_bv 5 k) = getr regs1 (Z_to_bv 5 k)) by exact RP2.
  assert (S2 : bv_unsigned (reg_get regs2 2) = spZ regs - 16).
  { change (bv_unsigned (getr regs2 (Z_to_bv 5 2)) = spZ regs - 16).
    rewrite (CS 2 ltac:(unfold callee_saved; lia)). exact S16. }
  rewrite R10 in CT2. rewrite R11 in CU2.
  assert (FR2 : rw_cells rsegs mem2 (spZ regs - 8) [C8 (reg_get regs 1)]).
  { assert (FR8 : rw_cells rsegs m1 (spZ regs - 8) [C8 (reg_get regs 1)]).
    { pose proof (rw_cells_tail1 _ _ _ _ FR) as T. cbn [csize Z.of_nat] in T.
      replace (spZ regs - 8) with (spZ regs + -16 + 8) by lia. exact T. }
    apply (rw_cells_keep m1 mem2 _ _ FR8). intros a Ha. cbn in Ha.
    rewrite <- SEG. apply HFR.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho). lia.
    + intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
    + unfold scratch_k, spZ. rewrite S16. unfold errno_low in ERR. lia.
    + unfold rd_writes, stat_writes, G_LIVE, G_COUNT, G_FAIL. lia. }
  rewrite R1.
  eapply (evt_SRcf_canon B); [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (nm_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 (reg_get regs 1)).
    rewrite S2. replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia. exact FR2. }
  intros ms3 (can & Ecan & EQV). subst can.
  apply eqv_shape in EQV as [Ems3 XR3]. rewrite Ems3.
  apply SRcf_ret. unfold names_post.
  exists fx2, L', A', (ms_regs ms3), mem2, md', res.
  split; [change (ret_pc (reg_get regs 1)) with (ret_pc (getr regs 1)); rewrite (ret_pc_ok _ HRA); rewrite SEG; reflexivity|].
  split; [exact FRM2|]. split; [exact INIT2|].
  split.
  { eapply (bpost_push16 B API L A regs mem md m1 regs1 L' A' regs2 mem2 md' (ms_regs ms3)).
    - exact SEG.
    - exact HM.
    - unfold NAMES_K, READINGS_KB, ALLOC_STACK. exact HWS.
    - unfold NAMES_K, READINGS_KB, ALLOC_STACK. lia.
    - exact H63.
    - exact S16.
    - replace (spZ regs - 16) with (spZ regs + -16) by lia. exact MU1.
    - rewrite SEG. exact WM1.
    - exact BP.
    - exact WR2.
    - intros r Hr. rewrite <- (getr_eqv _ _ XR3 (Z_to_bv 5 r)). unfold callee_saved in Hr.
      assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                   r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct HC as [-> | HC].
      + change (Z_to_bv 64 (bv_unsigned (reg_get regs2 2) + 16) = getr regs (Z_to_bv 5 2)).
        rewrite S2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ.
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      + assert (CR : callee_saved r) by (unfold callee_saved; lia).
        transitivity (getr regs2 (Z_to_bv 5 r)).
        { destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
            reflexivity. }
        rewrite (CS r CR). rewrite <- (getr_eqv _ _ XR1).
        destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
          reflexivity. }
  split.
  { rewrite <- (getr_eqv _ _ XR3). exact RES10. }
  split; [exact CT2|]. split; [exact CU2|]. split; [|exact SLOTS].
  destruct ARMS as [(E1 & E2 & E3 & _) | [(E1 & E2 & E3 & E4 & _) | (E1 & E2 & E3 & E4 & _)]].
  - left. exact (conj E1 (conj E2 E3)).
  - right. left. exact (conj E1 (conj E2 (conj E3 E4))).
  - right. right. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.

End Pcf.
