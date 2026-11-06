From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem LibcNeeds_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestB.
Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger ManifestB names_c readings_c KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import fuzz_malloc_c fuzz_free_c names has_prefixed_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require strlen_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YN03.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan has_prefixed_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import AgCf fuzz_malloc_c_cf fuzz_free_c_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import readings_c_cf readings.
Local Open Scope Z_scope.

(* The cut-free (agreement) twin of readings.rd_core / readings_holds: the same proof in SRcf form, with the
   cut-free contracts of fuzz_malloc and fuzz_free (fuzz_malloc_c_cf.v, fuzz_free_c_cf.v) at the two allocator
   calls. The agreement room at the fuzz_malloc call comes from AgCf.room_ag_of (cap <= CAP_AG, bytes <= 2^29). *)

Section R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis SF : statics_free B (aa_MR API).
Hypothesis SFA : statics_facts B.
Hypothesis CTX : ManifestB.ctx_owned B (aa_MR API).
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BSP : block_slack_present B API.
Hypothesis ERR : errno_low B.
Hypothesis GS : guard_syms B.

Hypothesis STRLEN : LibcNeeds_c.strlen_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis STRS : LibcNeeds_c.strstr_contract.
Hypothesis SCAN : readings_scan_c.readings_scan_contract.
Hypothesis MALLOC : forall fx' : FPState, @fuzz_malloc_contract_cf fx' rc B API.
Hypothesis FREE : forall fx' : FPState, @fuzz_free_contract_cf fx' rc B API.

Theorem rd_core_cf : readings_contract_cf B API.
Proof.
  unfold readings_contract_cf.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail v SEG' PRE INIT RPT FRM RA GC CT CU HT HU T4 U4 LT LU IMG
    OT OU RPB RPW SPRP DJ LED RES CAP BY0 BYT.
  clear SEG'.
  change (getr regs 1) with (reg_get regs 1) in *.
  change (getr regs 10) with (reg_get regs 10) in *.
  change (getr regs 11) with (reg_get regs 11) in *.
  change (getr regs 12) with (reg_get regs 12) in *.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in *.
  unfold off_stack in OT, OU. change (bv_unsigned (getr regs 2)) with (spZ regs) in OT, OU.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hlt. pose proof alloc_ceiling_value as [_ Hmod].
  assert (KB : READINGS_KB = 8400) by reflexivity. assert (AS : ALLOC_STACK = 8192) by reflexivity.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  change (getr regs 1) with (reg_get regs 1) in HRA.
  destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  pose proof RPW as (RP0 & RP8 & _).
  destruct (cstr_trim _ _ _ _ CT) as (st & CTt & Lst).
  destruct (cstr_trim _ _ _ _ CU) as (su & CUt & Lsu).
  destruct (cstr_bound _ _ _ _ CTt) as [Bt0 Bt1].
  destruct (cstr_bound _ _ _ _ CUt) as [Bu0 Bu1].
  pose proof (rd_str_low B API) as rd_str_low. rfeed rd_str_low.
  pose proof (rd_cells_after B API) as rd_cells_after. rfeed rd_cells_after.
  pose proof (rd_stk_after B API) as rd_stk_after. rfeed rd_stk_after.
  pose proof (rd_post_intro B API) as rd_post_intro. rfeed rd_post_intro.
  pose proof (rd_sandwich B API) as rd_sandwich. rfeed rd_sandwich.
  pose proof (rd_str_low L A mem md _ tb st HM HT Bt0 ltac:(lia) Lst) as TLO.
  pose proof (rd_str_low L A mem md _ ub su HM HU Bu0 ltac:(lia) Lsu) as ULO.
  assert (STK : stk rsegs mem (spZ regs - READINGS_KB) (spZ regs)).
  { apply stk_of_writable; [lia | lia |]. intros a Ha. rewrite <- SEG. apply HWS. exact Ha. }
  pose proof (rd_bpost_word B API) as BW. rfeed BW.
  pose proof (rd_cstr_keep B API) as RCK. rfeed RCK.
  pose proof (rd_block_facts B API) as RBF. rfeed RBF.
  pose proof (rd_guards B API) as RG. rfeed RG.
  assert (RPa : alloc_ceiling <= bv_unsigned (reg_get regs 12)) by lia.
  assert (RPb : bv_unsigned (reg_get regs 12) + 8 <= 2 ^ 64) by lia.
  assert (RPc : spZ regs <= bv_unsigned (reg_get regs 12)) by lia.
  assert (TS : spZ regs + 8 <= TASK_SIZE) by lia.
  assert (RK : readings_scan_c.READINGS_K = 2544) by reflexivity.
  assert (RF : readings_scan_c.READINGS_FRAME = 176) by reflexivity.
  assert (HK : has_prefixed_c.HAS_PREFIXED_K = 2368) by reflexivity.
  eapply evt_SRcf_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
    eapply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA |].
    eapply rd_pro with (m := normalize rsegs mem) (lo := spZ regs - READINGS_KB) (ub := ub) (us := su).
    - exact STRLEN.
    - exact (cstr_normalize _ _ _ _ RA CUt).
    - exact (mem_inv_normalize rsegs mem).
    - rewrite SP. apply stk_normalize; [exact STK | lia].
    - rewrite SP. lia.
    - unfold off_stack. rewrite SP. lia.
    - exact LU. }
  intros ms1 (can & (s0 & ARMS & REL & ROS) & EQV).
  destruct ARMS as [(UB & POST) | (UNE & POST)].
  - destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      E & MU & WM & MI' & ST').
    subst s0.
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ REL) as [Ecan HRc]. rewrite Ecan in EQV.
    destruct (rd_back mem (ms_mem can) m' _ RA HRc ROS MU WM) as (MU1 & WM1 & RA1).
    apply eqv_shape in EQV as [Ems1 XR1]. rewrite Ems1.
    rewrite SP in MU1.
    pose proof (rd_rp_final regs (ms_regs ms1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR1) as RP1.
    assert (BPs : bpost B (aa_MR API) READINGS_KB stat_writes L A regs mem md L A (ms_regs ms1) (ms_mem can) md).
    { pose proof (rd_bpost_kindA B API) as KA. rfeed KA.
      apply (KA READINGS_KB stat_writes L A regs mem md (ms_regs ms1) (ms_mem can) [(spZ regs - 176, spZ regs)]
        HM HWF HBD RP1 MU1).
      - rewrite SEG. exact WM1.
      - rewrite SEG. exact RA1.
      - intros x Hx HO. apply not_outside1 in HO. split; [lia | left; unfold scratch_k; lia].
      - intros a Ha. unfold writable_at. rewrite SEG. apply WM1. rewrite <- SEG.
        destruct Ha as [Ha|Ha]; [apply HWS; exact Ha | apply HER; exact Ha]. }
    destruct (BW READINGS_KB L A regs mem md L A (ms_regs ms1) (ms_mem can) md (bv_unsigned (reg_get regs 12)) (le8 v)
      BPs HM RPa RPb RPc (length_le8 v) RPB RPW) as [RPB1 RPW1].
    apply SRcf_ret.
    apply (rd_post_intro L A regs mem md b tb ts ub us Lam peak cnt fail v fx L A (ms_regs ms1) (ms_mem can) md 0).
    + exact HM.
    + exact RA.
    + exact CT.
    + exact CU.
    + exact HT.
    + exact HU.
    + rewrite (ret_pc_ok _ HRA). rewrite SEG. reflexivity.
    + exact FRM.
    + exact INIT.
    + eapply (rd_bpost_weak B API); [|exact BPs]. intros a Ha. left. exact Ha.
    + exact RPW1.
    + rewrite <- (getr_eqv _ _ XR1). reflexivity.
    + left. split; [exact UB|]. split; [reflexivity|]. split; [|exact RPB1].
      apply (ledger_munch B API L A mem md _ _ Lam peak cnt fail HM LED MU1). intros x Hx. apply outside_one. lia.
    + exact RES.
  - destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & m' &
      E & MU & WM & MI' & ST' & FR').
    subst s0.
    destruct (ms_rel_MS _ _ _ _ _ _ _ _ REL) as [Ecan HRc]. rewrite Ecan in EQV.
    destruct (rd_back mem (ms_mem can) m' _ RA HRc ROS MU WM) as (MU1 & WM1 & RA1).
    pose proof (rw_cells_back _ _ _ _ HRc FR') as FR1.
    apply eqv_shape in EQV as [Ems1 XR1]. rewrite Ems1.
    set (m1 := ms_mem can) in *. set (regs1 := ms_regs ms1) in *.
    change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *.
    clear SP. assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
    assert (E1_1 : getr regs1 1 = Z_to_bv 64 0x13c9c) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
    assert (E1_2 : getr regs1 2 = Z_to_bv 64 (spZ regs - 176)) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
    assert (E1_4 : getr regs1 4 = reg_get regs 4) by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
    assert (E1_10 : getr regs1 10 = Z_to_bv 64 (Z.of_nat (length ub) + 3))
      by (rewrite <- (getr_eqv _ _ XR1); reflexivity).
    assert (S1' : spZ regs1 = spZ regs - 176).
    { change (bv_unsigned (getr regs1 2) = spZ regs - 176). rewrite E1_2. apply unsigned_lit. lia. }
    assert (HM1 : aa_MR API L A m1 md).
    { apply (MR_high B API L A mem m1 md _ HM MU1). intros x Hx. apply outside_one. lia. }
    replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
    eapply SRcf_bind.
    { apply (MALLOC fx L A regs1 m1 md (Z.of_nat (length ub) + 3) b Lam peak cnt fail).
      - unfold call_pre_k. rewrite S1'.
        split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
        split; [rewrite E1_1; apply ret_ok_even; vm_compute; reflexivity|].
        split; [Z.div_mod_to_equations; lia|].
        split; [lia|]. split; [lia|].
        split; [intros a Ha; unfold writable_at; rewrite SEG; apply WM1; rewrite <- SEG; apply HWS; lia|].
        split; [rewrite E1_4; exact HTP|].
        split; [intros a Ha; unfold writable_at; rewrite SEG; apply WM1; rewrite <- SEG; apply HER; exact Ha|].
        intros H. rewrite INIT in H. discriminate.
      - exact E1_10.
      - lia.
      - apply (ledger_munch B API L A mem md m1 _ Lam peak cnt fail HM LED MU1). intros x Hx. apply outside_one. lia.
      - rewrite SEG. exact RA1.
      - exact RES.
      - pose proof RES as (_ & _ & _ & _ & _ & _ & _ & _ & RL & _).
        pose proof CAP as CAP'. pose proof CAP_AG_le_CAPMAX.
        apply room_ag_of; [apply room_slots_small | |]; unfold CAPMAX in *; lia. }
    intros c2 (L1 & A1 & regs2 & m2 & md1 & w & -> & RA2 & GK2 & INIT2 & _ & CP2 & LEN2 & R2_10 & SL2 & KP2 & UBK2 & ARMS2).
    rewrite SEG in RA2.
    pose proof CP2 as (HM2 & HWF2 & HBD2 & _ & _ & RP2 & HMD1 & HFR2 & _ & HSC2).
    rewrite SEG in HSC2.
    destruct (mr_model _ _ (aa_laws API) L1 A1 m2 md1 HM2) as (Hh2 & Hl2 & _).
    pose proof (INIT2 INIT) as INIT1.
    rewrite E1_1.
    assert (ST2 : stk rsegs m2 (spZ regs - READINGS_KB) (spZ regs - 176)).
    { apply stk_of_writable; [lia | lia |]. intros a Ha. apply HSC2. unfold scratch_k. left. rewrite S1'. lia. }
    assert (E2_2 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - 176)) by (rgp 2 RP2 XR1).
    assert (E2_3 : reg_get regs2 3 = reg_get regs 3) by (rgp 3 RP2 XR1).
    assert (E2_4 : reg_get regs2 4 = reg_get regs 4) by (rgp 4 RP2 XR1).
    assert (FRa : alloc_ceiling <= spZ regs - 176) by lia.
    assert (FRb : spZ regs - 176 + Z.of_nat 176 <= 2 ^ 64) by lia.
    pose proof (rd_cells_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM1 CP2 FR1) as FR2.
    rewrite rd_cells_size in FR2. specialize (FR2 FRa FRb).
    destruct ARMS2 as [(Ecf & Ew & _ & _ & _ & SLb & _ & HBL1 & LED1) |
                       (Ncf & Nw & Wm16 & NS & NI & NL & (b1 & b2 & E1 & E2) & LED1)].
    + subst w.
      assert (FRc : forall a, spZ regs - 176 <= a < spZ regs - 176 + Z.of_nat 176 ->
                ~ scratch_k B (ALLOC_STACK + 32) regs1 a /\ ~ alloc_writes 0 a).
      { intros a Ha. split.
        - unfold scratch_k. rewrite S1'. unfold errno_low in ERR. lia.
        - unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia. }
      specialize (FR2 FRc).
      assert (E2_10 : reg_get regs2 10 = Z_to_bv 64 0) by exact R2_10.
      eapply evt_SRcf_canon; [ | exact Hh2 | exact Hl2 | ].
      { rewrite canon_mkst. rewrite SEG. unfold mkR_of. rewrite E2_2, E2_3, E2_4, E2_10.
        eapply rd_fail with (ra := reg_get regs 1) (sp := reg_get regs 2) (gp := reg_get regs 3) (tp := reg_get regs 4)
          (s0 := reg_get regs 8) (s1 := reg_get regs 9) (s2 := reg_get regs 18) (s3 := reg_get regs 19)
          (s4 := reg_get regs 20) (s5 := reg_get regs 21) (s6 := reg_get regs 22) (s7 := reg_get regs 23)
          (s8 := reg_get regs 24) (s9 := reg_get regs 25) (s10 := reg_get regs 26) (s11 := reg_get regs 27)
          (lo := spZ regs - READINGS_KB) (junk := junk).
        - rewrite ?SP. lia.
        - rewrite ?SP. exact FR2.
        - rewrite ?SP. exact ST2.
        - rewrite ?SP. lia. }
      intros ms3 (can3 & (Ecan3 & ST3) & EQV3). subst can3.
      apply eqv_shape in EQV3 as [Ems3 XR3]. rewrite Ems3.
      pose proof (rd_rp_final regs (ms_regs ms3) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR3) as RP3.
      pose proof (rd_fail_inner B API) as FI. rfeed FI.
      assert (RA2' : ro_agree (ms_segs B) m2) by (rewrite SEG; exact RA2).
      pose proof (FI L A regs1 m1 md L1 A1 regs2 m2 md1 HM1 CP2 KP2 GK2 HBL1 RA2') as BPi.
      pose proof (rd_sandwich L A regs mem md m1 regs1 L1 A1 m2 md1 (ms_regs ms3) PRE S1' MU1 WM1 BPi RP3) as BPs.
      destruct (BW READINGS_KB L A regs mem md L1 A1 (ms_regs ms3) m2 md1 (bv_unsigned (reg_get regs 12)) (le8 v)
        BPs HM RPa RPb RPc (length_le8 v) RPB RPW) as [RPB3 RPW3].
      apply SRcf_ret.
      apply (rd_post_intro L A regs mem md b tb ts ub us Lam peak cnt fail v fx L1 A1 (ms_regs ms3) m2 md1 0).
      * exact HM.
      * exact RA.
      * exact CT.
      * exact CU.
      * exact HT.
      * exact HU.
      * rewrite (ret_pc_ok _ HRA). rewrite SEG. reflexivity.
      * exact FRM.
      * exact INIT1.
      * eapply (rd_bpost_weak B API); [|exact BPs]. intros a Ha. left. exact Ha.
      * exact RPW3.
      * rewrite <- (getr_eqv _ _ XR3). reflexivity.
      * right. left. split; [exact UNE|]. split; [exact Ecf|]. split; [reflexivity|]. split; [exact LED1 | exact RPB3].
      * exact SLb.
    + assert (INX : In (w - 16, Z.of_nat (length ub) + 3 + 16) (blocks L1 A1)).
      { rewrite E1. apply in_or_app. right. left. reflexivity. }
      assert (Z0 : 0 <= 0 < Z.of_nat (length ub) + 3 + 16) by lia.
      pose proof (RBF L1 A1 m2 md1 _ _ 0 HM2 INX Z0) as (_ & W16 & WE & _ & _).
      assert (WU : bv_unsigned (Z_to_bv 64 w) = w) by (apply unsigned_lit; lia).
      assert (FRc : forall a, spZ regs - 176 <= a < spZ regs - 176 + Z.of_nat 176 ->
                ~ scratch_k B (ALLOC_STACK + 32) regs1 a /\ ~ alloc_writes w a).
      { intros a Ha. split.
        - unfold scratch_k. rewrite S1'. unfold errno_low in ERR. lia.
        - unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia. }
      specialize (FR2 FRc).
      assert (HB1 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m2 (a + i) = mbyte rsegs m1 (a + i)).
      { intros a k i Hin Hi. pose proof (RBF L A m1 md a k i HM1 Hin Hi) as (_ & B1 & _ & _ & _).
        rewrite <- SEG. apply (KP2 a k i Hin); lia. }
      assert (INL1 : forall y, In y (blocks L A) -> In y (blocks L1 A1)).
      { intros y Hy. rewrite E1. rewrite E2 in Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app;
          [left; exact Hy | right; right; exact Hy]. }
      assert (CTm1 : cstr_at m1 (bv_unsigned (reg_get regs 10)) tb st).
      { eapply cstr_munch; [exact CTt | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
      assert (CUm1 : cstr_at m1 (bv_unsigned (reg_get regs 11)) ub su).
      { eapply cstr_munch; [exact CUt | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
      destruct (RCK L A m1 L1 A1 m2 md1 _ tb st RA1 RA2 HM2 CTm1 Lst HT INL1 HB1) as (st2 & Lst2 & CT2).
      destruct (RCK L A m1 L1 A1 m2 md1 _ ub su RA1 RA2 HM2 CUm1 Lsu HU INL1 HB1) as (su2 & Lsu2 & CU2).
      destruct (RG L1 A1 m2 md1 HM2) as (canary & GG2 & GD2).
      pose proof (img_strings_keep mem m2 RA RA2 IMG) as IMG2.
      assert (PB : forall i, 0 <= i < Z.of_nat (length ub + 3) -> exists bb, m2 (Z_to_bv 64 (w + i)) = Some bb).
      { intros i Hi. assert (Hi' : 0 <= i + 16 < Z.of_nat (length ub) + 3 + 16) by lia.
        pose proof (RBF L1 A1 m2 md1 _ _ (i + 16) HM2 INX Hi') as (P & _).
        replace (w - 16 + (i + 16)) with (w + i) in P by lia. exact P. }
      assert (Pw0 : 0 <= w) by lia.
      assert (Pw1 : w + Z.of_nat (length ub + 3) <= 2 ^ 64) by lia.
      destruct (present_bytes m2 w (length ub + 3) Pw0 Pw1 PB) as (wj & Lwj & Bwj).
      assert (WB : rw_cells rsegs m2 w [CB (length ub + 3) wj]).
      { split; [split; [split; [exact Lwj | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Bwj] |].
        cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
        assert (Hi2 : 0 <= i < Z.of_nat (length ub + 3)) by lia.
        destruct (PB i Hi2) as (bb & Hb). exact (YL01.present_writable rsegs m2 (w + i) (ex_intro _ bb Hb)). }
      pose proof (rd_img_all B) as RIA. rfeed RIA.
      assert (RFB : forall i, 0 <= i < Z.of_nat (length ub) + 3 -> ro_addr rsegs (wa (w + i)) = false).
      { intros i Hi. destruct (ro_addr rsegs (wa (w + i))) eqn:Er; [|reflexivity]. exfalso.
        assert (Hwi : 0 <= w + i < 2 ^ 64) by lia. unfold wa in Er.
        apply (proj1 (ro_addr_spec (w + i) Hwi)) in Er.
        apply (NI (i + 16)); [lia|]. replace (w - 16 + (i + 16)) with (w + i) by lia. apply RIA. lia. }
      assert (PS : forall i, 0 <= i < Z.of_nat (Z.to_nat ((- (w + Z.of_nat (length ub) + 3)) mod 8)) ->
                     exists bb, m2 (Z_to_bv 64 (w + Z.of_nat (length ub) + 3 + i)) = Some bb).
      { intros i Hi. rewrite Z2Nat.id in Hi by (apply Z.mod_pos_bound; lia).
        apply (BSP L1 A1 m2 md1 (w - 16) (Z.of_nat (length ub) + 3 + 16) _ HM2 INX). Z.div_mod_to_equations. lia. }
      assert (Ps0 : 0 <= w + Z.of_nat (length ub) + 3) by lia.
      assert (Ps1 : w + Z.of_nat (length ub) + 3 + Z.of_nat (Z.to_nat ((- (w + Z.of_nat (length ub) + 3)) mod 8)) <= 2 ^ 64).
      { rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia. }
      destruct (present_bytes m2 (w + Z.of_nat (length ub) + 3) _ Ps0 Ps1 PS) as (ns & Lns & Bns).
      pose proof (rd_str_vs_block B API) as RSB. rfeed RSB.
      pose proof (RSB L A L1 A1 m2 md1 _ ub (Z.of_nat (length su)) w (Z.of_nat (length ub) + 3) b1 b2 HM2 HU Bu0
        ltac:(lia) Lsu E1 E2 ltac:(lia) Wm16) as DU.
      pose proof (RSB L A L1 A1 m2 md1 _ tb (Z.of_nat (length st)) w (Z.of_nat (length ub) + 3) b1 b2 HM2 HT Bt0
        ltac:(lia) Lst E1 E2 ltac:(lia) Wm16) as DT.
      assert (E2_8 : reg_get regs2 8 = reg_get regs 12) by (rgp 8 RP2 XR1).
      assert (E2_9 : reg_get regs2 9 = reg_get regs 11) by (rgp 9 RP2 XR1).
      assert (E2_10 : reg_get regs2 10 = Z_to_bv 64 w) by exact R2_10.
      assert (E2_18 : reg_get regs2 18 = reg_get regs 10) by (rgp 18 RP2 XR1).
      assert (E2_19 : reg_get regs2 19 = Z_to_bv 64 (Z.of_nat (length ub))) by (rgp 19 RP2 XR1).
      assert (E2_21 : reg_get regs2 21 = Z_to_bv 64 (Z.of_nat (length ub) + 3)) by (rgp 21 RP2 XR1).
      eapply evt_SRcf_canon; [ | exact Hh2 | exact Hl2 | ].
      { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
        rewrite E2_2, E2_3, E2_4, E2_8, E2_9, E2_10, E2_18, E2_19, E2_21.
        eapply (evt_normalize_cj rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA2 |].
        eapply rd_mid with (ra := reg_get regs 1) (sp := reg_get regs 2) (gp := reg_get regs 3) (tp := reg_get regs 4)
          (s0 := reg_get regs 8) (s1 := reg_get regs 9) (s2 := reg_get regs 18) (s3 := reg_get regs 19)
          (s4 := reg_get regs 20) (s5 := reg_get regs 21) (s6 := reg_get regs 22) (s7 := reg_get regs 23)
          (s8 := reg_get regs 24) (s9 := reg_get regs 25) (s10 := reg_get regs 26) (s11 := reg_get regs 27)
          (rp := reg_get regs 12) (uri := reg_get regs 11) (w := Z_to_bv 64 w) (txt := reg_get regs 10)
          (un := Z_to_bv 64 (Z.of_nat (length ub))) (canary := canary) (m := normalize_cj rsegs m2)
          (lo := spZ regs - READINGS_KB) (junk := junk) (wj := wj) (ns := ns) (tb := tb) (ts := st2) (ub := ub) (us := su2).
        - exact SNP.
        - exact STRS.
        - rewrite ?SP. lia.
        - rewrite ?SP. lia.
        - rewrite ?SP. apply rw_cells_norm_cj; [exact RA2 | exact FR2 | rewrite rd_cells_size; lia |].
          intros i Hi. apply ro_false_hi. rewrite rd_cells_size in Hi. lia.
        - rewrite ?SP. apply stk_norm_cj; [exact RA2 | exact ST2 | lia |]. intros a Ha. apply ro_false_hi. lia.
        - rewrite ?SP. unfold SNPRINTF_K. lia.
        - unfold IMG_END. lia.
        - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m2)).
        - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m2)).
        - exact FRM.
        - apply cstr_norm_cj; [exact RA2 | exact CT2 | rewrite Lst2; lia].
        - apply cstr_norm_cj; [exact RA2 | exact CU2 | rewrite Lsu2; lia].
        - exact UNE.
        - exact LU.
        - apply bytes_at_normalize_cj_low; [exact RA2 | | exact (proj2 (proj2 IMG2))].
          change (Z.of_nat (length (map (Z_to_bv 8) (ManifestB.fmt_whole ++ [0])))) with 5.
          unfold ManifestB.FMT_WHOLE_STR. lia.
        - rewrite WU. apply rw_cells_norm_cj; [exact RA2 | exact WB | cbn [cells_size csize]; lia |].
          intros i Hi. cbn [cells_size csize] in Hi. apply RFB. lia.
        - rewrite WU. apply bytes_at_normalize_cj_low; [exact RA2 | | exact Bns].
          rewrite Lns, Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia.
        - rewrite WU, Lns, Z2Nat.id by (apply Z.mod_pos_bound; lia). lia.
        - rewrite WU. lia.
        - rewrite WU. intros i Hi s Hs Hr. apply (NI (i + 16)); [lia|].
          split; [rewrite SEG; intros Hn; pose proof rsegs_tri as T; rewrite Hn in T; cbn in T; discriminate T|].
          exists s. rewrite SEG. split; [exact Hs|]. replace (w - 16 + (i + 16)) with (w + i) by lia. exact Hr.
        - rewrite WU, Lns, Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia.
        - rewrite ?SP. left. rewrite Lst2. lia.
        - rewrite ?SP. left. rewrite Lsu2. lia.
        - rewrite WU, Lsu2. lia.
        - rewrite WU, Lst2. lia.
        - lia.
        - lia.
        - apply bytes_at_normalize_cj_low; [exact RA2 | rewrite length_le8; unfold GOT_GUARD; lia | exact (c8_bytes _ _ _ GG2)].
        - apply bytes_at_normalize_cj_low; [exact RA2 | rewrite length_le8; unfold GUARD; lia | exact (c8_bytes _ _ _ GD2)]. }
      intros ms3 (can3 & (s3 & POST3 & REL3 & ROS3) & EQV3).
      destruct POST3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & F' & fc' & m3' &
        E3 & MU3 & WM3 & MI3 & FRM3 & ST3 & FR3).
      subst s3.
      destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL3) as [Ecan3 HR3]. rewrite Ecan3 in EQV3.
      destruct (rd_back_cj m2 (ms_mem can3) m3' _ RA2 HR3 ROS3 MU3 WM3) as (MU3' & WM3' & RA3).
      pose proof (rw_cells_back_cj _ _ _ _ HR3 FR3) as FR3'.
      pose proof (eqv_shape (mkFP F' fc') _ _ _ _ _ EQV3) as [Ems3 XR3]. rewrite Ems3.
      set (m3 := ms_mem can3) in *. set (regs3 := ms_regs ms3) in *.
      change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *. rewrite WU in MU3'.
      clear SP. assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
      replace (w + Z.of_nat (length ub) + 3) with (w + (Z.of_nat (length ub) + 3)) in MU3' by lia.
      assert (E3_1 : getr regs3 1 = Z_to_bv 64 0x13cd4) by (rewrite <- (getr_eqv _ _ XR3); reflexivity).
      assert (E3_2 : getr regs3 2 = Z_to_bv 64 (spZ regs - 176)) by (rewrite <- (getr_eqv _ _ XR3); reflexivity).
      assert (E3_4 : getr regs3 4 = reg_get regs 4) by (rewrite <- (getr_eqv _ _ XR3); reflexivity).
      assert (E3_10 : getr regs3 10 = Z_to_bv 64 w) by (rewrite <- (getr_eqv _ _ XR3); reflexivity).
      assert (S3' : spZ regs3 = spZ regs - 176).
      { change (bv_unsigned (getr regs3 2) = spZ regs - 176). rewrite E3_2. apply unsigned_lit. lia. }
      pose proof (rd_MR_write B API) as MW. rfeed MW.
      assert (HM3 : aa_MR API L1 A1 m3 md1).
      { apply (MW L1 A1 m2 md1 m3 (spZ regs - READINGS_KB) (spZ regs - 176) w (Z.of_nat (length ub) + 3) HM2 INX);
          [lia | lia | exact MU3' | rewrite SEG; exact WM3']. }
      pose proof (rd_ledger_write B API) as LW. rfeed LW.
      pose proof (LW L1 A1 m2 md1 m3 (spZ regs - READINGS_KB) (spZ regs - 176) w (Z.of_nat (length ub) + 3) Lam _ _ _
        HM2 LED1 INX ltac:(lia) ltac:(lia) MU3') as LED3.
      replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
      eapply SRcf_bind.
      { apply (FREE (mkFP F' fc') L1 A1 regs3 m3 md1 w (Z.of_nat (length ub) + 3)
          (sb_malloc b (Z.of_nat (length ub) + 3 + 16)) ((w, Z.of_nat (length ub) + 3) :: Lam)
          (Z.max peak (lsum Lam + (Z.of_nat (length ub) + 3))) ((cnt + 1) mod 2 ^ 64) fail).
        - unfold call_pre_k. rewrite S3'.
          split; [exact HM3|]. split; [exact HWF2|]. split; [exact HBD2|].
          split; [rewrite E3_1; apply ret_ok_even; vm_compute; reflexivity|].
          split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
          split; [intros a Ha; unfold writable_at; rewrite SEG; apply WM3'; apply HSC2; unfold scratch_k; left;
                  rewrite S1'; lia|].
          split; [rewrite E3_4; exact HTP|].
          split; [intros a Ha; unfold writable_at; rewrite SEG; apply WM3'; apply HSC2; unfold scratch_k; right;
                  exact Ha|].
          intros H. rewrite INIT1 in H. discriminate.
        - exact E3_10.
        - exact LED3.
        - rewrite SEG. exact RA3.
        - right. left. reflexivity.
        - exact SL2. }
      intros c4 (L4 & A4 & regs4 & m4 & md2 & -> & RA4 & GK4 & INIT4 & _ & CP4 & LEN4 & KP4 & UBK4 & ARMS4).
      destruct ARMS4 as [(Ew0 & _) | (_ & (c1 & c2 & F1 & F2) & (l1 & l2 & EL & LED4) & SL4)]; [lia|].
      rewrite SEG in RA4.
      pose proof CP4 as (HM4 & HWF4 & HBD4 & _ & _ & RP4 & HMD2 & HFR4 & _ & HSC4).
      destruct (mr_model _ _ (aa_laws API) L4 A4 m4 md2 HM4) as (Hh4 & Hl4 & _).
      pose proof (INIT4 INIT1) as INIT5.
      pose proof (rd_inner B API) as RI. rfeed RI.
      assert (MU3i : munch [(spZ regs1 - (ALLOC_STACK + 32), spZ regs1); (w, w + (Z.of_nat (length ub) + 3))] m2 m3).
      { apply (munch_eq2 _ _ _ _ _ _ _ _ _ _ MU3'); lia. }
      assert (RA4' : ro_agree (ms_segs B) m4) by (rewrite SEG; exact RA4).
      assert (WM3s : wmono (ms_segs B) m2 m3) by (rewrite SEG; exact WM3').
      assert (Hac1 : alloc_ceiling + (ALLOC_STACK + 32) <= spZ regs1) by lia.
      assert (H631 : spZ regs1 < 2 ^ 63) by lia.
      assert (S31 : spZ regs3 = spZ regs1) by lia.
      assert (N0 : 0 <= Z.of_nat (length ub) + 3) by lia.
      pose proof (RI L A regs1 m1 md L1 A1 regs2 m2 md1 m3 regs3 L4 A4 regs4 m4 md2 w (Z.of_nat (length ub) + 3)
        b1 b2 c1 c2 HM1 Hac1 H631 S31 CP2 KP2 GK2 N0 NI E1 E2 MU3i WM3s HM3 CP4 KP4 GK4 F1 F2 RA4') as BPi.
      rewrite E3_1.
      assert (E4_2 : reg_get regs4 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - 176)) by (rgp 2 RP4 XR3).
      assert (E4_3 : reg_get regs4 3 = reg_get regs 3) by (rgp 3 RP4 XR3).
      assert (E4_4 : reg_get regs4 4 = reg_get regs 4) by (rgp 4 RP4 XR3).
      assert (E4_8 : reg_get regs4 8 = reg_get regs 12) by (rgp 8 RP4 XR3).
      assert (E4_9 : reg_get regs4 9 = reg_get regs 11) by (rgp 9 RP4 XR3).
      assert (E4_18 : reg_get regs4 18 = reg_get regs 10) by (rgp 18 RP4 XR3).
      assert (E4_19 : reg_get regs4 19 = Z_to_bv 64 (Z.of_nat (length ub))) by (rgp 19 RP4 XR3).
      assert (E4_21 : reg_get regs4 21 = rd_found (reg_get regs 10) tb ub) by (rgp 21 RP4 XR3).
      pose proof (rd_cells_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM3 CP4 FR3') as FR4.
      rewrite rd_cells_size in FR4.
      assert (FRc4 : forall a, spZ regs - 176 <= a < spZ regs - 176 + Z.of_nat 176 ->
                ~ scratch_k B ALLOC_STACK regs3 a /\ ~ free_writes w (Z.of_nat (length ub) + 3) a).
      { intros a Ha. split.
        - unfold scratch_k. rewrite S3'. unfold errno_low in ERR. lia.
        - unfold free_writes, G_LIVE. lia. }
      specialize (FR4 FRa FRb FRc4).
      assert (ST4 : stk rsegs m4 (spZ regs - READINGS_KB) (spZ regs - 176)).
      { apply (rd_stk_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM3 CP4); [lia | lia | |].
        - intros a Ha. unfold writable_at. apply WM3'. apply HSC2. unfold scratch_k. left. rewrite S1'. lia.
        - intros a Ha. unfold free_writes, G_LIVE. lia. }
      pose proof LED1 as (_ & _ & _ & _ & ND1 & _).
      pose proof (rd_lam_eq Lam l1 l2 _ ND1 EL) as ELam. rewrite ELam in LED4.
      replace (lsum Lam + (Z.of_nat (length ub) + 3)) with (lsum Lam + Z.of_nat (length ub) + 3) in LED4 by lia.
      assert (SL5 : res_ok_slots A4 b) by (rewrite sb_free_malloc in SL4; exact SL4).
      pose proof BPi as (_ & _ & _ & _ & _ & HBL4 & HBB4 & _). rewrite SEG in HBB4.
      assert (INL4 : forall y, In y (blocks L A) -> In y (blocks L4 A4)) by (intros y Hy; rewrite HBL4; exact Hy).
      destruct (RCK L A m1 L4 A4 m4 md2 _ tb st RA1 RA4 HM4 CTm1 Lst HT INL4 HBB4) as (st4 & Lst4 & CT4).
      destruct (RCK L A m1 L4 A4 m4 md2 _ ub su RA1 RA4 HM4 CUm1 Lsu HU INL4 HBB4) as (su4 & Lsu4 & CU4).
      destruct (RG L4 A4 m4 md2 HM4) as (canary4 & GG4 & GD4).
      pose proof (img_strings_keep mem m4 RA RA4 IMG) as IMG4.
      pose proof (rd_sandwich L A regs mem md m1 regs1 L4 A4 m4 md2 regs PRE S1' MU1 WM1 BPi (fun r _ => eq_refl)) as BPr.
      destruct (BW READINGS_KB L A regs mem md L4 A4 regs m4 md2 (bv_unsigned (reg_get regs 12)) (le8 v)
        BPr HM RPa RPb RPc (length_le8 v) RPB RPW) as [RPB4 RPW4].
      assert (LZ : (length (ManifestMem.zbytes ub) =? 0)%nat = false).
      { destruct ub; [exfalso; exact (UNE eq_refl) | reflexivity]. }
      assert (LTB : length (ManifestMem.zbytes tb) = length tb) by (unfold ManifestMem.zbytes; apply length_map).
      assert (TB64 : bv_unsigned (reg_get regs 10) + Z.of_nat (length tb) < 2 ^ 64) by lia.
      assert (TB0 : 0 < bv_unsigned (reg_get regs 10)) by lia.
      destruct (Z.eq_dec (bv_unsigned (rd_found (reg_get regs 10) tb ub)) 0) as [F0|F0].
      * pose proof (proj1 (rd_found_zero _ tb ub TB0 TB64) F0) as WH.
        eapply evt_SRcf_canon; [ | exact Hh4 | exact Hl4 | ].
        { rewrite canon_mkst. rewrite SEG. unfold mkR_of.
          rewrite E4_3, E4_4, E4_8, E4_9, E4_18, E4_19, E4_21.
          eapply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA4 |].
          eapply rd_miss; [exact F0|].
          eapply SCAN with (ra := reg_get regs 1) (sp := reg_get regs 2) (s0 := reg_get regs 8) (s1 := reg_get regs 9)
            (s2 := reg_get regs 18) (s3 := reg_get regs 19) (s4 := reg_get regs 20) (s5 := reg_get regs 21)
            (s6 := reg_get regs 22) (s7 := reg_get regs 23) (s8 := reg_get regs 24) (s9 := reg_get regs 25)
            (s10 := reg_get regs 26) (s11 := reg_get regs 27) (lo := spZ regs - READINGS_KB) (junk := junk)
            (tb := tb) (ts := st4) (ub := ub) (us := su4) (v := v).
          - rewrite E4_2. reflexivity.
          - rewrite ?SP. apply rw_cells_norm; [exact RA4 | exact FR4 |].
            intros i Hi. apply ro_false_hi. cbn [cells_size csize] in Hi. lia.
          - exact (mem_inv_normalize rsegs m4).
          - rewrite ?SP. apply stk_normalize; [exact ST4 | lia].
          - rewrite ?SP. lia.
          - exact (cstr_normalize _ _ _ _ RA4 CT4).
          - exact (cstr_normalize _ _ _ _ RA4 CU4).
          - exact UNE.
          - reflexivity.
          - exact T4.
          - lia.
          - exact U4.
          - exact (bytes_at_normalize rsegs _ _ _ RA4 RPB4).
          - apply (wr_at_norm rsegs m4 (normalize rsegs m4)); [exact (mem_rel_normalize rsegs m4 RA4) | exact RPW4 |].
            intros i Hi. apply ro_false_hi. lia.
          - exact (bytes_at_normalize rsegs _ _ _ RA4 (proj1 IMG4)).
          - exact (bytes_at_normalize rsegs _ _ _ RA4 (proj1 (proj2 IMG4))).
          - exact (bytes_at_normalize rsegs _ _ _ RA4 (c8_bytes _ _ _ GG4)).
          - exists canary4. exact (bytes_at_normalize rsegs _ _ _ RA4 (c8_bytes _ _ _ GD4)).
          - rewrite ?SP. lia.
          - rewrite ?SP. lia.
          - unfold off_stack. rewrite ?SP, Lst4. lia.
          - unfold off_stack. rewrite ?SP, Lsu4. lia.
          - unfold off_stack. rewrite ?SP. lia.
          - unfold off_stack, readings_scan_c.PREFIX_LC_AT. rewrite ?SP. lia.
          - unfold off_stack, readings_scan_c.PREFIX_UC_AT. rewrite ?SP. lia.
          - cbn [disjoint_from]. unfold readings_scan_c.PREFIX_LC_AT, readings_scan_c.PREFIX_UC_AT.
            rewrite Lst4, Lsu4. repeat split; lia. }
        intros ms5 (can5 & (s5 & POST5 & REL5 & ROS5) & EQV5).
        destruct POST5 as (u0 & u1 & u2 & a05 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5' &
          E5 & MU5 & WM5 & MI5 & ST5 & R5 & RB5).
        subst s5.
        destruct (ms_rel_MS _ _ _ _ _ _ _ _ REL5) as [Ecan5 HR5]. rewrite Ecan5 in EQV5.
        destruct (rd_back m4 (ms_mem can5) m5' _ RA4 HR5 ROS5 MU5 WM5) as (MU5' & WM5' & RA5).
        pose proof (proj2 (bytes_at_rel rsegs (ms_mem can5) m5' _ _ HR5) RB5) as RB5'.
        pose proof (eqv_shape (mkFP F' fc') _ _ _ _ _ EQV5) as [Ems5 XR5]. rewrite Ems5.
        set (m5 := ms_mem can5) in *.
        change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *.
        clear SP. assert (SP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
        pose proof (rd_rp_final regs (ms_regs ms5) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR5) as RP5.
        pose proof (rd_sandwich L A regs mem md m1 regs1 L4 A4 m4 md2 (ms_regs ms5) PRE S1' MU1 WM1 BPi RP5) as BPs.
        assert (BP5 : bpost B (aa_MR API) READINGS_KB (rd_writes (bv_unsigned (reg_get regs 12))) L A regs mem md L4 A4
                  (ms_regs ms5) m5 md2).
        { pose proof (rd_bpost_ext B API) as BE. rfeed BE.
          apply (BE READINGS_KB (rd_writes (bv_unsigned (reg_get regs 12))) L A regs mem md L4 A4 (ms_regs ms5) m4 md2
            [(spZ regs - readings_scan_c.READINGS_K, spZ regs);
             (bv_unsigned (reg_get regs 12), bv_unsigned (reg_get regs 12) + 8)] m5).
          - eapply (rd_bpost_weak B API); [|exact BPs]. intros a Ha. left. exact Ha.
          - exact MU5'.
          - rewrite SEG. exact WM5'.
          - rewrite SEG. exact RA5.
          - intros x Hx HO. apply not_outside2 in HO.
            destruct HO as [HO|HO]; (split; [lia|]); [left; unfold scratch_k; left; lia | right; unfold rd_writes; right; lia]. }
        apply SRcf_ret.
        apply (rd_post_intro L A regs mem md b tb ts ub us Lam peak cnt fail v (mkFP F' fc') L4 A4 (ms_regs ms5) m5 md2
          (ManifestModel.scan (ManifestMem.zbytes tb) (ManifestMem.zbytes ub) 0 0 (S (length tb)))).
        -- exact HM.
        -- exact RA.
        -- exact CT.
        -- exact CU.
        -- exact HT.
        -- exact HU.
        -- rewrite (ret_pc_ok _ HRA). rewrite SEG. reflexivity.
        -- exact FRM3.
        -- exact INIT5.
        -- exact BP5.
        -- exact (wr_at_wmono _ _ _ _ RPW4 WM5').
        -- rewrite <- (getr_eqv _ _ XR5). exact R5.
        -- right. right. split; [exact UNE|]. split; [exact Ncf|]. split.
           { unfold ManifestModel.names. rewrite LZ, WH, LTB. reflexivity. }
           split.
           { apply (ledger_munch B API L4 A4 m4 md2 m5 _ Lam _ _ fail HM4 LED4 MU5'). intros x Hx. cbn [outside].
             split; [lia | split; [lia | exact I]]. }
           replace (ManifestModel.nreadings (ManifestMem.zbytes tb) (ManifestMem.zbytes ub))
             with (ManifestModel.readings (ManifestMem.zbytes tb) (ManifestMem.zbytes ub) 0 0 (S (length tb)))
             by (unfold ManifestModel.nreadings; rewrite LZ, WH, LTB; reflexivity).
           exact RB5'.
        -- exact SL5.
      * assert (WH : whole (ManifestMem.zbytes tb) (ManifestMem.zbytes ub) = true).
        { destruct (whole (ManifestMem.zbytes tb) (ManifestMem.zbytes ub)) eqn:Wh; [reflexivity|].
          exfalso. apply F0. exact (proj2 (rd_found_zero _ tb ub TB0 TB64) Wh). }
        eapply evt_SRcf_canon; [ | exact Hh4 | exact Hl4 | ].
        { rewrite canon_mkst. rewrite SEG. unfold mkR_of. rewrite E4_2, E4_3, E4_4, E4_21.
          eapply rd_hit with (ra := reg_get regs 1) (sp := reg_get regs 2) (gp := reg_get regs 3) (tp := reg_get regs 4)
            (s0 := reg_get regs 8) (s1 := reg_get regs 9) (s2 := reg_get regs 18) (s3 := reg_get regs 19)
            (s4 := reg_get regs 20) (s5 := reg_get regs 21) (s6 := reg_get regs 22) (s7 := reg_get regs 23)
            (s8 := reg_get regs 24) (s9 := reg_get regs 25) (s10 := reg_get regs 26) (s11 := reg_get regs 27)
            (m := m4) (lo := spZ regs - READINGS_KB) (junk := junk).
          - rewrite ?SP. lia.
          - exact F0.
          - rewrite ?SP. exact FR4.
          - rewrite ?SP. exact ST4.
          - rewrite ?SP. lia. }
        intros ms5 (can5 & (Ecan5 & ST5) & EQV5). subst can5.
        pose proof (eqv_shape (mkFP F' fc') _ _ _ _ _ EQV5) as [Ems5 XR5]. rewrite Ems5.
        pose proof (rd_rp_final regs (ms_regs ms5) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR5) as RP5.
        pose proof (rd_sandwich L A regs mem md m1 regs1 L4 A4 m4 md2 (ms_regs ms5) PRE S1' MU1 WM1 BPi RP5) as BPs.
        apply SRcf_ret.
        apply (rd_post_intro L A regs mem md b tb ts ub us Lam peak cnt fail v (mkFP F' fc') L4 A4 (ms_regs ms5) m4 md2 1).
        -- exact HM.
        -- exact RA.
        -- exact CT.
        -- exact CU.
        -- exact HT.
        -- exact HU.
        -- rewrite (ret_pc_ok _ HRA). rewrite SEG. reflexivity.
        -- exact FRM3.
        -- exact INIT5.
        -- eapply (rd_bpost_weak B API); [|exact BPs]. intros a Ha. left. exact Ha.
        -- exact RPW4.
        -- rewrite <- (getr_eqv _ _ XR5). reflexivity.
        -- right. right. split; [exact UNE|]. split; [exact Ncf|]. split.
           { unfold ManifestModel.names. rewrite LZ, WH. reflexivity. }
           split; [exact LED4|].
           replace (ManifestModel.nreadings (ManifestMem.zbytes tb) (ManifestMem.zbytes ub)) with O
             by (unfold ManifestModel.nreadings; rewrite LZ, WH; reflexivity).
           cbn [Z.of_nat]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact RPB4.
        -- exact SL5.
Qed.


End R.

Theorem readings_cf_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) :
  statics_free B (aa_MR API) -> statics_facts B -> ManifestB.ctx_owned B (aa_MR API) -> AllocExtra B (aa_MR API) ->
  block_slack_present B API -> errno_low B -> guard_syms B ->
  LibcNeeds_c.strlen_contract -> LibcNeeds_c.strncmp_contract -> LibcNeeds_c.strncasecmp_contract ->
  LibcNeeds_c.strchr_contract -> LibcNeeds_c.isalnum_contract -> has_prefixed_c.has_prefixed_contract ->
  snprintf_contract -> LibcNeeds_c.strstr_contract ->
  (forall fx' : FPState, @fuzz_malloc_contract_cf fx' rc B API) ->
  (forall fx' : FPState, @fuzz_free_contract_cf fx' rc B API) ->
  readings_contract_cf B API.
Proof.
  intros SF SFA CTX AX BSP ERR GS LEN NCMP NCASE CHR ALNUM HP SNPc STRSc MALLOCc FREEc.
  pose proof (readings_scan.readings_scan_holds LEN NCMP NCASE CHR ALNUM HP) as SCANc.
  unfold readings_contract_cf.
  intros L A regs mem md b tb ts ub us Lam peak cnt fail v SEG.
  pose proof (rd_core_cf B API) as H. rfeed H.
  exact (H L A regs mem md b tb ts ub us Lam peak cnt fail v SEG).
Qed.
