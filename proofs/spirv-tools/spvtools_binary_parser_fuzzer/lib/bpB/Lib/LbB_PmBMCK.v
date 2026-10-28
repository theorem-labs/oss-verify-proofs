From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK LbB_PmMagRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_PmMagK LbB_Own LbB_RwStm LbB_PmMagRS LbB_PmMagW LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_DStat LbB_DiagStmt LbB_PmBMRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmBMT.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section BMCK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma bm_pre_proj : forall R m q sp words n x, hdrR_mg_pre R m q sp words n x -> bmR_x_pre R m q sp words n x.
  Proof. intros R m q sp words n x P. unfold hdrR_mg_pre in P. unfold bmR_x_pre. tauto. Qed.

  Lemma tail_of_post : forall e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M',
    frm_zero fc -> as_MPRES H mo0 mo ->
    wpre H e -> winv H e ff fp XSc s LB m -> bp_slots H e ff m -> bp_shad ff [14; 20; 21]%nat m ->
    bp_rc H e ff R -> bp_rmag H e ff R -> bp_wl H e ff w ->
    bp_pfresh H w s LB LBs m c -> w_words e <> 0 -> 5 <= w_n e ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_VIS H s msF1 = MS R' F (wz (0xea7c4 + 4812)) fc None M' (seg_rom asegs) -> rfull R' ->
    CatSim.msteps asegs (MS R F (wz (0xea7c4 + 4784)) fc None m (seg_rom asegs)) (MS R' F (wz (0xea7c4 + 4812)) fc None M' (seg_rom asegs)) ->
    munch [((wS1 e - 8), wS1 e); ((32 * (ff / 32) + 1728), (32 * (ff / 32) + 1744))] m M' -> wmono asegs m M' ->
    getr R' 2 = wz (wS1 e) -> getr R' 18 = wz ((32 * (ff / 32)) + 3456) -> getr R' 19 = wz ((4 * (ff / 32)) + ASHADOW_BASE) ->
    getr R' 20 = wz (32 * (ff / 32)) ->
    (forall r, In r [3; 4; 5; 6; 7; 8; 9; 21; 22; 23; 26; 27; 28; 29; 30; 31]%bv -> getr R' r = getr R r) ->
    bm_tail_at H e ff fp Q mo0 -> as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M' FZ MP HP HI SL SH RC RM WL PF HW HN
           KR1 MP1 VIS1 RF1 MS MU WM G2 G18 G19 G20 KEEP K.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16).
    assert (Hq : 32 * (ff / 32) = ff) by (clear - E1; Z.div_mod_to_equations; lia).
    assert (SHq : 4 * (ff / 32) + ASHADOW_BASE = sh ff).
    { unfold sh. rewrite <- Hq at 2. replace (32 * (ff / 32)) with ((4 * (ff / 32)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
    rewrite Hq in MU, G18, G20. rewrite SHq in G19.
    set (W := [(wS1 e - 8, wS1 e); (ff + 1728, ff + 1744)]) in MU.
    pose proof HI as (RFS & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FS & LVI).
    pose proof aceil_facts as ((AC1 & AC2) & _).
    assert (MI' : mem_inv asegs M') by exact (msteps_mem_inv asegs _ _ MS MI).
    assert (ST' : stk asegs M' (w_lo e) (wSP e)) by (apply (stk_keepW W m M'); [exact ST | exact MU | exact WM | unfold AIMG_TOP; lia]).
    assert (FW : Forall (wwin H e ff) W) by (subst W; repeat constructor; unfold wwin; cbn [fst snd]; unfold WO_FLAGP, WO_SAVED; lia).
    assert (HI' : winv H e ff fp XSc s LB M') by exact (winv_munch H HH e ff fp XSc s LB m M' W HP HI MU WM MI' ST' FW).
    assert (FL : Forall (bp_flw H e ff) W).
    { subst W. constructor; [| constructor; [| constructor]]; unfold bp_flw; cbn [fst snd].
      - split; [right; right; lia | unfold sh in *; lia].
      - split; [left; unfold WO_FLAGP; lia | unfold sh in *; lia]. }
    pose proof WL as (Wp & Wc & _).
    destruct PF as (PP & FR & AL & CC).
    destruct RC as (Rc2 & Rc3 & Rc4 & Rc8 & Rc9 & Rc19 & Rc20).
    destruct RM as (M10 & M11 & M18 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
    unfold bm_tail_at, bp_hdr0 in K.
    apply (K s LB LBs M' mo1 msF1 R' F fc XSc w c).
    - rewrite VIS1. reflexivity.
    - exact RF1.
    - exact FZ.
    - exact KR1.
    - exact (ah_mpres_trans H HH mo0 mo mo1 MP MP1).
    - exact HP.
    - exact HI'.
    - destruct SL as (SL1 & SL2 & SL3). split; [| split].
      + eapply rw_cells_transport; [exact SL1 | exact MU | exact WM |]. subst W. cbn. lia.
      + eapply rw_cells_transport; [exact SL2 | exact MU | exact WM |]. subst W. cbn. lia.
      + eapply rw_cells_transport; [exact SL3 | exact MU | exact WM |]. subst W. cbn. lia.
    - eapply u8arr_transport; [exact SH | exact MU | exact WM |].
      rewrite length_map. replace (Z.of_nat (length (wo_sh [14; 20; 21]%nat))) with 476 by (vm_compute; reflexivity).
      subst W. cbn. unfold sh in *. lia.
    - split; [exact G2 |].
      split; [etransitivity; [exact (KEEP 3%bv ltac:(repeat (first [left; reflexivity | right]))) | exact Rc3] |].
      split; [etransitivity; [exact (KEEP 4%bv ltac:(repeat (first [left; reflexivity | right]))) | exact Rc4] |].
      split; [etransitivity; [exact (KEEP 8%bv ltac:(repeat (first [left; reflexivity | right]))) | exact Rc8] |].
      split; [etransitivity; [exact (KEEP 9%bv ltac:(repeat (first [left; reflexivity | right]))) | exact Rc9] |].
      split; [exact G19 | exact G20].
    - split; [exact G18 |].
      split; [etransitivity; [exact (KEEP 22%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M22] |].
      etransitivity; [exact (KEEP 27%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M27].
    - exact WL.
    - split; [| split; [exact HW | exact HN]].
      split; [exact (bp_pp_keepW H HH e ff fp XSc w s LB LBs m M' c W HP HI WL PP MU WM FL) |].
      split; [exact FR |]. split; [exact AL |].
      eapply rw_cells_transport; [exact CC | exact MU | exact WM |]. rewrite Wc. subst W. cbn. lia.
  Qed.
End BMCK.
