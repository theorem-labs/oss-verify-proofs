(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (main_entry_h0X reads the restated main_entry_A, with its launch input and premises and its new stack cells; the stack VMA's end STKHI is the draw's page top, its facts from the launch, and the heap's stack floor STKLO is sp0 - 6144512). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Asan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec AxSymExec3 AxSymExec3Sound AsanCertDefs AsanPlanImages AsanPlanSound AsanMainEntryKit AsanMainEntryFacts AsanMainEntryLemmas.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Arr Asn1Aux CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil AModel AModelX AVmLib AVm AVst HMLib HM AHeapR AH0Spec0 AH0Spec AH0Facts AH0Base AH0Layout AH0Pure AH0Vwf AH0K AH0K2 AH0Rom AH0Mem0 AH0Mem1 AH0Mem2 AH0Mem3 AH0XR.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import APS.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AH0Bridge () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.ABoot.AsanMainEntryFacts.main_entry_A"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.AHeap.AH0Spec0.boot_params"; "OSSVerify.KrLib.AHeap.AH0Spec0.bp_sp0"; "OSSVerify.KrLib.AHeap.AH0Spec0.bp_stkhi"; "OSSVerify.KrLib.AHeap.AH0Spec.h0_goal"].


Section Bridge.
  Context {hAR : arun}.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis HACsp : ACEIL = bv_unsigned sp / 4096 * 4096 - 2 ^ 23.

  (* LPS 727298f3: the stack VMA's end is the draw's [ed_top] ([Run.entry_page_top]), and the
     heap's stack floor is sp0 - 6144512, the bottom of the window the launch maps below sp. *)
  Let STKHI : Z := entry_page_top rdraw.
  Let STKLO : Z := bv_unsigned sp - 6144512.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit HACsp"] Theorem main_entry_h0X : ltac2:(CDefT.buildp (gd_tbl_AH0Bridge ()) "PR,(9.&5.(:.&40.))Pmem,P,(:.&40.)(;.(:.&8.))Pmd,$<.P,(=.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vfs,Vuid,Vhw,R3.R2.R1.)(>.$?.Lbp,$?.(0.(3.$4.(10.R1.)(2.&40.Vsp,))(0.(3.$4.(11.R1.)VSTKHI,)(12.VhAR,VSTKLO,R1.R4.R3.))))")
(* [comment removed for export] *).
  Proof.
    intros R mem md H. ddestruct H as (inp & mb & p & Eav & Eev & Euid & Ehw & Hvl & Hlau & HI & HCN & HREG & HMOD & HMEM).
    ddestruct HMEM as (HCOM & HRC & HSTK & Hzero & Hargs & Hwin & HNN & HDEF).   (* [comment removed for export] *)
    pose proof HMOD as X. unfold me_model in X. ddestruct X as (_ & _ & _ & _ & _ & (fog & FL & FSM & HFOG) & _).
    (* LPS 727298f3: the stack VMA's end, from the launch *)
    destruct (launch_stkhi_facts sp brk0 mb rdraw inp Hvl Hlau) as (S2 & S3 & S1' & S4').
    assert (S1 : bv_unsigned sp < STKHI) by (unfold STKHI; lia).
    assert (S4 : STKHI <= bv_unsigned sp + 2 ^ 23) by (unfold STKHI; lia).
    clear S1' S4'.
    (* [comment removed for export] *)
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2.
    assert (HSP : bv_unsigned sp = SP p).
    { rewrite <- (sp0w_eq sp brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit inp p HI). unfold sp0w, AsanMainEntryLemmas.SP0, SP. rewrite (zev_exact p) by (cbn [zev]; lia). cbn [zev]. lia. }
    assert (HAC : ACEIL = STKPG p - 0x800000).
    { rewrite HACsp, HSP. unfold SP, STKPG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    rewrite HSP in S1, S4.
    (* [comment removed for export] *)
    assert (RC : exists TF, 1 <= TF <= 3 /\ ((TF = 3 /\ Forall (cell_ok ASEGS mem) (cells_rcase1 p)) \/ (TF = 2 /\ Forall (cell_ok ASEGS mem) (cells_rcase2 p)))).
    { destruct HRC as [[_ H1]|[_ H2]]; [exists 3 | exists 2]; split; [lia | left; auto | lia | right; auto]. }
    ddestruct RC as (TF & TF_ok & HR).
    set (FOGZ := FOG fog).
    assert (FOK := fog_ok sp fs p HCN md fog HMOD HAC HSP HFOG).
    assert (FLEN := fog_len fog FL). assert (FSMALL := fog_small fog FSM).
    assert (FSEPS := fog_seps sp fs p md fog HMOD HFOG). assert (FAPART := fog_apart sp fs p HCN md fog HMOD HFOG).
    fold FOGZ in FOK, FLEN, FSMALL, FSEPS, FAPART.
    exists (bp_of p STKHI FOGZ TF).
    split; [cbn [bp_of bp_sp0]; rewrite HSP; reflexivity|]. split; [reflexivity|].
    assert (AWF : awf' (h0_of (bp_of p STKHI FOGZ TF))).
    { exact (h0_awf p HCN STKHI FOGZ TF HAC S1 S2 S3 S4 FOK FLEN FSMALL TF_ok). }
    assert (VWF : vwf AL0 (vst_of (h0_of (bp_of p STKHI FOGZ TF)))).
    { exact (h0_vwf p HCN STKHI FOGZ TF HAC S1 S2 S3 S4 FOK FLEN TF_ok FSEPS FAPART). }
    assert (HOK : hok STKLO (h0_of (bp_of p STKHI FOGZ TF))).
    { split; [cbn [h_L h0_of L0_of l_stk_lo bp_of bp_sp0]; unfold STKLO; rewrite HSP; reflexivity | split; [exact AWF | exact VWF]]. }
    split; [unfold STKLO; cbn [bp_of bp_sp0]; rewrite HSP; reflexivity|].
    exists HOK.
    (* [comment removed for export] *)
    pose proof (M_bounds sp fs p HCN md HMOD HAC HSP _ (new_nth p md fog HFOG 3 _ eq_refl)) as BN.
    pose proof (M_bounds sp fs p HCN md HMOD HAC HSP _ (new_nth p md fog HFOG 2 _ eq_refl)) as BS.
    pose proof (M_disj sp fs p md HMOD _ _ (new_nth p md fog HFOG 3 _ eq_refl) (new_nth p md fog HFOG 2 _ eq_refl)
                  ltac:(intros E; apply (f_equal (fun e => bv_unsigned (snd e))) in E; unfold pinst in E; cbn [nth fst snd] in E; rewrite !(u_wlit p) in E by lia; lia)) as BD.
    unfold pinst, iv_disjoint in BN, BS, BD. cbn [nth fst snd] in BN, BS, BD. revert BN BS BD.
    rewrite ?(u_dnodes p HCN), ?(u_dstore p HCN). rewrite ?(u_wlit p) by lia. intros BN BS BD.
    split.
    { (* [comment removed for export] *) split; [| split].
      - (* [comment removed for export] *)
        split; [split; [exact AWF | reflexivity]|]. cbn [hh].
        split; [exact (h0_hm_maps mem p HCN HCOM HDEF STKHI FOGZ TF S1 S3 ltac:(intros a Ha; apply Hwin; rewrite HSP; unfold STKHI in *; exact Ha) (RZI inp) HSTK)|].
        split; [exact (h0_hm_statics mem p HCN HCOM STKHI FOGZ TF)|].
        split; [exact (h0_hm_thread mem p HCN HCOM STKHI FOGZ TF)|].
        split; [exact (h0_hm_depot mem p HCN HCOM HDEF STKHI FOGZ TF HR ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (h0_hm_chunks mem p STKHI FOGZ TF)|].
        split; [exact (h0_hm_regions mem p HCN HCOM STKHI FOGZ TF)|].
        split; [exact (h0_hm_quar mem p HCN HCOM STKHI FOGZ TF)|].
        split; [exact (h0_hm_sec mem p HCN HCOM STKHI FOGZ TF)|].
        split; [exact (h0_hm_fake mem p HCN HCOM STKHI FOGZ TF)|].
        split; [exact (h0_hm_ia mem p HCOM STKHI FOGZ TF)|].
        exact (h0_hm_emb mem p HCOM STKHI FOGZ TF).
      - (* [comment removed for export] *) exact (h0_XR mem p HCOM).
      - (* [comment removed for export] *)
        cbn [hh]. intros x Zx. apply HNN. exact (h0_habs_nn sp fs p HCN STKHI TF md fog HMOD (bv_unsigned x) Zx). }
    split.
    { (* [comment removed for export] *) split; [exact (h0_HK sp fs p HCN STKHI TF md fog HMOD HAC HSP HFOG FL FSM S1 S2 S3 S4 TF_ok) | cbn; constructor]. }
    split; [reflexivity|].
    split; [exact (h0_hfr p STKHI FOGZ TF FLEN TF_ok)|].
    split; [intros c; reflexivity|].
    split; reflexivity.
  Qed.

  End Bridge.
