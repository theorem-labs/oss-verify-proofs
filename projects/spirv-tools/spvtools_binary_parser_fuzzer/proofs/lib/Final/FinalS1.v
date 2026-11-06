(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.AllocCeil OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Lib_Cxx_OperatorNew OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocIfaceStmt OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocInstS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocHeapOwnS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.DrvLibContract OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.S1Statics OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.LibContractS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.S1TargetConsts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmts.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_JumpP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_LookupOpP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_StrlenP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagMain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DsRoom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module DiagMallocS1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocIfaceStmt OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocInstS1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DsRoom.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
Open Scope Z_scope.

Lemma mng_classes_sep : forall j, 0 <= j -> 96 * 2 ^ j < MNG_BIG -> mng_size_class (48 * 2 ^ j) + 1 < mng_size_class (96 * 2 ^ j).
Proof.
  intros j Hj Hb. unfold MNG_BIG in Hb.
  assert (Hj10 : j <= 10).
  { destruct (Z.le_gt_cases j 10) as [H|H]; [exact H|]. exfalso.
    assert (2 ^ 11 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (Z.eq_dec j 0) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 1) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 2) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 3) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 4) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 5) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 6) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 7) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 8) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 9) as [->|]; [vm_compute; split; reflexivity|].
  destruct (Z.eq_dec j 10) as [->|]; [vm_compute; split; reflexivity|].
  lia.
Qed.

Lemma mng_round_up_pg_bounds : forall x, 0 <= x -> x <= mng_round_up_pg x <= x + 4095.
Proof.
  intros x Hx. unfold mng_round_up_pg, MNG_PGSZ.
  change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (- x) (2 ^ 12) ltac:(lia)). lia.
Qed.

Lemma mng_round_big_add : forall a b, 0 <= a -> 0 <= b -> mng_round_big a + mng_round_big b <= mng_round_big (a + b + 2 ^ 14).
Proof.
  intros a b Ha Hb. unfold mng_round_big, MNG_IB, MNG_UNIT.
  pose proof (mng_round_up_pg_bounds (a + 4 + 16) ltac:(lia)).
  pose proof (mng_round_up_pg_bounds (b + 4 + 16) ltac:(lia)).
  pose proof (mng_round_up_pg_bounds (a + b + 2 ^ 14 + 4 + 16) ltac:(lia)). lia.
Qed.

Theorem diag_classes_S1 {AC : AllocCeiling} {RRND : RunRandom} : classes_sep _ _ MI_S1.
Proof. exact mng_classes_sep. Qed.

Theorem diag_round_big_S1 {AC : AllocCeiling} {RRND : RunRandom} : round_big_add _ _ MI_S1.
Proof. exact mng_round_big_add. Qed.
End DiagMallocS1.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.Overlay OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.RunsLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.StaticsGen OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.S1CxxTable.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module DiagStaticsS1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.Overlay OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.RunsLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.StaticsGen OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.S1CxxTable OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.S1Statics.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagS1.
Import ListNotations.
Open Scope Z_scope.

Lemma D_DIAG_sub : runs_sub D_DIAG D_SX = true.
Proof. vm_compute. reflexivity. Qed.

Theorem diag_statics_S1 : forall (s : SX S1ST) (M : LibIface.mem), sx_inv S1ST s M -> pins D_DIAG M.
Proof.
  intros s M (HP & _ & _). eapply pins_sub; [apply D_DIAG_sub | exact HP].
Qed.
End DiagStaticsS1.
From Stdlib Require NArith Classical_Prop Sorting.Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagVia OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagViaS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SbOverflow OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Xsputn.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module ExhOpStr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagVia OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagViaS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1.DiagStmtsEx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1.ExhLib.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition A_OPCODE_STRING : Z := 0x6b0f4.
Definition OS_RET_LOOKUP : Z := 0x6b108.
Definition OS_RET_NAME : Z := 0x6b128.
Definition OS_RETPC : Z := 0x6b130.

Section OpStr.
Context {AC : AllocCeiling}.
  Variables (G : grammar) (tc : tabl_consts) (idesc : Z -> Z -> Prop).
  Hypothesis EN : exhausted_needs G tc idesc.

  Lemma opcode_string : forall (fx : FPState) R M (sp op : Z) (ret : word),
    ro_clear Ly.L M -> getr R 10%bv = Z_to_bv 64 op -> 0 <= op < 2 ^ 16 ->
    getr R 2%bv = Z_to_bv 64 sp -> alloc_ceiling + 80 <= sp -> sp < 2 ^ 47 -> sp mod 16 = 0 ->
    mdef M (sp - 80) 80 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M' p n,
      msteps SEGS (@mkst fx R (Z_to_bv 64 A_OPCODE_STRING) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS)) /\
      kept R R' /\ getr R' 10%bv = Z_to_bv 64 p /\ ro_cstr SEGS Ly.L p n /\ n <= 256 /\
      stores_in (zwin (sp - 80) sp) M M'.
  Proof using AC G tc idesc EN.
    intros fx R M sp op ret ROC Ha0 Hop Hsp Hceil Hsphi Hal HD Hra Hret.
    pose proof EN as (TLO & TNM & _ & _ & TLS & LOOK & NAME & _ & _).
    pose proof ac_bounds_lit as Hcv. pose proof (u64_range ret) as Hretr.
    unfold lookup_opcode_stmt, lookup_shape in LOOK. unfold idesc_name_stmt, PrsGrammar.leafA in NAME. rewrite TLO in LOOK. rewrite TNM in NAME.

    set (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M [KWr (SA (EVar 2) (-80)) (ELit 80); KRange (EVar 2) (2 ^ 40) (2 ^ 47); KAlign (EVar 2) 16]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ sp (-80) 80); [evs; exact Hsp | lia | lia | lia | lia | exact HD].
      - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hal]. }
    xrun_at HR HK fx A_OPCODE_STRING (seg_rom SEGS) 40%nat [TC_LOOKUP_OPCODE] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK. rename R' into R1. rename HR' into HR1. rename Hms into Hms1. wnorm_in Hms1.
    lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
    assert (ST1 : stores_in (zwin (sp - 16) sp) M M1) by (subst M1; stores_tower).
    assert (F0 : fld SEGS M1 (sp - 16) 8 0) by (unfold fld; subst M1; peel).
    assert (Fra : fld SEGS M1 (sp - 8) 8 (bv_unsigned ret)).
    { unfold fld. rewrite Z_to_bv_bv_unsigned. subst M1. peel. }
    assert (ROC1 : ro_clear Ly.L M1).
    { eapply ro_clear_frame; [exact ROC | eapply stores_in_frame_eq; [exact ST1 | intros a Ha; exact Ha] |].
      intros a (Himg & _) Hw. unfold zwin in Hw. exact (hi_offimg (AC:=AC) a ltac:(lia) Himg). }
    assert (HD1 : mdef M1 (sp - 80) 80) by (eapply stores_in_mdef; [exact ST1 | exact HD]).
    regval HR1 (10%bv : reg) op X10. regval HR1 (11%bv : reg) (sp - 16) X11. regval HR1 (2%bv : reg) (sp - 16) X2. regval HR1 (1%bv : reg) OS_RET_LOOKUP X1.
    destruct (LOOK fx R1 M1 op 0 (sp - 16) (sp - 16) (Z_to_bv 64 OS_RET_LOOKUP) ROC1 X10 ltac:(lia) ltac:(intros _; exact X11) ltac:(intros E3; discriminate E3) X2
                ltac:(lia) ltac:(lia) ltac:(eapply mdef_sub; [exact HD1 | lia | lia]) ltac:(mlia)
                ltac:(intros a Ha; unfold zwin in *; lia)
                ltac:(unfold stack_room; replace (Z_to_bv 64 (sp - 16 - tc_lookup_stack tc)) with (Z_to_bv 64 (sp - 80 + (64 - tc_lookup_stack tc))) by (f_equal; lia);
                      apply (mdef_store_ok_off SEGS M1 (sp - 80) 80); [exact HD1 | lia | lia | lia | lia])
                ltac:(lia) ltac:(lia) ltac:(mlia) X1 ltac:(apply bv_eq; vm_compute; reflexivity))
      as (R2 & M2 & r & d & Hms2 & KEPT2 & Y10 & Hr & Fd & Hfound & Hhnd & FR2 & DK2).
    assert (ST2 : stores_in (zwin (sp - 80) (sp - 8)) M1 M2).
    { split; [| exact DK2]. intros a Ha. apply FR2. intros [Hz|Hz]; apply Ha; unfold zwin in *; lia. }
    assert (ROC2 : ro_clear Ly.L M2).
    { eapply ro_clear_frame; [exact ROC1 | eapply stores_in_frame_eq; [exact ST2 | intros a Ha; exact Ha] |].
      intros a (Himg & _) Hw. unfold zwin in Hw. exact (hi_offimg (AC:=AC) a ltac:(lia) Himg). }
    assert (Fra2 : fld SEGS M2 (sp - 8) 8 (bv_unsigned ret)).
    { eapply (fld_via_stores SEGS); [exact ST2 | intros y Hy; unfold zwin; lia | lia | cbn; lia | exact Fra]. }
    assert (Y2 : getr R2 2%bv = Z_to_bv 64 (sp - 16)) by (rewrite (KEPT2 2%bv) by inl; exact X2).
    assert (Y1 : getr R2 1%bv = Z_to_bv 64 OS_RET_LOOKUP) by (rewrite (KEPT2 1%bv) by inl; exact X1).
    assert (HD2 : mdef M2 (sp - 80) 80) by (eapply stores_in_mdef; [exact ST2 | exact HD1]).
    destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
    -
      subst r. specialize (Hhnd eq_refl).
      set (E2 := Eseed R2 [Z_to_bv 64 (d mod 2 ^ 64); ret]).
      assert (HR2 : regs_ok E2 sr_id R2) by (apply regs_ok_seed).
      pose proof (Z.mod_pos_bound d (2 ^ 64) ltac:(lia)) as Hdm.
      assert (Fd' : cellw SEGS M2 (sp - 16) 8 (d mod 2 ^ 64)).
      { split; [cbn; lia|]. change (N.to_nat 8) with 8%nat. unfold fld in Fd. rewrite Fd. do 2 f_equal. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia. reflexivity. }
      assert (HK2 : know_ok SEGS E2 M2 [KRange (EVar 2) (2 ^ 40) (2 ^ 47); KRange (EVar 10) 0 0;
                                        KWord (SA (EVar 2) 0) (N.to_nat 8) (EVar 32); KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 33)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv Y2. - krv Y10.
        - kwe Fd' Y2.
        - kwe Fra2 Y2. }
      xrun_at HR2 HK2 fx OS_RET_LOOKUP (seg_rom SEGS) 20%nat [TC_IDESC_NAME] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK2. rename R' into R3. rename HR' into HR3. rename Hms into Hms3.
      regval HR3 (10%bv : reg) (d mod 2 ^ 64) Z10. regval HR3 (1%bv : reg) OS_RET_NAME Z1.
      assert (Z10' : getr R3 10%bv = Z_to_bv 64 d) by (rewrite Z10; apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; reflexivity).
      destruct (NAME fx R3 M2 (Z_to_bv 64 OS_RET_NAME) ROC2 ltac:(exists d, op; split; [exact Hhnd | exact Z10']) Z1 ltac:(apply bv_eq; vm_compute; reflexivity))
        as (R4 & Hms4 & KEPT4 & p & n & ROS & Hn & W10).

      set (E4 := Eseed R4 [ret]).
      assert (V2 : getr R4 2%bv = Z_to_bv 64 (sp - 16)) by (rewrite (KEPT4 2%bv) by inl; regval HR3 (2%bv : reg) (sp - 16) X; exact X).
      assert (HR4 : regs_ok E4 sr_id R4) by (apply regs_ok_seed).
      assert (HK4 : know_ok SEGS E4 M2 [KRange (EVar 2) (2 ^ 40) (2 ^ 47); KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 32)]).
      { repeat apply Forall_cons; try apply Forall_nil. - krv V2. - kwe Fra2 V2. }
      xrun_at HR4 HK4 fx OS_RET_NAME (seg_rom SEGS) 20%nat [OS_RETPC] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK4. rename R' into R5. rename HR' into HR5. rename Hms into Hms5.
      rreg HR5 (1%bv : reg) V1. evs_in V1.
      exists R5, M2, p, n. split; [|split; [|split; [|split; [exact ROS | split; [exact Hn|]]]]].
      + eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|].
        apply (ret_at SEGS OS_RETPC R5 M2 (seg_rom SEGS) ret ltac:(vm_refl_bv) V1 Hret).
      + intros rr Hrr. unfold callee_saved in Hrr. cbn in Hrr.
        repeat (destruct Hrr as [<-|Hrr]; [kept_chain HR5 KEPT4 HR3 KEPT2 HR1|]). destruct Hrr.
      + regval HR5 (10%bv : reg) p X; exact X.
      + eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact ST2 | ..]; intros a Ha; unfold zwin in *; lia.
    -
      set (E2 := Eseed R2 [ret]).
      assert (HR2 : regs_ok E2 sr_id R2) by (apply regs_ok_seed).
      assert (HK2 : know_ok SEGS E2 M2 [KRange (EVar 2) (2 ^ 40) (2 ^ 47); KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 32)]).
      { repeat apply Forall_cons; try apply Forall_nil. - krv Y2. - kwe Fra2 Y2. }
      xrun_at HR2 HK2 fx OS_RET_LOOKUP (seg_rom SEGS) 20%nat [TC_IDESC_NAME; OS_RETPC; 0x6b11c] (SCR [false] [] []) 40%N.
      { repeat apply Forall_cons; try apply Forall_nil. cbn [sc_denot]. evs. gnorm (10%bv : reg). rewrite Y10.
        pose proof (Z.mod_pos_bound r (2 ^ 64) ltac:(lia)) as Hrm.
        replace (Z_to_bv 64 r) with (Z_to_bv 64 (r mod 2 ^ 64)) by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; reflexivity).
        rewrite ?br_eq, ?br_ne by lia.
        first [ apply Z.eqb_neq; mlia
              | apply (proj2 (Bool.negb_true_iff _)); apply Z.eqb_neq; mlia
              | apply (proj2 (Bool.negb_false_iff _)); apply Z.eqb_eq; mlia
              | match goal with |- ?g => idtac "SCGOAL" g; fail end ]. }
      clear HK2. rename R' into R3. rename HR' into HR3. rename Hms into Hms3.
      rreg HR3 (1%bv : reg) V1. evs_in V1.
      exists R3, M2, 0x1109c, 7. split; [|split; [|split; [|split; [exact ro_1109c | split; [lia|]]]]].
      + eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        apply (ret_at SEGS 0x6b11c R3 M2 (seg_rom SEGS) ret ltac:(vm_refl_bv) V1 Hret).
      + intros rr Hrr. unfold callee_saved in Hrr. cbn in Hrr.
        repeat (destruct Hrr as [<-|Hrr]; [kept_chain HR3 KEPT2 HR1|]). destruct Hrr.
      + regval HR3 (10%bv : reg) 0x1109c X; exact X.
      + eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact ST2 | ..]; intros a Ha; unfold zwin in *; lia.
  Qed.
End OpStr.
End ExhOpStr.

Module Exhausted2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.Classical_Prop Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagVia OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagViaS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1.DiagStmtsEx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SbOverflow OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Xsputn OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1.ExhLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final.FinalS1.ExhOpStr OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition XR_CTOR : Z := 0x694ac.
Definition XR_C1 : Z := 0x694f8.
Definition XR_OPS : Z := 0x69500.
Definition XR_SL1 : Z := 0x69508.
Definition XR_C2 : Z := 0x69518.
Definition XR_C3 : Z := 0x6952c.
Definition XR_U1 : Z := 0x69538.
Definition XR_C4 : Z := 0x69568.
Definition XR_OTS : Z := 0x69570.
Definition XR_SL2 : Z := 0x69578.
Definition XR_C5 : Z := 0x69588.
Definition XR_C6 : Z := 0x6959c.
Definition XR_U2 : Z := 0x695ac.
Definition XR_C7 : Z := 0x695c0.
Definition XR_DTOR : Z := 0x695cc.
Definition X_RETPC : Z := 0x695e8.

Section Exh.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis DN : diag_needs MI ST.
  Variables (G : grammar) (tc : tabl_consts) (idesc : Z -> Z -> Prop).
  Hypothesis EN : exhausted_needs G tc idesc.

  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  Let MSP : 0 <= MALLOC_STACK MI <= 8192. Proof. exact (dn_mstack MI ST DN). Qed.
  Let DL : ds_rep_laws SEGS Ly.L MI ST dcS1 (ds_rep MI). Proof. exact (diag_laws MI ST). Qed.

  Section Call.
    Context {fx : FPState}.
    Variables (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret this pcons nwords widx icount inst_offset opcode type : Z) (K : TSet).
    Hypothesis CB : callB MI ST A s R M model sp ret 12288.
    Hypothesis ROC : ro_clear Ly.L M.
    Hypothesis Hio : 0 <= inst_offset < 2 ^ 63.
    Hypothesis Hop : 0 <= opcode < 2 ^ 16.
    Hypothesis Hty : 0 <= type < 2 ^ 32.
    Hypothesis PL : placed MI A this 288.
    Hypothesis Hthis : this + 288 <= 2 ^ 47.
    Hypothesis THW : forall a, zwin this (this + 288) a -> ~ zwin (sp - 12288) sp a.
    Hypothesis F56 : fld SEGS M (this + 56) 8 nwords.
    Hypothesis F72 : fld SEGS M (this + 72) 8 widx.
    Hypothesis Hnw : 0 <= nwords < 2 ^ 63.
    Hypothesis Hwi : 0 <= widx < 2 ^ 63.
    Hypothesis ROOM1 : ds_room1 SEGS Ly.L MI A.
    Hypothesis POST : forall A' R' M' model' (J : Z -> Prop),
        retB MI ST A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (2 ^ 64 - 4) ->
        Permutation (live MI A') (live MI A) ->
        junk_ok MI A J ->
        eff MI A A' M M' (sp - 12288, sp) (fun a => J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    #[local] Notation sp' := (sp - 512).
    #[local] Notation xinv := (Exhausted1.xinv MI ST A s R M model sp ret).
    #[local] Notation xregs := (Exhausted1.xregs R sp this).
    #[local] Notation XSTEP := (Exhausted1.xinv_step MI ST DN A s R M model sp ret nwords widx CB Hnw Hwi).
    #[local] Notation XSTORES := (Exhausted1.xinv_stores MI ST A s R M model sp ret CB).
    #[local] Notation XCALLB := (Exhausted1.xinv_callB MI ST A s R M model sp ret nwords widx CB ROC Hnw Hwi).
    #[local] Notation XTHIS := (Exhausted1.xinv_this MI ST A s R M model sp ret this nwords widx CB PL Hthis THW F56 F72).
    #[local] Notation XROC := (Exhausted1.xinv_roc MI ST A s R M model sp ret CB ROC).
    #[local] Notation XLEN := (Exhausted1.xinv_len MI ST A s R M model sp ret).
    #[local] Notation SCSTR := (Exhausted1.stage_cstr MI ST DN A s R M model sp ret this nwords widx K CB ROC Hnw Hwi ROOM1).
    #[local] Notation SU64 := (Exhausted1.stage_u64 MI ST DN A s R M model sp ret this nwords widx K CB ROC Hnw Hwi ROOM1).

    Lemma ctx : alloc_ceiling + 12288 <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0 <= ret < 2 ^ 64 /\
                getr R 2%bv = Z_to_bv 64 sp /\ getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\
                getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) /\ 0 < this.
    Proof using AC MI ST A s R M model sp ret this CB PL.
      clear Hnw Hwi Hio Hop Hty. destruct CB as [AI MS ROC' SXI SXH [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp] Hceil HROOM Hwin Hown_sx Herr_sx].
      assert (Hth0 : 0 < this).
      { destruct PL as [H|(q & k & Hin & Hq & _)]; [pose proof ac_bounds_lit; lia | pose proof (ai_live_block MI A M model q k AI Hin); lia]. }
      repeat split; try assumption; lia.
    Qed.

    Ltac xr HR K2 :=
      unfold Exhausted1.xregs; repeat match goal with |- _ /\ _ => split end;
      first [ intros rr Hrr; cbn in Hrr; repeat (destruct Hrr as [<-|Hrr]; [kept_chain HR K2|]); destruct Hrr
            | kept_chain HR K2 ].

    Lemma stage9 : forall A1 M1 model1 len B1 JJ R1 s0 s2 s3,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 s0 s2 s3 ->
      srealizes SEGS (cfg fx R1 XR_C7 M1 model1) K.
    Proof using AC RRND MI ST DN fx A s R M model sp ret this nwords widx inst_offset opcode type K CB ROC Hio Hop Hty PL Hnw Hwi POST.
      intros A1 M1 model1 len B1 JJ R1 s0 s2 s3 X XR.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS).
      pose proof X as [AI1 MS1 FS1 FDS1 SX1 DS1 XF1 JJ1 EFF1 FR1 FRD1 STK1].
      pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS1) as Ferr. change ((-4) mod 2 ^ 32) with 4294967292 in Ferr.
      set (E := Eseed R1 []).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512); KWord (SA (EVar 2) 360) (N.to_nat 4) (ELit 4294967292)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv X2.
        - kwv Ferr X2. }
      xruns HR HK 20%nat [A_DS_DTOR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_DTOR V1. regval HR2 (10%bv : reg) (sp - 512) V10.
      eapply (ds_dtor_S MI ST DN fx A1 s R2 M1 model1 sp' XR_DTOR EXH_S sp' (-4) len B1 K).
      - apply (XCALLB _ _ _ _ _ _ R2 XR_DTOR X V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_DTOR; lia)); kept_chain HR2.
      - unfold EXH_S. lia.
      - exact (XROC _ _ _ _ _ _ X).
      - exact V10.
      - exact DS1.
      - exact (Exhausted1.xinv_above MI ST A s R M model sp ret CB _ _ _ _ _ _ X).
      -
        intros A' R3 M3 model3 RB XF HDM EFF. destruct RB as [AI3 MS3 FS3 FDS3 SX3 KP].
        unfold EXH_S in EFF.
        destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS1) as [_ HB1].
        assert (LOW : forall a, ds_foot sp' B1 a -> a < alloc_ceiling \/ (sp' <= a < sp' + 392)).
        { intros a Hf. exact (Exhausted1.xinv_foot MI ST A s R M model sp ret _ _ _ _ _ _ a X (or_introl Hf)). }
        assert (FR3 : slots SEGS M3 sp [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]).
        { eapply slots_agree; [exact FR1 | cbn; lia | lia | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
          eapply agree_on_weaken; [eapply (agree_hi_via_eff MI A1 A' M1 M3 model1 model3 _ _ (sp - 120) sp); [exact EFF | exact AI1 | exact AI3 | lia | lia | replace (sp - (sp - 120)) with 120 by lia; exact FRD1 | intros a Ha HF; destruct (LOW a HF); lia | cbn; lia] |].
          intros a Ha. unfold zwin in *. lia. }

        set (E3 := Eseed R3 [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]).
        assert (Y2 : getr R3 2%bv = Z_to_bv 64 sp') by (rewrite (KP 2%bv) by inl; kept_chain HR2).
        assert (Y8 : getr R3 8%bv = Z_to_bv 64 18446744073709551612).
        { rewrite (KP 8%bv) by inl. rreg HR2 (8%bv : reg) Q8; rewrite Q8. evs. reflexivity. }
        assert (HR3 : regs_ok E3 sr_id R3) by (apply regs_ok_seed).
        assert (HK3 : know_ok SEGS E3 M3 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512);
           KWord (SA (EVar 2) 504) (N.to_nat 8) (EVar 32); KWord (SA (EVar 2) 496) (N.to_nat 8) (EVar 33); KWord (SA (EVar 2) 488) (N.to_nat 8) (EVar 34);
           KWord (SA (EVar 2) 480) (N.to_nat 8) (EVar 35); KWord (SA (EVar 2) 472) (N.to_nat 8) (EVar 36)]).
        { repeat apply Forall_cons; try apply Forall_nil.
          - krv Y2.
          - kwe (FR3 0%nat ltac:(cbn; lia)) Y2. - kwe (FR3 1%nat ltac:(cbn; lia)) Y2. - kwe (FR3 2%nat ltac:(cbn; lia)) Y2.
          - kwe (FR3 3%nat ltac:(cbn; lia)) Y2. - kwe (FR3 4%nat ltac:(cbn; lia)) Y2. }
        xruns HR3 HK3 20%nat [X_RETPC] (SCR [] [] []) 40%N.
        { scs_auto. }
        clear HK3. rename HR' into HR4. rename R' into R4.
        regval HR4 (1%bv : reg) ret W1.
        eapply srz_msteps; [exact (ms_halt _ MS3) | exact (ms_lazy _ MS3) | apply (ret_at SEGS X_RETPC R4 M3 _ (Z_to_bv 64 ret) ltac:(vm_refl_bv) W1 Hret) |].
        apply (POST A' R4 M3 model3 (fun a => JJ a \/ blkpart B1 a)).
        + constructor.
          * exact AI3. * exact MS3. * rewrite FS3; exact FS1. * rewrite FDS3; exact FDS1. * exact SX3.
          * intros r Hr. unfold callee_saved in Hr. cbn in Hr.
            repeat (destruct Hr as [<-|Hr]; [kept_chain HR4 KP HR2 XCS|]). destruct Hr.
        + rreg HR4 (10%bv : reg) Q10; rewrite Q10. evs. gnorm (8%bv : reg). rewrite Y8. apply bv_eq. vm_compute. reflexivity.
        + destruct CB as [AI _ _ _ _ _ _ _ _ _ _].
          eapply (blk_xfer_nil_perm MI A A' M M3 model model3); [exact AI | exact AI3 | exact (blk_xfer_nil_trans _ _ _ _ _ XF1 XF)].
        + apply junk_ok_or; [exact JJ1|]. eapply (blkpart_junk MI A A1 M1 model1 B1); [exact AI1 | exact XF1 | intros [q k] Hb; exact (proj1 (HB1 q k Hb))].
        + pose proof (eff_widen MI A1 A' M1 M3 _ (sp - 12288, sp) _ EFF ltac:(cbn; lia) ltac:(cbn; lia)) as E12.
          assert (WUN : forall a, W_of (sp - 12288, sp) a -> ~ owned MI A' a).
          { intros a Ha. unfold W_of in Ha. cbn in Ha. apply (hi_unowned MI A' M3 model3); [exact AI3 | lia]. }
          pose proof (eff_trans _ _ _ _ _ _ _ _ _ _ EFF1 E12 WUN) as E02. cbn beta in E02.
          eapply (eff_drop_window MI); [exact E02|]. intros a Ha.
          cbn beta in Ha. assert (Hc : ds_foot sp' B1 a \/ JJ a) by (destruct Ha as [Ha|Ha]; [exact Ha | left; exact Ha]).
          destruct Hc as [Hf | Hj]; [| left; left; exact Hj].
          unfold ds_foot, DS_SIZE in Hf. destruct Hf as [Hz | Hb]; [| left; right; exact Hb].
          right. unfold zwin in Hz. split; [unfold W_of; cbn; lia|]. split; [| apply (hi_unowned MI A' M3 model3); [exact AI3 | lia]].
          replace a with (sp' + (a - sp')) by lia. apply HDM. unfold DS_SIZE. lia.
    Qed.

    Lemma stage8 : forall A1 M1 model1 len B1 JJ R1 s0 s2 s3,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 s0 s2 s3 -> len + 1 <= DS_MAXLEN ->
      srealizes SEGS (cfg fx R1 XR_U2 M1 model1) K.
    Proof using AC RRND MI ST DN fx A s R M model sp ret this nwords widx inst_offset opcode type K CB ROC Hio Hop Hty PL Hnw Hwi ROOM1 POST.
      intros A1 M1 model1 len B1 JJ R1 s0 s2 s3 X XR BUD.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      set (E := Eseed R1 []).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv X2).
      xruns HR HK 20%nat [A_PUT_CSTR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_C7 V1. regval HR2 (10%bv : reg) (sp - 512) V10. regval HR2 (11%bv : reg) 0x11098 V11. regval HR2 (12%bv : reg) 1 V12.
      apply (SCSTR _ _ _ _ _ _ R2 s0 s2 s3 0x11098 1 XR_C7 X ltac:(xr HR2 XCS) V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_C7; lia) V10 V11 V12 ro_11098 BUD).
      intros A2 M2 model2 B2 JJ2 R3 X' XR' _. exact (stage9 _ _ _ _ _ _ _ _ _ _ X' XR').
    Qed.

    Lemma stage7 : forall A1 M1 model1 len B1 JJ R1 s2 s3,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 inst_offset s2 s3 -> len + 25 <= DS_MAXLEN ->
      srealizes SEGS (cfg fx R1 XR_C6 M1 model1) K.
    Proof using AC RRND MI ST DN fx A s R M model sp ret this nwords widx inst_offset opcode type K CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi ROOM1 POST.
      intros A1 M1 model1 len B1 JJ R1 s2 s3 X XR BUD.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      destruct (XTHIS _ _ _ _ _ _ X) as [G56 G72].
      set (E := Eseed R1 [Z_to_bv 64 widx]).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512); KRange (EVar 9) 1 (2 ^ 47 - 288); KRange (EVar 8) 0 (2 ^ 63); KRange (EVar 32) 0 (2 ^ 63);
                                      KWord (SA (EVar 9) 72) (N.to_nat 8) (EVar 32)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv X2. - krv X9. - krv X8. - eapply krange_var; [evs; reflexivity | lia | lia].
        - kwv G72 X9. }
      xruns HR HK 20%nat [A_PUT_U64] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_U2 V1. regval HR2 (10%bv : reg) (sp - 512) V10.
      regval HR2 (11%bv : reg) ((widx - inst_offset) mod 2 ^ 64) V11.
      apply (SU64 _ _ _ _ _ _ R2 inst_offset s2 s3 ((widx - inst_offset) mod 2 ^ 64) XR_U2 X ltac:(xr HR2 XCS) V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_U2; lia) V10 V11
               ltac:(apply Z.mod_pos_bound; lia) ltac:(lia)).
      intros A2 M2 model2 B2 JJ2 R3 X' XR' _. eapply (stage8 _ _ _ _ _ _ _ _ _ _ X' XR'). lia.
    Qed.

    Lemma stage6 : forall A1 M1 model1 len B1 JJ R1 s2 s3,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 inst_offset s2 s3 -> len + 49 <= DS_MAXLEN ->
      srealizes SEGS (cfg fx R1 XR_C5 M1 model1) K.
    Proof using AC RRND MI ST DN fx A s R M model sp ret this nwords widx inst_offset opcode type K CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi ROOM1 POST.
      intros A1 M1 model1 len B1 JJ R1 s2 s3 X XR BUD.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      set (E := Eseed R1 []).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv X2).
      xruns HR HK 20%nat [A_PUT_CSTR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_C6 V1. regval HR2 (10%bv : reg) (sp - 512) V10. regval HR2 (11%bv : reg) 0x1064a V11. regval HR2 (12%bv : reg) 24 V12.
      apply (SCSTR _ _ _ _ _ _ R2 inst_offset s2 s3 0x1064a 24 XR_C6 X ltac:(xr HR2 XCS) V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_C6; lia) V10 V11 V12 ro_1064a ltac:(lia)).
      intros A2 M2 model2 B2 JJ2 R3 X' XR' _. eapply (stage7 _ _ _ _ _ _ _ _ _ X' XR'). lia.
    Qed.

    Lemma stage5 : forall A1 M1 model1 len B1 JJ R1 s3,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 inst_offset type s3 -> len + 305 <= DS_MAXLEN ->
      srealizes SEGS (cfg fx R1 XR_C4 M1 model1) K.
    Proof using AC RRND MI ST DN G tc idesc EN fx A s R M model sp ret this nwords widx inst_offset opcode type K CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi ROOM1 POST.
      intros A1 M1 model1 len B1 JJ R1 s3 X XR BUD.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      pose proof EN as (_ & _ & TOT & TSL & _ & _ & _ & OTS & SLEN).
      unfold operand_type_str_stmt, PrsGrammar.leafA in OTS. unfold strlen_ro_stmt, PrsGrammar.leafA in SLEN. rewrite TOT in OTS. rewrite TSL in SLEN.
      pose proof (XROC _ _ _ _ _ _ X) as ROC1.

      set (E := Eseed R1 []).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv X2).
      xruns HR HK 20%nat [TC_OPERAND_TYPE_STR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_OTS V1. regval HR2 (10%bv : reg) type V10.
      destruct (OTS fx R2 M1 (Z_to_bv 64 XR_OTS) ROC1 ltac:(exists type; split; [exact Hty | exact V10]) V1 ltac:(apply bv_eq; vm_compute; reflexivity))
        as (R3 & Hms3 & KP3 & p & n & ROS & Hn & W10).
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | exact Hms3 |].
      pose proof ROS as (Hp0 & Hn0 & Hpn & _).

      set (E3 := Eseed R3 [Z_to_bv 64 p]).
      assert (Y2 : getr R3 2%bv = Z_to_bv 64 sp') by (rewrite (KP3 2%bv) by inl; kept_chain HR2).
      assert (HR3 : regs_ok E3 sr_id R3) by (apply regs_ok_seed).
      assert (HK3 : know_ok SEGS E3 M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv Y2).
      xruns HR3 HK3 20%nat [TC_STRLEN] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK3. rename HR' into HR4. rename R' into R4.
      regval HR4 (1%bv : reg) XR_SL2 Z1. assert (Z10 : getr R4 10%bv = Z_to_bv 64 p) by kept_chain HR4.
      destruct (SLEN fx R4 M1 (Z_to_bv 64 XR_SL2) ROC1 ltac:(exists p, n; split; [exact ROS | exact Z10]) Z1 ltac:(apply bv_eq; vm_compute; reflexivity))
        as (R5 & Hms5 & KP5 & W10').
      specialize (W10' p n ROS Z10).
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | exact Hms5 |].

      set (E5 := Eseed R5 [Z_to_bv 64 p; Z_to_bv 64 n]).
      assert (Y2' : getr R5 2%bv = Z_to_bv 64 sp') by (rewrite (KP5 2%bv) by inl; kept_chain HR4).
      assert (Y18 : getr R5 18%bv = Z_to_bv 64 p) by (rewrite (KP5 18%bv) by inl; kept_chain HR4).
      assert (HR5 : regs_ok E5 sr_id R5) by (apply regs_ok_seed).
      assert (HK5 : know_ok SEGS E5 M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv Y2').
      xruns HR5 HK5 20%nat [A_PUT_CSTR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK5. rename HR' into HR6. rename R' into R6.
      regval HR6 (1%bv : reg) XR_C5 V1'. regval HR6 (10%bv : reg) (sp - 512) V10'.
      assert (V11 : getr R6 11%bv = Z_to_bv 64 p) by kept_chain HR6.
      assert (V12 : getr R6 12%bv = Z_to_bv 64 n) by kept_chain HR6.
      assert (XR6 : xregs R6 inst_offset p s3).
      { unfold Exhausted1.xregs. repeat match goal with |- _ /\ _ => split end.
        - kept_chain HR6. - kept_chain HR6 KP5 HR4 KP3 HR2. - kept_chain HR6 KP5 HR4 KP3 HR2.
        - kept_chain HR6 KP5 HR4 KP3 HR2. - kept_chain HR6 KP5 HR4 KP3 HR2.
        - exact Y18 || kept_chain HR6. - kept_chain HR6 KP5 HR4 KP3 HR2.
        - intros rr Hrr; cbn in Hrr; repeat (destruct Hrr as [<-|Hrr]; [kept_chain HR6 KP5 HR4 KP3 HR2 XCS|]); destruct Hrr. }
      apply (SCSTR _ _ _ _ _ _ R6 inst_offset p s3 p n XR_C5 X XR6 V1' ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_C5; lia) V10' V11 V12 ROS ltac:(lia)).
      intros A2 M2 model2 B2 JJ2 R7 X' XR' _. eapply (stage6 _ _ _ _ _ _ _ _ _ X' XR'). lia.
    Qed.
  End Call.
End Exh.
End Exhausted2.

Module Exhausted3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.Classical_Prop Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagVia OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagViaS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1.DiagStmtsEx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SbOverflow OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Xsputn OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1.ExhLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final.FinalS1.ExhOpStr OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final.FinalS1.Exhausted2.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Section Exh.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis DN : diag_needs MI ST.
  Variables (G : grammar) (tc : tabl_consts) (idesc : Z -> Z -> Prop).
  Hypothesis EN : exhausted_needs G tc idesc.

  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  Let MSP : 0 <= MALLOC_STACK MI <= 8192. Proof. exact (dn_mstack MI ST DN). Qed.
  Let DL : ds_rep_laws SEGS Ly.L MI ST dcS1 (ds_rep MI). Proof. exact (diag_laws MI ST). Qed.

  Section Call.
    Context {fx : FPState}.
    Variables (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret this pcons nwords widx icount inst_offset opcode type : Z) (K : TSet).
    Hypothesis CB : callB MI ST A s R M model sp ret 12288.
    Hypothesis ROC : ro_clear Ly.L M.
    Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 this.
    Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 inst_offset.
    Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 opcode.
    Hypothesis Ha3 : getr R 13%bv = Z_to_bv 64 type.
    Hypothesis Hio : 0 <= inst_offset < 2 ^ 63.
    Hypothesis Hop : 0 <= opcode < 2 ^ 16.
    Hypothesis Hty : 0 <= type < 2 ^ 32.
    Hypothesis PL : placed MI A this 288.
    Hypothesis Hthis : this + 288 <= 2 ^ 47.
    Hypothesis THW : forall a, zwin this (this + 288) a -> ~ zwin (sp - 12288) sp a.
    Hypothesis F8 : fld SEGS M (this + 8) 8 pcons.
    Hypothesis F56 : fld SEGS M (this + 56) 8 nwords.
    Hypothesis F72 : fld SEGS M (this + 72) 8 widx.
    Hypothesis F80 : fld SEGS M (this + 80) 8 icount.
    Hypothesis Hnw : 0 <= nwords < 2 ^ 63.
    Hypothesis Hwi : 0 <= widx < 2 ^ 63.
    Hypothesis Hic : 0 <= icount < 2 ^ 63.
    Hypothesis OBJ : obj_ok MI A sp 12288 pcons 48.
    Hypothesis Hpc : pcons + 48 <= 2 ^ 47.
    Hypothesis F32 : fld SEGS M (pcons + 32) 8 0.
    Hypothesis ROOM1 : ds_room1 SEGS Ly.L MI A.
    Hypothesis POST : forall A' R' M' model' (J : Z -> Prop),
        retB MI ST A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (2 ^ 64 - 4) ->
        Permutation (live MI A') (live MI A) ->
        junk_ok MI A J ->
        eff MI A A' M M' (sp - 12288, sp) (fun a => J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    #[local] Notation sp' := (sp - 512).
    #[local] Notation xinv := (Exhausted1.xinv MI ST A s R M model sp ret).
    #[local] Notation xregs := (Exhausted1.xregs R sp this).
    #[local] Notation XSTEP := (Exhausted1.xinv_step MI ST DN A s R M model sp ret nwords widx CB Hnw Hwi).
    #[local] Notation XSTORES := (Exhausted1.xinv_stores MI ST A s R M model sp ret CB).
    #[local] Notation XCALLB := (Exhausted1.xinv_callB MI ST A s R M model sp ret nwords widx CB ROC Hnw Hwi).
    #[local] Notation XTHIS := (Exhausted1.xinv_this MI ST A s R M model sp ret this nwords widx CB PL Hthis THW F56 F72).
    #[local] Notation XROC := (Exhausted1.xinv_roc MI ST A s R M model sp ret CB ROC).
    #[local] Notation XLEN := (Exhausted1.xinv_len MI ST A s R M model sp ret).
    #[local] Notation SCSTR := (Exhausted1.stage_cstr MI ST DN A s R M model sp ret this nwords widx K CB ROC Hnw Hwi ROOM1).
    #[local] Notation SU64 := (Exhausted1.stage_u64 MI ST DN A s R M model sp ret this nwords widx K CB ROC Hnw Hwi ROOM1).
    #[local] Notation S5 := (Exhausted2.stage5 MI ST DN G tc idesc EN A s R M model sp ret this nwords widx inst_offset opcode type K
                               CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi ROOM1 POST).

    Lemma ctx : alloc_ceiling + 12288 <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0 <= ret < 2 ^ 64 /\
                getr R 2%bv = Z_to_bv 64 sp /\ getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\
                getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) /\ 0 < this.
    Proof using AC MI ST A s R M model sp ret this CB PL.
      clear Hnw Hwi Hio Hop Hty Hic. destruct CB as [AI MS ROC' SXI SXH [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp] Hceil HROOM Hwin Hown_sx Herr_sx].
      assert (Hth0 : 0 < this).
      { destruct PL as [H|(q & k & Hin & Hq & _)]; [pose proof ac_bounds_lit; lia | pose proof (ai_live_block MI A M model q k AI Hin); lia]. }
      repeat split; try assumption; lia.
    Qed.

    Ltac xr HR K2 :=
      unfold Exhausted1.xregs; repeat match goal with |- _ /\ _ => split end;
      first [ intros rr Hrr; cbn in Hrr; repeat (destruct Hrr as [<-|Hrr]; [kept_chain HR K2|]); destruct Hrr
            | kept_chain HR K2 ].

    Lemma stage4 : forall A1 M1 model1 len B1 JJ R1 s3,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 inst_offset type s3 -> len + 317 <= DS_MAXLEN ->
      srealizes SEGS (cfg fx R1 XR_U1 M1 model1) K.
    Proof using AC RRND MI ST DN G tc idesc EN fx A s R M model sp ret this nwords widx icount inst_offset opcode type K CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi Hic ROOM1 POST.
      intros A1 M1 model1 len B1 JJ R1 s3 X XR BUD.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      destruct (XTHIS _ _ _ _ _ _ X) as [G56 G72].
      set (E := Eseed R1 [Z_to_bv 64 nwords; Z_to_bv 64 widx]).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512); KRange (EVar 9) 1 (2 ^ 47 - 288);
                                      KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 33) 0 (2 ^ 63);
                                      KWord (SA (EVar 9) 56) (N.to_nat 8) (EVar 32); KWord (SA (EVar 9) 72) (N.to_nat 8) (EVar 33)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv X2. - krv X9.
        - eapply krange_var; [evs; reflexivity | lia | lia]. - eapply krange_var; [evs; reflexivity | lia | lia].
        - kwv G56 X9. - kwv G72 X9. }
      destruct (Z.lt_ge_cases widx nwords) as [Hlt | Hge].
      -
        xruns HR HK 20%nat [A_PUT_CSTR] (SCR [true] [] []) 40%N.
        { scs_auto. }
        clear HK. rename HR' into HR2. rename R' into R2.
        regval HR2 (1%bv : reg) XR_C4 V1. regval HR2 (10%bv : reg) (sp - 512) V10. regval HR2 (11%bv : reg) 0x13af3 V11. regval HR2 (12%bv : reg) 12 V12.
        apply (SCSTR _ _ _ _ _ _ R2 inst_offset type s3 0x13af3 12 XR_C4 X ltac:(xr HR2 XCS) V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_C4; lia) V10 V11 V12 ro_13b59 ltac:(lia)).
        intros A2 M2 model2 B2 JJ2 R3 X' XR' _. eapply (S5 _ _ _ _ _ _ _ _ X' XR'). lia.
      -
        xruns HR HK 20%nat [A_PUT_CSTR] (SCR [false] [] []) 40%N.
        { scs_auto. }
        clear HK. rename HR' into HR2. rename R' into R2.
        regval HR2 (1%bv : reg) XR_C4 V1. regval HR2 (10%bv : reg) (sp - 512) V10. regval HR2 (11%bv : reg) 0x140e5 V11. regval HR2 (12%bv : reg) 10 V12.
        apply (SCSTR _ _ _ _ _ _ R2 inst_offset type s3 0x140e5 10 XR_C4 X ltac:(xr HR2 XCS) V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_C4; lia) V10 V11 V12 ro_1414b ltac:(lia)).
        intros A2 M2 model2 B2 JJ2 R3 X' XR' _. eapply (S5 _ _ _ _ _ _ _ _ X' XR'). lia.
    Qed.

    Lemma stage3 : forall A1 M1 model1 len B1 JJ R1 s3,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 inst_offset type s3 -> len + 341 <= DS_MAXLEN ->
      srealizes SEGS (cfg fx R1 XR_C3 M1 model1) K.
    Proof using AC RRND MI ST DN G tc idesc EN fx A s R M model sp ret this nwords widx icount inst_offset opcode type K CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi Hic ROOM1 POST.
      intros A1 M1 model1 len B1 JJ R1 s3 X XR BUD.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      set (E := Eseed R1 []).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv X2).
      xruns HR HK 20%nat [A_PUT_U64] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_U1 V1. regval HR2 (10%bv : reg) (sp - 512) V10. regval HR2 (11%bv : reg) inst_offset V11.
      apply (SU64 _ _ _ _ _ _ R2 inst_offset type s3 inst_offset XR_U1 X ltac:(xr HR2 XCS) V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_U1; lia) V10 V11
               ltac:(lia) ltac:(lia)).
      intros A2 M2 model2 B2 JJ2 R3 X' XR' _. eapply (stage4 _ _ _ _ _ _ _ _ X' XR'). lia.
    Qed.

    Lemma stage2 : forall A1 M1 model1 len B1 JJ R1 s3,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 inst_offset type s3 -> len + 359 <= DS_MAXLEN ->
      srealizes SEGS (cfg fx R1 XR_C2 M1 model1) K.
    Proof using AC RRND MI ST DN G tc idesc EN fx A s R M model sp ret this nwords widx icount inst_offset opcode type K CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi Hic ROOM1 POST.
      intros A1 M1 model1 len B1 JJ R1 s3 X XR BUD.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      set (E := Eseed R1 []).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv X2).
      xruns HR HK 20%nat [A_PUT_CSTR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_C3 V1. regval HR2 (10%bv : reg) (sp - 512) V10. regval HR2 (11%bv : reg) 0x11599 V11. regval HR2 (12%bv : reg) 18 V12.
      apply (SCSTR _ _ _ _ _ _ R2 inst_offset type s3 0x11599 18 XR_C3 X ltac:(xr HR2 XCS) V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_C3; lia) V10 V11 V12 ro_11599 ltac:(lia)).
      intros A2 M2 model2 B2 JJ2 R3 X' XR' _. eapply (stage3 _ _ _ _ _ _ _ _ X' XR'). lia.
    Qed.

    Lemma stage1 : forall A1 M1 model1 len B1 JJ R1,
      xinv A1 M1 model1 len B1 JJ -> xregs R1 inst_offset type opcode -> len + 615 <= DS_MAXLEN ->
      srealizes SEGS (cfg fx R1 XR_C1 M1 model1) K.
    Proof using AC RRND MI ST DN G tc idesc EN fx A s R M model sp ret this nwords widx icount inst_offset opcode type K CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi Hic ROOM1 POST.
      intros A1 M1 model1 len B1 JJ R1 X XR BUD.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      pose proof EN as (_ & _ & _ & TSL & _ & _ & _ & _ & SLEN).
      unfold strlen_ro_stmt, PrsGrammar.leafA in SLEN. rewrite TSL in SLEN.
      pose proof (XROC _ _ _ _ _ _ X) as ROC1.

      set (E := Eseed R1 []).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv X2).
      xruns HR HK 20%nat [A_OPCODE_STRING] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_OPS V1. regval HR2 (10%bv : reg) opcode V10. regval HR2 (2%bv : reg) (sp - 512) V2.
      assert (HD80 : mdef M1 (sp' - 80) 80).
      { pose proof (xi_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK. unfold EXH_S in STK. eapply mdef_sub; [exact STK | lia | lia]. }
      destruct (opcode_string G tc idesc EN fx R2 M1 sp' opcode (Z_to_bv 64 XR_OPS) ROC1 V10 Hop V2 ltac:(lia) ltac:(lia) ltac:(mlia)
                  HD80 V1 ltac:(apply bv_eq; vm_compute; reflexivity))
        as (R3 & M2 & p & n & Hms3 & KP3 & W10 & ROS & Hn256 & ST2).
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | exact Hms3 |].
      pose proof (XSTORES _ _ _ _ _ _ M2 (sp' - 80) X ST2 ltac:(lia)) as X2'.
      clear X. rename X2' into X.
      pose proof (XROC _ _ _ _ _ _ X) as ROC2. pose proof ROS as (Hp0 & Hn0 & Hpn & _).

      set (E3 := Eseed R3 [Z_to_bv 64 p]).
      assert (Y2 : getr R3 2%bv = Z_to_bv 64 sp') by (rewrite (KP3 2%bv) by inl; exact V2).
      assert (HR3 : regs_ok E3 sr_id R3) by (apply regs_ok_seed).
      assert (HK3 : know_ok SEGS E3 M2 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv Y2).
      xruns HR3 HK3 20%nat [TC_STRLEN] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK3. rename HR' into HR4. rename R' into R4.
      regval HR4 (1%bv : reg) XR_SL1 Z1. assert (Z10 : getr R4 10%bv = Z_to_bv 64 p) by kept_chain HR4.
      destruct (SLEN fx R4 M2 (Z_to_bv 64 XR_SL1) ROC2 ltac:(exists p, n; split; [exact ROS | exact Z10]) Z1 ltac:(apply bv_eq; vm_compute; reflexivity))
        as (R5 & Hms5 & KP5 & W10').
      specialize (W10' p n ROS Z10).
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | exact Hms5 |].

      set (E5 := Eseed R5 [Z_to_bv 64 p; Z_to_bv 64 n]).
      assert (Y2' : getr R5 2%bv = Z_to_bv 64 sp') by (rewrite (KP5 2%bv) by inl; kept_chain HR4).
      assert (Y19 : getr R5 19%bv = Z_to_bv 64 p) by (rewrite (KP5 19%bv) by inl; kept_chain HR4).
      assert (HR5 : regs_ok E5 sr_id R5) by (apply regs_ok_seed).
      assert (HK5 : know_ok SEGS E5 M2 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512)]) by (repeat apply Forall_cons; try apply Forall_nil; krv Y2').
      xruns HR5 HK5 20%nat [A_PUT_CSTR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK5. rename HR' into HR6. rename R' into R6.
      regval HR6 (1%bv : reg) XR_C2 V1'. regval HR6 (10%bv : reg) (sp - 512) V10'.
      assert (V11 : getr R6 11%bv = Z_to_bv 64 p) by kept_chain HR6.
      assert (V12 : getr R6 12%bv = Z_to_bv 64 n) by kept_chain HR6.
      assert (XR6 : xregs R6 inst_offset type p).
      { unfold Exhausted1.xregs. repeat match goal with |- _ /\ _ => split end.
        - kept_chain HR6. - kept_chain HR6 KP5 HR4 KP3 HR2. - kept_chain HR6 KP5 HR4 KP3 HR2.
        - kept_chain HR6 KP5 HR4 KP3 HR2. - kept_chain HR6 KP5 HR4 KP3 HR2.
        - kept_chain HR6 KP5 HR4 KP3 HR2. - exact Y19 || kept_chain HR6.
        - intros rr Hrr; cbn in Hrr; repeat (destruct Hrr as [<-|Hrr]; [kept_chain HR6 KP5 HR4 KP3 HR2 XCS|]); destruct Hrr. }
      apply (SCSTR _ _ _ _ _ _ R6 inst_offset type p p n XR_C2 X XR6 V1' ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_C2; lia) V10' V11 V12 ROS ltac:(lia)).
      intros A2 M3 model2 B2 JJ2 R7 X' XR' _. eapply (stage2 _ _ _ _ _ _ _ _ X' XR'). lia.
    Qed.

    Lemma stage0 : forall A1 M1 model1 B1 JJ R1,
      xinv A1 M1 model1 0 B1 JJ -> xregs R1 inst_offset type opcode ->
      fld SEGS M1 (sp' + 400) 2 0 -> fld SEGS M1 (sp' + 424) 2 0 ->
      srealizes SEGS (cfg fx R1 XR_CTOR M1 model1) K.
    Proof using AC RRND MI ST DN G tc idesc EN fx A s R M model sp ret this nwords widx icount inst_offset opcode type K CB ROC Hio Hop Hty PL Hthis THW F56 F72 Hnw Hwi Hic ROOM1 POST.
      intros A1 M1 model1 B1 JJ R1 X XR G400 G424.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof XR as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & XCS). pose proof (xi_ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MS1.
      set (E := Eseed R1 []).
      assert (HR : regs_ok E sr_id R1) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M1 [KRange (EVar 2) (2 ^ 40) (2 ^ 47 - 512);
                                      KWord (SA (EVar 2) 400) (N.to_nat 2) (ELit 0); KWord (SA (EVar 2) 424) (N.to_nat 2) (ELit 0)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - krv X2. - kwv G400 X2. - kwv G424 X2. }
      xruns HR HK 40%nat [A_PUT_CSTR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR2. rename R' into R2.
      regval HR2 (1%bv : reg) XR_C1 V1. regval HR2 (10%bv : reg) (sp - 512) V10. regval HR2 (11%bv : reg) 0x11738 V11. regval HR2 (12%bv : reg) 38 V12.
      apply (SCSTR _ _ _ _ _ _ R2 inst_offset type opcode 0x11738 38 XR_C1 X ltac:(xr HR2 XCS) V1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold XR_C1; lia) V10 V11 V12 ro_11738 ltac:(unfold DS_MAXLEN; lia)).
      intros A2 M2 model2 B2 JJ2 R3 X' XR' _. eapply (stage1 _ _ _ _ _ _ _ X' XR'). unfold DS_MAXLEN. lia.
    Qed.

    Lemma exh_main : srealizes SEGS (cfg fx R A_EXHAUSTED M model) K.
    Proof using AC RRND MI ST DN G tc idesc EN fx A s R M model sp ret this pcons nwords widx icount inst_offset opcode type K CB ROC Ha0 Ha1 Ha2 Ha3 Hio Hop Hty PL Hthis THW F8 F56 F72 F80 Hnw Hwi Hic OBJ Hpc F32 ROOM1 POST.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hsp & Hra & Hret & Hgp & Htp & Hth0). pose proof ac_bounds_lit as Hcv.
      pose proof CB as CB0. destruct CB0 as [AI MS ROC' SXI SXH _ _ HROOM Hwin Hown_sx Herr_sx].
      cbn [ly_gp ly_tp Ly.L] in Hgp, Htp.
      destruct OBJ as [PLc DJc].
      assert (HDstk : mdef M (sp - 12288) 12288).
      { eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia | intros x Hx; apply ly_noseg; lia]. }
      assert (Hth : this + 288 <= sp - 12288 \/ sp <= this).
      { destruct (Z.lt_ge_cases this sp); [left|right; lia].
        destruct (Z.lt_ge_cases (this + 288) (sp - 12288 + 1)); [lia|]. exfalso.
        destruct (Z.lt_ge_cases this (sp - 12288)).
        + apply (THW (sp - 12288)); unfold zwin; lia.
        + apply (THW this); unfold zwin; lia. }
      assert (Hpcw : 0 <= pcons /\ (pcons + 48 <= sp - 12288 \/ sp <= pcons)).
      { destruct PLc as [Hhi|(q & k & HIn & Hq & Hk)].
        - split; [lia|]. destruct (Z.lt_ge_cases pcons sp); [left|right; lia].
          destruct (Z.lt_ge_cases (pcons + 48) (sp - 12288 + 1)); [lia|]. exfalso.
          destruct (Z.lt_ge_cases pcons (sp - 12288)).
          + apply (DJc (sp - 12288)); unfold zwin; lia.
          + apply (DJc pcons); unfold zwin; lia.
        - pose proof (ai_live_block MI A M model q k AI HIn). lia. }

      set (E := Eseed R [Z_to_bv 64 pcons; Z_to_bv 64 icount]).
      assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M [KWr (SA (EVar 2) (-512)) (ELit 512); KRange (EVar 2) (2 ^ 40) (2 ^ 47); KAlign (EVar 2) 16;
                                     KRange (EVar 10) 1 (2 ^ 47 - 288); KRange (EVar 33) 0 (2 ^ 63);
                                     KWord (SA (EVar 10) 8) (N.to_nat 8) (EVar 32); KWord (SA (EVar 10) 80) (N.to_nat 8) (EVar 33);
                                     KDisj (SA (EVar 10) 0) (ELit 288) (SA (EVar 2) (-512)) (ELit 512)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - eapply kwr_stack; [evs; exact Hsp | reflexivity | lia | lia | eapply stack_room_mono; [exact HROOM | lia | lia | lia]].
        - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hsp16]. - krv Ha0.
        - eapply krange_var; [evs; reflexivity | lia | lia].
        - kwv F8 Ha0. - kwv F80 Ha0.
        - kdjx Ha0 Hsp this 288 sp 512. lia. }
      xruns HR HK 40%nat [A_DS_CTOR] (SCR [] [] []) 40%N.
      { scs_auto. }
      clear HK. rename HR' into HR1. rename R' into R1. wnorm_goal.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M1 := mm) end.
      regval HR1 (1%bv : reg) XR_CTOR X1. regval HR1 (2%bv : reg) (sp - 512) X2. regval HR1 (10%bv : reg) (sp - 512) X10.
      regval HR1 (11%bv : reg) (sp - 512 + 448) X11. regval HR1 (12%bv : reg) pcons X12. regval HR1 (13%bv : reg) (sp - 512 + 424) X13.
      regval HR1 (14%bv : reg) ((-4) mod 2 ^ 64) X14. regval HR1 (15%bv : reg) (sp - 512 + 400) X15.
      assert (Y3 : getr R1 3%bv = getr R 3%bv) by kept_chain HR1. assert (Y4 : getr R1 4%bv = getr R 4%bv) by kept_chain HR1.
      assert (ST1 : stores_in (zwin (sp - 112) sp) M M1) by (clear - M1 Hceil Hcv Hsphi Hretr Hic; subst M1; stores_tower).
      assert (SL1 : slots SEGS M1 sp [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv])
        by (clear - M1 Hceil Hcv Hsphi Hretr Hic; subst M1; slots_tower).
      assert (G424 : fld SEGS M1 (sp' + 424) 2 0).
      { clear - M1 Hceil Hcv Hsphi Hretr Hic. unfold fld. subst M1. peel.
        lazymatch goal with |- rdn _ (wbytes _ (Z_to_bv 64 ?bb) _) (Z_to_bv 64 ?aa) _ = _ => replace (Z_to_bv 64 aa) with (Z_to_bv 64 bb) by (f_equal; lia) end.
        rewrite <- (length_N_to_le_bytes 2 (Z_to_bv 64 0)) at 2. apply SeqExec.rdn_wbytes_hit. rewrite length_N_to_le_bytes, u64_of_Z by lia. lia. }
      assert (G400 : fld SEGS M1 (sp' + 400) 2 0).
      { clear - M1 Hceil Hcv Hsphi Hretr Hic. unfold fld. subst M1. peel.
        lazymatch goal with |- rdn _ (wbytes _ (Z_to_bv 64 ?bb) _) (Z_to_bv 64 ?aa) _ = _ => replace (Z_to_bv 64 aa) with (Z_to_bv 64 bb) by (f_equal; lia) end.
        rewrite <- (length_N_to_le_bytes 2 (Z_to_bv 64 0)) at 2. apply SeqExec.rdn_wbytes_hit. rewrite length_N_to_le_bytes, u64_of_Z by lia. lia. }
      assert (WNO : forall a, zwin (sp - 112) sp a -> ~ owned MI A a /\ ~ in_ranges (ly_img Ly.L) a /\ ~ sx_region ST a).
      { intros a Ha. unfold zwin in Ha. pose proof (Hwin a ltac:(unfold zwin; lia)) as [H1 H2]. split; [exact H1|]. split; [apply hi_offimg; lia | exact H2]. }
      assert (AI1 : ainv MI A M1 model) by (eapply stores_in_ainv; [exact AI | exact ST1 | intros a Ha; exact (proj1 (WNO a Ha))]).
      assert (SX1 : sx_inv ST s M1).
      { eapply stores_in_sx; [exact SXI | exact ST1 |]. intros a Ha. pose proof (WNO a Ha) as (_ & Hni & Hns).
        split; [exact Hns | intros Hr; apply Hni; apply ly_relro_img; exact Hr]. }
      assert (ROC1 : ro_clear Ly.L M1).
      { eapply ro_clear_frame; [exact ROC | eapply stores_in_frame_eq; [exact ST1 | intros a Ha; exact Ha] |].
        intros a (Himg & _) Hw. exact (proj1 (proj2 (WNO a Hw)) Himg). }
      assert (HDstk1 : mdef M1 (sp - 12288) 12288) by (eapply stores_in_mdef; [exact ST1 | exact HDstk]).
      apply (ds_ctor_S MI ST DN fx A s R1 M1 model sp' XR_CTOR EXH_S sp' (sp' + 448) pcons (sp' + 424) (-4) (sp' + 400) K).
      - constructor.
        + exact AI1. + exact MS. + exact (img_ro_clear_of' ST s M1 ROC1 SX1). + exact SX1. + exact SXH.
        + constructor; [exact X1 | apply bv_eq; vm_compute; reflexivity | unfold XR_CTOR; lia | exact X2 | mlia | lia
                       | rewrite Y3; exact Hgp | rewrite Y4; exact Htp].
        + unfold EXH_S. lia.
        + unfold stack_room, EXH_S. replace (Z_to_bv 64 (sp' - 11776)) with (Z_to_bv 64 (sp - 12288)) by (f_equal; lia).
          apply (mdef_store_ok SEGS M1 (sp - 12288) 12288); [exact HDstk1 | lia | lia | lia].
        + intros a Ha. unfold EXH_S in Ha. split; [apply (hi_unowned MI A M1 model); [exact AI1 | unfold zwin in Ha; lia] | apply (proj2 (Hwin a ltac:(unfold zwin in *; lia)))].
        + exact Hown_sx. + exact Herr_sx.
      - unfold EXH_S. lia.
      - exact ROC1.
      - exact X10. - rewrite X11; f_equal; lia. - exact X12. - rewrite X13; f_equal; lia. - exact X14. - rewrite X15; f_equal; lia.
      - lia.
      - unfold above_sp, DS_SIZE. split; [lia | split; [lia | intros i Hi; apply (hi_unowned MI A M model); [exact AI | lia]]].
      - mlia.
      - unfold DS_SIZE. eapply mdef_sub; [exact HDstk1 | lia | lia].
      - unfold above_sp. split; [lia | split; [lia | intros i Hi; apply (hi_unowned MI A M model); [exact AI | lia]]].
      - eapply mdef_sub; [exact HDstk1 | lia | lia].
      - unfold above_sp. split; [lia | split; [lia | intros i Hi; apply (hi_unowned MI A M model); [exact AI | lia]]].
      - exact G424.
      - eapply mdef_sub; [exact HDstk1 | lia | lia].
      - unfold above_sp. split; [lia | split; [lia | intros i Hi; apply (hi_unowned MI A M model); [exact AI | lia]]].
      - exact G400.
      - eapply mdef_sub; [exact HDstk1 | lia | lia].
      - unfold obj_ok. split; [exact PLc | intros a Ha Hw; apply (DJc a Ha); unfold EXH_S, zwin in *; lia].
      - exact Hpc.
      - eapply fld_agree; [lia | cbn; lia | exact F32 |]. eapply stores_in_agree; [exact ST1|]. intros x Hx. unfold zwin in *. split; [lia|].
        intros Hw. apply (DJc x); unfold zwin; lia.
      - intros a Ha. unfold DS_SIZE, zwin in *. split; [lia|]. split; [lia|]. split; [lia|]. intros Hp. apply (DJc a); unfold zwin; lia.
      -
        intros A' R' M' model' B RB DS XF EF.
        pose proof RB as RB0. destruct RB as [AI' MS' FS' FDS' SX' KEPT]. unfold EXH_S in EF.
        assert (HB : forall q k, In (q, k) B -> q + k <= alloc_ceiling).
        { intros q k Hin. destruct (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as [_ HB]. destruct (HB q k Hin) as [HIn _].
          pose proof (ai_live_block MI A' M' model' q k AI' HIn) as (_ & _ & _ & Hc & _). lia. }
        assert (LOW : forall a, ds_foot sp' B a -> a < alloc_ceiling \/ (sp' <= a < sp' + 392)).
        { intros a [Hz|(q & k & Hin & Hqa)]; [right; unfold DS_SIZE, zwin in Hz; lia | pose proof (HB q k Hin); left; lia]. }
        assert (AGS : agree_on (zwin (sp - 120) sp) M1 M').
        { eapply (agree_hi_via_eff MI A A' M1 M' model model' _ _ (sp - 120) sp); [exact EF | exact AI1 | exact AI' | lia | lia | replace (sp - (sp - 120)) with 120 by lia; eapply mdef_sub; [exact HDstk1 | lia | lia] | | cbn; lia].
          intros a Ha HF. destruct (LOW a HF); lia. }
        assert (X0 : xinv A' M' model' 0 B (fun _ => False)).
        { constructor.
          - exact AI'. - exact MS'. - exact FS'. - exact FDS'. - exact SX'. - exact DS. - exact XF. - apply junk_ok_false.
          - assert (E01 : eff MI A A M M1 (sp - 12288, sp) (fun _ => False)).
            { eapply (eff_of_stores MI); [exact ST1|]. intros a Ha. right. unfold W_of, zwin in *. cbn. lia. }
            pose proof (eff_widen MI A A' M1 M' _ (sp - 12288, sp) _ EF ltac:(cbn; lia) ltac:(cbn; lia)) as E12.
            assert (WUN : forall a, W_of (sp - 12288, sp) a -> ~ owned MI A' a).
            { intros a Ha. unfold W_of in Ha. cbn in Ha. apply (hi_unowned MI A' M' model'); [exact AI' | lia]. }
            pose proof (eff_trans _ _ _ _ _ _ _ _ _ _ E01 E12 WUN) as E02. cbn beta in E02.
            eapply eff_weaken; [exact E02|]. intros a [[]|Ha]. left; exact Ha.
          - eapply slots_agree; [exact SL1 | cbn; lia | lia | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
            eapply agree_on_weaken; [exact AGS|]. intros a Ha. unfold zwin in *. lia.
          - eapply (mdef_via_eff MI A A' M1 M'); [exact EF | left; lia | lia | lia | intros j Hj; apply (hi_unowned MI A M1 model); [exact AI1 | lia] | intros j Hj HF; destruct (LOW _ HF); lia | eapply mdef_sub; [exact HDstk1 | lia | lia]].
          - unfold EXH_S. eapply (mdef_via_eff MI A A' M1 M'); [exact EF | left; lia | lia | lia | intros j Hj; apply (hi_unowned MI A M1 model); [exact AI1 | lia] | intros j Hj HF; destruct (LOW _ HF); lia | eapply mdef_sub; [exact HDstk1 | lia | lia]]. }
        assert (XR0 : xregs R' inst_offset type opcode).
        { unfold Exhausted1.xregs. repeat match goal with |- _ /\ _ => split end.
          - rewrite (KEPT 2%bv) by inl. exact X2.
          - rewrite (KEPT 3%bv) by inl. kept_chain HR1. - rewrite (KEPT 4%bv) by inl. kept_chain HR1.
          - rewrite (KEPT 8%bv) by inl. rewrite <- Ha1. kept_chain HR1.
          - rewrite (KEPT 9%bv) by inl. rewrite <- Ha0. kept_chain HR1.
          - rewrite (KEPT 18%bv) by inl. rewrite <- Ha3. kept_chain HR1.
          - rewrite (KEPT 19%bv) by inl. rewrite <- Ha2. kept_chain HR1.
          - intros rr Hrr; cbn in Hrr; repeat (destruct Hrr as [<-|Hrr]; [kept_chain KEPT HR1|]); destruct Hrr. }
        apply (stage0 A' M' model' B (fun _ => False) R' X0 XR0).
        + eapply fld_agree; [lia | cbn; lia | exact G400 | eapply agree_on_weaken; [exact AGS | intros a Ha; unfold zwin in *; lia]].
        + eapply fld_agree; [lia | cbn; lia | exact G424 | eapply agree_on_weaken; [exact AGS | intros a Ha; unfold zwin in *; lia]].
    Qed.
  End Call.
End Exh.

Theorem exhausted {AC : AllocCeiling} {RRND : RunRandom} : forall MI ST, diag_exhausted_goal MI ST.
Proof.
  intros MI ST G tc idesc DN EN fx A s R M model sp ret this pcons nwords widx icount inst_offset opcode type K
         CB ROC Ha0 Ha1 Ha2 Ha3 Hio Hop Hty PL Hthis THW F8 F56 F72 F80 Hnw Hwi Hic OBJ Hpc F32 ROOM1 POST.
  cbn [dc_stack dc_exhausted dcS1] in *.
  exact (exh_main MI ST DN G tc idesc EN A s R M model sp ret this pcons nwords widx icount inst_offset opcode type K
           CB ROC Ha0 Ha1 Ha2 Ha3 Hio Hop Hty PL Hthis THW F8 F56 F72 F80 Hnw Hwi Hic OBJ Hpc F32 ROOM1 POST).
Qed.
End Exhausted3.

Module DiagInstS1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Lib_Cxx_OperatorNew.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocIfaceStmt OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocInstS1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.S1Statics.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.Tabl_AccessorsP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_JumpP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_LookupOpP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_StrlenP1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.Exhausted1.DiagStmtsEx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagMain OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final.FinalS1.DiagMallocS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final.FinalS1.DiagStaticsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final.FinalS1.Exhausted3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
Import ListNotations.
Open Scope Z_scope.

Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Theorem diag_needs_S1 {AC : AllocCeiling} {RRND : RunRandom} : diag_needs MI_S1 S1ST.
Proof.
  pose proof (mc_stack _ _ _ MI_S1_consts_ok) as HMS. unfold MNG_MALLOC_STACK in HMS.
  constructor.
  - rewrite HMS. lia.
  - exact (operator_new_spec MI_S1 S1ST ltac:(rewrite HMS; lia)).
  - exact diag_statics_S1.
  - exact diag_classes_S1.
  - exact diag_round_big_S1.
  - change (static_cells MI_S1) with mng_static_cells. unfold mng_static_cells. right. left. reflexivity.
Qed.

Theorem diag_contract_S1 {AC : AllocCeiling} {RRND : RunRandom} : diag_contract MI_S1 S1ST.
Proof. exact (diag_main MI_S1 S1ST diag_needs_S1). Qed.

Theorem exhausted_needs_S1 {AC : AllocCeiling} : exhausted_needs TG TablImgP1.tc (idesc TablImgP1.ti).
Proof.
  unfold exhausted_needs. cbn [tc_lookup_opcode tc_idesc_name tc_operand_type_str tc_strlen tc_lookup_stack TablImgP1.tc].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  split; [exact lookup_opcode_spec|]. split; [exact idesc_name_spec|]. split; [exact operand_type_str_spec | exact strlen_ro_spec].
Qed.

Theorem exhausted_S1 {AC : AllocCeiling} {RRND : RunRandom} : PrsNeeds.exhausted_stmt S1Layout.SEGS S1Layout.L MI_S1 S1ST PmCoreS1.dcS1.
Proof. exact (exhausted MI_S1 S1ST TG TablImgP1.tc (idesc TablImgP1.ti) diag_needs_S1 exhausted_needs_S1). Qed.
End DiagInstS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop.TopS1Inst.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom LibIface LibBudget Lib_Cxx_OperatorNew S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocIfaceStmt MallocInstS1 MallocHeapOwnS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import DrvLibContract S1Statics LibContractS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require S1TargetConsts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final.FinalS1.DiagInstS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PmCoreS1 PmInstS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTop Require Import TopS1Inst.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section F.
Context {AC : AllocCeiling} {RRND : RunRandom}.
  Let D  : DiagStmts.diag_contract MI_S1 S1ST := diag_contract_S1.
  Let DX : PrsNeeds.exhausted_stmt S1Layout.SEGS S1Layout.L MI_S1 S1ST PmCoreS1.dcS1 := exhausted_S1.

  Lemma new_S1 : new_rule_stmt S1Layout.SEGS S1Layout.L MI_S1 S1ST (Lib_Cxx_OperatorNew.NEW_STACK MI_S1).
  Proof using AC RRND. apply operator_new_spec. rewrite (mc_stack _ _ _ MI_S1_consts_ok). unfold MNG_MALLOC_STACK. lia. Qed.

  Lemma lib_call_S1 :
    lib_call_stmt S1Layout.SEGS S1Layout.L MI_S1 S1ST
      S1TargetConsts.LLVM_ENTRY S1TargetConsts.EMPTY_OBJ LIB_STACK lib_caps LIB_BIGCAP
      S1TargetConsts.TD_LOCALE S1TargetConsts.GLOBAL_LOCALE.
  Proof using AC RRND.
    eapply (lib_top_S1_inst MI_S1 S1ST MI_S1_consts_ok new_S1 (mi_s1_heap_owned) PmCoreS1.kcS1).
    - cbn. lia.
    - exact (binary_parse_S1_inst D DX).
  Qed.
End F.

Theorem lib_contract_S1_final : lib_contract_S1.
Proof. intros AC RRND. exact (@lib_call_S1 AC RRND). Qed.
