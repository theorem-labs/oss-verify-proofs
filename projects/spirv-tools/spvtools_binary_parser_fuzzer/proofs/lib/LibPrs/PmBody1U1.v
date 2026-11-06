(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmClearU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition CD_STOPS : list Z := [0x67614; 0x67624; 0x67690; 0x676a8; 0x67764; 0x67774; 0x690d8].

Definition all_but (x : reg) : list reg :=
  filter (fun r => negb (bv_eqb r x))
    [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.

Section CD.
  Context {fx : FPState}.
  #[local] Notation st R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)).

  Ltac fixr := try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) by (apply bv_eq; reflexivity);
               try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) by (apply bv_eq; reflexivity);
               try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) by (apply bv_eq; reflexivity);
               try replace (Z_to_bv 5 (Z.of_N 20)) with (20%bv : reg) by (apply bv_eq; reflexivity);
               try replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) by (apply bv_eq; reflexivity).
  Ltac sctac Hb H25 := cbn [sc_denot]; evs; fixr; rewrite ?Hb, ?H25, ?zbv_mul, ?zbv_add; rewrite ?br_geu, ?br_ne, ?br_ltu, ?br_eq by lia; bool_lia.

  Lemma cd4_gen : forall (pcL pcX : Z) (rc rb : reg) M (b : Z) (k : nat) R,
    (pcL = 0x67614 /\ pcX = 0x67624 /\ rc = 11%bv /\ rb = 12%bv \/ pcL = 0x67764 /\ pcX = 0x67774 /\ rc = 10%bv /\ rb = 11%bv) ->
    getr R rc = Z_to_bv 64 (b + 4 * Z.of_nat k) -> getr R rb = Z_to_bv 64 b -> getr R 25%bv = Z_to_bv 64 5 ->
    8 <= b -> b + 4 * Z.of_nat k <= 2 ^ 63 -> (1 <= k)%nat ->
    exists R', msteps SEGS (st R pcL M) (st R' pcX M)
      /\ (forall r, In r (all_but rc) -> getr R' r = getr R r) /\ getr R' rc = Z_to_bv 64 b.
  Proof using fx.
    intros pcL pcX rc rb M b k. induction k as [|k IH]; intros R CASE Hc Hb H25 Hb8 Hhi Hk; [lia|].
    destruct CASE as [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
    - pose (E := Eseed R [Z_to_bv 64 b; Z_to_bv 64 (b + 4 * Z.of_nat (S k))]).
      assert (HR : regs_ok E (srs sr_id [(11%bv, EVar 33)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact Hc. }
      assert (HK : know_ok SEGS E M [KRange (EVar 32) 8 (2 ^ 63); KRange (EVar 33) 12 (2 ^ 63)]).
      { repeat apply Forall_cons; try apply Forall_nil; (eapply krange_var; [evs; reflexivity | lia | lia]). }
      destruct k as [|k'].
      + xrun HR HK 20%nat CD_STOPS (SCR [true; false] [] []) 20%N.
        { split_scs. all: try sc_auto1. all: sctac Hb H25. }
        exists R'. split; [exact Hms|]. split.
        * exact (syms_id_sound _ _ _ R' (all_but 11%bv) HR' eq_refl).
        * rreg HR' 11%bv G. rewrite G. evs. rewrite ?zbv_add. f_equal. lia.
      + xrun HR HK 20%nat CD_STOPS (SCR [true; true] [] []) 20%N.
        { split_scs. all: try sc_auto1. all: sctac Hb H25. }
        rreg HR' 11%bv G. evs_in G. rewrite ?zbv_add in G.
        destruct (IH R' ltac:(left; repeat split; reflexivity) ltac:(rewrite G; f_equal; lia)
                     ltac:(rewrite (syms_id_sound _ _ _ R' (all_but 11%bv) HR' eq_refl 12%bv ltac:(vm_compute; tauto)); exact Hb)
                     ltac:(rewrite (syms_id_sound _ _ _ R' (all_but 11%bv) HR' eq_refl 25%bv ltac:(vm_compute; tauto)); exact H25)
                     Hb8 ltac:(lia) ltac:(lia)) as (R2 & RUN2 & K2 & G2).
        exists R2. split; [eapply msteps_trans; [exact Hms | exact RUN2] |]. split; [| exact G2].
        intros r Hr. rewrite (K2 r Hr). exact (syms_id_sound _ _ _ R' (all_but 11%bv) HR' eq_refl r Hr).
    - pose (E := Eseed R [Z_to_bv 64 b; Z_to_bv 64 (b + 4 * Z.of_nat (S k))]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 33)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact Hc. }
      assert (HK : know_ok SEGS E M [KRange (EVar 32) 8 (2 ^ 63); KRange (EVar 33) 12 (2 ^ 63)]).
      { repeat apply Forall_cons; try apply Forall_nil; (eapply krange_var; [evs; reflexivity | lia | lia]). }
      destruct k as [|k'].
      + xrun HR HK 20%nat CD_STOPS (SCR [true; false] [] []) 20%N.
        { split_scs. all: try sc_auto1. all: sctac Hb H25. }
        exists R'. split; [exact Hms|]. split.
        * exact (syms_id_sound _ _ _ R' (all_but 10%bv) HR' eq_refl).
        * rreg HR' 10%bv G. rewrite G. evs. rewrite ?zbv_add. f_equal. lia.
      + xrun HR HK 20%nat CD_STOPS (SCR [true; true] [] []) 20%N.
        { split_scs. all: try sc_auto1. all: sctac Hb H25. }
        rreg HR' 10%bv G. evs_in G. rewrite ?zbv_add in G.
        destruct (IH R' ltac:(right; repeat split; reflexivity) ltac:(rewrite G; f_equal; lia)
                     ltac:(rewrite (syms_id_sound _ _ _ R' (all_but 10%bv) HR' eq_refl 11%bv ltac:(vm_compute; tauto)); exact Hb)
                     ltac:(rewrite (syms_id_sound _ _ _ R' (all_but 10%bv) HR' eq_refl 25%bv ltac:(vm_compute; tauto)); exact H25)
                     Hb8 ltac:(lia) ltac:(lia)) as (R2 & RUN2 & K2 & G2).
        exists R2. split; [eapply msteps_trans; [exact Hms | exact RUN2] |]. split; [| exact G2].
        intros r Hr. rewrite (K2 r Hr). exact (syms_id_sound _ _ _ R' (all_but 10%bv) HR' eq_refl r Hr).
  Qed.

  Lemma cd20 : forall M (b : Z) (k : nat) R,
    getr R 10%bv = Z_to_bv 64 (b + 20 * Z.of_nat k) -> getr R 11%bv = Z_to_bv 64 b -> getr R 20%bv = Z_to_bv 64 20 ->
    16 <= b -> b + 20 * Z.of_nat k <= 2 ^ 63 -> (1 <= k)%nat ->
    exists R', msteps SEGS (st R 0x67690 M) (st R' 0x676a8 M)
      /\ (forall r, In r (all_but 10%bv) -> getr R' r = getr R r) /\ getr R' 10%bv = Z_to_bv 64 b.
  Proof using fx.
    intros M b k. induction k as [|k IH]; intros R Hc Hb H20 Hb8 Hhi Hk; [lia|].
    pose (E := Eseed R [Z_to_bv 64 b; Z_to_bv 64 (b + 20 * Z.of_nat (S k))]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact Hc. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) 16 (2 ^ 63); KRange (EVar 33) 36 (2 ^ 63)]).
    { repeat apply Forall_cons; try apply Forall_nil; (eapply krange_var; [evs; reflexivity | lia | lia]). }
    destruct k as [|k'].
    + xrun HR HK 20%nat CD_STOPS (SCR [true; true; false] [] []) 20%N.
      { split_scs. all: try sc_auto1. all: sctac Hb H20. }
      exists R'. split; [exact Hms|]. split.
      * exact (syms_id_sound _ _ _ R' (all_but 10%bv) HR' eq_refl).
      * rreg HR' 10%bv G. rewrite G. evs. rewrite ?zbv_add. f_equal. lia.
    + xrun HR HK 20%nat CD_STOPS (SCR [true; true; true] [] []) 20%N.
      { split_scs. all: try sc_auto1. all: sctac Hb H20. }
      rreg HR' 10%bv G. evs_in G. rewrite ?zbv_add in G.
      destruct (IH R' ltac:(rewrite G; f_equal; lia)
                   ltac:(rewrite (syms_id_sound _ _ _ R' (all_but 10%bv) HR' eq_refl 11%bv ltac:(vm_compute; tauto)); exact Hb)
                   ltac:(rewrite (syms_id_sound _ _ _ R' (all_but 10%bv) HR' eq_refl 20%bv ltac:(vm_compute; tauto)); exact H20)
                   Hb8 ltac:(lia) ltac:(lia)) as (R2 & RUN2 & K2 & G2).
      exists R2. split; [eapply msteps_trans; [exact Hms | exact RUN2] |]. split; [| exact G2].
      intros r Hr. rewrite (K2 r Hr). exact (syms_id_sound _ _ _ R' (all_but 10%bv) HR' eq_refl r Hr).
  Qed.
End CD.
End PmClearU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HFpu HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmStep3U1 PmLoopU1 PmInstU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1U1.PmClearU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_latch_err := (PmLoopU1.pm_latch_err (MI:=MI) (ST:=ST)).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_ecw_pbs2 := (PmStep2U1.pm_ecw_pbs2 CL).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation loop_mem := (PmStepU1.loop_mem (MI:=MI) (ST:=ST)).
  #[local] Notation loop_regs := (PmStepU1.loop_regs (MI:=MI) (ST:=ST)).

  Lemma pm_tail_676a4 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (err len : Z) (B : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B -> pm_bud (w_n w) c ->
    ds_rep A M (w_sp w + 304) err len B -> - 2 ^ 31 <= err < 0 ->
    frm_zero (@fp_csr fx) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x67748 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R err len B PS X Htr BUD DS Herr FZ Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME in *.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M (w_sp w + 304 + 360) (err mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound err (2 ^ 32)); cbn; lia | exact Herrc]. }
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); sxw (err mod 2 ^ 32)]).
    seedHR HR E [(2%bv, EVar 32)] R.
    assert (HK : know_ok SEGS E M [KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [EVar 33] []) 50%N.
    { split_scs. sc_rd_sx Cerr. }
    name_run HRn R1. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. evs_in G10. rewrite ?w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A M model c R1 err len _ B []);
      [exact PS | exact X | rewrite Htr, app_nil_r; reflexivity | exact BUD | rewrite Zlength_nil; lia | exact DS | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros A' R' M' model' X' BUD' KEPT AG.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound err (2 ^ 32) ltac:(lia)) as Hm.
    assert (Hnz : err mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add err 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms X') as MS'.
    pm_seed R' w (set_tr c []) (@nil word). seedHR HR E [(2%bv, EVar 32)] R'. seedHK HK w A' M' model' (set_tr c []) E X'.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    name_run HRn R2. rreg HRn (2%bv) H2. rreg HRn (3%bv) H3. rreg HRn (4%bv) H4. rreg HRn (22%bv) H22. clear HRn HR HK. fixregs.
    rewrite Qgp' in H3. rewrite Qtp' in H4. replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in H22 by (apply bv_eq; reflexivity). rewrite Qs6 in H22.
    eapply (pm_latch_err w c0 K fx A' M' model' (set_tr c []) R2 (err mod 2 ^ 32) PS X' eq_refl BUD' FZ H2 H3 H4 H22 ltac:(lia)).
  Qed.

  Lemma pm_D5 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (iwc : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> loop_mem w M ->
    cellw SEGS M (w_sp w + 234) 2 iwc ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x6771c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R iwc PS X Htr BUD LM Ciwc FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (proj1 Ciwc) as Riwc. cbn in Riwc.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | rewrite Zlength_nil; lia | cregs_tac G1 G2 G3 G4 | exact G10 | exact G11
      | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G10; try clear G11; try clear G12.
    eapply (loop_mem_frame w M M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; intros; lia]].
    eapply (cellw_frame M M1) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear AG. pose proof (x_ms X1) as MS1.
    pose proof (loop_mem_cell w M1 112 0x140bc LM ltac:((first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ])) ltac:(lia)) as C112.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    apply (know_more E M1 [KWord (SA (EVar 32) 112) (N.to_nat 8) (ELit 0x140bc)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact C112 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x140bc 32 32 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | rewrite Zlength_nil; lia | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G10; try clear G11; try clear G12.
    eapply (cellw_frame M1 M2) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear AG LM X1 BUD1 DS1 MS1 C112. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 iwc].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite ?w_add in G10 by lia. try rewrite ext_val_zx2 in G11 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u16 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ iwc _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (pm_tail_676a4 w c0 K fx A3 M3 model3 _ R3c (-4) _ B3);
      [exact PS | exact X3 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD3 | exact DS3 | lia | exact FZ
      | exact Qsp | exact Qgp | exact Qtp].
  Qed.

  Lemma pm_D6 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (op : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    cellw SEGS M (w_sp w + 250) 2 op ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x676f0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R op PS X Htr BUD Cop FZ Qs0 Qsp Qgp Qtp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (proj1 Cop) as Rop. cbn in Rop.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | rewrite Zlength_nil; lia | cregs_tac G1 G2 G3 G4 | exact G10 | exact G11
      | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G10; try clear G11; try clear G12.
    eapply (cellw_frame M M1) in Cop; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear AG. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite ?w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x13548 16 16 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | rewrite Zlength_nil; lia | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT; try clear G10; try clear G11; try clear G12.
    eapply (cellw_frame M1 M2) in Cop; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear AG X1 BUD1 DS1 MS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 op].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 250) (N.to_nat 2) (EVar 39)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Cop | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite ?w_add in G10 by lia. try rewrite ext_val_zx2 in G11 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u16 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ op _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (pm_tail_676a4 w c0 K fx A3 M3 model3 _ R3c (-4) _ B3);
      [exact PS | exact X3 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD3 | exact DS3 | lia | exact FZ
      | exact Qsp | exact Qgp | exact Qtp].
  Qed.

  Lemma zbv_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof using.
    intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
  Qed.
  Lemma zbv_mul : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof using.
    intros a b. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zmult_mod. reflexivity.
  Qed.

  Lemma kword_expr : forall E M (base : expr) (b off : Z) (w : N) (v : Z) (e : expr),
    cellw SEGS M (b + off) w v -> (w <= 8)%N ->
    edenot E base = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= b + off < 2 ^ 64 -> b + off + Z.of_N w <= 2 ^ 64 ->
    edenot E e = Z_to_bv 64 v ->
    kentry_ok SEGS E M (KWord (SA base off) (N.to_nat w) e).
  Proof using.
    intros E M base b off w v e [Hv Hr] Hw Hn Hb Hbo Hbow He. cbn [kentry_ok]. rewrite !N_nat_Z.
    split; [lia|]. split.
    - unfold flat, estart. cbn [a_base a_off]. rewrite Hn, u64_of_Z by lia. lia.
    - unfold adenot. cbn [a_base a_off]. rewrite Hn, He, v_addi_Z by lia. exact Hr.
  Qed.
  Lemma kdisj_expr : forall E M (e1 e2 : expr) (b1 b2 o1 o2 l1 l2 : Z),
    edenot E e1 = Z_to_bv 64 b1 -> edenot E e2 = Z_to_bv 64 b2 -> 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
    0 <= l1 < 2 ^ 64 -> 0 <= l2 < 2 ^ 64 ->
    (b1 + o1 + l1 <= b2 + o2 \/ b2 + o2 + l2 <= b1 + o1) ->
    kentry_ok SEGS E M (KDisj (SA e1 o1) (ELit l1) (SA e2 o2) (ELit l2)).
  Proof using.
    intros E M e1 e2 b1 b2 o1 o2 l1 l2 H1 H2 Hb1 Hb2 Hl1 Hl2 H. cbn [kentry_ok].
    unfold estart, elenZ. cbn [a_base a_off]. rewrite H1, H2. cbn [edenot]. rewrite !u64_of_Z by lia. exact H.
  Qed.

  Ltac lrsplit LR := let H := fresh "LRc" in pose proof LR as H;
    destruct H as (?LQ2 & ?LQ3 & ?LQ4 & ?LQ8 & ?LQ9 & ?LQ18 & ?LQ19 & ?LQ20 & ?LQ21 & ?LQ25).
  Tactic Notation "seedLR" ident(HR) constr(E) constr(R) uconstr(extra) :=
    let l := constr:(([(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61));
                        (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)] ++ extra) : list (reg * expr)) in
    let l' := eval cbn [app] in l in
    seedHR_ HR E l' R.

  Lemma pm_v2_end_store : forall (w : pmw MI ST) A M model c (b cap : Z) (xs : list Z),
    PMX w A M model c -> c_v2 c = (b, xs, cap) ->
    PMX w A (wbytes M (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs)))) model c.
  Proof using AC MI ST.
    intros w A M model c b cap xs X Ev2. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_v2 X) as V. rewrite Ev2 in V. cbn [t3a t3b t3c fst snd] in V.
    destruct V as (V1 & V2 & V3 & V4 & V5 & F0 & F1 & F2 & FE). unfold O_V2 in *.
    assert (Hbn : 0 <= b + 4 * Zlen xs < 2 ^ 64).
    { destruct V5 as [[-> ->]|(Hb0 & _ & Hc0 & Hbc & _)]; lia. }
    assert (SI : stores_in (zwin (w_p w + 248) (w_p w + 256)) M (wbytes M (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs))))) by stin.
    eapply (pmx_upd_own CV2 w A M _ model c c _ X SI);
      [intros a Ha; cbn; unfold O_V2, zwin in *; lia | intros j Hj; destruct j; cbn; reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
    cbn [crep]. rewrite Ev2. cbn [t3a t3b t3c fst snd]. unfold O_V2, CRep.vec32.
    split; [exact V1|]. split; [exact V2|]. split; [eapply stores_in_mdef; [exact SI | exact V3]|]. split; [exact V4|]. split; [exact V5|].
    split; [eapply fld_keep; [exact SI | exact F0 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
    split; [replace (w_p w + 240 + 8) with (w_p w + 248) by lia; rdback|].
    split; [eapply fld_keep; [exact SI | exact F2 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
    intros i Hi. destruct (FE i Hi) as [R1 F3]. split; [exact R1|].
    eapply fld_keep; [exact SI | exact F3 | lia | cbn; lia | ]. unfold zwin; cbn; intros x Hx HW.
    destruct V5 as [[Hb0 Hc0]|(Hb0 & _ & Hc0 & Hbc & _ & Hdj)]; [lia|]. lia.
  Qed.

  Lemma pm_B1c : forall (w : pmw MI ST) c0 K (fx : FPState) A M model (c cB : pmc) R (fw : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    loop_regs w R -> loop_mem w M -> izero w M -> c_endian c < 2 -> w_words w <> 0 -> c_widx c < w_n w -> c_icount c <= c_widx c ->
    cellw SEGS M (w_sp w + 236) 4 fw -> t3b (c_v2 c) = [fw] ->
    getr R 11%bv = Z_to_bv 64 (t3a (c_v1 c)) ->
    (forall A' M' model' c' R' (iwc op d : Z),
        PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> loop_regs w R' -> loop_mem w M' -> izero w M' ->
        ictx w M' (c_widx c) fw iwc op d -> iwc = fw / 2 ^ 16 -> op = fw mod 2 ^ 16 -> iwc <> 0 ->
        (exists l, g_op G op = Some l) -> idesc d op ->
        c_widx c' = c_widx c + 1 -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
        t3b (c_v1 c') = 0 -> c_v2 c' = c_v2 c ->
        c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c -> c_v3 c' = c_v3 c -> t3c (c_v1 c') = t3c (c_v1 c) ->
        srealizes SEGS (cfg fx R' 0x67758 M' model') K) ->
    srealizes SEGS (cfg fx R 0x676a8 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c cB R fw PS FZ X Htr BUD LR LM IZ He2 Hw Hlt Hic Cfw Ev2b Qa1 B2K.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof (proj1 Cfw) as Rfw. cbn in Rfw.

    pm_seed R w c [Z_to_bv 64 (t3a (c_v1 c)); Z_to_bv 64 fw].
    seedLR HR E R [(11%bv, EVar 39)].
    seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 32) 236) (N.to_nat 4) (EVar 40)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Cfw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
    assert (LR1 : loop_regs w R1) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
    clear T9 T18 T19 T20 T21 T25.
    rewrite ?ext_val_sx4 in G10 by lia. rewrite ?w_add in G11, G12 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M4 := m) in * end.
    assert (ST4 : stores_in (fun a => zwin (w_p w + 224) (w_p w + 232) a \/ zwin (w_sp w + 234) (w_sp w + 236) a) M M4) by (unfold M4; stin).
    pose proof (pm_v1_clear w A M model c (t3a (c_v1 c)) X eq_refl) as X4a.
    assert (X4 : PMX w A M4 model (set_v1 c (t3a (c_v1 c), 0, t3c (c_v1 c)))).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A _ _ model _ (zwin (w_sp w + 234) (w_sp w + 236)));
        [exact X4a | unfold M4; stin | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (loop_mem_frame w M M4) in LM; [| lia | lia | eapply stores_in_agree; [exact ST4 | unfold zwin; intros; lia]].
    eapply (izero_agree w M M4) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST4 | unfold zwin; intros; lia]].
    eapply (cellw_frame M M4) in Cfw; [| lia | cbn; lia | eapply stores_in_agree; [exact ST4 | unfold zwin; cbn; intros; lia]].
    clear ST4 X4a X MS. clearbody M4. pose proof (x_ms X4) as MS4.
    set (c4 := set_v1 c (t3a (c_v1 c), 0, t3c (c_v1 c))) in *.

    eapply (pm_opcode_split w A M4 model c4 fx R1 fw (w_sp w + 234) (w_sp w + 250) _ K X4 ltac:(rewrite G10; reflexivity) G11 G12);
      [lia | lia | unfold w_sp0, PM_FRAME; lia | lia | unfold w_sp0, PM_FRAME; lia
      | apply mod16_2; [exact Gsp16 | reflexivity] | apply mod16_2; [exact Gsp16 | reflexivity] | exact G1 | apply bv_eq; vm_compute; reflexivity |].
    intros R2 KEPT M5 X5.
    pose proof (loop_regs_kept w R1 R2 LR1 KEPT) as LR2.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. clear G1 G2 G3 G4 G8 G10 G11 G12 KEPT LR1.
    assert (ST5 : stores_in (fun a => zwin (w_sp w + 234) (w_sp w + 236) a \/ zwin (w_sp w + 250) (w_sp w + 252) a) M4 M5) by (unfold M5; stin).
    eapply (loop_mem_frame w M4 M5) in LM; [| lia | lia | eapply stores_in_agree; [exact ST5 | unfold zwin; intros; lia]].
    eapply (izero_agree w M4 M5) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST5 | unfold zwin; intros; lia]].
    eapply (cellw_frame M4 M5) in Cfw; [| lia | cbn; lia | eapply stores_in_agree; [exact ST5 | unfold zwin; cbn; intros; lia]].
    pose proof (hi16_range fw Rfw) as Riwc. pose proof (lo16_range fw) as Rop.
    set (iwc := fw / 2 ^ 16) in *. set (op := fw mod 2 ^ 16) in *.
    assert (Ciwc : cellw SEGS M5 (w_sp w + 234) 2 iwc) by (split; [cbn; lia | unfold M5; rdback]).
    assert (Cop : cellw SEGS M5 (w_sp w + 250) 2 op) by (split; [cbn; lia | unfold M5; rdback]).
    clear ST5. clearbody M5. clear X4 MS4 M4. pose proof (x_ms X5) as MS5.

    destruct (Z.eq_dec iwc 0) as [Hz0|Hnz].
    { pm_seed R2 w c4 (@nil word). lrsplit LR2.
      seedLR HR E R2 (@nil (reg * expr)).
      seedHK HK w A M5 model c4 E X5.
      apply (know_more E M5 [KWord (SA (EVar 32) 234) (N.to_nat 2) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [rewrite Hz0 in Ciwc; exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      xruns HR HK 100%nat (0x6771c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R7. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4.
      eapply (pm_D5 w c0 K fx A M5 model c4 R7 iwc PS X5 Htr BUD LM Ciwc FZ G8 G2 G3 G4). }

    pm_seed R2 w c4 [Z_to_bv 64 iwc; Z_to_bv 64 op]. try lrsplit LR2.
    seedLR HR E R2 (@nil (reg * expr)).
    seedHK HK w A M5 model c4 E X5.
    apply (know_more E M5 [KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 39); KWord (SA (EVar 32) 250) (N.to_nat 2) (EVar 40); KRange (EVar 39) 1 (2 ^ 16); KRange (EVar 40) 0 (2 ^ 16 - 1)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cop | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_zx2 by lia; rewrite ?br_eq, ?br_ne by lia; bool_lia. }
    postrun. name_run HRn R7.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
    clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
    assert (LR7 : loop_regs w R7) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
    clear T9 T18 T19 T20 T21 T25.
    rewrite ?ext_val_zx2 in G10 by lia. rewrite ?w_add in G11 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M6 := m) in * end.
    assert (ST6 : stores_in (zwin (w_sp w + 224) (w_sp w + 232)) M5 M6) by (unfold M6; stin).
    assert (X6 : PMX w A M6 model c4).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M5 M6 model c4 (zwin (w_sp w + 224) (w_sp w + 232)));
        [exact X5 | exact ST6 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (loop_mem_frame w M5 M6) in LM; [| lia | lia | eapply stores_in_agree; [exact ST6 | unfold zwin; intros; lia]].
    eapply (izero_agree w M5 M6) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST6 | unfold zwin; intros; lia]].
    eapply (cellw_frame M5 M6) in Cfw; [| lia | cbn; lia | eapply stores_in_agree; [exact ST6 | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame M5 M6) in Ciwc; [| lia | cbn; lia | eapply stores_in_agree; [exact ST6 | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame M5 M6) in Cop; [| lia | cbn; lia | eapply stores_in_agree; [exact ST6 | unfold zwin; cbn; intros; lia]].
    clear ST6 X5 MS5. clearbody M6. clear M5. pose proof (x_ms X6) as MS6.

    eapply (pm_lookup_opcode w A M6 model c4 fx R7 op 0 (w_sp w + 224) _ K X6 G10);
      [lia | intros _; exact G11 | intros Hn; discriminate Hn | exact G2 | lia | unfold w_sp0, PM_FRAME; lia
      | apply mod16_8; [exact Gsp16 | reflexivity] | exact G1 | apply bv_eq; vm_compute; reflexivity |].
    intros R8 M7 r d KEPT Hr Rr Fd Hfound Hdesc X7 AG.
    pose proof (loop_regs_kept w R7 R8 LR7 KEPT) as LR8.
    keptQ KEPT G2 Qsp8. keptQ KEPT G8 Qs08. keptQ KEPT G3 Qgp8. keptQ KEPT G4 Qtp8. clear G1 G2 G3 G4 G8 G10 G11 KEPT LR7 LR2 Qsp2 Qs02 Qgp2 Qtp2.
    eapply (loop_mem_frame w M6 M7) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (izero_agree w M6 M7) in IZ; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (cellw_frame M6 M7) in Cfw; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    eapply (cellw_frame M6 M7) in Ciwc; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    eapply (cellw_frame M6 M7) in Cop; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    clear AG X6 MS6 M6. pose proof (x_ms X7) as MS7.

    destruct (Z.eq_dec r 0) as [Hr0|Hrn].
    2: { pm_seed R8 w c4 [Z_to_bv 64 r]. lrsplit LR8.
         seedLR HR E R8 [(10%bv, EVar 39)].
         seedHK HK w A M7 model c4 E X7.
         apply (know_more E M7 [KWord (SA (EVar 33) 40) (N.to_nat 1) (ELit 0); KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil.
              - eapply kword_var; [eapply fld_cellw; [exact (x_hunk X7) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
              - eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (0x676f0 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
         postrun. name_run HRn R9. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
         clear HRn HR HK. fixregs. rewrite Qgp8 in G3. rewrite Qtp8 in G4.
         eapply (pm_D6 w c0 K fx A M7 model c4 R9 op PS X7 Htr BUD Cop FZ G8 G2 G3 G4). }

    rewrite Hr0 in Hr.
    pose proof (fld_cellw M7 _ 8 _ (x_widx X7) ltac:(cbn [c4 set_v1 c_widx]; lia)) as Cwi. unfold O_WIDX in Cwi. cbn [c4 set_v1 c_widx] in Cwi.
    pm_seed R8 w c4 (@nil word). try lrsplit LR8.
    seedLR HR E R8 [(10%bv, ELit 0)].
    seedHK HK w A M7 model c4 E X7.
    apply (know_more E M7 [KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat (0x67758 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
    rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
    clear HRn HR HK. fixregs. rewrite Qgp8 in G3. rewrite Qtp8 in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
    assert (LR9 : loop_regs w R9) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
    clear T9 T18 T19 T20 T21 T25.
    rewrite ?w_add by (cbn [c4 set_v1 c_widx]; lia).
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M8 := m) in * end.
    assert (ST8 : stores_in (fun a => zwin (w_sp w + 176) (w_sp w + 224) a \/ zwin (w_p w + 72) (w_p w + 80) a) M7 M8) by (unfold M8; stin).
    set (c8 := set_scal c4 (c_widx c + 1) (c_icount c4) (c_endian c4) (c_reqconv c4)).
    pose proof (x_scal X7) as (Sc1' & Sc2' & Sc3' & Sc4'). cbn [c4 set_v1 c_widx c_icount c_endian c_reqconv] in Sc1', Sc2', Sc3', Sc4'.
    assert (X8 : PMX w A M8 model c8).
    { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img);
        [exact X7 | exact ST8 | intros a [Ha|Ha]; unfold scal_win, zwin, O_WIDX, O_FLAGS, w_sp0, PM_FRAME in *; [left; lia | right; lia]
        | unfold M8, O_WIDX; rdback
        | eapply fld_keep; [exact ST8 | exact (x_icount X7) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST8 | exact (x_endian X7) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST8 | exact (x_flags X7) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia]
        | cbn [c4 set_v1 c_widx]; lia | cbn [c4 set_v1 c_widx c_icount]; lia
        | cbn [c4 set_v1 c_endian]; lia | cbn [c4 set_v1 c_reqconv]; exact Sc4]. }
    eapply (loop_mem_frame w M7 M8) in LM; [| lia | lia | eapply stores_in_agree; [exact ST8 | unfold zwin; intros; lia]].
    eapply (izero_agree w M7 M8) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST8 | unfold zwin; intros; lia]].
    eapply (cellw_frame M7 M8) in Cfw; [| lia | cbn; lia | eapply stores_in_agree; [exact ST8 | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame M7 M8) in Ciwc; [| lia | cbn; lia | eapply stores_in_agree; [exact ST8 | unfold zwin; cbn; intros; lia]].
    eapply (cellw_frame M7 M8) in Cop; [| lia | cbn; lia | eapply stores_in_agree; [exact ST8 | unfold zwin; cbn; intros; lia]].
    assert (Fd8 : fld SEGS M8 (w_sp w + 224) 8 d).
    { eapply fld_keep; [exact ST8 | exact Fd | lia | cbn; lia | unfold zwin; cbn; intros; lia]. }
    assert (Cio : cellw SEGS M8 (w_sp w + 216) 8 (c_widx c)) by (split; [cbn; lia | unfold M8; rdback]).
    eapply (B2K A M8 model c8 R9 iwc op d X8 Htr BUD LR9 LM IZ);
      [split; [exact Cio | split; [exact Cfw | split; [exact Ciwc | split; [exact Cop | exact Fd8]]]]
      | reflexivity | reflexivity | exact Hnz | apply (proj1 Hfound); exact Hr0 | exact (Hdesc Hr0)
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
  Qed.

  Lemma pm_B1t : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (fw e : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) ->
    PMX w A (wbytes M (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 e))) model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    loop_regs w R -> loop_mem w M -> izero w M -> c_endian c < 2 -> w_words w <> 0 -> c_widx c < w_n w -> c_icount c <= c_widx c ->
    cellw SEGS M (w_sp w + 236) 4 fw -> t3b (c_v2 c) = [fw] -> e = t3a (c_v2 c) + 4 -> 16 <= t3a (c_v2 c) -> t3a (c_v2 c) mod 16 = 0 ->
    mdef M (w_p w) PARSER_SIZE ->
    getr R 11%bv = Z_to_bv 64 e ->
    (forall A' M' model' c' R' (iwc op d : Z),
        PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> loop_regs w R' -> loop_mem w M' -> izero w M' ->
        ictx w M' (c_widx c) fw iwc op d -> iwc = fw / 2 ^ 16 -> op = fw mod 2 ^ 16 -> iwc <> 0 ->
        (exists l, g_op G op = Some l) -> idesc d op ->
        c_widx c' = c_widx c + 1 -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
        t3b (c_v1 c') = 0 -> c_v2 c' = c_v2 c ->
        c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c -> c_v3 c' = c_v3 c -> t3c (c_v1 c') = t3c (c_v1 c) ->
        srealizes SEGS (cfg fx R' 0x67758 M' model') K) ->
    srealizes SEGS (cfg fx R 0x67668 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R fw e PS FZ X Htr BUD LR LM IZ He2 Hw Hlt Hic Cfw Ev2b He Hb16 Hbal PD Qa1 B2K.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof (proj1 Cfw) as Rfw. cbn in Rfw.
    assert (He63 : e <= 2 ^ 63).
    { pose proof (x_v2 X) as V2. destruct V2 as (_ & _ & _ & V2n & V2blk & _). rewrite Ev2b in V2n. unfold Zlen in V2n. cbn in V2n.
      destruct V2blk as [[Hb0 Hc0]|(Hb0 & _ & Hc0 & Hbc & _)]; lia. }

    pose proof (x_v1 X) as V1. unfold O_V1, CRep.vec_opnd, OPND_SZ in V1.
    destruct V1 as (_ & _ & _ & V1n & V1blk & F10 & F11 & F12).
    set (b1 := t3a (c_v1 c)) in *. set (n1 := t3b (c_v1 c)) in *. set (cap1 := t3c (c_v1 c)) in *.
    assert (Eb1 : b1 = t3a (c_v1 c)) by reflexivity. assert (En1 : n1 = t3b (c_v1 c)) by reflexivity. assert (Ec1 : cap1 = t3c (c_v1 c)) by reflexivity.
    clearbody b1 n1 cap1. rewrite ?Eb1, ?En1, ?Ec1 in B2K.
    assert (Hb1 : 0 <= b1 /\ b1 + 20 * cap1 <= 2 ^ 63 /\ (n1 = 0 \/ 16 <= b1) /\ 0 <= n1 <= cap1).
    { destruct V1blk as [[Hb0 Hc0]|(Hb0 & Hal0 & Hc0 & Hbc & _)].
      { split; [lia|]; split; [lia|]; split; [left; lia | lia]. }
      split; [lia|]. split; [lia|]. split; [|lia]. right. pose proof (Z.div_mod b1 16 ltac:(lia)). lia. }
    destruct Hb1 as (Hb1lo & Hb1hi & Hn1 & Hn1c).
    assert (C216 : cellw SEGS M (w_p w + 216) 8 b1).
    { eapply fld_cellw; [|cbn; lia]. eapply (fld_agree SEGS _ M); [lia | cbn; lia | exact F10 |].
      eapply agree_on_weaken; [| intros a Ha; exact Ha]. intros a Ha. unfold zwin in Ha. cbn in Ha.
      symmetry. apply MemSplit.wbytes_outside; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn; lia. }
    assert (C224 : cellw SEGS M (w_p w + 224) 8 (b1 + 20 * n1)).
    { eapply fld_cellw; [|cbn; lia]. eapply (fld_agree SEGS _ M); [lia | cbn; lia | replace (w_p w + 224) with (w_p w + 216 + 8) by lia; exact F11 |].
      eapply agree_on_weaken; [| intros a Ha; exact Ha]. intros a Ha. unfold zwin in Ha. cbn in Ha.
      symmetry. apply MemSplit.wbytes_outside; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn; lia. }
    pm_seed R w c [Z_to_bv 64 e; Z_to_bv 64 b1; Z_to_bv 64 n1].
    seedLR HR E R [(11%bv, EVar 39)].
    assert (HK : know_ok SEGS E M [KWr (SA (EVar 33) 216) (ELit 72); KRange (EVar 32) (2 ^ 24) (2 ^ 47 - 864); KRange (EVar 33) (2 ^ 24) (2 ^ 47 - 288);
                                  KAlign (EVar 32) 16; KAlign (EVar 33) 16; KRange (EVar 39) 20 (2 ^ 63); KAlign (EVar 39) 4;
                                  KWord (SA (EVar 33) 216) (N.to_nat 8) (EVar 40); KWord (SA (EVar 33) 224) (N.to_nat 8) (EAlu ALU_ADD (EVar 40) (EMd M_MUL (ELit 20) (EVar 41)))]).
    { unfold PARSER_SIZE in PD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact PD | lia | lia] | lia | lia | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Gsp16].
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Gp16].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kalign_var; [evs; reflexivity | lia | lia | ]. subst e. replace (t3a (c_v2 c) + 4) with ((t3a (c_v2 c) / 16 * 4 + 1) * 4) by (pose proof (Z.div_mod (t3a (c_v2 c)) 16 ltac:(lia)); lia). apply Z_mod_mult.
      - eapply kword_var; [exact C216 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
      - eapply kword_var; [exact C224 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite zbv_mul, zbv_add; reflexivity]. }

    set (M1 := wbytes M (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 e))) in X.
    assert (ST1 : stores_in (zwin (w_p w + 248) (w_p w + 256)) M M1) by (unfold M1; stin).
    eapply (loop_mem_frame w M M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    eapply (izero_agree w M M1) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    eapply (cellw_frame M M1) in Cfw; [| lia | cbn; lia | eapply stores_in_agree; [exact ST1 | unfold zwin; cbn; intros; lia]].
    destruct (Z.eq_dec n1 0) as [Hz|Hnz].
    -
      xruns HR HK 100%nat (0x676a8 :: 0x67690 :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (11%bv) G11.
      rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
      assert (LR1 : loop_regs w R1) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
      clear T9 T18 T19 T20 T21 T25.
      change (wbytes M _ _) with M1.
      eapply (pm_B1c w c0 K fx A M1 model c c R1 fw PS FZ X Htr BUD LR1 LM IZ He2 Hw Hlt Hic Cfw Ev2b ltac:(rewrite G11, Eb1; reflexivity) B2K).
    -
      xruns HR HK 100%nat (0x676a8 :: 0x67690 :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (20%bv) G20.
      rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
      evs_in G10. rewrite ?zbv_mul, ?zbv_add in G10.
      change (wbytes M _ _) with M1.
      destruct (cd20 (fx:=fx) M1 b1 (Z.to_nat n1) R1 ltac:(rewrite G10; f_equal; lia) G11 G20 ltac:(lia) ltac:(lia) ltac:(lia)) as (R2 & RUN2 & K2 & G10').
      pose proof (x_ms X) as MS1.
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | exact RUN2 |].
      assert (KQ : forall r, In r (all_but 10%bv) -> getr R2 r = getr R1 r) by exact K2.
      assert (LR2 : loop_regs w R2).
      { unfold loop_regs. rewrite !KQ by (vm_compute; repeat (first [left; reflexivity | right])). rewrite G2, G3, G4, G8, T9, T18, T19, G20, T21, T25. repeat split; reflexivity. }
      eapply (pm_B1c w c0 K fx A M1 model c c R2 fw PS FZ X Htr BUD LR2 LM IZ He2 Hw Hlt Hic Cfw Ev2b ltac:(rewrite (KQ 11%bv) by (vm_compute; repeat (first [left; reflexivity | right])); rewrite G11, Eb1; reflexivity) B2K).
  Qed.

  Lemma pm_B1b : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (fw : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    loop_regs w R -> loop_mem w M -> izero w M -> c_endian c < 2 -> w_words w <> 0 -> c_widx c < w_n w -> c_icount c <= c_widx c ->
    0 <= fw < 2 ^ 32 -> cellw SEGS M (w_sp w + 236) 4 fw ->
    getr R 12%bv = Z_to_bv 64 (t3a (c_v2 c)) -> getr R 10%bv = Z_to_bv 64 (PrsNeeds.sx32 fw) ->
    (forall A' M' model' c' R' (iwc op d : Z),
        PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> loop_regs w R' -> loop_mem w M' -> izero w M' ->
        ictx w M' (c_widx c) fw iwc op d -> iwc = fw / 2 ^ 16 -> op = fw mod 2 ^ 16 -> iwc <> 0 ->
        (exists l, g_op G op = Some l) -> idesc d op ->
        c_widx c' = c_widx c + 1 -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
        t3b (c_v1 c') = 0 -> t3b (c_v2 c') = [fw] ->
        c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c -> c_v3 c' = c_v3 c -> t3c (c_v1 c') = t3c (c_v1 c) ->
        srealizes SEGS (cfg fx R' 0x67758 M' model') K) ->
    srealizes SEGS (cfg fx R 0x67624 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R fw PS FZ X Htr BUD LR LM IZ He2 Hw Hlt Hic Rfw Cfw Qa2 Qa0 B2K.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof (sx32_range fw Rfw) as Rsx.

    destruct (c_v2 c) as [[b2 xs] cap2] eqn:Ev2. cbn [t3a t3b t3c fst snd] in Qa2.
    pose proof (x_v2 X) as V. rewrite Ev2 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (_ & _ & _ & Hxl & Hblk & F0 & F1 & F2 & _). unfold O_V2 in F0, F1, F2, Hblk.
    pose proof (fld_cellw M _ 8 _ F2 ltac:(destruct Hblk as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; lia)) as Ccap.
    replace (w_p w + 240 + 16) with (w_p w + 256) in Ccap by lia.
    pose proof (x_pdef X) as PD.
    destruct (Z.eq_dec cap2 0) as [Hc0 | Hcpos].
    -
      assert (Hxs : xs = []) by (destruct xs as [|x0 xs']; [reflexivity | unfold Zlen in Hxl; cbn in Hxl; lia]). subst xs.
      rewrite Hc0 in *. replace (b2 + 4 * 0) with b2 in Ccap by lia.
      pose proof (loop_mem_cell w M 120 (w_p w + 240) LM ltac:((first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ])) ltac:(lia)) as C120.
      pm_seed R w c [Z_to_bv 64 b2; Z_to_bv 64 (PrsNeeds.sx32 fw)].
      seedLR HR E R [(12%bv, EVar 39); (10%bv, EVar 40)].
      seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 33) 256) (N.to_nat 8) (EVar 39); KWord (SA (EVar 32) 120) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 240))]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Ccap | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact C120 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
      rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
      assert (LR1 : loop_regs w R1) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
      clear T9 T18 T19 T20 T21 T25. evs_in G10. evs_in G11. rewrite ?w_add in G10 by lia. rewrite ?w_add in G11 by lia.
      set (Mclr := wbytes M (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 b2))) in *.
      pose proof (pm_v2_clear w A M model c b2 X ltac:(rewrite Ev2; reflexivity)) as X2. rewrite Ev2 in X2. cbn [t3c] in X2. change (wbytes M _ _) with Mclr in X2.
      assert (ST2 : stores_in (zwin (w_p w + 248) (w_p w + 256)) M Mclr) by (unfold Mclr; stin).
      eapply (loop_mem_frame w M Mclr) in LM; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      eapply (izero_agree w M Mclr) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      eapply (cellw_frame M Mclr) in Cfw; [| lia | cbn; lia | eapply stores_in_agree; [exact ST2 | unfold zwin; cbn; intros; lia]].
      assert (PD2 : mdef Mclr (w_p w) PARSER_SIZE) by (eapply stores_in_mdef; [exact ST2 | unfold PARSER_SIZE; exact PD]).
      pose proof (x_ms X2) as MS2.
      assert (BUD2 : pm_bud (w_n w) (set_v2 c (b2, [], 0))).
      { destruct BUD as (Bq1 & Bq2 & Bq3 & Bq4 & Bq5 & Bq6 & Bq7 & Bq8 & Bq9). unfold pm_bud. cbn [set_v2 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
        rewrite Ev2 in *. cbn [t3a t3b t3c fst snd] in *. repeat (split; [assumption|]). exact Bq9. }
      eapply (pm_ecw_pbs2 w c0 K fx A Mclr model (set_v2 c (b2, [], 0)) R1 (w_sp w + 236) fw _ PS X2 ltac:(cbn [c_tr set_v2]; exact Htr) BUD2
                ltac:(cregs_tac G1 G2 G3 G4));
        [unfold O_V2; exact G10 | exact G11 | exact (proj2 Cfw) | exact Rfw | lia | unfold w_sp0, PM_FRAME; lia | apply mod16_4; [exact Gsp16 | reflexivity]
        | cbn [set_v2 c_v2 t3b t3c fst snd]; reflexivity | cbn [set_v2 c_v2 t3c snd]; unfold vgrow; lia |].
      cbn [set_v2 c_v2 t3a t3b t3c fst snd app].
      intros A4 R4 M4 model4 b4 X4 BUD4 KEPT Hend AG.
      pose proof (loop_regs_kept w R1 R4 LR1 KEPT) as LR4. pose proof (x_ms X4) as MS4.
      eapply (loop_mem_frame w Mclr M4) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
      eapply (izero_agree w Mclr M4) in IZ; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
      eapply (cellw_frame Mclr M4) in Cfw; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      clear AG ST2 PD2 MS2 X2 X.

      pose proof (x_v2 X4) as V4. cbn [set_v2 c_v2 t3a t3b t3c fst snd] in V4.
      destruct V4 as (_ & _ & _ & _ & Hblk4 & _). destruct Hblk4 as [[-> E0]|(Hb4 & Hbal4 & _ & Hbc4 & HIn4 & _)]; [unfold vgrow in E0; lia|].
      assert (Hb16 : 16 <= b4) by (pose proof (Z.div_mod b4 16 ltac:(lia)); lia).

      pm_seed R4 w (set_v2 c (b4, [fw], vgrow 0)) [Z_to_bv 64 (b4 + 4)]. lrsplit LR4.
      seedLR HR E R4 [(10%bv, EVar 39)].
      seedHK HK w A4 M4 model4 (set_v2 c (b4, [fw], vgrow 0)) E X4.
      xruns HR HK 100%nat (0x67668 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5.
      rreg HRn (2%bv) H2. rreg HRn (3%bv) H3. rreg HRn (4%bv) H4. rreg HRn (8%bv) H8. rreg HRn (11%bv) H11.
      rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
      clear HRn HR HK. fixregs. rewrite LQ3 in H3. rewrite LQ4 in H4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
      assert (LR5 : loop_regs w R5) by (unfold loop_regs; rewrite H2, H3, H4, H8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
      clear T9 T18 T19 T20 T21 T25. evs_in H11.
      pose proof (pm_v2_end_store w A4 M4 model4 (set_v2 c (b4, [fw], vgrow 0)) b4 (vgrow 0) [fw] X4 eq_refl) as X5.
      replace (b4 + 4 * Zlen [fw]) with (b4 + 4) in X5 by (unfold Zlen; cbn; lia).
      eapply (pm_B1t w c0 K fx A4 M4 model4 (set_v2 c (b4, [fw], vgrow 0)) R5 fw (b4 + 4) PS FZ X5).
      + cbn [c_tr set_v2]. exact Htr.
      + exact BUD4.
      + exact LR5. + exact LM. + exact IZ.
      + cbn [set_v2 c_endian]. exact He2. + exact Hw. + cbn [set_v2 c_widx]. exact Hlt. + cbn [set_v2 c_widx c_icount]. exact Hic.
      + exact Cfw. + reflexivity. + reflexivity. + cbn [set_v2 c_v2 t3a fst]. exact Hb16. + cbn [set_v2 c_v2 t3a fst]. exact Hbal4.
      + exact (x_pdef X4). + exact H11.
      + intros A' M' model' c' R' iwc op d X' Htr' BUD' LR' LM' IZ' IC' E1 E2 E3 E4 E5 W1 W2 W3 W4 V1' V2' Em1 Em2 Em3 Ev3 Ec1.
        eapply (B2K A' M' model' c' R' iwc op d X' Htr' BUD' LR' LM' IZ' IC' E1 E2 E3 E4 E5);
          cbn [set_v2 c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 t3b t3c fst snd] in W1, W2, W3, W4, V1', V2', Em1, Em2, Em3, Ev3, Ec1 |- *;
          try assumption. rewrite V2'. reflexivity.
    -
      destruct Hblk as [[-> ->]|(Hb0 & Hbal & Hc0 & Hbc & HIn & Hdj)]; [lia|].
      destruct (ai_live_block MI A M model b2 (4 * cap2) AI HIn) as (_ & _ & _ & Hbce & Hall).
      assert (Hb16 : 16 <= b2) by (pose proof (Z.div_mod b2 16 ltac:(lia)); lia).
      assert (Hb4 : b2 mod 4 = 0) by (replace b2 with (b2 / 16 * 4 * 4) by (pose proof (Z.div_mod b2 16 ltac:(lia)); lia); apply Z_mod_mult).
      assert (WRb : mdef M b2 4) by (intros i Hi; exact (proj2 (proj2 (Hall (b2 + i) ltac:(lia))))).
      pose proof (live_below_sp w A M model c b2 (4 * cap2) (b2 + 3) X HIn ltac:(lia)) as Hbsp.
      pm_seed R w c [Z_to_bv 64 b2; Z_to_bv 64 (b2 + 4 * cap2); Z_to_bv 64 (PrsNeeds.sx32 fw)].
      seedLR HR E R [(12%bv, EVar 39); (10%bv, EVar 41)].
      seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 33) 256) (N.to_nat 8) (EVar 40); KWr (SA (EVar 39) 0) (ELit 4); KRange (EVar 39) 16 (2 ^ 47); KAlign (EVar 39) 4;
                             KRange (EVar 40) 20 (2 ^ 63); KDisj (SA (EVar 32) 0) (ELit 864) (SA (EVar 39) 0) (ELit 4); KDisj (SA (EVar 33) 0) (ELit 288) (SA (EVar 39) 0) (ELit 4)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Ccap | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kwr_mdef; [evs; reflexivity | replace (b2 + 0) with b2 by lia; exact WRb | lia | lia | lia | lia].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hb4].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia].
           - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | right; lia]. }
      xruns HR HK 100%nat (0x67668 :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (11%bv) G11.
      rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
      assert (LR1 : loop_regs w R1) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
      clear T9 T18 T19 T20 T21 T25. evs_in G11. rewrite ?zbv_add in G11.

      set (Mclr := wbytes M (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 b2))).
      set (u := Z_to_bv 64 (PrsNeeds.sx32 fw)).
      pose proof (pm_v2_clear w A M model c b2 X ltac:(rewrite Ev2; reflexivity)) as X2. rewrite Ev2 in X2. cbn [t3c] in X2. change (wbytes M _ _) with Mclr in X2.
      pose proof (pm_v2_push_fast w A Mclr model (set_v2 c (b2, [], cap2)) b2 cap2 [] u X2 eq_refl ltac:(unfold Zlen; cbn; lia)) as X3. cbn zeta in X3.
      replace (b2 + 4 * Zlen (@nil Z)) with b2 in X3 by (unfold Zlen; cbn; lia).
      replace (bv_unsigned u mod 2 ^ 32) with fw in X3.
      2: { unfold u. rewrite u64_of_Z by lia. unfold PrsGrammar.sx32. destruct (Z.ltb_spec fw (2 ^ 31)).
           - rewrite Z.mod_small by lia. reflexivity.
           - replace (fw + 2 ^ 64 - 2 ^ 32) with (fw + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
      cbn [app] in X3.
      set (Mcur := wbytes Mclr (Z_to_bv 64 b2) (word_to_le_bytes 4 u)) in *.
      assert (ST3 : stores_in (fun a => zwin (w_p w + 248) (w_p w + 256) a \/ zwin b2 (b2 + 4) a) M Mcur).
      { unfold Mcur, Mclr. eapply stores_in_wbytes_more; [| lia | w2blen; cbn; lia | intros a' Ha'; w2blen; cbn in Ha'; right; unfold zwin; lia].
        eapply stores_in_wbytes_more; [apply stores_in_refl | lia | w2blen; cbn; lia | intros a' Ha'; w2blen; cbn in Ha'; left; unfold zwin; lia]. }
      eapply (loop_mem_frame w M Mcur) in LM; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
      eapply (izero_agree w M Mcur) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
      eapply (cellw_frame M Mcur) in Cfw; [| lia | cbn; lia | eapply stores_in_agree; [exact ST3 | unfold zwin; cbn; intros; lia]].
      assert (PD3 : mdef Mcur (w_p w) PARSER_SIZE) by (eapply stores_in_mdef; [exact ST3 | unfold PARSER_SIZE; exact PD]).
      eapply (pm_B1t w c0 K fx A Mcur model (set_v2 (set_v2 c (b2, [], cap2)) (b2, [fw], cap2)) R1 fw (b2 + 4) PS FZ X3).
      + cbn [c_tr set_v2]. exact Htr.
      + unfold pm_bud in BUD |- *. cbn [set_v2 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in BUD |- *. rewrite Ev2 in BUD. cbn [t3c snd] in BUD. exact BUD.
      + exact LR1. + exact LM. + exact IZ.
      + cbn [set_v2 c_endian]. exact He2. + exact Hw. + cbn [set_v2 c_widx]. exact Hlt. + cbn [set_v2 c_widx c_icount]. exact Hic.
      + exact Cfw. + reflexivity. + reflexivity. + cbn [set_v2 c_v2 t3a fst]. exact Hb16. + cbn [set_v2 c_v2 t3a fst]. exact Hbal.
      + exact PD3. + exact G11.
      + intros A' M' model' c' R' iwc op d X' Htr' BUD' LR' LM' IZ' IC' E1 E2 E3 E4 E5 W1 W2 W3 W4 V1' V2' Em1 Em2 Em3 Ev3 Ec1.
        eapply (B2K A' M' model' c' R' iwc op d X' Htr' BUD' LR' LM' IZ' IC' E1 E2 E3 E4 E5);
          cbn [set_v2 c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 t3b t3c fst snd] in W1, W2, W3, W4, V1', V2', Em1, Em2, Em3, Ev3, Ec1 |- *;
          try assumption. rewrite V2'. reflexivity.
  Qed.

  Lemma pm_B1 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> LI w A M model c R -> c_widx c < w_n w ->
    getr R 11%bv = Z_to_bv 64 (c_widx c) -> getr R 10%bv = Z_to_bv 64 (w_n w) ->
    (forall A' M' model' c' R' (fw iwc op d : Z),
        PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> loop_regs w R' -> loop_mem w M' -> izero w M' ->
        ictx w M' (c_widx c) fw iwc op d -> iwc = fw / 2 ^ 16 -> op = fw mod 2 ^ 16 -> iwc <> 0 -> 0 <= fw < 2 ^ 32 ->
        (exists l, g_op G op = Some l) -> idesc d op ->
        c_widx c' = c_widx c + 1 -> c_icount c' = c_icount c + 1 -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
        t3b (c_v1 c') = 0 -> t3b (c_v2 c') = [fw] ->
        c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c -> c_v3 c' = c_v3 c -> t3c (c_v1 c') = t3c (c_v1 c) ->
        srealizes SEGS (cfg fx R' 0x67758 M' model') K) ->
    srealizes SEGS (cfg fx R 0x67588 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS FZ FC HLI Hlt Qa1 Qa0 B2K.
    destruct HLI as (X & Htr & BUD & LR & LM & Hw5 & He2 & Hw & ACC & MACC & LACC).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).

    destruct (mdef_cell4 M (w_words w + 4 * c_widx c) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (fw & Cfw).
    pose proof (proj1 Cfw) as Rfw. cbn in Rfw.
    pose proof (fld_cellw M _ 4 _ (x_endian X) ltac:(lia)) as Ce. unfold O_ENDIAN in Ce.
    pm_seed R w c [Z_to_bv 64 (c_endian c); Z_to_bv 64 fw].
    seedLR HR E R [(11%bv, EVar 38); (10%bv, EVar 35)].
    seedHK HK w A M model c E X.
    assert (AW : edenot E WIX = Z_to_bv 64 (w_words w + 4 * c_widx c)) by (apply wix_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 39); KRange (EVar 39) 0 1; KWord (SA WIX 0) (N.to_nat 4) (EVar 40);
                           KDisj (SA WIX 0) (ELit 4) (SA (EVar 32) 0) (ELit 864); KDisj (SA WIX 0) (ELit 4) (SA (EVar 33) 0) (ELit 288);
                           KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 4]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_expr; [rewrite Z.add_0_r; exact Cfw | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * c_widx c) ltac:(unfold zwin; lia)) as [Hnw _].
           destruct (W5 (w_words w + 4 * c_widx c + 3) ltac:(unfold zwin; lia)) as [Hnw' _]. unfold zwin in Hnw, Hnw'. lia.
         - eapply kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * c_widx c) ltac:(unfold zwin; lia)) as [_ Hnp].
           destruct (W5 (w_words w + 4 * c_widx c + 3) ltac:(unfold zwin; lia)) as [_ Hnp']. lia.
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2]. }
    xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
    { split_scs; try sc_auto1. all: try (eapply sc_flat; [exact AW | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]).
      all: try (cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia).
      all: match goal with |- ?g => idtac "SC1:" g end. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ [22;23;24;26;27]%bv HRn eq_refl) as GS.
    rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
    assert (LR1 : loop_regs w R1) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
    clear T9 T18 T19 T20 T21 T25.
    rewrite ext_val_sx4 in G10 by lia. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) end.
    assert (ST1 : stores_in (fun a => zwin (w_p w + 80) (w_p w + 88) a \/ zwin (w_sp w + 240) (w_sp w + 280) a) M M1) by (unfold M1; stin).
    set (c1 := set_scal c (c_widx c) (c_icount c + 1) (c_endian c) (c_reqconv c)).
    assert (X1 : PMX w A M1 model c1).
    { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img);
        [exact X | exact ST1 | intros a [Ha|Ha]; unfold scal_win, zwin, O_WIDX, O_FLAGS, w_sp0, PM_FRAME in *; [right; lia | left; lia]
        | eapply fld_keep; [exact ST1 | exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros; lia]
        | unfold M1, O_ICOUNT; rdback
        | eapply fld_keep; [exact ST1 | exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST1 | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia]
        | lia | lia | lia | exact Sc4]. }
    eapply (loop_mem_frame w _ M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    assert (IZ : izero w M1) by (unfold izero, M1; repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | rdbackz])).
    clear ST1 X. clearbody M1. pose proof (x_ms X1) as MS1. assert (He32 : 0 <= c_endian c < 2 ^ 32) by lia.

    eapply (pm_fixword w A M1 model c1 fx R1 _ K X1 (ex_intro _ fw (ex_intro _ (c_endian c) (conj Rfw (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (r1 & Rr1 & Hr1). rewrite TablStmts.sx32_prs in Hr1.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. clear G1 G2 G3 G4 G8 G10 G11 Qa0 Qa1.
    pose proof (loop_regs_kept w R1 R2 LR1 KEPT) as LR2. clear LR1 KEPT GS.
    rename Qsp' into Qsp2. rename Qs0' into Qs02. rename Qgp' into Qgp2. rename Qtp' into Qtp2.

    pose proof (x_v2 X1) as V2. cbn [c1 c_v2 set_scal] in V2. destruct V2 as (_ & _ & _ & V2len & V2blk & V2f0 & V2f1 & _). unfold O_V2 in V2f0, V2f1.
    set (b2 := t3a (c_v2 c)) in *. set (xs := t3b (c_v2 c)) in *. set (cap2 := t3c (c_v2 c)) in *.
    assert (Eb2 : b2 = t3a (c_v2 c)) by reflexivity. clearbody b2 xs cap2.
    assert (Hb2 : 0 <= b2 /\ b2 + 4 * cap2 <= 2 ^ 63 /\ (cap2 = 0 \/ 16 <= b2) /\ 0 <= cap2).
    { destruct V2blk as [[Hb0 Hc0]|(Hb0 & Hal0 & Hc0 & Hbc & _)].
      { split; [lia|]; split; [lia|]; split; [left; lia | lia]. }
      split; [lia|]. split; [lia|]. split; [|lia]. right. pose proof (Z.div_mod b2 16 ltac:(lia)). lia. }
    destruct Hb2 as (Hb2lo & Hb2hi & Hb2al & Hc2).
    pose proof (fld_cellw M1 _ 8 _ V2f0 ltac:(lia)) as C240.
    pose proof (fld_cellw M1 _ 8 _ V2f1 ltac:(lia)) as C248. replace (w_p w + 240 + 8) with (w_p w + 248) in C248 by lia.
    pm_seed R2 w c1 [Z_to_bv 64 (PrsGrammar.sx32 r1); Z_to_bv 64 b2; Z_to_bv 64 (Zlen xs)].
    lrsplit LR2. seedLR HR E R2 [(10%bv, EVar 39)].
    seedHK HK w A M1 model c1 E X1.
    apply (know_more E M1 [KWord (SA (EVar 33) 240) (N.to_nat 8) (EVar 40); KWord (SA (EVar 33) 248) (N.to_nat 8) (EAlu ALU_ADD (EVar 40) (EMd M_MUL (ELit 4) (EVar 41)))]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C240 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C248 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite zbv_mul, zbv_add; reflexivity]. }
    pose proof (sx32_range r1 Rr1) as Rsx1.
    assert (Hic1 : c_icount c1 <= c_widx c1) by (cbn [c1 set_scal c_icount c_widx]; lia).
    destruct (Z.eq_dec (Zlen xs) 0) as [Hz|Hnz].
    -
      xruns HR HK 100%nat (0x67624 :: 0x67614 :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (12%bv) G12.
      rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
      clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
      assert (LR3 : loop_regs w R3) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity).
      clear T9 T18 T19 T20 T21 T25. evs_in G10. evs_in G12.
      rewrite (PmInstU1.w2lb4_sx32 r1) by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
      assert (ST2 : stores_in (zwin (w_sp w + 236) (w_sp w + 240)) M1 M2) by (unfold M2; stin).
      assert (X2 : PMX w A M2 model c1).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 _ model c1 (zwin (w_sp w + 236) (w_sp w + 240)));
          [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      eapply (loop_mem_frame w M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      eapply (izero_agree w M1) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      assert (Cr1 : cellw SEGS M2 (w_sp w + 236) 4 r1) by (split; [cbn; lia | unfold M2; change (N.to_nat 4) with 4%nat; rdback]).
      clear ST2.
      eapply (pm_B1b w c0 K fx A M2 model c1 R3 r1 PS FZ X2 Htr BUD LR3 LM IZ He2 Hw Hlt Hic1 Rr1 Cr1 ltac:(cbn [c1 set_scal c_v2]; rewrite <- Eb2; exact G12) G10).
      intros A' M' model' c' R' iwc op d X' Htr' BUD' LR' LM' IZ' IC' E1 E2 E3 E4 E5 Wc1 Wc2 Wc3 Wc4 V1' V2' Em1 Em2 Em3 Ev3 Ec1.
      eapply (B2K A' M' model' c' R' r1 iwc op d X' Htr' BUD' LR' LM' IZ');
        cbn [c1 set_scal c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 t3b t3c fst snd] in IC', Wc1, Wc2, Wc3, Wc4, V1', V2', Em1, Em2, Em3, Ev3, Ec1 |- *;
        try assumption.
    -
      xruns HR HK 100%nat (0x67624 :: 0x67614 :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
      rreg HRn (9%bv) T9. rreg HRn (18%bv) T18. rreg HRn (19%bv) T19. rreg HRn (20%bv) T20. rreg HRn (21%bv) T21. rreg HRn (25%bv) T25.
      clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4. evs_in T9. evs_in T21. rewrite ?w_add in T9 by lia. rewrite ?w_add in T21 by lia.
      evs_in G10. evs_in G11. evs_in G12. rewrite ?zbv_mul, ?zbv_add in G11.
      rewrite (PmInstU1.w2lb4_sx32 r1) by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
      assert (ST2 : stores_in (zwin (w_sp w + 236) (w_sp w + 240)) M1 M2) by (unfold M2; stin).
      assert (X2 : PMX w A M2 model c1).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 _ model c1 (zwin (w_sp w + 236) (w_sp w + 240)));
          [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      eapply (loop_mem_frame w M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      eapply (izero_agree w M1) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      assert (Cr1 : cellw SEGS M2 (w_sp w + 236) 4 r1) by (split; [cbn; lia | unfold M2; change (N.to_nat 4) with 4%nat; rdback]).
      clear ST2.
      destruct (cd4_gen (fx:=fx) 0x67614 0x67624 11%bv 12%bv M2 b2 (Z.to_nat (Zlen xs)) R3 (or_introl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))
                  ltac:(rewrite G11; f_equal; lia) G12 T25 ltac:(lia) ltac:(lia) ltac:(lia)) as (R4 & RUN4 & K4 & G11').
      pose proof (x_ms X2) as MS2.
      eapply srz_msteps; [exact (ms_halt _ MS2) | exact (ms_lazy _ MS2) | exact RUN4 |].
      assert (KQ : forall r, In r (all_but 11%bv) -> getr R4 r = getr R3 r) by exact K4.
      assert (LR4 : loop_regs w R4).
      { unfold loop_regs. rewrite !KQ by (vm_compute; repeat (first [left; reflexivity | right])). rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25. repeat split; reflexivity. }
      clear T9 T18 T19 T20 T21.
      eapply (pm_B1b w c0 K fx A M2 model c1 R4 r1 PS FZ X2 Htr BUD LR4 LM IZ He2 Hw Hlt Hic1 Rr1 Cr1
                ltac:(rewrite (KQ 12%bv) by (vm_compute; repeat (first [left; reflexivity | right])); cbn [c1 set_scal c_v2]; rewrite <- Eb2; exact G12)
                ltac:(rewrite (KQ 10%bv) by (vm_compute; repeat (first [left; reflexivity | right])); exact G10)).
      intros A' M' model' c' R' iwc op d X' Htr' BUD' LR' LM' IZ' IC' E1 E2 E3 E4 E5 Wc1 Wc2 Wc3 Wc4 V1' V2' Em1 Em2 Em3 Ev3 Ec1.
      eapply (B2K A' M' model' c' R' r1 iwc op d X' Htr' BUD' LR' LM' IZ');
        cbn [c1 set_scal c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 t3b t3c fst snd] in IC', Wc1, Wc2, Wc3, Wc4, V1', V2', Em1, Em2, Em3, Ev3, Ec1 |- *;
        try assumption.
  Qed.
End PM.
