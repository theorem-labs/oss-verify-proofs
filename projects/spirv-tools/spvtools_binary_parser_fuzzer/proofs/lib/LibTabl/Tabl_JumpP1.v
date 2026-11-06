(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablStmts TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgP1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgP1.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation ti := Img.ti.
Abbreviation tc := Img.tc.

Definition IO_RETS : list Z := [0x6bb98; 0x6bba0].
Definition FP_RETS : list Z := [0x6bd18; 0x6bd24; 0x6bd2c; 0x6bd34; 0x6bd3c; 0x6bd44; 0x6bd4c; 0x6bd54; 0x6bd5c].
Definition TS_RETS : list Z := [0x6b98c; 0x6b998].

Section Jump.

  Lemma HKimg : forall E M, ro_clear L M -> know_ok SEGS E M [KImg (ti_ro_lo ti) (ti_ro_hi ti)].
  Proof.
    intros E M HRO. constructor; [|constructor].
    apply (kimg_ro SEGS L E M _ _ HRO Img.rodata); cbn; lia.
  Qed.

  Ltac concrete_run HRO Ha0 Hra Hret rets :=
    lazymatch type of Ha0 with getr ?R 10%bv = Z_to_bv 64 ?v =>
    lazymatch goal with |- exists R', msteps _ (mkst R _ ?M _) _ /\ _ =>
      let E := fresh "E" in pose (E := Eseed R (@nil word));
      let HR := fresh "HR" in
      assert (HR : regs_ok E (srs sr_id [(10%bv, ELit v)]) R)
        by (apply regs_ok_srs; [apply regs_ok_seed|];
            repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact Ha0);
      let HK := fresh "HK" in pose proof (HKimg E M HRO) as HK;
      xrun HR HK 60%nat rets (SCR [] [] []) 40%N; [ split_scs; try sc_auto1 | leaf_ret Hra Hret ]
    end end.

  Theorem is_optional_spec : is_optional_stmt SEGS L tc.
  Proof.
    intros fx R M ret HRO (x & Hx & Ha0) Hra Hret.
    destruct (Z_lt_le_dec x 42) as [Hlo | Hge]; [| destruct (Z_lt_le_dec 106 x) as [Hhi | Hle]].
    -
      pose (E := Eseed R [Z_to_bv 64 x]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KRange (EVar 32) 0 41]).
      { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xrun HR HK 60%nat IO_RETS (SCR [] [] []) 40%N; [ split_scs; try sc_auto1 | leaf_ret Hra Hret ].
      exists false. split; [reflexivity | intros X; discriminate X].
    -
      pose (E := Eseed R [Z_to_bv 64 x]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KRange (EVar 32) 107 4294967295]).
      { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xrun HR HK 60%nat IO_RETS (SCR [] [] []) 40%N; [ split_scs; try sc_auto1 | leaf_ret Hra Hret ].
      exists false. split; [reflexivity | intros X; discriminate X].
    -
      assert (Hr : 42 <= x < 42 + Z.of_nat 65) by lia.
      enum_range x 42 65%nat Hr; lit_in Ha0;
        (concrete_run HRO Ha0 Hra Hret IO_RETS; first [exists true; split; [reflexivity | intros _; refine (ex_intro _ _ (conj _ Ha0)); lia] | exists false; split; [reflexivity | intros X; discriminate X]]).
  Qed.

  Theorem fpenc_spec : fpenc_stmt SEGS L tc.
  Proof.
    intros fx R M ret HRO _ Hra Hret.
    pose proof (Z_to_bv_bv_unsigned 64 (getr R 10%bv)) as Ha0. symmetry in Ha0.
    pose proof (bv_unsigned_in_range _ (getr R 10%bv)) as Hx. unfold bv_modulus in Hx.
    set (x := bv_unsigned (getr R 10%bv)) in *. clearbody x. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hx.
    assert (Hc : x = 0 \/ 1 <= x <= 4213 \/ 4228 <= x \/ 4214 <= x < 4214 + Z.of_nat 14) by lia.
    destruct Hc as [Hc | [Hc | [Hc | Hc]]].
    - subst x. concrete_run HRO Ha0 Hra Hret FP_RETS. eexists; split; [|reflexivity]; lia.
    - pose (E := Eseed R [Z_to_bv 64 x]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KRange (EVar 32) 1 4213]).
      { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xrun HR HK 60%nat FP_RETS (SCR [] [] []) 40%N; [ split_scs; try sc_auto1 | leaf_ret Hra Hret ].
      eexists; split; [|reflexivity]; lia.
    - pose (E := Eseed R [Z_to_bv 64 x]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KRange (EVar 32) 4228 18446744073709551615]).
      { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xrun HR HK 60%nat FP_RETS (SCR [] [] []) 40%N; [ split_scs; try sc_auto1 | leaf_ret Hra Hret ].
      eexists; split; [|reflexivity]; lia.
    - enum_range x 4214 14%nat Hc; lit_in Ha0;
        (concrete_run HRO Ha0 Hra Hret FP_RETS; eexists; split; [|reflexivity]; lia).
  Qed.

  Ltac tstr_post :=
    idtac;
    lazymatch goal with |- exists p n, _ /\ _ /\ Z_to_bv 64 ?v = Z_to_bv 64 p =>
      let r := eval vm_compute in (find (fun pn => fst pn =? v) (ti_tstr_dflt ti :: ti_tstr ti)) in
      lazymatch r with Some (_, ?n) =>
        let Hf := fresh "Hf" in
        assert (Hf : find (fun pn => fst pn =? v) (ti_tstr_dflt ti :: ti_tstr ti) = Some (v, n)) by (vm_compute; reflexivity);
        apply find_some in Hf; destruct Hf as [Hf _];
        destruct (proj2 (tstr_facts SEGS L ti Img.rodata Img.IFX) _ Hf) as [Hc Hn];
        exists v, n; split; [exact Hc | split; [exact Hn | reflexivity]]
      end
    end.

  Theorem operand_type_str_spec : operand_type_str_stmt SEGS L tc.
  Proof.
    intros fx R M ret HRO (x & Hx & Ha0) Hra Hret.
    destruct (Z_lt_le_dec 107 x) as [Hhi | Hle].
    - pose (E := Eseed R [Z_to_bv 64 x]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KRange (EVar 32) 108 4294967295]).
      { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xrun HR HK 60%nat TS_RETS (SCR [] [] []) 40%N; [ split_scs; try sc_auto1 | leaf_ret Hra Hret ].
      tstr_post.
    - assert (Hr : 0 <= x < 0 + Z.of_nat 108) by lia.
      enum_range x 0 108%nat Hr; lit_in Ha0; (concrete_run HRO Ha0 Hra Hret TS_RETS; tstr_post).
  Qed.
End Jump.
