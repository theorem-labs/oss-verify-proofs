(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import U1_code_6c578_6c7c4.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation ti := Img.ti.
Abbreviation tc := Img.tc.

Definition IOPS_RET : Z := 0x6c7b0.
Definition OOPS_RET : Z := 0x6c788.
Definition EOPS_RET : Z := 0x6c7fc.
Definition NAME_RET : Z := 0x6c7d4.

Lemma cell4_of_fld : forall M a v, CRep.fld SEGS M a 4 v -> 0 <= v < 2 ^ 32 -> cell4 SEGS M a v.
Proof. intros M a v H Hv. split; [cbn; lia | exact H]. Qed.

Section Acc.

  Theorem idesc_operands_spec : idesc_operands_stmt SEGS L TG tc (idesc ti).
  Proof.
    intros fx R M ret HRO (d & op & Hd & Ha0) Hra Hret.
    destruct (idesc_facts SEGS L ti Img.rodata Img.IFX d op Hd)
      as (r & Hfind & Hop & Htg & Hd0 & Hd1 & Hfld & Hf0 & Hc0 & Hfc & Hnc & Hnf & Hncb & SP & AL & LEN & CS & CN).
    destruct (Hfld M HRO) as (F0 & F8 & F12 & F16 & F20).
    assert (Zlen SPANS = 1151) as HLS by reflexivity.
    pose proof (cell4_of_fld M _ _ F8 ltac:(lia)) as C8. pose proof (cell4_of_fld M _ _ F12 ltac:(lia)) as C12.
    unfold INSN_STRIDE in *.
    pose (E := Eseed R [Z_to_bv 64 d; Z_to_bv 64 (i_first r); Z_to_bv 64 (i_count r)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 50%nat [IOPS_RET] (SCR [false] [EVar 33; EVar 34] []) 40%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?w_mul by lia; rewrite ?br_ltu by lia; bool_lia. }
    assert (Hra1 : getr R' 1%bv = ret).
    { rewrite <- Hra. apply (kept_of_syms R _ _ R' HR' eq_refl). cbn. tauto. }
    exists R'. split; [|split].
    - eapply msteps_trans; [exact Hms|].
      norm_pc. stepjr F_6c770 D_6c770 ret ltac:(exact Hra1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
    - exact (kept_of_syms R _ _ R' HR' eq_refl).
    - intros d' op' Hd' Ha0'.
      destruct (idesc_facts SEGS L ti Img.rodata Img.IFX d' op' Hd') as (r' & Hfind' & Hop' & Htg' & Hd0' & Hd1' & _).
      assert (Ed : d' = d).
      { rewrite Ha0 in Ha0'. apply (f_equal bv_unsigned) in Ha0'. unfold INSN_STRIDE in Hd1'.
        rewrite (u64_of_Z d) in Ha0' by lia. rewrite (u64_of_Z d') in Ha0' by lia. lia. }
      subst d'. destruct (find_insn_fun _ _ _ _ _ Hfind Hfind') as [<- <-].
      exists (ti_spans ti + 4 * i_first r), (i_span r).
      split; [exact Htg|]. split; [exact SP|]. split; [exact AL|].
      rreg HR' 10%bv H10. rreg HR' 11%bv H11. rewrite H10, H11. split.
      + rewrite w_mul, w_add by lia. f_equal. cbn [ti_spans Img.ti]. lia.
      + rewrite LEN. reflexivity.
  Qed.

  Theorem odesc_operands_spec : odesc_operands_stmt SEGS L TG tc (odesc ti).
  Proof.
    intros fx R M ret HRO (d & t & v & Hd & Ha0) Hra Hret.
    destruct (odesc_facts SEGS L ti Img.rodata Img.IFX d t v Hd)
      as (r & Hfind & Htg & Hv & Hd0 & Hd1 & Hfld & Hvb & Hf0 & Hc0 & Hfc & SP & AL & LEN).
    destruct (Hfld M HRO) as (F0 & F4 & F8).
    assert (Zlen SPANS = 1151) as HLS by reflexivity.
    pose proof (cell4_of_fld M _ _ F4 ltac:(lia)) as C4. pose proof (cell4_of_fld M _ _ F8 ltac:(lia)) as C8.
    unfold OPND_STRIDE in *.
    pose (E := Eseed R [Z_to_bv 64 d; Z_to_bv 64 (v_first r); Z_to_bv 64 (v_count r)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 50%nat [OOPS_RET] (SCR [false] [EVar 33; EVar 34] []) 40%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?w_mul by lia; rewrite ?br_ltu by lia; bool_lia. }
    assert (Hra1 : getr R' 1%bv = ret).
    { rewrite <- Hra. apply (kept_of_syms R _ _ R' HR' eq_refl). cbn. tauto. }
    exists R'. split; [|split].
    - eapply msteps_trans; [exact Hms|].
      norm_pc. stepjr F_6c748 D_6c748 ret ltac:(exact Hra1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
    - exact (kept_of_syms R _ _ R' HR' eq_refl).
    - intros d' t' v' Hd' Ha0'.
      destruct (odesc_facts SEGS L ti Img.rodata Img.IFX d' t' v' Hd') as (r' & Hfind' & Htg' & Hv' & Hd0' & Hd1' & _).
      assert (Ed : d' = d).
      { rewrite Ha0 in Ha0'. apply (f_equal bv_unsigned) in Ha0'. unfold OPND_STRIDE in Hd1'.
        rewrite (u64_of_Z d) in Ha0' by lia. rewrite (u64_of_Z d') in Ha0' by lia. lia. }
      subst d'. unfold find_opnd in Hfind, Hfind'.
      destruct (find_byvalue_ix_fun _ _ _ _ _ _ _ _ _ Hfind Hfind') as [<- <-].
      exists (ti_spans ti + 4 * v_first r), (v_span r).
      split; [exact Htg'|]. split; [exact SP|]. split; [exact AL|].
      rreg HR' 10%bv H10. rreg HR' 11%bv H11. rewrite H10, H11. split.
      + rewrite w_mul, w_add by lia. f_equal. cbn [ti_spans Img.ti]. lia.
      + rewrite LEN. reflexivity.
  Qed.

  Theorem edesc_operands_spec : edesc_operands_stmt SEGS L TG tc (edesc ti).
  Proof.
    intros fx R M ret HRO (d & t & v & Hd & Ha0) Hra Hret.
    destruct (edesc_facts SEGS L ti Img.rodata Img.IFX d t v Hd)
      as (r & Hfind & Htg & Hv & Hd0 & Hd1 & Hfld & Hvb & Hf0 & Hc0 & Hfc & SP & AL & LEN).
    destruct (Hfld M HRO) as (F0 & F4 & F8).
    assert (Zlen SPANS = 1151) as HLS by reflexivity.
    pose proof (cell4_of_fld M _ _ F4 ltac:(lia)) as C4. pose proof (cell4_of_fld M _ _ F8 ltac:(lia)) as C8.
    unfold EXT_STRIDE in *.
    pose (E := Eseed R [Z_to_bv 64 d; Z_to_bv 64 (v_first r); Z_to_bv 64 (v_count r)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 50%nat [EOPS_RET] (SCR [false] [EVar 33; EVar 34] []) 40%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?w_mul by lia; rewrite ?br_ltu by lia; bool_lia. }
    assert (Hra1 : getr R' 1%bv = ret).
    { rewrite <- Hra. apply (kept_of_syms R _ _ R' HR' eq_refl). cbn. tauto. }
    exists R'. split; [|split].
    - eapply msteps_trans; [exact Hms|].
      norm_pc. stepjr F_6c7bc D_6c7bc ret ltac:(exact Hra1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
    - exact (kept_of_syms R _ _ R' HR' eq_refl).
    - intros d' t' v' Hd' Ha0'.
      destruct (edesc_facts SEGS L ti Img.rodata Img.IFX d' t' v' Hd') as (r' & Hfind' & Htg' & Hv' & Hd0' & Hd1' & _).
      assert (Ed : d' = d).
      { rewrite Ha0 in Ha0'. apply (f_equal bv_unsigned) in Ha0'. unfold EXT_STRIDE in Hd1'.
        rewrite (u64_of_Z d) in Ha0' by lia. rewrite (u64_of_Z d') in Ha0' by lia. lia. }
      subst d'. unfold find_ext in Hfind, Hfind'.
      destruct (find_byvalue_ix_fun _ _ _ _ _ _ _ _ _ Hfind Hfind') as [<- <-].
      exists (ti_spans ti + 4 * v_first r), (v_span r).
      split; [exact Htg'|]. split; [exact SP|]. split; [exact AL|].
      rreg HR' 10%bv H10. rreg HR' 11%bv H11. rewrite H10, H11. split.
      + rewrite w_mul, w_add by lia. f_equal. cbn [ti_spans Img.ti]. lia.
      + rewrite LEN. reflexivity.
  Qed.

  Theorem idesc_name_spec : idesc_name_stmt SEGS L tc (idesc ti).
  Proof.
    intros fx R M ret HRO (d & op & Hd & Ha0) Hra Hret.
    destruct (idesc_facts SEGS L ti Img.rodata Img.IFX d op Hd)
      as (r & Hfind & Hop & Htg & Hd0 & Hd1 & Hfld & Hf0 & Hc0 & Hfc & Hnc & Hnf & Hncb & SP & AL & LEN & CS & CN).
    destruct (Hfld M HRO) as (F0 & F8 & F12 & F16 & F20).
    pose proof (cell4_of_fld M _ _ F16 ltac:(lia)) as C16. pose proof (cell4_of_fld M _ _ F20 ltac:(lia)) as C20.
    unfold INSN_STRIDE in *.
    pose (E := Eseed R [Z_to_bv 64 d; Z_to_bv 64 (i_nfirst r); Z_to_bv 64 (i_ncount r)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 50%nat [NAME_RET] (SCR [false] [EVar 33; EVar 34] []) 40%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?w_mul by lia; rewrite ?br_ltu by lia; bool_lia. }
    assert (Hra1 : getr R' 1%bv = ret).
    { rewrite <- Hra. apply (kept_of_syms R _ _ R' HR' eq_refl). cbn. tauto. }
    exists R'. split; [|split].
    - eapply msteps_trans; [exact Hms|].
      norm_pc. stepjr F_6c794 D_6c794 ret ltac:(exact Hra1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
    - exact (kept_of_syms R _ _ R' HR' eq_refl).
    - exists (ti_strings ti + i_nfirst r), (i_ncount r - 1).
      split; [exact CS|]. split; [exact CN|].
      rreg HR' 10%bv H10. rewrite H10. rewrite w_add by lia. f_equal. cbn [ti_strings Img.ti]. lia.
  Qed.

  Theorem odesc_value_spec : odesc_value_stmt SEGS L (odesc ti).
  Proof.
    intros d t v M Hd HRO.
    destruct (odesc_facts SEGS L ti Img.rodata Img.IFX d t v Hd) as (r & _ & _ & _ & Hd0 & Hd1 & Hfld & _).
    destruct (Hfld M HRO) as (F0 & _). unfold OPND_STRIDE in Hd1. split; [exact F0 | lia].
  Qed.
End Acc.
