(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_6aab4_6ab84.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6aae8 : bv 32 := 0x00008067.
Lemma F_6aae8 : fetch_word Plain.M.loaded_segments (0x6ab28 : word) = Some W_6aae8.
Proof. vm_refl. Qed.
Lemma D_6aae8 : decode_any W_6aae8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ab7c : bv 32 := 0x00153513.

Definition W_6ab80 : bv 32 := 0x00008067.
Lemma F_6ab80 : fetch_word Plain.M.loaded_segments (0x6abc0 : word) = Some W_6ab80.
Proof. vm_refl. Qed.
Lemma D_6ab80 : decode_any W_6ab80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_6aab4_6ab84.

Module S1_code_6b09c_6b294.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6b114 : bv 32 := 0x00008067.
Lemma F_6b114 : fetch_word Plain.M.loaded_segments (0x6b154 : word) = Some W_6b114.
Proof. vm_refl. Qed.
Lemma D_6b114 : decode_any W_6b114 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b1d0 : bv 32 := 0xf40692e3.

Definition W_6b204 : bv 32 := 0x00008067.
Lemma F_6b204 : fetch_word Plain.M.loaded_segments (0x6b244 : word) = Some W_6b204.
Proof. vm_refl. Qed.
Lemma D_6b204 : decode_any W_6b204 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b224 : bv 32 := 0x00008067.
Lemma F_6b224 : fetch_word Plain.M.loaded_segments (0x6b264 : word) = Some W_6b224.
Proof. vm_refl. Qed.
Lemma D_6b224 : decode_any W_6b224 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b240 : bv 32 := 0x00008067.
Lemma F_6b240 : fetch_word Plain.M.loaded_segments (0x6b280 : word) = Some W_6b240.
Proof. vm_refl. Qed.
Lemma D_6b240 : decode_any W_6b240 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b25c : bv 32 := 0x00008067.
Lemma F_6b25c : fetch_word Plain.M.loaded_segments (0x6b29c : word) = Some W_6b25c.
Proof. vm_refl. Qed.
Lemma D_6b25c : decode_any W_6b25c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b274 : bv 32 := 0x00008067.
Lemma F_6b274 : fetch_word Plain.M.loaded_segments (0x6b2b4 : word) = Some W_6b274.
Proof. vm_refl. Qed.
Lemma D_6b274 : decode_any W_6b274 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b290 : bv 32 := 0x00008067.
Lemma F_6b290 : fetch_word Plain.M.loaded_segments (0x6b2d0 : word) = Some W_6b290.
Proof. vm_refl. Qed.
Lemma D_6b290 : decode_any W_6b290 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_6b09c_6b294.

Module S1_code_6bd64_6c040.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6bd64 : bv 32 := 0xff010113.

Definition W_6bd68 : bv 32 := 0x00113423.

Definition W_6bd6c : bv 32 := 0x00813023.

Definition W_6bd70 : bv 32 := 0x00050413.

Definition W_6bd74 : bv 32 := 0xfffa6517.

Definition W_6bd78 : bv 32 := 0x6a350513.

Definition W_6bd7c : bv 32 := 0x00040593.

Definition W_6bd80 : bv 32 := 0x019750ef.

Definition W_6bd84 : bv 32 := 0x14050e63.

Definition W_6bd90 : bv 32 := 0x00040593.

Definition W_6bd94 : bv 32 := 0x005750ef.

Definition W_6bd98 : bv 32 := 0x14050e63.

Definition W_6bd9c : bv 32 := 0xfffa7517.

Definition W_6bda0 : bv 32 := 0xe1450513.

Definition W_6bda4 : bv 32 := 0x00040593.

Definition W_6bda8 : bv 32 := 0x7f0750ef.

Definition W_6bdbc : bv 32 := 0x7dc750ef.

Definition W_6bdc0 : bv 32 := 0x14050e63.

Definition W_6bdc4 : bv 32 := 0xfffa7517.

Definition W_6bdc8 : bv 32 := 0x1d750513.

Definition W_6bdcc : bv 32 := 0x00040593.

Definition W_6bdd0 : bv 32 := 0x7c8750ef.

Definition W_6bdd4 : bv 32 := 0x14050e63.

Definition W_6bdd8 : bv 32 := 0xfffa7517.

Definition W_6bddc : bv 32 := 0xe0150513.

Definition W_6bde0 : bv 32 := 0x00040593.

Definition W_6bde4 : bv 32 := 0x7b4750ef.

Definition W_6bde8 : bv 32 := 0x14050e63.

Definition W_6bdec : bv 32 := 0xfffa8517.

Definition W_6bdf0 : bv 32 := 0x9df50513.

Definition W_6bdf4 : bv 32 := 0x00040593.

Definition W_6bdf8 : bv 32 := 0x7a0750ef.

Definition W_6bdfc : bv 32 := 0x14050e63.

Definition W_6be00 : bv 32 := 0xfffa4517.

Definition W_6be04 : bv 32 := 0x4e650513.

Definition W_6be08 : bv 32 := 0x00040593.

Definition W_6be0c : bv 32 := 0x78c750ef.

Definition W_6be10 : bv 32 := 0x14050e63.

Definition W_6be14 : bv 32 := 0xfffa5517.

Definition W_6be18 : bv 32 := 0xba750513.

Definition W_6be1c : bv 32 := 0x01d00613.

Definition W_6be20 : bv 32 := 0x00040593.

Definition W_6be24 : bv 32 := 0x2d5750ef.

Definition W_6be28 : bv 32 := 0x14050c63.

Definition W_6be2c : bv 32 := 0xfffa5517.

Definition W_6be30 : bv 32 := 0x0ae50513.

Definition W_6be34 : bv 32 := 0x01c00613.

Definition W_6be38 : bv 32 := 0x00040593.

Definition W_6be3c : bv 32 := 0x2bd750ef.

Definition W_6be40 : bv 32 := 0x14050a63.

Definition W_6be44 : bv 32 := 0xfffa5517.

Definition W_6be48 : bv 32 := 0xb9550513.

Definition W_6be4c : bv 32 := 0x01c00613.

Definition W_6be50 : bv 32 := 0x00040593.

Definition W_6be54 : bv 32 := 0x2a5750ef.

Definition W_6be58 : bv 32 := 0x14050863.

Definition W_6be5c : bv 32 := 0xfffa8517.

Definition W_6be60 : bv 32 := 0xcc750513.

Definition W_6be64 : bv 32 := 0x01b00613.

Definition W_6be68 : bv 32 := 0x00040593.

Definition W_6be6c : bv 32 := 0x28d750ef.

Definition W_6be70 : bv 32 := 0x14050663.

Definition W_6be74 : bv 32 := 0xfffa6517.

Definition W_6be78 : bv 32 := 0xd8750513.

Definition W_6be7c : bv 32 := 0x00040593.

Definition W_6be80 : bv 32 := 0x718750ef.

Definition W_6be84 : bv 32 := 0x14050663.

Definition W_6be88 : bv 32 := 0xfffa4517.

Definition W_6be8c : bv 32 := 0x7c650513.

Definition W_6be90 : bv 32 := 0x00040593.

Definition W_6be94 : bv 32 := 0x704750ef.

Definition W_6be98 : bv 32 := 0x14050663.

Definition W_6be9c : bv 32 := 0xfffa6517.

Definition W_6bea0 : bv 32 := 0x0b950513.

Definition W_6bea4 : bv 32 := 0x01d00613.

Definition W_6bea8 : bv 32 := 0x00040593.

Definition W_6beac : bv 32 := 0x24d750ef.

Definition W_6beb0 : bv 32 := 0x14050463.

Definition W_6beb4 : bv 32 := 0xfffa8517.

Definition W_6beb8 : bv 32 := 0x2a350513.

Definition W_6bebc : bv 32 := 0x00c00613.

Definition W_6bf08 : bv 32 := 0x00300513.

Definition W_6bfd8 : bv 32 := 0x00013403.

Definition W_6c03c : bv 32 := 0x00008067.
Lemma F_6c03c : fetch_word Plain.M.loaded_segments (0x6c07c : word) = Some W_6c03c.
Proof. vm_refl. Qed.
Lemma D_6c03c : decode_any W_6c03c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_6bd64_6c040.

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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablStmts TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SmallP1.S1_code_6aab4_6ab84. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SmallP1.S1_code_6b09c_6b294. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SmallP1.S1_code_6bd64_6c040.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgP1.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation tc := Img.tc.

Definition HE_RET : Z := 0x6abc0.
Definition IEI_RET : Z := 0x6b264.
Definition NS_RET : Z := 0x6c07c.
Definition GT_RET1 : Z := 0x6b154.
Definition GT_RET0 : Z := 0x6b244.
Definition FW_RET : Z := 0x6ab28.

Ltac bool_post :=
  idtac;
  rewrite ?lit_b2w_1, ?lit_b2w_0;
  repeat match goal with
  | |- context [alu64 ALU_SLTU ?a ?b] => let t := fresh "t" in destruct (sltu_b2w a b) as [t ->]
  | |- context [alu64 ALU_SLT ?a ?b] => let t := fresh "t" in destruct (slt_b2w a b) as [t ->]
  end;
  rewrite ?or_b2w;
  repeat match goal with
  | |- context [alu64 ALU_AND (b2w ?s) ?y] => let t := fresh "t" in destruct (and_b2w_l s y) as [t ->]
  end;
  rewrite ?or_b2w;
  lazymatch goal with |- exists b : bool, b2w ?t = _ => exists t; reflexivity | |- ?g => idtac "bool_post leaves" g end.

Ltac leaf_fin Hra Hret :=
  idtac;
  lazymatch type of Hra with getr _ _ = ?retv =>
  lazymatch goal with
  | HR' : regs_ok _ _ ?R', Hms : msteps _ _ _ |- _ =>
      let Hra1 := fresh "Hra1" in
      assert (Hra1 : getr R' 1%bv = retv) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]);
      exists R'; split; [|split];
      [ eapply msteps_trans; [exact Hms|]; norm_pc;
        first [ stepjr F_6ab80 D_6ab80 retv ltac:(exact Hra1)
              | stepjr F_6b224 D_6b224 retv ltac:(exact Hra1)
              | stepjr F_6c03c D_6c03c retv ltac:(exact Hra1)
              | stepjr F_6b114 D_6b114 retv ltac:(exact Hra1)
              | stepjr F_6b204 D_6b204 retv ltac:(exact Hra1)
              | stepjr F_6aae8 D_6aae8 retv ltac:(exact Hra1) ];
        change (bv_signed (0%bv : bv 12)) with 0%Z; unfold ret_ok in Hret; rewrite Hret; apply mst_refl
      | exact (kept_of_syms _ _ _ R' HR' eq_refl)
      | let H10 := fresh "H10" in rreg HR' 10%bv H10; rewrite H10 ]
  end end.

Section Small.

  Theorem is_host_endian_spec : is_host_endian_stmt SEGS L tc.
  Proof.
    intros fx R M ret HRO (x & Hx & Ha0) Hra Hret.
    pose (E := Eseed R [Z_to_bv 64 x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xtree HR HK 50%nat [HE_RET] 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(leaf_fin Hra Hret) ltac:(br_kill).
    destruct (sltu_b2w (Z_to_bv 64 x) (Z_to_bv 64 1)) as [t ->]. exists (if t then 1 else 0). split; [destruct t; lia | reflexivity].
  Qed.

  Theorem is_ext_inst_spec : is_ext_inst_stmt SEGS L tc.
  Proof.
    intros fx R M ret HRO (x & Hx & Ha0) Hra Hret.
    pose (E := Eseed R [Z_to_bv 64 x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xtree HR HK 50%nat [IEI_RET] 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(leaf_fin Hra Hret) ltac:(br_kill).
    all: bool_post.
  Qed.

  Theorem is_nonsemantic_spec : is_nonsemantic_stmt SEGS L tc.
  Proof.
    intros fx R M ret HRO (x & Hx & Ha0) Hra Hret.
    pose (E := Eseed R [Z_to_bv 64 x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xtree HR HK 50%nat [NS_RET] 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(leaf_fin Hra Hret) ltac:(br_kill).
    all: bool_post.
  Qed.

  Ltac crun Ha0 Hra Hret rets :=
    lazymatch type of Ha0 with getr ?R 10%bv = Z_to_bv 64 ?v =>
    lazymatch goal with |- exists R', msteps _ (mkst R _ ?M _) _ /\ _ =>
      let E := fresh "E" in pose (E := Eseed R (@nil word));
      let HR := fresh "HR" in
      assert (HR : regs_ok E (srs sr_id [(10%bv, ELit v)]) R)
        by (apply regs_ok_srs; [apply regs_ok_seed|];
            repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact Ha0);
      let HK := fresh "HK" in assert (HK : know_ok SEGS E M []) by constructor;
      xrun HR HK 80%nat rets (SCR [] [] []) 40%N; [ split_scs; try sc_auto1 | leaf_ret Hra Hret ]
    end end.

  Ltac srun Ha0 Hra Hret rets lo hi :=
    lazymatch type of Ha0 with getr ?R 10%bv = Z_to_bv 64 ?xv =>
    lazymatch goal with |- exists R', msteps _ (mkst R _ ?M _) _ /\ _ =>
      let E := fresh "E" in pose (E := Eseed R [Z_to_bv 64 xv]);
      let HR := fresh "HR" in
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
        by (apply regs_ok_srs; [apply regs_ok_seed|];
            repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact Ha0);
      let HK := fresh "HK" in assert (HK : know_ok SEGS E M [KRange (EVar 32) lo hi])
        by (constructor; [|constructor]; eapply krange_var; [evs; reflexivity | lia | lia]);
      xrun HR HK 80%nat rets (SCR [] [] []) 40%N; [ split_scs; try sc_auto1 | leaf_ret Hra Hret ]
    end end.
  Ltac gt_post Hx Ha0 :=
    first [ exists false; split; [reflexivity | intros X; discriminate X]
          | exists true; split; [reflexivity | intros _; refine (ex_intro _ _ (conj Hx (conj Ha0 _))); vm_compute; reflexivity] ].

  Theorem generates_type_spec : generates_type_stmt SEGS L tc tg_generates_type.
  Proof.
    intros fx R M ret HRO (x & Hx & Ha0) Hra Hret.
    assert (Hc : x < 19 \/ 19 <= x < 19 + Z.of_nat 20 \/ 39 <= x <= 321 \/ x = 322 \/ 323 <= x <= 326 \/ x = 327 \/ 328 <= x <= 4162
                 \/ x = 4163 \/ 4164 <= x <= 4189 \/ x = 4190 \/ 4191 <= x <= 4416 \/ 4417 <= x < 4417 + Z.of_nat 56
                 \/ 4473 <= x <= 5075 \/ x = 5076 \/ 5077 <= x <= 5114 \/ x = 5115 \/ 5116 <= x <= 5280 \/ 5281 <= x < 5281 + Z.of_nat 61
                 \/ 5342 <= x <= 5357 \/ 5358 <= x < 5358 + Z.of_nat 14 \/ 5372 <= x <= 6198 \/ x = 6199 \/ 6200 <= x <= 2 ^ 32 - 1) by lia.
    destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]].
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 0 18. gt_post Hx Ha0.
    - enum_range x 19 20%nat H; lit_in Ha0; (crun Ha0 Hra Hret [GT_RET1; GT_RET0]; gt_post Hx Ha0).
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 39 321. gt_post Hx Ha0.
    - subst x. crun Ha0 Hra Hret [GT_RET1; GT_RET0]. gt_post Hx Ha0.
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 323 326. gt_post Hx Ha0.
    - subst x. crun Ha0 Hra Hret [GT_RET1; GT_RET0]. gt_post Hx Ha0.
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 328 4162. gt_post Hx Ha0.
    - subst x. crun Ha0 Hra Hret [GT_RET1; GT_RET0]. gt_post Hx Ha0.
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 4164 4189. gt_post Hx Ha0.
    - subst x. crun Ha0 Hra Hret [GT_RET1; GT_RET0]. gt_post Hx Ha0.
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 4191 4416. gt_post Hx Ha0.
    - enum_range x 4417 56%nat H; lit_in Ha0; (crun Ha0 Hra Hret [GT_RET1; GT_RET0]; gt_post Hx Ha0).
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 4473 5075. gt_post Hx Ha0.
    - subst x. crun Ha0 Hra Hret [GT_RET1; GT_RET0]. gt_post Hx Ha0.
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 5077 5114. gt_post Hx Ha0.
    - subst x. crun Ha0 Hra Hret [GT_RET1; GT_RET0]. gt_post Hx Ha0.
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 5116 5280. gt_post Hx Ha0.
    - enum_range x 5281 61%nat H; lit_in Ha0; (crun Ha0 Hra Hret [GT_RET1; GT_RET0]; gt_post Hx Ha0).
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 5342 5357. gt_post Hx Ha0.
    - enum_range x 5358 14%nat H; lit_in Ha0; (crun Ha0 Hra Hret [GT_RET1; GT_RET0]; gt_post Hx Ha0).
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 5372 6198. gt_post Hx Ha0.
    - subst x. crun Ha0 Hra Hret [GT_RET1; GT_RET0]. gt_post Hx Ha0.
    - srun Ha0 Hra Hret [GT_RET1; GT_RET0] 6200 (2 ^ 32 - 1). gt_post Hx Ha0.
  Qed.

  Theorem fixword_spec : fixword_stmt SEGS L tc.
  Proof.
    intros fx R M ret HRO (w & e & Hw & Ha0 & He & Ha1) Hra Hret.
    pose proof (sx32_range w Hw) as Hsw.
    pose (E := Eseed R [Z_to_bv 64 (TablStmts.sx32 w); Z_to_bv 64 e]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 33) 0 4294967295]).
    { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
    xtree HR HK 60%nat [FW_RET] 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(leaf_fin Hra Hret) ltac:(br_kill).
    -   exists w. split; [exact Hw | reflexivity].
    -   destruct (fixword_swap w Hw) as (r & Hr & E1). exists r. split; [exact Hr | exact E1].
  Qed.
End Small.
