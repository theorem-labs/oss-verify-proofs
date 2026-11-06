(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6bed0_6bfe0.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6bf08 : bv 32 := 0x00008067.
Lemma F_6bf08 : fetch_word Ubsan.M.loaded_segments (0x6bf48 : word) = Some W_6bf08.
Proof. vm_refl. Qed.
Lemma D_6bf08 : decode_any W_6bf08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfd8 : bv 32 := 0x00008067.
Lemma F_6bfd8 : fetch_word Ubsan.M.loaded_segments (0x6c018 : word) = Some W_6bfd8.
Proof. vm_refl. Qed.
Lemma D_6bfd8 : decode_any W_6bfd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6bed0_6bfe0.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.U1_code_6c578_6c7c4.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6d99c_6dcb4.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6db30 : bv 32 := 0x00040593.

Definition W_6db34 : bv 32 := 0x31d750ef.

Definition W_6db38 : bv 32 := 0x14050463.

Definition W_6dcac : bv 32 := 0x00008067.
Lemma F_6dcac : fetch_word Ubsan.M.loaded_segments (0x6dcec : word) = Some W_6dcac.
Proof. vm_refl. Qed.
Lemma D_6dcac : decode_any W_6dcac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6d99c_6dcb4.

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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablStmts TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SmallU1.U1_code_6bed0_6bfe0. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import U1_code_6c578_6c7c4.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SmallU1.U1_code_6d99c_6dcb4.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation tc := Img.tc.

Definition HE_RET : Z := 0x6c018.
Definition IEI_RET : Z := 0x6c764.
Definition NS_RET : Z := 0x6dcec.
Definition GT_RET1 : Z := 0x6c654.
Definition GT_RET0 : Z := 0x6c744.
Definition FW_RET : Z := 0x6bf48.

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
        first [ stepjr F_6bfd8 D_6bfd8 retv ltac:(exact Hra1)
              | stepjr F_6c724 D_6c724 retv ltac:(exact Hra1)
              | stepjr F_6dcac D_6dcac retv ltac:(exact Hra1)
              | stepjr F_6c614 D_6c614 retv ltac:(exact Hra1)
              | stepjr F_6c704 D_6c704 retv ltac:(exact Hra1)
              | stepjr F_6bf08 D_6bf08 retv ltac:(exact Hra1) ];
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
