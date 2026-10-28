(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_TablStmt LbB_TablImg.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac rleaf_fin HR0 qtac :=
  idtac;
  lazymatch goal with
  | HR' : regs_ok _ _ ?R', Hms : CatSim.msteps _ _ _ |- _ =>
      eapply evt_of_msteps; [exact Hms|];
      let HF := fresh "HF" in
      assert (HF : rfull R') by (eapply (msteps_full _ _ _ Hms); rewrite HR0; apply rfull_mkR);
      let HRe := fresh "HRe" in
      readback HR' HF HR0 HRe;
      rewrite HRe; cbn [mem_denot];
      rewrite mkst_MS;
      step;
      apply evt_done;
      do 16 eexists;
      split; [reflexivity|];
      split; [apply munch_refl|]; split; [intros ? H_; exact H_|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
      qtac
  end.

Ltac b2w_norm :=
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
  rewrite ?or_b2w.

Ltac a0_b2w :=
  idtac;
  lazymatch goal with HR' : regs_ok _ _ ?R' |- _ =>
    let G := fresh "G10" in rreg HR' 10%bv G; rewrite G; b2w_norm end.

Ltac rl_start Ha0 R0 HR0 entry :=
  remember (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as R0 eqn:HR0;
  change (MS R0 ?F (Z_to_bv 64 entry) ?fc None ?m (seg_rom asegs))
    with (@PropExec.mkst (PropExec.mkFP F fc) R0 (Z_to_bv 64 entry) m (seg_rom asegs)).

Ltac bool_leaf_run entry rets :=
  idtac;
  lazymatch goal with Ha0 : ?a0 = Z_to_bv 64 ?x |- evt _ _ (MS (mkR ?ra ?sp ?gp ?tp ?t0 ?t1 ?t2 ?s0 ?s1 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7
                                                             ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?t3 ?t4 ?t5 ?t6) ?F _ ?fc None ?m _) =>
    let R0 := fresh "R0" in let HR0 := fresh "HR0" in
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R0 eqn:HR0;
    change (MS R0 F (Z_to_bv 64 entry) fc None m (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R0 (Z_to_bv 64 entry) m (seg_rom asegs));
    let E := fresh "E" in pose (E := Eseed R0 [Z_to_bv 64 x]);
    let HR := fresh "HR" in
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R0)
      by (apply regs_ok_srs; [apply regs_ok_seed|];
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; subst R0; cbn [getr mkR]; assumption);
    let HK := fresh "HK" in assert (HK : know_ok asegs E m []) by constructor;
    xtree HR HK 50%nat rets 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(rleaf_fin HR0 ltac:(idtac)) ltac:(br_kill)
  end.

Ltac rl_run_gen mode entry rets :=
  idtac;
  lazymatch goal with
  | MI : mem_inv asegs ?m, Ha0 : ?a0 = Z_to_bv 64 ?xv
    |- evt _ _ (MS (mkR ?ra ?sp ?gp ?tp ?t0 ?t1 ?t2 ?s0 ?s1 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7
                       ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?t3 ?t4 ?t5 ?t6) ?F _ ?fc None ?m _) =>
    let R0 := fresh "R0" in let HR0 := fresh "HR0" in
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R0 eqn:HR0;
    change (MS R0 F (Z_to_bv 64 entry) fc None m (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R0 (Z_to_bv 64 entry) m (seg_rom asegs));
    lazymatch mode with
    | None =>
        let E := fresh "E" in pose (E := Eseed R0 (@nil word));
        let HR := fresh "HR" in
        assert (HR : regs_ok E (srs sr_id [(10%bv, ELit xv)]) R0)
          by (apply regs_ok_srs; [apply regs_ok_seed|];
              repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; subst R0; cbn [getr mkR]; assumption);
        let HK := fresh "HK" in
        assert (HK : know_ok asegs E m [KImg 0x10000 0x91000]) by (constructor; [apply kimg_of_mem_inv; [exact MI | lia | lia] | constructor]);
        xtree HR HK 80%nat rets 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(rleaf_fin HR0 ltac:(idtac)) ltac:(br_kill)
    | Some (?lo, ?hi) =>
        let E := fresh "E" in pose (E := Eseed R0 [Z_to_bv 64 xv]);
        let HR := fresh "HR" in
        assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R0)
          by (apply regs_ok_srs; [apply regs_ok_seed|];
              repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; subst R0; cbn [getr mkR]; assumption);
        let HK := fresh "HK" in
        assert (HK : know_ok asegs E m [KRange (EVar 32) lo hi; KImg 0x10000 0x91000])
          by (constructor; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|];
              constructor; [apply kimg_of_mem_inv; [exact MI | lia | lia] | constructor]);
        xtree HR HK 80%nat rets 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(rleaf_fin HR0 ltac:(idtac)) ltac:(br_kill)
    end
  end.

Ltac bool_lit_post :=
  idtac;
  lazymatch goal with HR' : regs_ok _ _ ?R' |- _ =>
    let G := fresh "G10" in rreg HR' 10%bv G; rewrite G end;
  first [ exists false; split; [reflexivity | intros X; discriminate X]
        | exists true; split; [reflexivity | intros _; first [vm_compute; reflexivity | lia]] ].

Section Reg.
  Context {HCEIL : HeapCeil}.

  Definition FW_RET : Z := 0xfc838.

  Theorem fixword_okA : fixword_stmtA.
  Proof.
    intros [w e] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hw & Ha0 & He & Ha1).
    pose proof (sx32_range w Hw) as Hsw.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R0 eqn:HR0.
    change (MS R0 F (Z_to_bv 64 AT_FIXWORD) fc None m (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R0 (Z_to_bv 64 AT_FIXWORD) m (seg_rom asegs)).
    pose (E := Eseed R0 [Z_to_bv 64 (TablStmts.sx32 w); Z_to_bv 64 e]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R0).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; subst R0; cbn [getr mkR]; assumption. }
    assert (HK : know_ok asegs E m [KRange (EVar 33) 0 4294967295]).
    { constructor; [|constructor]. cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
    xtree HR HK 60%nat [FW_RET] 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(rleaf_fin HR0 ltac:(idtac)) ltac:(br_kill).
    -   exists w. split; [exact Hw|]. rreg HR' 10%bv G10. rewrite G10. reflexivity.
    -   destruct (fixword_swap w Hw) as (r & Hr & E1). exists r. split; [exact Hr|].
      rreg HR' 10%bv G10. rewrite G10. exact E1.
  Qed.

  Definition HE_RET : Z := 0xfc9a8.
  Theorem is_host_endian_okA : is_host_endian_stmtA.
  Proof.
    intros x ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hx & Ha0).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R0 eqn:HR0.
    change (MS R0 F (Z_to_bv 64 AT_IS_HOST_ENDIAN) fc None m (seg_rom asegs))
      with (@PropExec.mkst (PropExec.mkFP F fc) R0 (Z_to_bv 64 AT_IS_HOST_ENDIAN) m (seg_rom asegs)).
    pose (E := Eseed R0 [Z_to_bv 64 x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R0).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; subst R0; cbn [getr mkR]; assumption. }
    assert (HK : know_ok asegs E m []) by constructor.
    xtree HR HK 50%nat [HE_RET] 40%N (@nil bool) (@nil expr) ltac:(try sc_auto1) ltac:(rleaf_fin HR0 ltac:(idtac)) ltac:(br_kill).
    a0_b2w. exists (if t then 1 else 0). split; [destruct t; lia | reflexivity].
  Qed.

  Definition IEI_RET : Z := 0xfdd9c.
  Theorem is_ext_inst_okA : is_ext_inst_stmtA.
  Proof.
    intros x ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hx & Ha0).
    bool_leaf_run AT_IS_EXT_INST [IEI_RET].
    all: a0_b2w; lazymatch goal with |- exists b : bool, b2w ?X = _ /\ _ => exists X; split; [reflexivity | intros _; exact I] end.
  Qed.

  Definition NS_RET : Z := 0x100610.
  Theorem is_nonsemantic_okA : is_nonsemantic_stmtA.
  Proof.
    intros x ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hx & Ha0).
    bool_leaf_run AT_IS_NONSEMANTIC [NS_RET].
    all: a0_b2w; lazymatch goal with |- exists b : bool, b2w ?X = _ /\ _ => exists X; split; [reflexivity | intros _; exact I] end.
  Qed.

End Reg.
