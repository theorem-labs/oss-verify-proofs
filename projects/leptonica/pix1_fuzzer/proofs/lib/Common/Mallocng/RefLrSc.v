(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec ShapeAlg PureModel.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Section LrSc.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition mkst_r (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (a : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := Some a; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma mkst_r_svc : forall regs pc mem rom a, ms_svc_pending (mkst_r regs pc mem rom a) = None.
Proof. reflexivity. Qed.

Ltac red_eff :=
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     access_value accessed_ranges
     ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst mkst_r].

Ltac step_pipeline_r Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst mkst_r];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  red_eff;
  rewrite ?bv_eqb0_is_x0.

Lemma step_lrw : forall segs regs pc mem rom w rd rs (a : word) bs (v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AW true true rd rs, 4%Z) ->
  bv_eqb rd 0 = false ->
  getr regs rs = a ->
  (bv_unsigned a mod 4 = 0)%Z ->
  rdn segs mem a 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst_r (regupd regs rd (v_lw v)) (v_addi pc 4) mem rom a).
Proof.
  intros segs regs pc mem rom w rd rs a bs v Hfetch Hecall Hdecode Hrd Ha Hal Hread Hv. subst a.
  step_pipeline_r Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. rewrite bv_eqb0_is_x0 in Hrd.
  unfold getr in Hread, Hal; rewrite ?bv_eqb0_is_x0 in Hread, Hal.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal. cbn [Z.eqb negb]. red_eff.
  rewrite ov_rdn, Hread. red_eff.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  rewrite Hrd. reflexivity.
Qed.

Lemma step_bne_ft_r : forall segs regs pc mem rom ra w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  getr regs rs1 = getr regs rs2 ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom ra) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom ra).
Proof.
  intros segs regs pc mem rom ra w rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  step_pipeline_r Hfetch Hecall Hdecode.
  cbn [branch_taken]. unfold getr in Hc. rewrite ?bv_eqb0_is_x0 in Hc. rewrite Hc.
  unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. rewrite b_npc4. reflexivity.
Qed.

Lemma step_scw_ok : forall segs regs pc mem rom w rd rs1 rs2 (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AW true true rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  getr regs rs1 = a -> getr regs rs2 = v ->
  (bv_unsigned a mod 4 = 0)%Z ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom a) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
               (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 a v Hfetch Hecall Hdecode Hrd Ha Hv Hal Hok. subst a v.
  step_pipeline_r Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. rewrite bv_eqb0_is_x0 in Hrd.
  unfold getr in Hok, Hal; rewrite ?bv_eqb0_is_x0 in Hok, Hal.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal. cbn [Z.eqb negb]. red_eff.
  rewrite Z.eqb_refl. red_eff.
  rewrite Hok. red_eff.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  rewrite Hrd. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_step_r : forall segs ms md ms' T,
  md_pure md -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes segs (mkCfg ms' md) T -> realizes segs (mkCfg ms md) T.
Proof.
  intros segs ms md ms' T [Hh Hl Hm] Hsvc Hs H. eapply rz_step; eassumption.
Qed.

End LrSc.
