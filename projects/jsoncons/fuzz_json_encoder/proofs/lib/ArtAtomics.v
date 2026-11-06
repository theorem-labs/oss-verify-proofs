(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma art_mod32_helper : forall a b : Z,
  ((a + b mod 4294967296) mod 4294967296 = ((a + b) mod (4294967296 * 4294967296)) mod 4294967296)%Z.
Proof.
  intros a b. rewrite Z.add_mod_idemp_r by lia.
  set (x := (a + b)%Z). set (MM := (4294967296 * 4294967296)%Z).
  rewrite (Z.div_mod x MM) at 1 by lia.
  replace (MM * (x / MM))%Z with ((4294967296 * (x / MM)) * 4294967296)%Z by (unfold MM; lia).
  rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_step_amoadd_d_x0 : forall segs regs pc mem rom w aq rl (rs1 rs2 : reg) (a v old : word) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AD aq rl 0 rs1 rs2, 4%Z) ->
  getr regs rs1 = a -> (bv_unsigned a mod 8 = 0)%Z ->
  rdn segs mem a 8%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned old ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 (v_add old v))) rom).
Proof.
  intros segs regs pc mem rom w aq rl rs1 rs2 a v old bs Hf He Hd Ha Hal Hread Hv Hrs2 Hok.
  step_pipeline Hf He Hd.
  unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2.
  rewrite Ha, Hrs2.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal. rewrite Z.eqb_refl.
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkst].
  assert (Hz : bv_extract 0 64 old = old).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz.
  rewrite Hok; cbv beta iota.
  replace (bv_unsigned (0%bv : bv 5) =? 0)%Z with true by reflexivity. cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?b_npc4, <- alu_add.
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition mkstr (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : option word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := None; ms_resv := r; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma mkstr_none : forall regs pc mem rom, mkstr regs pc mem rom None = mkst regs pc mem rom.
Proof. reflexivity. Qed.

#[local] Ltac step_pipeline_r Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkstr];
  rewrite Hfetch; cbv beta iota;
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses;
  rewrite Hecall; cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Lemma art_step_op_r : forall segs regs pc mem rom w op rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) =
  MachineOk (mkstr (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 r Hf He Hd.
  step_pipeline_r Hf He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); destruct (is_x0 rs2); destruct (is_x0 rd); cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.

Lemma art_step_and_r : forall segs regs pc mem rom w rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_and (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof. intros * Hf He Hd Hrd. rewrite (art_step_op_r _ _ _ _ _ _ _ _ _ _ r Hf He Hd), Hrd, alu_and. reflexivity. Qed.
Lemma art_step_xor_r : forall segs regs pc mem rom w rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_XOR rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_xor (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof. intros * Hf He Hd Hrd. rewrite (art_step_op_r _ _ _ _ _ _ _ _ _ _ r Hf He Hd), Hrd, alu_xor. reflexivity. Qed.
Lemma art_step_or_r : forall segs regs pc mem rom w rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_or (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof. intros * Hf He Hd Hrd. rewrite (art_step_op_r _ _ _ _ _ _ _ _ _ _ r Hf He Hd), Hrd, alu_or. reflexivity. Qed.

(* [comment removed for export] *)
Lemma art_step_branch_tk_r : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13) r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm r Hfetch Hecall Hdecode Hc.
  step_pipeline_r Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2); cbv beta iota; rewrite Hc; cbv beta iota; rewrite b_addsext; reflexivity.
Qed.
Lemma art_step_branch_ft_r : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13) r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm r Hfetch Hecall Hdecode Hc.
  step_pipeline_r Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2); cbv beta iota; rewrite Hc; cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_lr_w : forall segs regs pc mem rom w aq rl rd rs1 a bs v r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AW aq rl rd rs1, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn segs mem a 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_lw v)) (v_addi pc 4) mem rom (Some a)).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 a bs v r Hf He Hd Hrd Ha Hal Hread Hv.
  step_pipeline_r Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha. rewrite Ha.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl.
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr].
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, ?b_npc4.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  reflexivity.
Qed.

#[local] Ltac amo_unfold :=
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr mkst].

(* [comment removed for export] *)
Lemma art_step_lr_d : forall segs regs pc mem rom w aq rl rd rs1 a bs v r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AD aq rl rd rs1, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 8 = 0)%Z ->
  rdn segs mem a 8%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd v) (v_addi pc 4) mem rom (Some a)).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 a bs v r Hf He Hd Hrd Ha Hal Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  step_pipeline_r Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha. rewrite Ha.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl. amo_unfold.
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, ?b_npc4.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_sc_w_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 a v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 4 = 0)%Z -> getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkstr regs pc mem rom (Some a)) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 a v Hf He Hd Hrd Ha Hal Hv Hok.
  step_pipeline_r Hf He Hd.
  unfold getr in Ha, Hv; rewrite ?bv_eqb0_is_x0 in Ha, Hv. rewrite Ha, Hv.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, !Z.eqb_refl. amo_unfold.
  rewrite Hok; cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?store_bytes_low32, ?b_npc4.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_sc_d_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 a v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AD aq rl rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 8 = 0)%Z -> getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkstr regs pc mem rom (Some a)) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 a v Hf He Hd Hrd Ha Hal Hv Hok.
  step_pipeline_r Hf He Hd.
  unfold getr in Ha, Hv; rewrite ?bv_eqb0_is_x0 in Ha, Hv. rewrite Ha, Hv.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, !Z.eqb_refl. amo_unfold.
  rewrite Hok; cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?b_npc4.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_amoadd_w_x0 : forall segs regs pc mem rom w aq rl (rs1 rs2 : reg) (a v old : word) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AW aq rl 0 rs1 rs2, 4%Z) ->
  getr regs rs1 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn segs mem a 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned old -> (bv_unsigned old < 2 ^ 32)%Z ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 (v_add old v))) rom).
Proof.
  intros segs regs pc mem rom w aq rl rs1 rs2 a v old bs Hf He Hd Ha Hal Hread Hv Hold Hrs2 Hok.
  step_pipeline Hf He Hd.
  unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2. rewrite Ha, Hrs2.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl. amo_unfold.
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv).
  rewrite Hok; cbv beta iota.
  replace (bv_unsigned (0%bv : bv 5) =? 0)%Z with true by reflexivity. cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?b_npc4.
  assert (Hb : Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 old) (low32 v))) = word_to_le_bytes 4 (v_add old v)).
  { cbn [amo_val]. unfold low32, word_to_le_bytes, v_add.
    rewrite bv_add_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r, Z_to_bv_unsigned.
    rewrite (bv_wrap_small 32 (bv_unsigned old)) by (pose proof (u64_range old); change (bv_modulus 32) with 4294967296%Z; lia).
    rewrite Z_to_le_bytes_wrap by (cbn; lia).
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_wrap 64 _)) by (cbn; lia).
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_unsigned old + bv_wrap 32 (bv_unsigned v))) by (cbn; lia).
    f_equal. unfold bv_wrap.
    change (bv_modulus 64) with (4294967296 * 4294967296)%Z. change (bv_modulus 32) with 4294967296%Z.
    apply art_mod32_helper. }
  rewrite Hb. reflexivity.
Qed.
End FPX.
