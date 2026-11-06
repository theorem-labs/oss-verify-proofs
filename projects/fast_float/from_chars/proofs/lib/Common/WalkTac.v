(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare.
Import ListNotations.

Module LibAtomic.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec SeqExec StepTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition mkst_r (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : word)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := Some r; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

#[using="Type"] Lemma mkst_r_svc : forall regs pc mem rom r, ms_svc_pending (mkst_r regs pc mem rom r) = None.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

End WithFP1.

Ltac atomic_pipeline Hfetch Hecall Hdecode :=
  unfold mkst_r;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Ltac norm_pc_r :=
  try lazymatch goal with
      | |- CatSim.msteps _ (mkst_r _ ?p _ _ _) _ => wlit p
      end.

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma step_lr_w : forall segs regs pc mem rom w aq rl rd rs bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AW aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
                    (v_addi pc 4) mem rom (getr regs rs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

#[using="Type"] Lemma step_lr_d : forall segs regs pc mem rom w aq rl rd rs bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AD aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod 8 = 0)%Z ->
  rdn segs mem (getr regs rs) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd v)
                    (v_addi pc 4) mem rom (getr regs rs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma step_sc_w_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  subst r. rewrite Z.eqb_refl. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_sc_d_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AD aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  subst r. rewrite Z.eqb_refl. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  unfold regupd, word_to_le_bytes.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_sc_fail : forall segs regs pc mem rom w wd aq rl rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 1)) (v_addi pc 4) mem rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom w wd aq rl rd rs1 rs2 Hfetch Hecall Hdecode Hal.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  unfold amo_bytes in Hal. rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite b_npc4. unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_sc_mismatch : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  (bv_unsigned r =? bv_unsigned (getr regs rs1))%Z = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 1)) (v_addi pc 4) mem rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hne.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  unfold amo_bytes in Hal. rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite Hne. cbv beta iota.
  rewrite b_npc4. unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma step_branch_tk_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

#[using="Type"] Lemma step_branch_ft_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_bne_tk_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

#[using="Type"] Lemma step_bne_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

#[using="Type"] Lemma step_beq_tk_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_r segs regs pc mem rom r w BC_EQ rs1 rs2 imm Hf He Hd). exact Hc.
Qed.

#[using="Type"] Lemma step_beq_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_r segs regs pc mem rom r w BC_EQ rs1 rs2 imm Hf He Hd). exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_opimm_r : forall segs regs pc mem rom r w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs
                     else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                    (v_addi pc 4) mem rom r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom r w op rd rs imm Hfetch Hecall Hdecode.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_op_r : forall segs regs pc mem rom r w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs
                     else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                    (v_addi pc 4) mem rom r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom r w op rd rs1 rs2 Hfetch Hecall Hdecode.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

End WithFP2.
End LibAtomic.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require GresFast.  (* [comment removed for export] *)
Ltac gres := GresFast.gres_fast.

(* [comment removed for export] *)
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Ltac is_pos_lit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_pos_lit q
  | xI ?q => is_pos_lit q
  end.
Ltac is_Z_lit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => is_pos_lit p
  | Zneg ?p => is_pos_lit p
  end.

(* [comment removed for export] *)
Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

(* [comment removed for export] *)
Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

Ltac vnorm := gres; imm_norm; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; vals_lit.

(* [comment removed for export] *)
Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

(* [comment removed for export] *)
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

(* [comment removed for export] *)
Ltac stepb_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

Ltac stepb_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

(* [comment removed for export] *)
Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

(* [comment removed for export] *)
Ltac stepsd F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepld F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
