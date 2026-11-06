(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module LibAtomic.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition mkst_r (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : word)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := Some r; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

End FPGen1.


Ltac atomic_pipeline Hfetch Hecall Hdecode :=
  unfold mkst_r;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Ltac norm_pc_r :=
  try lazymatch goal with
      | |- CatExec.CatSim.msteps _ (mkst_r _ ?p _ _ _) _ => wlit p
      end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.


Lemma step_lr_w : forall segs regs pc mem rom w aq rl rd rs bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AW aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
                    (v_addi pc 4) mem rom (getr regs rs)).
Proof.
  intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_lr_d : forall segs regs pc mem rom w aq rl rd rs bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AD aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod 8 = 0)%Z ->
  rdn segs mem (getr regs rs) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd v)
                    (v_addi pc 4) mem rom (getr regs rs)).
Proof.
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
Lemma step_sc_w_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
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
Lemma step_sc_d_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AD aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
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




Lemma step_branch_ft_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.


Lemma step_bne_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.



(* [comment removed for export] *)
Lemma step_opimm_r : forall segs regs pc mem rom r w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs
                     else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                    (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w op rd rs imm Hfetch Hecall Hdecode.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_op_r : forall segs regs pc mem rom r w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs
                     else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                    (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w op rd rs1 rs2 Hfetch Hecall Hdecode.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.
End FPGen2.
End LibAtomic.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Ltac gres :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive rlp : Type := RLP (r : reg) (v : word).

Fixpoint rl_build (acc : list rlp) (R : bvmap 5 word) : bvmap 5 word :=
  match acc with
  | nil => R
  | cons (RLP r v) t => rl_build t (regupd R r v)
  end.

Fixpoint rl_find (r' : reg) (acc : list rlp) (res : option word) : option word :=
  match acc with
  | nil => res
  | cons (RLP r v) t => rl_find r' t (if bv_eqb r' r then Some v else res)
  end.

Lemma rl_bv_eqb_false_neq : forall {n} (a b : bv n), bv_eqb a b = false -> a <> b.
Proof. intros n a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.

Lemma rl_bv_eqb_true_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma rl_gen : forall (r' : reg) acc R res w, bv_eqb r' 0 = false ->
  getr R r' = match res with Some v => v | None => w end ->
  getr (rl_build acc R) r' = match rl_find r' acc res with Some v => v | None => w end.
Proof.
  intros r' acc. induction acc as [|[r v] t IH]; intros R res w H0 HR; cbn [rl_build rl_find]; [exact HR|].
  apply IH; [exact H0|].
  destruct (bv_eqb r' r) eqn:E.
  - apply rl_bv_eqb_true_eq in E. subst r. apply getr_same. apply rl_bv_eqb_false_neq. exact H0.
  - rewrite getr_other by (apply rl_bv_eqb_false_neq; exact E). exact HR.
Qed.

Lemma rl_some : forall (r' : reg) acc R v, bv_eqb r' 0 = false -> rl_find r' acc None = Some v ->
  getr (rl_build acc R) r' = v.
Proof. intros r' acc R v H0 HF. pose proof (rl_gen r' acc R None (getr R r') H0 eq_refl) as G. rewrite HF in G. exact G. Qed.

Lemma rl_none : forall (r' : reg) acc R, bv_eqb r' 0 = false -> rl_find r' acc None = None ->
  getr (rl_build acc R) r' = getr R r'.
Proof. intros r' acc R H0 HF. pose proof (rl_gen r' acc R None (getr R r') H0 eq_refl) as G. rewrite HF in G. exact G. Qed.

(* [comment removed for export] *)
Ltac rl_eqb r' r :=
  match constr:(Set) with
  | _ => lazymatch r' with
         | @BV _ ?z' _ =>
             lazymatch r with
             | @BV _ ?z _ =>
                 let _ := match goal with _ => is_Z_lit z'; is_Z_lit z end in
                 match constr:(Set) with
                 | _ => let _ := match goal with _ => constr_eq z z' end in constr:(true)
                 | _ => constr:(false)
                 end
             end
         end
  | _ => eval cbv in (bv_eqb r' r)
  end.

(* [comment removed for export] *)
Ltac rl_walk C r' acc :=
  lazymatch C with
  | regupd ?R0 ?r ?v =>
      let b := rl_eqb r' r in
      lazymatch b with
      | true => constr:(pair (pair (cons (RLP r v) acc) R0) (Some v))
      | false => rl_walk R0 r' constr:(cons (RLP r v) acc)
      | _ => constr:(pair (pair acc C) (@None word))
      end
  | _ => constr:(pair (pair acc C) (@None word))
  end.

Ltac gres_fast1 :=
  match goal with
  | |- context [getr (regupd ?R0 ?r ?v) ?r'] =>
      let z := rl_eqb r' (0%bv : reg) in
      let C := constr:(regupd R0 r v) in
      lazymatch z with
      | true => rewrite (getr_zero C)
      | false =>
      let res := rl_walk C r' constr:(@nil rlp) in
      lazymatch res with
      | pair (pair ?acc ?Rr) (Some ?w) =>
          change (getr C r') with (getr (rl_build acc Rr) r');
          rewrite (rl_some r' acc Rr w (@eq_refl bool false) (@eq_refl (option word) (Some w)))
      | pair (pair nil _) None => fail
      | pair (pair ?acc ?Rr) None =>
          change (getr C r') with (getr (rl_build acc Rr) r');
          rewrite (rl_none r' acc Rr (@eq_refl bool false) (@eq_refl (option word) None))
      end
      end
  end.

Ltac gres_fast :=
  repeat gres_fast1;
  lazymatch goal with
  | |- context [getr (regupd _ _ _) _] =>
      repeat first [ rewrite getr_same by reg_neq_tac
                   | rewrite getr_other by reg_neq_tac ]
  | |- _ => idtac
  end;
  (* [comment removed for export] *)
  lazymatch goal with
  | |- context [getr _ (@BV _ Z0 _)] => rewrite ?getr_zero
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac is_plain_var x :=
  is_var x; tryif (let _ := eval unfold x in x in idtac) then fail else idtac.

Ltac check_closed_term_fast p :=
  (* [comment removed for export] *)
  tryif match p with context [?x] => is_plain_var x end
  then fail 0 "check_closed_term: the term mentions a context variable"
  else
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term: the term contains an evar"
  else tryif match p' with context [?x] => is_var x end
  then fail 0 "check_closed_term: the term mentions a context variable"
  else idtac.

Ltac vnorm_rw0 :=
  lazymatch goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | |- _ => idtac end;
  lazymatch goal with |- context [v_add _ (Z_to_bv 64 0%Z)] => rewrite ?v_add_0_r | |- _ => idtac end;
  lazymatch goal with |- context [v_add (Z_to_bv 64 0%Z) _] => rewrite ?v_add_0_l | |- _ => idtac end.
Ltac vnorm_fast := gres; imm_norm; vnorm_rw0; vals_lit.
Ltac step_simpl_fast :=
  reduce_bv_eqb_ifs;
  lazymatch goal with |- context [skipn O _] => rewrite ?skipn_O | |- _ => idtac end;
  norm_pc.

(* [comment removed for export] *)
Ltac gres_orig :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.
Ltac check_closed_term_orig p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term:" p "contains an evar"
  else tryif match goal with
             | H : _ |- _ => lazymatch p' with context [H] => idtac end
             end
  then fail 0 "check_closed_term:" p "mentions a context variable"
  else idtac.
Ltac vnorm_orig := gres; imm_norm; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; vals_lit.
Ltac step_simpl_orig := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pc.

Ltac gres ::= gres_fast.
Ltac check_closed_term ::= check_closed_term_fast.
Ltac vnorm ::= vnorm_fast.
Ltac step_simpl ::= step_simpl_fast.
