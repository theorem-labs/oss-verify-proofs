(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BAgentLib BFrame BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BLibKnowFrame BSymAux BHoare BainWalk_defs BsPrintfFirst.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import BPropExec.
Import SX2. Import SX2S.

Record mv := MV { v_sp0 : word; v_tid : word; v_pp : word; v_A : word; v_len : word; v_cap : word; v_A2 : word;
                  v_n : word; v_b8 : word; v_b9 : word; v_b10 : word; v_b11 : word; v_b0 : word; v_b1 : word }.

Definition mvals (v : mv) (regs : bvmap 5 word) : list word :=
  [v_sp0 v; v_tid v; v_pp v; v_A v; v_len v; v_cap v; v_A2 v; v_n v; v_b8 v; v_b9 v; v_b10 v; v_b11 v; v_b0 v; v_b1 v]
  ++ junk_vals regs.

Definition MENV (v : mv) (regs : bvmap 5 word) : env := Env (vals_ev (mvals v regs)) (blobs_ev []).

Lemma ev_junk : forall v regs i, (i < 32)%nat -> ev (MENV v regs) (14 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros v regs i Hi. unfold MENV, mvals. cbn [ev]. unfold vals_ev.
  change (14 + i)%nat with (length [v_sp0 v; v_tid v; v_pp v; v_A v; v_len v; v_cap v; v_A2 v; v_n v; v_b8 v; v_b9 v; v_b10 v; v_b11 v; v_b0 v; v_b1 v] + i)%nat.
  rewrite app_nth2_plus. unfold junk_vals.
  rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
Qed.

Lemma ev0 : forall v regs, ev (MENV v regs) 0 = v_sp0 v. Proof. reflexivity. Qed.

Ltac mreg_case :=
  lazymatch goal with
  | |- getr ?R ?r = edenot ?E ?e =>
      first [ apply getr_zero
            | lazymatch e with
              | EVar ?n => change (edenot E (EVar n)) with (ev E n);
                           first [ rewrite (ev_junk _ _ (n - 14)) by lia; reflexivity
                                 | cbn [ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1];
                                   first [reflexivity | assumption | symmetry; assumption] ]
              | ELit _ => cbn [edenot]; first [assumption | symmetry; assumption]
              | spx ?k => unfold spx; mreg_case
              | EAlu ALU_ADD (EVar 0) (ELit ?k) =>
                  cbn [edenot]; rewrite alu_add;
                  cbn [ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1];
                  lazymatch goal with H : getr R r = _ |- _ => rewrite H end;
                  unfold v_add; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, ?Zplus_mod_idemp_r, ?Zplus_mod_idemp_l;
                  f_equal; lia
              end ]
  end.

Ltac prove_regs_ok :=
  lazymatch goal with |- regs_ok _ ?sr _ => unfold sr end;
  apply regs_ok_by_idx; intros i Hi;
  destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
  cbn [nth allregs32]; mreg_case.

Definition regL : list sregion := [(SA (EVar 0) (-128 - MSTK), MSTK)]%Z.

Definition regL_w (sp0 : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 128 - MSTK), MSTK)].

Lemma regL_denot : forall v regs, (0x7fff80000000 <= bv_unsigned (v_sp0 v))%Z ->
  map (rdenot (MENV v regs)) regL = regL_w (v_sp0 v).
Proof.
  intros v regs Hlo. unfold regL, regL_w, rdenot, estart, MSTK. cbn [map fst snd a_base a_off edenot].
  try rewrite ev0. repeat f_equal; lia.
Qed.

Lemma regL_flat : forall v regs, (0x7fff80000000 <= bv_unsigned (v_sp0 v) <= 0x800000000000)%Z ->
  regions_flat (MENV v regs) regL.
Proof.
  intros v regs H r Hr. unfold regL, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
  unfold flat, estart; cbn [fst snd a_base a_off edenot]. try rewrite ev0. lia.
Qed.

Ltac scs_nil :=
  lazymatch goal with
  | |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l'
  | |- Forall _ ?l => let l' := eval vm_compute in l in change l with l'
  end; apply Forall_nil.
