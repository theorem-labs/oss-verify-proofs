(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import RegEqv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import MState Frame. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import RT_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootStep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxState AxSys AxModelRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Notation rr R k := (reg_get R (Z_to_bv 5 k)).

Definition canon_regs (R : bvmap 5 word) : bvmap 5 word :=
  mkR (rr R 1) (rr R 2) (rr R 3) (rr R 4) (rr R 5) (rr R 6) (rr R 7) (rr R 8) (rr R 9) (rr R 10) (rr R 11) (rr R 12) (rr R 13) (rr R 14)
      (rr R 15) (rr R 16) (rr R 17) (rr R 18) (rr R 19) (rr R 20) (rr R 21) (rr R 22) (rr R 23) (rr R 24) (rr R 25) (rr R 26) (rr R 27)
      (rr R 28) (rr R 29) (rr R 30) (rr R 31).

Lemma reg_cases (r : bv 5) : r <> 0%bv -> exists k, 1 <= k <= 31 /\ r = Z_to_bv 5 k.
Proof.
  intros Hr. exists (bv_unsigned r). split.
  - pose proof (bv_unsigned_in_range 5 r) as Hb. unfold bv_modulus in Hb. cbn in Hb.
    destruct (Z.eq_dec (bv_unsigned r) 0) as [E0|E0]; [|lia]. exfalso. apply Hr. apply bv_eq. rewrite E0. reflexivity.
  - apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma canon_regs_eqv (R : bvmap 5 word) : regs_eqv (canon_regs R) R.
Proof.
  intros r Hr. destruct (reg_cases r Hr) as (k & Hk & ->).
  assert (Hk' : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12
                \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23
                \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
  unfold canon_regs.
  repeat (destruct Hk' as [-> | Hk']); try (subst k); reflexivity.
Qed.

Definition canon_ms (ms : machine_state) : machine_state :=
  {| ms_regs := canon_regs (ms_regs ms); ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

Lemma canon_cfg_eqv (ms : machine_state) (model : Model) : cfg_eqv (mkCfg (canon_ms ms) model) (mkCfg ms model).
Proof. split; [|reflexivity]. cbn [cfg_ms]. repeat split; cbn; try reflexivity. apply canon_regs_eqv. Qed.

Section Regs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R ctasegs amodel (MR ctasegs fs0 ρ) LIM ρ B (mkCfg ms model).

(* [comment removed for export] *)
Theorem canon_entry (main_pc : Z) (A : list (Z * Z)) :
  w_eqb (a_pc B) (wofZ main_pc) = true -> 0 <= main_pc < 2 ^ 64 -> a_resv B = RNone ->
  let Rg := ms_regs ms in
  restrict (RzCPS.HID A model) (canon_ms ms)
  = entry_st (rr Rg 1) (rr Rg 2) (rr Rg 3) (rr Rg 4) (rr Rg 5) (rr Rg 6) (rr Rg 7) (rr Rg 8) (rr Rg 9) (rr Rg 10) (rr Rg 11) (rr Rg 12)
             (rr Rg 13) (rr Rg 14) (rr Rg 15) (rr Rg 16) (rr Rg 17) (rr Rg 18) (rr Rg 19) (rr Rg 20) (rr Rg 21) (rr Rg 22) (rr Rg 23)
             (rr Rg 24) (rr Rg 25) (rr Rg 26) (rr Rg 27) (rr Rg 28) (rr Rg 29) (rr Rg 30) (rr Rg 31)
             (ms_fregs ms) (ms_fcsr ms) main_pc (mrestrict (RzCPS.HID A model) (ms_mem ms)).
Proof.
  intros Hpc Hpr Hrv. cbv zeta.
  pose proof (r_pc _ _ _ _ _ _ _ HR) as Epc. pose proof (r_svc _ _ _ _ _ _ _ HR) as Esvc. pose proof (r_resv _ _ _ _ _ _ _ HR) as Ersv.
  pose proof (r_rom _ _ _ _ _ _ _ HR) as Erom. cbn [cfg_ms] in *. rewrite Hrv in Ersv. cbn [RResv] in Ersv.
  rewrite w_eqb_spec in Hpc. apply Z.eqb_eq in Hpc. apply wZ_inj in Hpc.
  unfold restrict, canon_ms, entry_st, MS. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite Epc, Esvc, Ersv, Erom, Hpc. unfold wbv. rewrite wZ_wofZ, Z.mod_small by (unfold FastWord.two64; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition reg_lit (r : Z) (v : Z) : bool := match aget (a_regs B) (of_Z r) with XL w => wZ w =? v | _ => false end.
Definition reg_form (r : Z) (f : lin) : bool :=
  match aget (a_regs B) (of_Z r) with
  | XS ts o => teqb ts (snd f) &&& (wZ o =? fst f mod 18446744073709551616)
  | _ => false
  end.

Lemma reg_rel (r : Z) : 0 < r < 32 -> xv_val ρ (aget (a_regs B) (of_Z r)) (rr (ms_regs ms) r).
Proof.
  intros Hr. pose proof (r_regs _ _ _ _ _ _ _ HR (Z_to_bv 5 r)) as H. cbn [cfg_ms] in H.
  assert (Eu : bv_unsigned (Z_to_bv 5 r) = r) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 5) with 32; lia).
  unfold ri in H. rewrite Eu in H. unfold rg in H.
  replace (is_x0 (Z_to_bv 5 r)) with false in H; [exact H|]. symmetry. unfold is_x0. rewrite Eu. apply Z.eqb_neq. lia.
Qed.

Lemma reg_lit_sound (r v : Z) : 0 < r < 32 -> reg_lit r v = true -> rr (ms_regs ms) r = Z_to_bv 64 v.
Proof.
  intros Hr H. pose proof (reg_rel r Hr) as X. unfold reg_lit in H. destruct (aget (a_regs B) (of_Z r)) as [w| | | | |]; try discriminate H.
  apply Z.eqb_eq in H. cbn [xv_val] in X. apply bv_eq. rewrite X, H. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (wZ_range w). change (bv_modulus 64) with (2 ^ 64). unfold FastWord.two64 in *. lia.
Qed.

Lemma reg_form_sound (r : Z) (f : lin) : 0 < r < 32 -> reg_form r f = true -> 0 <= leval ρ f < 2 ^ 64 ->
  rr (ms_regs ms) r = Z_to_bv 64 (leval ρ f).
Proof.
  intros Hr H Hf. pose proof (reg_rel r Hr) as X. unfold reg_form in H. destruct (aget (a_regs B) (of_Z r)) as [|ts o| | | |]; try discriminate H.
  apply land_true in H as [H1 H2]. apply teqb_eq in H1. apply Z.eqb_eq in H2. cbn [xv_val] in X. apply bv_eq. rewrite X.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold smod. rewrite H2. unfold FastWord.two64. change 18446744073709551616 with (2 ^ 64). rewrite Zplus_mod_idemp_r.
  destruct f as [c tf]. cbn [fst snd] in *. subst ts. unfold leval in *. cbn [fst snd] in *. rewrite Z.mod_small by lia. lia.
Qed.

End Regs.
