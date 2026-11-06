(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector bitvector.tactics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxMemSound FxValSound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ireg_to_Z : forall r : reg, to_Z (ireg r) = bv_unsigned r.
Proof.
  intros r. unfold ireg. rewrite Uint63.of_Z_spec.
  pose proof (bv_unsigned_in_range _ r) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 5) with 32 in H.
  apply Z.mod_small. change wB with (2^63). lia.
Qed.

Lemma ireg_eqb : forall r r' : reg, (ireg r =? ireg r')%uint63 = bv_eqb r r'.
Proof.
  intros r r'. unfold bv_eqb.
  destruct (Z.eqb_spec (bv_unsigned r) (bv_unsigned r')) as [E|E].
  - apply Uint63.eqb_spec. apply Uint63.to_Z_inj. rewrite !ireg_to_Z. exact E.
  - destruct (ireg r =? ireg r')%uint63 eqn:E'; [|reflexivity].
    apply Uint63.eqb_spec in E'. apply (f_equal to_Z) in E'. rewrite !ireg_to_Z in E'. contradiction.
Qed.

Lemma ireg_is0 : forall r : reg, (ireg r =? 0)%uint63 = is_x0 r.
Proof.
  intros r. unfold is_x0.
  destruct (Z.eqb_spec (bv_unsigned r) 0) as [E|E].
  - apply Uint63.eqb_spec. apply Uint63.to_Z_inj. rewrite ireg_to_Z. exact E.
  - destruct (ireg r =? 0)%uint63 eqn:E'; [|reflexivity].
    apply Uint63.eqb_spec in E'. apply (f_equal to_Z) in E'. rewrite ireg_to_Z in E'. contradiction.
Qed.

(* [comment removed for export] *)
Lemma sem_rget_rset : forall rd v c r,
  Sem.rget (Sem.rset rd v c) r = if is_x0 r then w0 else if bv_eqb r rd then v else Sem.rget c r.
Proof.
  intros rd v c r. unfold Sem.rget, Sem.rset.
  destruct (is_x0 r) eqn:Er; [destruct (is_x0 rd); reflexivity|].
  destruct (is_x0 rd) eqn:Erd.
  - destruct (bv_eqb r rd) eqn:E; [|reflexivity].
    unfold bv_eqb in E. apply Z.eqb_eq in E. unfold is_x0 in *. rewrite E in Er. congruence.
  - cbn [with_regs c_regs]. unfold reg_get.
    destruct (bv_eqb r rd) eqn:E.
    + unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst r. rewrite bvmap_get_set_same. reflexivity.
    + rewrite bvmap_get_set_other; [reflexivity|]. intros ->. unfold bv_eqb in E. rewrite Z.eqb_refl in E. discriminate.
Qed.

Lemma sem_rget_with_pc : forall p c r, Sem.rget (with_pc p c) r = Sem.rget c r.
Proof. reflexivity. Qed.
Lemma sem_rget_with_resv : forall p c r, Sem.rget (with_resv p c) r = Sem.rget c r.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fx_rget_rset : forall F rd v npc r,
  FxState.rget (FxState.rset F rd v npc) r =
  if (r =? 0)%uint63 then fv0 else if (r =? rd)%uint63 then v else FxState.rget F r.
Proof.
  intros F rd v npc r. unfold FxState.rget, FxState.rset. cbn [f_regs].
  destruct (r =? 0)%uint63 eqn:Er; [reflexivity|].
  destruct (rd =? 0)%uint63 eqn:Erd.
  - apply Uint63.eqb_spec in Erd. subst rd. rewrite Er. reflexivity.
  - destruct (r =? rd)%uint63 eqn:E.
    + apply Uint63.eqb_spec in E. subst r. rewrite iget_iset_same. reflexivity.
    + rewrite iget_iset_other; [reflexivity|]. intros ->. rewrite Uint63.eqb_refl in E. discriminate.
Qed.

Section Step.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.

Local Abbreviation Rr := (R segs IM rho).
Local Abbreviation dvr := (dv rho).

Lemma core_of_ms_of : forall ms c m, core_of (ms_of ms c m) = c.
Proof. intros ms [] m. reflexivity. Qed.

Lemma R_intro_step : forall (ms : machine_state) F' c' m',
  c_pc c' = Z_to_bv 64 (to_Z (f_pc F')) ->
  (forall r, Sem.rget c' r = dvr (FxState.rget F' (ireg r))) ->
  c_resv c' = option_map dvr (f_resv F') ->
  mem_ok segs IM rho (f_mem F') m' ->
  Rr F' (ms_of ms c' m').
Proof.
  intros ms F' c' m' Hpc Hr Hres Hm. constructor.
  - exact Hpc.
  - intros r. rewrite core_of_ms_of. apply Hr.
  - reflexivity.
  - exact Hres.
  - exact Hm.
Qed.

Lemma R_regs_ok : forall F ms, Rr F ms -> regs_ok rho (f_mem F).
Proof. intros F ms HR t rg Ht. exact (proj1 (proj1 (R_mem _ _ _ _ _ HR) t rg Ht)). Qed.

(* [comment removed for export] *)
Lemma regs_after_rset : forall F ms rd w v npc c,
  Rr F ms -> dvr v = w ->
  (forall r, Sem.rget c r = Sem.rget (core_of ms) r) ->
  forall r, Sem.rget (Sem.rset rd w c) r = dvr (FxState.rget (FxState.rset F (ireg rd) v npc) (ireg r)).
Proof.
  intros F ms rd w v npc c HR Hv Hc r.
  rewrite sem_rget_rset, fx_rget_rset, ireg_is0, ireg_eqb.
  destruct (is_x0 r); [symmetry; apply dv_fv0; exact Hrho0|].
  destruct (bv_eqb r rd); [symmetry; exact Hv|].
  rewrite Hc. apply (R_regs _ _ _ _ _ HR).
Qed.

(* [comment removed for export] *)
Lemma pc_plus4 : forall pc : int,
  to_Z pc < pc_bound - 4 ->
  bv_add (Z_to_bv 64 (to_Z pc)) (Z_to_bv 64 4) = Z_to_bv 64 (to_Z (pc + 4)%uint63).
Proof.
  intros pc H. unfold pc_bound in H. pose proof (Uint63.to_Z_bounded pc) as Hb.
  rewrite Uint63.add_spec. change (to_Z 4) with 4. rewrite Z.mod_small by (change wB with (2^63); lia).
  apply bv_eq. rewrite bv_add_unsigned.
  rewrite !Z_to_bv_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia.
Qed.

Lemma pc_of_word_sound : forall w t, pc_of_word w = Some t -> Z_to_bv 64 (to_Z t) = w.
Proof.
  intros w t H. unfold pc_of_word in H. destruct (Z.ltb_spec (bv_unsigned w) pc_bound) as [Hlt|]; [|discriminate].
  apply some_inj in H. subst t. unfold pc_bound in Hlt. pose proof (bv_unsigned_in_range _ w) as Hr.
  rewrite Uint63.of_Z_spec, Z.mod_small by (change wB with (2^63); lia).
  apply bv_eq. rewrite Z_to_bv_small; [reflexivity | exact Hr].
Qed.
End Step.
