(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare L5Defs L5Core FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMPX.
Section Steps.
Variable segs : list Segment. Context {bmK : BMode}.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Lemma rdn1_of_defined (M : word -> option byte) a : L5.defined M a 1 ->
  exists b : byte, rdn segs M (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros D. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. cbn [rdn].
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|congruence]. exists b. reflexivity.
Qed.

Lemma lbu_run (fx : FPState) R M (pc : Z) (W : bv 32) (rd rs : bv 5) (imm : bv 12) (a0 : Z) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rd <> 0%bv -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  getr R rs = Z_to_bv 64 a0 -> 0 <= a0 < 2 ^ 64 -> 0 <= a0 + bv_signed imm < 2 ^ 64 -> L5.defined M (a0 + bv_signed imm) 1 ->
  exists b, 0 <= b < 256 /\ L5.u8_at segs M (a0 + bv_signed imm) b
    /\ msteps segs (st fx R pc M) (st fx (regupd R rd (Z_to_bv 64 b)) (pc + 4) M).
Proof.
  intros HF HE HD Hrd Hpc Hpc4 Hrs Ha0 Ha D.
  destruct (rdn1_of_defined M _ D) as (b & RB).
  exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Bb. change (bv_modulus 8) with 256 in Bb.
  split; [exact Bb|]. split. { unfold L5.u8_at. rewrite RB. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  eapply mst_step; [reflexivity| | apply mst_refl].
  rewrite (step_lbu segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs imm b HF HE HD).
  - rewrite (bv_eqb_neq rd 0%bv Hrd). f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
  - unfold v_addi. rewrite Hrs, L5.unsigned_lit by lia. exact RB.
Qed.

Lemma fmv_fx_run (fx : FPState) R M (pc : Z) (W : bv 32) fmt (rd rs : bv 5) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Fmv FMV_F_X fmt rd rs, 4%Z) ->
  (fmt = FMT_S \/ fmt = FMT_D) -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  exists fx', msteps segs (st fx R pc M) (st fx' R (pc + 4) M).
Proof.
  intros HF HE HD Hfmt Hpc Hpc4.
  assert (NPC : v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4)).
  { unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity. }
  destruct Hfmt as [->| ->].
  - pose proof (fp_step_fmv_w_x fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs HF HE HD) as ST. rewrite NPC in ST.
    exists (mkFP (bvmap_set rd (nan_box (low32 (getr R rs))) (@fp_regs fx)) (@fp_csr fx)). eapply mst_step; [reflexivity| exact ST| apply mst_refl].
  - pose proof (fp_step_fmv_d_x fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs HF HE HD) as ST. rewrite NPC in ST.
    exists (mkFP (bvmap_set rd (getr R rs) (@fp_regs fx)) (@fp_csr fx)). eapply mst_step; [reflexivity| exact ST| apply mst_refl].
Qed.

Lemma fp_resolve_static (rm : bv 3) (x : Z) : (bv_unsigned rm <= 4)%Z -> exists md, rmode_of_field (bv_unsigned rm) x = Some md.
Proof.
  intros Hrm. unfold rmode_of_field. pose proof (bv_unsigned_in_range _ rm) as Hr.
  destruct (Z.eqb_spec (bv_unsigned rm) 7) as [E|NE]; [lia|].
  unfold rmode_of_Z.
  destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
  destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
  destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
  destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
  destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|].
  exfalso. lia.
Qed.

Lemma fcvt_f_static_step : forall (fx : FPState) regs pc mem rom w dst src rd rs1 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) -> (dst = FC_S \/ dst = FC_D) -> (bv_unsigned rm <= 4)%Z ->
  exists fr' cs', RiscvSemantics.step segs (@mkst fx regs pc mem rom) = MachineOk (@mkst (mkFP fr' cs') regs (v_addi pc 4) mem rom).
Proof.
  intros fx regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hrm.
  destruct fx as [fr cs]. cbn [fp_csr] in *.
  destruct (fp_resolve_static rm (Z.land (Z.shiftr (bv_unsigned cs) 5) 7) Hrm) as [md Hmd].
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct Hdst as [-> | ->]; destruct src; cbv beta iota;
    repeat match goal with
           | |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
           end;
    try (destruct (is_x0 rs1); cbv beta iota);
    repeat match goal with
           | |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
           end;
    rewrite b_npc4;
    (eexists _, _; reflexivity).
Qed.
Lemma fcvt_f_run (fx : FPState) R M (pc : Z) (W : bv 32) dst src (rd rs : bv 5) (rm : bv 3) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Fcvt dst src rd rs rm, 4%Z) ->
  (dst = FC_S \/ dst = FC_D) -> (bv_unsigned rm <= 4)%Z -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  exists fx', msteps segs (st fx R pc M) (st fx' R (pc + 4) M).
Proof.
  intros HF HE HD Hdst Hrm Hpc Hpc4.
  assert (NPC : v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4)).
  { unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity. }
  destruct (fcvt_f_static_step fx R (Z_to_bv 64 pc) M (seg_rom segs) W dst src rd rs rm HF HE HD Hdst Hrm) as (fr' & cs' & ST).
  rewrite NPC in ST. exists (mkFP fr' cs'). eapply mst_step; [reflexivity| exact ST| apply mst_refl].
Qed.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Lemma regupd_other_idx (R : bvmap 5 word) (rd k : nat) v : k <> rd -> (k < 32)%nat -> (rd < 32)%nat -> getr (regupd R (reg rd) v) (reg k) = getr R (reg k).
Proof.
  intros NE Hk Hr. apply getr_other. intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 5) with 32 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.
Lemma regupd_same_idx (R : bvmap 5 word) (rd : nat) v : (0 < rd < 32)%nat -> getr (regupd R (reg rd) v) (reg rd) = v.
Proof.
  intros Hr. apply getr_same. intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
Qed.

End Steps.
End PMPX.
