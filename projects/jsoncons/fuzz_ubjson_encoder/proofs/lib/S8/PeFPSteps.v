(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare HeapIface L5Defs L5Core FPSteps AxSymExec3Sound.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEFX.
Section Steps.
Variable segs : list Segment. Context {bmK : BMode}.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Lemma npc4 (pc : Z) : 0 <= pc -> pc + 4 < 2 ^ 64 -> v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof. intros H1 H2. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity. Qed.

Lemma ea_of (R : bvmap 5 word) (rs : bv 5) (imm : bv 12) (a : Z) :
  bv_unsigned (getr R rs) + bv_signed imm = a -> v_addi (getr R rs) (bv_signed imm) = Z_to_bv 64 a.
Proof. intros E. unfold v_addi. rewrite E. reflexivity. Qed.

Lemma fsd_run (fx : FPState) R M (pc : Z) (W : bv 32) (rs1 rs2 : bv 5) (imm : bv 12) (a : Z) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (FStore FMT_D rs1 rs2 imm, 4%Z) ->
  bv_unsigned (getr R rs1) + bv_signed imm = a -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.writable segs M a 8 ->
  0 <= pc -> pc + 4 < 2 ^ 64 ->
  exists M', msteps segs (st fx R pc M) (st fx R (pc + 4) M')
    /\ mem_grows M M'
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (a <= i < a + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ L5.defined M' a 8.
Proof.
  intros HF HE HD Ha A0 A8 WR Hpc Hpc4.
  assert (SOK : store_ok segs M (Z_to_bv 64 a) 8%nat = true).
  { replace a with (a + 0) by lia. apply (WR 0 8%nat); cbn; lia. }
  pose proof (fp_step_fsd fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W rs1 rs2 imm (Z_to_bv 64 a) HF HE HD (ea_of R rs1 imm a Ha) SOK) as ST.
  rewrite (npc4 pc Hpc Hpc4) in ST.
  set (bs := word_to_le_bytes 8 (reg_get (@fp_regs fx) rs2)) in ST.
  assert (LEN : length bs = 8%nat) by (unfold bs, word_to_le_bytes; apply length_Z_to_le_bytes).
  exists (wbytes M (Z_to_bv 64 a) bs). split; [|split; [|split]].
  - eapply mst_step; [reflexivity| exact ST| apply mst_refl].
  - apply wbytes_grows.
  - intros i Hi Hout. destruct (Z_lt_le_dec i a) as [Lo|Hi2].
    + apply wbytes_below; rewrite !L5.unsigned_lit by lia; lia.
    + apply wbytes_above. rewrite !L5.unsigned_lit by lia. rewrite LEN. lia.
  - intros i Hi. replace (a + i) with (bv_unsigned (Z_to_bv 64 a) + Z.of_nat (Z.to_nat i)) by (rewrite L5.unsigned_lit by lia; lia).
    rewrite AX2S.wbytes_nth; [discriminate| rewrite L5.unsigned_lit by lia; rewrite LEN; lia| rewrite LEN; lia].
Qed.

Lemma rdn_of_defined (M : word -> option byte) : forall (k : nat) (a : Z),
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> L5.defined M a (Z.of_nat k) ->
  exists bs, rdn segs M (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  induction k as [|k IH]; intros a Ha Hk D. { exists []. split; reflexivity. }
  cbn [rdn]. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|congruence].
  destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & RB & LB).
  { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply D. lia. }
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1%bv : bv 64)) with 1. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite RB. exists (b :: bs). split; [reflexivity| cbn; lia].
Qed.

Lemma fld_run (fx : FPState) R M (pc : Z) (W : bv 32) (rd rs1 : bv 5) (imm : bv 12) (a : Z) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (FLoad FMT_D rd rs1 imm, 4%Z) ->
  bv_unsigned (getr R rs1) + bv_signed imm = a -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8 ->
  0 <= pc -> pc + 4 < 2 ^ 64 ->
  exists fx', msteps segs (st fx R pc M) (st fx' R (pc + 4) M) /\ @fp_csr fx' = @fp_csr fx.
Proof.
  intros HF HE HD Ha A0 A8 D Hpc Hpc4.
  destruct (rdn_of_defined M 8%nat a A0 ltac:(cbn; lia) D) as (bs & RD & _).
  pose proof (fp_step_fld fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs1 imm (Z_to_bv 64 a) bs HF HE HD (ea_of R rs1 imm a Ha) RD) as ST.
  rewrite (npc4 pc Hpc Hpc4) in ST.
  exists (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx)).
  split; [eapply mst_step; [reflexivity| exact ST| apply mst_refl]| reflexivity].
Qed.

Lemma fsgnj_run (fx : FPState) R M (pc : Z) (W : bv 32) op fmt (rd rs1 rs2 : bv 5) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
  0 <= pc -> pc + 4 < 2 ^ 64 ->
  exists fx', msteps segs (st fx R pc M) (st fx' R (pc + 4) M) /\ @fp_csr fx' = @fp_csr fx.
Proof.
  intros HF HE HD Hpc Hpc4.
  destruct (fp_step_fsgnj fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W op fmt rd rs1 rs2 HF HE HD) as (fr' & ST).
  rewrite (npc4 pc Hpc Hpc4) in ST.
  exists (mkFP fr' (@fp_csr fx)). split; [eapply mst_step; [reflexivity| exact ST| apply mst_refl]| reflexivity].
Qed.

Lemma fcmp_run (fx : FPState) R M (pc : Z) (W : bv 32) op fmt (rd rs1 rs2 : bv 5) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0%bv = false -> frm_zero (@fp_csr fx) -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  exists fx' (v : Z), (v = 0 \/ v = 1) /\ frm_zero (@fp_csr fx')
    /\ msteps segs (st fx R pc M) (st fx' (regupd R rd (Z_to_bv 64 v)) (pc + 4) M).
Proof.
  intros HF HE HD Hrd Hz Hpc Hpc4.
  destruct (fp_step_fcmp fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W op fmt rd rs1 rs2 HF HE HD Hz) as (b & cs' & Hz' & ST).
  rewrite (npc4 pc Hpc Hpc4), Hrd in ST.
  exists (mkFP (@fp_regs fx) cs'), (if b then 1 else 0). split; [destruct b; [right|left]; reflexivity|]. split; [exact Hz'|].
  eapply mst_step; [reflexivity| | apply mst_refl]. destruct b; exact ST.
Qed.

Lemma fcvt_dyn_run (fx : FPState) R M (pc : Z) (W : bv 32) dst src (rd rs1 : bv 5) (rm : bv 3) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_S \/ dst = FC_D) -> frm_zero (@fp_csr fx) -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7) -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  exists fx', frm_zero (@fp_csr fx') /\ msteps segs (st fx R pc M) (st fx' R (pc + 4) M).
Proof.
  intros HF HE HD Hdst Hz Hrm Hpc Hpc4.
  destruct (fp_step_fcvt_to_f fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W dst src rd rs1 rm HF HE HD Hdst Hz Hrm) as (fr' & cs' & Hz' & ST).
  rewrite (npc4 pc Hpc Hpc4) in ST.
  exists (mkFP fr' cs'). split; [exact Hz'|]. eapply mst_step; [reflexivity| exact ST| apply mst_refl].
Qed.

Lemma fmv_xf_run (fx : FPState) R M (pc : Z) (W : bv 32) fmt (rd rs1 : bv 5) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Fmv FMV_X_F fmt rd rs1, 4%Z) ->
  (fmt = FMT_S \/ fmt = FMT_D) -> bv_eqb rd 0%bv = false -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  exists v : Z, 0 <= v < 2 ^ 64 /\ msteps segs (st fx R pc M) (st fx (regupd R rd (Z_to_bv 64 v)) (pc + 4) M).
Proof.
  intros HF HE HD Hfmt Hrd Hpc Hpc4.
  destruct Hfmt as [-> | ->].
  - pose proof (fp_step_fmv_x_w fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs1 HF HE HD) as ST. rewrite (npc4 pc Hpc Hpc4), Hrd in ST.
    set (v := sext 64 (low32 (reg_get (@fp_regs fx) rs1))) in ST.
    exists (bv_unsigned v). pose proof (bv_unsigned_in_range 64 v) as RB. change (bv_modulus 64) with (2 ^ 64) in RB.
    split; [exact RB|]. rewrite Z_to_bv_bv_unsigned. eapply mst_step; [reflexivity| exact ST| apply mst_refl].
  - pose proof (fp_step_fmv_x_d fx segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs1 HF HE HD) as ST. rewrite (npc4 pc Hpc Hpc4), Hrd in ST.
    set (v := reg_get (@fp_regs fx) rs1) in ST.
    exists (bv_unsigned v). pose proof (bv_unsigned_in_range 64 v) as RB. change (bv_modulus 64) with (2 ^ 64) in RB.
    split; [exact RB|]. rewrite Z_to_bv_bv_unsigned. eapply mst_step; [reflexivity| exact ST| apply mst_refl].
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

Lemma preserved_regupd_scratch (R R1 : bvmap 5 word) (rd : nat) v :
  regs_preserved R R1 -> ~ In (Z.of_nat rd) callee_saved_idx -> (rd < 32)%nat -> regs_preserved R (regupd R1 (reg rd) v).
Proof.
  intros RP NI Hrd r0 Hr0. rewrite <- (RP r0 Hr0). apply getr_other. intros E. subst r0. apply NI.
  rewrite Z_to_bv_unsigned in Hr0. unfold bv_wrap in Hr0. change (bv_modulus 5) with 32 in Hr0. rewrite Z.mod_small in Hr0 by lia. exact Hr0.
Qed.

End Steps.
End PEFX.
