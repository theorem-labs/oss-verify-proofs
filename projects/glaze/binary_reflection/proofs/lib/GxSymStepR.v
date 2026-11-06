(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module FPSteps.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition frm_zero (f : bv 32) : Prop :=
  Z.land (Z.shiftr (bv_unsigned f) 5) 7 = 0%Z.


Lemma fp_fflags_bits_range : forall fl, (0 <= fflags_bits fl < 32)%Z.
Proof.
  intros [nv dz of uf nx]. unfold fflags_bits. cbn [fl_nx fl_uf fl_of fl_dz fl_nv].
  destruct nv, dz, of, uf, nx; vm_compute; split; congruence.
Qed.

Lemma fp_u32_range : forall f : bv 32, (0 <= bv_unsigned f < 2^32)%Z.
Proof. intros f. pose proof (bv_unsigned_in_range _ f) as H. unfold bv_modulus in H. exact H. Qed.


Lemma fp_Z_lor_range : forall n a b, (0 <= n)%Z -> (0 <= a < 2^n)%Z -> (0 <= b < 2^n)%Z ->
  (0 <= Z.lor a b < 2^n)%Z.
Proof.
  intros n a b Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high n a k) by lia. rewrite (Z_testbit_high n b k) by lia. reflexivity.
Qed.

Lemma fp_u_Z2bv32 : forall z, (0 <= z < 2^32)%Z -> bv_unsigned (Z_to_bv 32 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz.
Qed.

(* [comment removed for export] *)
Lemma fp_frm_zero_accrue : forall (f : bv 32) (b : Z),
  (0 <= b < 32)%Z -> frm_zero f ->
  frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned f) b)).
Proof.
  intros f b Hb Hf. unfold frm_zero in *.
  pose proof (fp_u32_range f) as Hr.
  rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
  rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 b 5) by lia.
  rewrite (Z.div_small b (2^5)) by lia. rewrite Z.lor_0_r. exact Hf.
Qed.


(* [comment removed for export] *)
Lemma fp_resolve_rm : forall (rm : bv 3) (f : bv 32),
  frm_zero f ->
  (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  exists md, rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned f) 5) 7) = Some md.
Proof.
  intros rm f Hf Hrm. unfold rmode_of_field. rewrite Hf.
  pose proof (bv_unsigned_in_range _ rm) as Hr.
  destruct (Z.eqb_spec (bv_unsigned rm) 7) as [E|NE].
  - exists RNE. reflexivity.
  - unfold rmode_of_Z.
    destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|].
    exfalso. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac fp_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val Sem.exec_csr
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.fget Sem.fset Sem.with_fregs Sem.with_fcsr Sem.fread Sem.fwrite
     Sem.accrue Sem.resolve_rm Sem.frm_of
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     RiscvSemantics.access_value RiscvSemantics.drop_access_report
     ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst fp_regs fp_csr];
  rewrite ?bv_eqb0_is_x0.















End FPSteps.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec FPSteps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkstR (fx : FPState) (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (rv : option word)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := @fp_regs fx; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := rv; ms_fcsr := @fp_csr fx;
     ms_mem := mem; ms_rom := rom |}.

Lemma mkstR_None : forall fx regs pc mem rom, mkstR fx regs pc mem rom None = @mkst fx regs pc mem rom.
Proof. reflexivity. Qed.




(* [comment removed for export] *)
Definition fx_ok (fx : FPState) : Prop := frm_zero (@fp_csr fx).

Lemma fx_ok_fx0 : fx_ok fx0.
Proof. reflexivity. Qed.

Lemma frm_zero_accrue_fl : forall (f : bv 32) fl,
  frm_zero f -> frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned f) (fflags_bits fl))).
Proof. intros f fl Hf. apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hf]. Qed.

(* [comment removed for export] *)
Definition rm_ok (rm : bv 3) : Prop := (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z.

Lemma resolve_rm_ok : forall (rm : bv 3) (f : bv 32),
  frm_zero f -> rm_ok rm ->
  exists md, rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned f) 5) 7) = Some md.
Proof. intros rm f Hf Hrm. exact (fp_resolve_rm rm f Hf Hrm). Qed.

(* [comment removed for export] *)
Definition resv_inval_w (rv : option word) (a : word) : option word :=
  match rv with
  | Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else rv
  | None => None
  end.

(* [comment removed for export] *)
Definition load_result (sz : msize) (sx : bool) (bs : list byte) : word :=
  match sz with
  | SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
  | SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
  | SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
  end.

Definition eff_sx (sz : msize) (sx : bool) : bool :=
  match sz with SZ8 => false | _ => sx end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition amo_msize (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition amo_nbytes (wd : awidth) : nat := match wd with AW => 4%nat | AD => 8%nat end.

(* [comment removed for export] *)
Definition amo_store_bytes (op : amoop) (wd : awidth) (bs : list byte) (src : word) : list byte :=
  match wd with
  | AW => Z_to_le_bytes 4 (bv_unsigned (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 src)))
  | AD => Z_to_le_bytes 8 (bv_unsigned (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) src))
  end.

Ltac stepR_pipeline Hfetch Hecall Hdecode :=
  unfold mkstR;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.

Section WithFX.
Variable fx : FPState.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stepR_opimm_gen : forall segs regs pc mem rom rv w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_opimm32_gen : forall segs regs pc mem rom rv w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm32_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs
                    else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_lui : forall segs regs pc mem rom rv w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma stepR_auipc : forall segs regs pc mem rom rv w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma stepR_jal_link : forall segs regs pc mem rom rv w rd (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                   (btgt pc (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

Lemma stepR_jalr : forall segs regs pc mem rom rv w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                   (v_jalr (getr regs rs1) (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs1 imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd, v_jalr.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_jalr; reflexivity.
Qed.

Lemma stepR_branch_tk_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx regs (btgt pc (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma stepR_branch_ft_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

Lemma stepR_fence : forall segs regs pc mem rom rv w a b c d e,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) = MachineOk (mkstR fx regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w a b c d e Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Lemma stepR_fencei : forall segs regs pc mem rom rv w a b c,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI a b c, 4%Z) ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) = MachineOk (mkstR fx regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w a b c Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stepR_load : forall segs regs pc mem rom rv w sz sx rd rs (imm : bv 12) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs))
                   (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w sz sx rd rs imm bs Hfetch Hecall Hdecode Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
    rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4;
    destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_store : forall segs regs pc mem rom rv w sz (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) (msize_bytes sz) = true ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes (msize_bytes sz) (getr regs rs2))) rom
    (resv_inval_w rv (v_addi (getr regs rs1) (bv_signed imm)))).
Proof.
  intros segs regs pc mem rom rv w sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite !b_addsext.
  destruct sz; cbn [msize_bytes] in Hok |- *; cbv beta iota delta [store_val];
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?Hsb, ?store_bytes_low16, ?store_bytes_low32, b_npc4;
    (destruct rv as [r|]; cbv beta iota; [|reflexivity]);
    unfold resv_inval_w;
    match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y); cbv beta iota; reflexivity end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepR_lr : forall segs regs pc mem rom rv w wd aq rl rd rs bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr wd aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod amo_bytes wd = 0)%Z ->
  rdn segs mem (getr regs rs) (amo_nbytes wd) = Some bs ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
                   (v_addi pc 4) mem rom (Some (getr regs rs))).
Proof.
  intros segs regs pc mem rom rv w wd aq rl rd rs bs Hfetch Hecall Hdecode Hal Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite b_npc4; unfold regupd;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_sc_ok : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom (Some r)) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                   (wbytes mem (getr regs rs1) (word_to_le_bytes (amo_nbytes wd) (getr regs rs2))) rom None).
Proof.
  intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    subst r; rewrite Z.eqb_refl; cbv beta iota;
    cbn [amo_nbytes] in Hok |- *; rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?store_bytes_low32, b_npc4;
    unfold regupd, word_to_le_bytes;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_amo : forall segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  rdn segs mem (getr regs rs1) (amo_nbytes wd) = Some bs ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
                   (v_addi pc 4)
                   (wbytes mem (getr regs rs1) (amo_store_bytes op wd bs (getr regs rs2)))
                   rom (resv_inval_w rv (getr regs rs1))).
Proof.
  intros segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread, Hok |- *; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, b_npc4; unfold regupd, amo_store_bytes;
    (destruct rv as [r|]; cbv beta iota);
    unfold resv_inval_w;
    try match goal with |- context [Z.eqb (bv_unsigned r) ?y] =>
          destruct (Z.eqb (bv_unsigned r) y); cbv beta iota end;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

End WithFX.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ffmt_nbytes (fmt : ffmt) : nat := match fmt with FMT_S => 4%nat | FMT_D => 8%nat end.

Ltac stepF_pipeline Hfetch Hecall Hdecode :=
  unfold mkstR;
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val Sem.exec_csr
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.fget Sem.fset Sem.with_fregs Sem.with_fcsr Sem.fread Sem.fwrite
     Sem.accrue Sem.resolve_rm Sem.frm_of
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     RiscvSemantics.access_value RiscvSemantics.drop_access_report
     ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.

Section FPSteps.
Variable fx : FPState.

(* [comment removed for export] *)
Lemma stepR_fload : forall segs regs pc mem rom rv w fmt rd rs (imm : bv 12) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FLoad fmt rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (ffmt_nbytes fmt) = Some bs ->
  fx_ok fx ->
  exists fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w fmt rd rs imm bs Hf He Hd Hr Hok.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  unfold getr in Hr; rewrite ?bv_eqb0_is_x0 in Hr.
  destruct fmt; cbn [ffmt_nbytes] in Hr.
  - exists (mkFP (bvmap_set rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) fr) cs).
    split; [exact Hok|].
    stepF_pipeline Hf He Hd.
    rewrite ov_rdn, b_addsext, Hr. cbv beta iota. cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
  - exists (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) fr) cs).
    split; [exact Hok|].
    stepF_pipeline Hf He Hd.
    rewrite ov_rdn, b_addsext, Hr. cbv beta iota. cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_fstore : forall segs regs pc mem rom rv w fmt (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FStore fmt rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) (ffmt_nbytes fmt) = true ->
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes (ffmt_nbytes fmt) (reg_get (@fp_regs fx) rs2))) rom
    (resv_inval_w rv (v_addi (getr regs rs1) (bv_signed imm)))).
Proof.
  intros segs regs pc mem rom rv w fmt rs1 rs2 imm Hf He Hd Hok.
  destruct fx as [fr cs].
  stepF_pipeline Hf He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite !b_addsext.
  destruct fmt; cbn [ffmt_nbytes fp_regs fp_csr] in Hok |- *;
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?store_bytes_low32, b_npc4;
    (destruct rv as [r|]; cbv beta iota; [|reflexivity]);
    unfold resv_inval_w;
    match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y); cbv beta iota; reflexivity end.
Qed.

(* [comment removed for export] *)
Lemma stepR_fmv_fx : forall segs regs pc mem rom rv w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_F_X fmt rd rs1, 4%Z) ->
  fx_ok fx ->
  exists fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w fmt rd rs1 Hf He Hd Hok.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  destruct fmt.
  - exists (mkFP (bvmap_set rd (nan_box (low32 (getr regs rs1))) fr) cs). split; [exact Hok|].
    stepF_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
    destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
  - exists (mkFP (bvmap_set rd (getr regs rs1) fr) cs). split; [exact Hok|].
    stepF_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
    destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.

Lemma stepR_fsgnj : forall segs regs pc mem rom rv w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
  fx_ok fx ->
  exists fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op fmt rd rs1 rs2 Hf He Hd Hok.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  destruct fmt; (eexists (mkFP _ cs); split; [exact Hok|]);
    stepF_pipeline Hf He Hd; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.

Lemma stepR_fminmax : forall segs regs pc mem rom rv w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fminmax op fmt rd rs1 rs2, 4%Z) ->
  fx_ok fx ->
  exists fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op fmt rd rs1 rs2 Hf He Hd Hok.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  pose proof (fun fl => frm_zero_accrue_fl cs fl Hok) as Hacc.
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr].
  repeat match goal with
         | |- context [let '(_, _) := ?pr in _] => destruct pr as [?v ?fl]; cbv beta iota
         end.
  destruct fmt; cbv beta iota; rewrite b_npc4;
    (eexists (mkFP _ _); split; [apply Hacc | reflexivity]).
Qed.

Lemma stepR_fari : forall segs regs pc mem rom rv w op fmt rd rs1 rs2 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fari op fmt rd rs1 rs2 rm, 4%Z) ->
  fx_ok fx -> rm_ok rm ->
  exists fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op fmt rd rs1 rs2 rm Hf He Hd Hok Hrm.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  destruct (resolve_rm_ok rm _ Hok Hrm) as [md Hmd].
  pose proof (fun fl => frm_zero_accrue_fl cs fl Hok) as Hacc.
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. rewrite Hmd. cbv beta iota.
  repeat match goal with
         | |- context [let '(_, _) := ?pr in _] => destruct pr as [?v ?fl]; cbv beta iota
         end.
  destruct fmt; cbv beta iota; rewrite b_npc4;
    (eexists (mkFP _ _); split; [apply Hacc | reflexivity]).
Qed.

Lemma stepR_fsqrt : forall segs regs pc mem rom rv w fmt rd rs1 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsqrt fmt rd rs1 rm, 4%Z) ->
  fx_ok fx -> rm_ok rm ->
  exists fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w fmt rd rs1 rm Hf He Hd Hok Hrm.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  destruct (resolve_rm_ok rm _ Hok Hrm) as [md Hmd].
  pose proof (fun fl => frm_zero_accrue_fl cs fl Hok) as Hacc.
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. rewrite Hmd. cbv beta iota.
  repeat match goal with
         | |- context [let '(_, _) := ?pr in _] => destruct pr as [?v ?fl]; cbv beta iota
         end.
  destruct fmt; cbv beta iota; rewrite b_npc4;
    (eexists (mkFP _ _); split; [apply Hacc | reflexivity]).
Qed.

Lemma stepR_fma : forall segs regs pc mem rom rv w op fmt rd rs1 rs2 rs3 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fma op fmt rd rs1 rs2 rs3 rm, 4%Z) ->
  fx_ok fx -> rm_ok rm ->
  exists fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op fmt rd rs1 rs2 rs3 rm Hf He Hd Hok Hrm.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  destruct (resolve_rm_ok rm _ Hok Hrm) as [md Hmd].
  pose proof (fun fl => frm_zero_accrue_fl cs fl Hok) as Hacc.
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. rewrite Hmd. cbv beta iota.
  repeat match goal with
         | |- context [let '(_, _) := ?pr in _] => destruct pr as [?v ?fl]; cbv beta iota
         end.
  destruct fmt; cbv beta iota; rewrite b_npc4;
    (eexists (mkFP _ _); split; [apply Hacc | reflexivity]).
Qed.

(* [comment removed for export] *)
Definition fcvt_fp (t : fcvt_ty) : bool := match t with FC_S | FC_D => true | _ => false end.

(* [comment removed for export] *)
Lemma stepR_fcvt_f : forall segs regs pc mem rom rv w dst src rd rs1 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  fcvt_fp dst = true ->
  fx_ok fx -> rm_ok rm ->
  exists fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' regs (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w dst src rd rs1 rm Hf He Hd Hdst Hok Hrm.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  destruct (resolve_rm_ok rm _ Hok Hrm) as [md Hmd].
  pose proof (fun fl => frm_zero_accrue_fl cs fl Hok) as Hacc.
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. rewrite Hmd. cbv beta iota.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct dst; try discriminate; destruct src; cbv beta iota;
    repeat match goal with
           | |- context [let '(_, _) := ?pr in _] => destruct pr as [?v ?fl]; cbv beta iota
           end;
    try (destruct (is_x0 rs1); cbv beta iota);
    repeat match goal with
           | |- context [let '(_, _) := ?pr in _] => destruct pr as [?v ?fl]; cbv beta iota
           end;
    rewrite b_npc4;
    (eexists (mkFP _ _); split; [ | reflexivity ]; first [apply Hacc | exact Hok]).
Qed.

(* [comment removed for export] *)
Lemma stepR_fmv_xf : forall segs regs pc mem rom rv w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_X_F fmt rd rs1, 4%Z) ->
  fx_ok fx ->
  exists (v : word) fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w fmt rd rs1 Hf He Hd Hok.
  destruct fx as [fr cs].
  destruct fmt.
  - exists (sext 64 (low32 (reg_get fr rs1))), (mkFP fr cs). split; [exact Hok|].
    stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. unfold regupd.
    destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
  - exists (reg_get fr rs1), (mkFP fr cs). split; [exact Hok|].
    stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. unfold regupd.
    destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_fmv_xw : forall segs regs pc mem rom rv w rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_X_F FMT_S rd rs1, 4%Z) ->
  fx_ok fx ->
  exists (u : word) fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' (if bv_eqb rd 0 then regs else regupd regs rd (sext 64 (low32 u))) (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs1 Hf He Hd Hok.
  destruct fx as [fr cs].
  exists (reg_get fr rs1), (mkFP fr cs). split; [exact Hok|].
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. unfold regupd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

Lemma stepR_fcvt_x : forall segs regs pc mem rom rv w dst src rd rs1 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  fcvt_fp dst = false -> fcvt_fp src = true ->
  fx_ok fx -> rm_ok rm ->
  exists (v : word) fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w dst src rd rs1 rm Hf He Hd Hdst Hsrc Hok Hrm.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  destruct (resolve_rm_ok rm _ Hok Hrm) as [md Hmd].
  pose proof (fun fl => frm_zero_accrue_fl cs fl Hok) as Hacc.
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. rewrite Hmd. cbv beta iota.
  unfold regupd.
  destruct dst; try discriminate; destruct src; try discriminate; cbv beta iota;
    repeat match goal with
           | |- context [let '(_, _) := ?pr in _] => destruct pr as [?v ?fl]; cbv beta iota
           end;
    (destruct (is_x0 rd); cbv beta iota; rewrite b_npc4;
     [ exists (Z_to_bv 64 0); eexists (mkFP _ _); split; [ apply Hacc | reflexivity ]
     | eexists _, (mkFP _ _); split; [ apply Hacc | reflexivity ] ]).
Qed.

Lemma stepR_fcmp : forall segs regs pc mem rom rv w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
  fx_ok fx ->
  exists (v : word) fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op fmt rd rs1 rs2 Hf He Hd Hok.
  destruct fx as [fr cs]. unfold fx_ok in Hok. cbn [fp_csr] in Hok.
  pose proof (fun fl => frm_zero_accrue_fl cs fl Hok) as Hacc.
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. unfold regupd.
  repeat match goal with
         | |- context [let '(_, _) := ?pr in _] => destruct pr as [?v ?fl]; cbv beta iota
         end.
  destruct (is_x0 rd);
    [ exists (Z_to_bv 64 0); eexists (mkFP _ _); split; [ apply Hacc | rewrite b_npc4; reflexivity ]
    | exists (if v then Z_to_bv 64 1 else Z_to_bv 64 0); destruct v; cbv beta iota; rewrite b_npc4;
      (eexists (mkFP _ _); split; [ apply Hacc | reflexivity ]) ].
Qed.

Lemma stepR_fclass : forall segs regs pc mem rom rv w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass fmt rd rs1, 4%Z) ->
  fx_ok fx ->
  exists (v : word) fx', fx_ok fx' /\
  RiscvSemantics.step segs (mkstR fx regs pc mem rom rv) =
  MachineOk (mkstR fx' (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w fmt rd rs1 Hf He Hd Hok.
  destruct fx as [fr cs].
  eexists _, (mkFP fr cs). split; [exact Hok|].
  stepF_pipeline Hf He Hd. cbn [fp_regs fp_csr]. unfold regupd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; [reflexivity|]. reflexivity.
Qed.

End FPSteps.
