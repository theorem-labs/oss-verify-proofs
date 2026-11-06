(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Module VDF.

(* [comment removed for export] *)
Lemma feq0_nz (d : Z) : (0 <= d < 2 ^ 64)%Z -> fst (fp_eq fmt_double d 0) = false -> (d mod 2 ^ 63 <> 0)%Z.
Proof.
  intros R H E. assert (C : (d = 0 \/ d = 2 ^ 63)%Z).
  { pose proof (Z.div_mod d (2 ^ 63) ltac:(lia)) as DM. rewrite E, Z.add_0_r in DM.
    assert (0 <= d / 2 ^ 63 < 2)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
  destruct C as [-> | ->]; vm_compute in H; discriminate.
Qed.

(* [comment removed for export] *)
Lemma fp_step_feq_d : forall (fx : FPState) segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp F_EQ FMT_D rd rs1 rs2, 4%Z) ->
  frm_zero (@fp_csr fx) ->
  exists cs',
    frm_zero cs' /\
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (@fp_regs fx) cs')
                 (if bv_eqb rd 0 then regs
                  else regupd regs rd (if fst (fp_eq fmt_double (bv_unsigned (reg_get (@fp_regs fx) rs1)) (bv_unsigned (reg_get (@fp_regs fx) rs2)))
                                       then Z_to_bv 64 1 else Z_to_bv 64 0))
                 (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hz.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
    by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
  fp_pipeline Hf He Hd. change (fp_format FMT_D) with fmt_double.
  match goal with |- context [fp_eq ?f ?a ?b] => destruct (fp_eq f a b) as [v fl] eqn:E end.
  cbv beta iota. cbn [fst].
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; (eexists; split; [apply Hacc | reflexivity]).
Qed.

(* [comment removed for export] *)
Lemma fp_step_fsgnj_d : forall (fx : FPState) segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj op FMT_D rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (sgnj_val op (reg_get (@fp_regs fx) rs1) (reg_get (@fp_regs fx) rs2)) (@fp_regs fx)) (@fp_csr fx)) regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op rd rs1 rs2 Hf He Hd.
  fp_pipeline Hf He Hd; cbn [fp_regs fp_csr]; rewrite b_npc4; destruct fx; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sgnjx_abs (a : word) : bv_unsigned (sgnj_val F_SGNJX a a) = (bv_unsigned a mod 2 ^ 63)%Z.
Proof.
  rewrite FP.sgnjx_self. unfold FP.fabs_d. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  rewrite Z.land_ones by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 63) ltac:(lia)). lia.
Qed.
Lemma sgnj_copy (a : word) : sgnj_val F_SGNJ a a = a.
Proof. apply FP.sgnj_self. Qed.

(* [comment removed for export] *)
Lemma fp_class_range f a : (0 <= fp_class f a < 1024)%Z.
Proof.
  unfold fp_class.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; try lia.
  all: split; [apply Z.shiftl_nonneg; lia| rewrite Z.shiftl_mul_pow2 by lia; cbn; lia].
Qed.
Lemma fp_step_fclass_d : forall (fx : FPState) segs regs pc mem rom w rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass FMT_D rd rs1, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (fp_class fmt_double (bv_unsigned (reg_get (@fp_regs fx) rs1)))))
               (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  fp_pipeline Hf He Hd. change (fp_format FMT_D) with fmt_double.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

End VDF.
