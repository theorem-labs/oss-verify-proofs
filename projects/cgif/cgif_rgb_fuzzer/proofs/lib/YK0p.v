(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Definition frm_zero (f : bv 32) : Prop :=
Z.land (Z.shiftr (bv_unsigned f) 5) 7 = 0%Z.
Lemma fp_frm_zero_fx0 : frm_zero (@fp_csr fx0).
Proof. reflexivity. Qed.
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















