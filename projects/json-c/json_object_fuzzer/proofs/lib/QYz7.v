(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0.
Import ListNotations.
Open Scope Z_scope.

Lemma bv5_cases : forall (P : bv 5 -> Prop), (forall i, 0 <= i < 32 -> P (Z_to_bv 5 i)) -> forall r : bv 5, P r.
Proof.
intros P H r. assert (E : Z_to_bv 5 (bv_unsigned r) = r) by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
rewrite <- E. apply H. pose proof (bv_unsigned_in_range 5 r) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 5) with 32 in Hr. exact Hr.
Qed.

Lemma sb_zero_decode : forall rX : bv 5, bv_unsigned rX <> 0 ->
let w := Z_to_bv 32 (0x23 + Z.shiftl (bv_unsigned rX) 15) in
is_ecall w = false /\ decode_any w = Some (Store SZ1 rX (Z_to_bv 5 0) (Z_to_bv 12 0), 4).
Proof.
intros rX. pattern rX. apply bv5_cases. clear rX. intros i Hi Hn.
assert (Ei : i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16
\/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31).
{ assert (i <> 0) by (intros ->; apply Hn; reflexivity). lia. }
repeat (destruct Ei as [-> | Ei]); try subst i; (split; vm_compute; reflexivity).
Qed.

Section Step.
Variable segs : list Segment.

Lemma sb_zero_mstep : forall (R F : bvmap 5 word) (pc : Z) (fc : bv 32) (m ro : word -> option byte) (rX : bv 5) (a : word),
fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 (0x23 + Z.shiftl (bv_unsigned rX) 15)) ->
bv_unsigned rX <> 0 ->
reg_get R rX = a ->
wview segs m a <> None ->
mstep segs (MS R F (Z_to_bv 64 pc) fc None m ro) (MS R F (Z_to_bv 64 (pc + 4)) fc None (write_to_mem m a [Z_to_bv 8 0]) ro).
Proof.
intros R F pc fc m ro rX a Hf Hx Hr Hw. destruct (sb_zero_decode rX Hx) as [He Hd]. cbv zeta in He, Hd.
split; [reflexivity|].
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc None m ro _ _ _ Hf He Hd).
cbn [exec store_val]. unfold rget. cbn [c_regs c_pc with_pc].
assert (Ex : is_x0 rX = false) by (unfold is_x0; apply Z.eqb_neq; exact Hx). rewrite Ex.
change (is_x0 (Z_to_bv 5 0)) with true. cbv iota.
assert (Ea : bv_add (reg_get R rX) (sext 64 (Z_to_bv 12 0)) = a).
{ rewrite Hr. change (sext 64 (Z_to_bv 12 0)) with (Z_to_bv 64 0). apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
rewrite Ea. cbn [interp_eff]. change (width_bytes 8) with 1%nat.
assert (Es : store_ok segs m a 1 = true).
{ cbn [store_ok]. destruct (wview segs m a); [reflexivity| contradiction]. }
rewrite Es. cbn [lift_result]. unfold inval_resv. cbn [c_resv with_pc]. unfold MS_of_core. cbn [c_regs c_fregs c_pc c_fcsr c_resv].
rewrite lit_add_lit. reflexivity.
Qed.

Lemma sb_zero_evt : forall (Q : machine_state -> Prop) (R F : bvmap 5 word) (pc : Z) (fc : bv 32) (m ro : word -> option byte) (rX : bv 5) (a : word),
fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 (0x23 + Z.shiftl (bv_unsigned rX) 15)) ->
bv_unsigned rX <> 0 ->
reg_get R rX = a ->
wview segs m a <> None ->
evt segs Q (MS R F (Z_to_bv 64 (pc + 4)) fc None (write_to_mem m a [Z_to_bv 8 0]) ro) ->
evt segs Q (MS R F (Z_to_bv 64 pc) fc None m ro).
Proof. intros Q R F pc fc m ro rX a Hf Hx Hr Hw H. exact (evt_step segs Q _ _ (sb_zero_mstep R F pc fc m ro rX a Hf Hx Hr Hw) H). Qed.
End Step.
