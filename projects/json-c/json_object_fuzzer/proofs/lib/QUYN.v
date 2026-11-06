(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs Q0Do Qc6I QJFf Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5 QNQk.Mq1.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).

Lemma rw_cells_apart : forall m m' A cs W, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) W -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs W RC MU WM HW.
eapply (rw_cells_agree asegs (fun a => A <= a < A + Z.of_nat (cells_size cs))); [eapply agree_on_of_munch; [exact MU| exact WM|]| exact RC| intros a Ha; exact Ha].
intros x Hx _. clear MU. induction HW as [|[lo hi] W H HW IH]; cbn; [exact I|]. cbn in H. split; [lia| exact IH].
Qed.

Lemma slow_flag_zero : forall r v, 0 <= v < 8 -> 0 <= r < 8 -> (v = 0 \/ r < v) ->
Z.land (bv_unsigned (v_sltu (wz 0) (wz v))) (bv_unsigned (wz (Z.lxor (bv_unsigned (v_slt (wz r) (wz v))) 1))) = 0.
Proof.
intros r v Hv Hr C. unfold v_sltu, c_ltu, bv_ltu, v_slt, c_lts, bv_lts.
rewrite !signed_small, !unsigned_lit by lia. change (bv_unsigned (wz 0)) with 0.
destruct (Z.ltb_spec0 0 v); destruct (Z.ltb_spec0 r v); cbn -[Z.land]; try reflexivity; try lia.
Qed.

Lemma qslow_loop_sd : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a3', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz e) (wz e) (wz 0) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (0x572e8 + 16)) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) (wz e) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x572e8) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK.
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B.
step. stp. stp. step. destruct (Z_lt_le_dec (p + 1) e) as [X1|X1].
- ifz. eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. replace (p + 1) with e by lia. apply K.
Qed.

Lemma shadow_ok_sub : forall m A n0 p n, blk_shadow asegs m A n0 -> A <= p -> p + n <= A + n0 -> 0 < n -> shadow_ok m p n.
Proof.
intros m A n0 p n (A0 & A8 & N0 & SK & BS) Hp Hn N k Hk Hkn.
set (j := (p / 8 * 8 - A) / 8 + k).
assert (J : 0 <= j /\ 8 * j < n0 /\ SH A + j = SH (p / 8 * 8) + k /\ A + 8 * j = p / 8 * 8 + 8 * k).
{ unfold j. rewrite !SH_eq. Z.div_mod_to_equations. lia. }
destruct J as (J0 & J1 & J2 & J3).
exists (gran n0 j). split; [rewrite <- J2; exact (BS j J0 J1)|].
destruct (gran_cases n0 j J0 J1) as [G|[G1 G2]]; [left; exact G| right; split; [exact G1| lia]].
Qed.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).

Lemma rw_cells_apart : forall m m' A cs W, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) W -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs W RC MU WM HW.
eapply (rw_cells_agree asegs (fun a => A <= a < A + Z.of_nat (cells_size cs))); [eapply agree_on_of_munch; [exact MU| exact WM|]| exact RC| intros a Ha; exact Ha].
intros x Hx _. clear MU. induction HW as [|[lo hi] W H HW IH]; cbn; [exact I|]. cbn in H. split; [lia| exact IH].
Qed.

Lemma slow_flag_zero : forall r v, 0 <= v < 8 -> 0 <= r < 8 -> (v = 0 \/ r < v) ->
Z.land (bv_unsigned (v_sltu (wz 0) (wz v))) (bv_unsigned (wz (Z.lxor (bv_unsigned (v_slt (wz r) (wz v))) 1))) = 0.
Proof.
intros r v Hv Hr C. unfold v_sltu, c_ltu, bv_ltu, v_slt, c_lts, bv_lts.
rewrite !signed_small, !unsigned_lit by lia. change (bv_unsigned (wz 0)) with 0.
destruct (Z.ltb_spec0 0 v); destruct (Z.ltb_spec0 r v); cbn -[Z.land]; try reflexivity; try lia.
Qed.

Lemma qslow_loop_sd : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a3', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz e) (wz e) (wz 0) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (0x576c0 + 16)) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) (wz e) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x576c0) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK.
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B.
step. stp. stp. step. destruct (Z_lt_le_dec (p + 1) e) as [X1|X1].
- ifz. eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. replace (p + 1) with e by lia. apply K.
Qed.

Lemma shadow_ok_sub : forall m A n0 p n, blk_shadow asegs m A n0 -> A <= p -> p + n <= A + n0 -> 0 < n -> shadow_ok m p n.
Proof.
intros m A n0 p n (A0 & A8 & N0 & SK & BS) Hp Hn N k Hk Hkn.
set (j := (p / 8 * 8 - A) / 8 + k).
assert (J : 0 <= j /\ 8 * j < n0 /\ SH A + j = SH (p / 8 * 8) + k /\ A + 8 * j = p / 8 * 8 + 8 * k).
{ unfold j. rewrite !SH_eq. Z.div_mod_to_equations. lia. }
destruct J as (J0 & J1 & J2 & J3).
exists (gran n0 j). split; [rewrite <- J2; exact (BS j J0 J1)|].
destruct (gran_cases n0 j J0 J1) as [G|[G1 G2]]; [left; exact G| right; split; [exact G1| lia]].
Qed.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src.
