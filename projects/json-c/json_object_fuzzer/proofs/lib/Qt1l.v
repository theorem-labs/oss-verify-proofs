(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs Q0Do Qc6I QJFf QVsB QvG1 QyW2 Qp4j QsGW Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QvG1 QyW2 Qp4j QsGW Qu1d.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition istrlen_entry : Z := 0x750c4.

Ltac has_var c := match c with context [?x] => is_var x end.
Ltac bif := try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
tryif has_var c then idtac else
(let v := eval vm_compute in c in
lazymatch v with
| true => replace c with true by (vm_compute; reflexivity); cbv iota
| false => replace c with false by (vm_compute; reflexivity); cbv iota
end) end).
Ltac ifT := unfold_cond; cond_unsig; if_true.

Lemma byte_nz : forall b : byte, b <> b8 0 -> 0 < bv_unsigned b < 256.
Proof.
intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia]. exfalso. apply Hb. apply bv_eq. rewrite E. reflexivity.
Qed.

Section IStrlen.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (p : Z) (str t : list byte).
Hypothesis SRC : bytes_at asegs m p (str ++ b8 0 :: t).
Hypothesis NZ : ~ In (b8 0) str.
Local Notation len := (Z.of_nat (length str)).

Definition istrlen_post : machine_state -> Prop :=
eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz len) (wz (len + 1)) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).

Lemma istrlen_loop : forall (n : nat) (i : Z) (a2 : word), Z.of_nat n = len - i -> 0 <= i <= len ->
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) (wz i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x750c8) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros i a2 Hn Hi.
- assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 0]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app; cbn; lia).
replace i with len by lia. rewrite Nat2Z.id, skipn_app, skipn_all2, Nat.sub_diag by lia. reflexivity. }
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app in BS. cbn [length] in BS.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
change (zxb (b8 0)) with (wz 0). step. step. bif. step. step.
apply evt_done. unfold istrlen_post. replace i with len by lia. reflexivity.
- pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app in BS. cbn [length] in BS.
assert (Hi' : (Z.to_nat i < length str)%nat) by lia.
destruct (nth_error str (Z.to_nat i)) as [c|] eqn:Ec; [| apply nth_error_None in Ec; lia].
assert (CR : 0 < bv_unsigned c < 256).
{ apply byte_nz. intros ->. apply NZ. eapply nth_error_In. exact Ec. }
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [c]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app; cbn; lia).
rewrite skipn_app. replace (Z.to_nat i - length str)%nat with 0%nat by lia. cbn [skipn].
apply nth_error_split in Ec as (l1 & l2 & -> & L1). rewrite skipn_app, skipn_all2, L1, Nat.sub_diag by lia. reflexivity. }
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
step. step. unfold zxb. ifT. apply (IH (i + 1)); lia.
Qed.

Lemma istrlen_spec : forall (a1 a2 : word),
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz istrlen_entry) fc None m (seg_rom asegs)).
Proof.
intros a1 a2. unfold istrlen_entry. step. apply (istrlen_loop (Z.to_nat len) 0); lia.
Qed.
End IStrlen.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition istrlen_entry : Z := 0x7549c.

Ltac has_var c := match c with context [?x] => is_var x end.
Ltac bif := try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
tryif has_var c then idtac else
(let v := eval vm_compute in c in
lazymatch v with
| true => replace c with true by (vm_compute; reflexivity); cbv iota
| false => replace c with false by (vm_compute; reflexivity); cbv iota
end) end).
Ltac ifT := unfold_cond; cond_unsig; if_true.

Lemma byte_nz : forall b : byte, b <> b8 0 -> 0 < bv_unsigned b < 256.
Proof.
intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia]. exfalso. apply Hb. apply bv_eq. rewrite E. reflexivity.
Qed.

Section IStrlen.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (p : Z) (str t : list byte).
Hypothesis SRC : bytes_at asegs m p (str ++ b8 0 :: t).
Hypothesis NZ : ~ In (b8 0) str.
Local Notation len := (Z.of_nat (length str)).

Definition istrlen_post : machine_state -> Prop :=
eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz len) (wz (len + 1)) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).

Lemma istrlen_loop : forall (n : nat) (i : Z) (a2 : word), Z.of_nat n = len - i -> 0 <= i <= len ->
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) (wz i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x754a0) fc None m (seg_rom asegs)).
Proof.
induction n as [|n IH]; intros i a2 Hn Hi.
- assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [b8 0]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app; cbn; lia).
replace i with len by lia. rewrite Nat2Z.id, skipn_app, skipn_all2, Nat.sub_diag by lia. reflexivity. }
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app in BS. cbn [length] in BS.
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
change (zxb (b8 0)) with (wz 0). step. step. bif. step. step.
apply evt_done. unfold istrlen_post. replace i with len by lia. reflexivity.
- pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_app in BS. cbn [length] in BS.
assert (Hi' : (Z.to_nat i < length str)%nat) by lia.
destruct (nth_error str (Z.to_nat i)) as [c|] eqn:Ec; [| apply nth_error_None in Ec; lia].
assert (CR : 0 < bv_unsigned c < 256).
{ apply byte_nz. intros ->. apply NZ. eapply nth_error_In. exact Ec. }
assert (RD : ov_read_bytes asegs m (wa (p + i)) 1 = Some [c]).
{ rewrite (bytes_at_read asegs m p _ i 1 SRC) by (rewrite ?length_app; cbn; lia).
rewrite skipn_app. replace (Z.to_nat i - length str)%nat with 0%nat by lia. cbn [skipn].
apply nth_error_split in Ec as (l1 & l2 & -> & L1). rewrite skipn_app, skipn_all2, L1, Nat.sub_diag by lia. reflexivity. }
step. replace (wz (p + i) : word) with (wa (p + i)) by reflexivity. step. clear RD.
step. step. unfold zxb. ifT. apply (IH (i + 1)); lia.
Qed.

Lemma istrlen_spec : forall (a1 a2 : word),
evt asegs istrlen_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz istrlen_entry) fc None m (seg_rom asegs)).
Proof.
intros a1 a2. unfold istrlen_entry. step. apply (istrlen_loop (Z.to_nat len) 0); lia.
Qed.
End IStrlen.
