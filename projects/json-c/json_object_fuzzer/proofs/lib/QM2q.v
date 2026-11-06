(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QZDE QRjH QHnV QCcH QfLs Qsw7 Q7UD QZsi Qwm6 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE.
Import QRjH.
Import QHnV QCcH QfLs Qsw7.
Import Q7UD QZsi Qwm6.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lb_remove_none : forall p (LB : list blk), (forall b, In b LB -> blk_addr b <> p) -> lb_remove p LB = LB.
Proof.
intros p LB. induction LB as [|b LB IH]; intros Hn; [reflexivity|]. cbn [lb_remove].
destruct (Z.eqb_spec (blk_addr b) p) as [E|E]; [exfalso; exact (Hn b (or_introl eq_refl) E)|].
rewrite IH; [reflexivity|]. intros b' Hb'. apply Hn. right. exact Hb'.
Qed.

Section F2N.
Variable J : aj_base (hl_segs A4L).
Variable ASA : Type.
Variable HEAPA : ASA -> list blk -> list blk -> list frame -> bud -> (word -> option byte) -> config -> Prop.
Variable top : Z.
Hypothesis Hpos : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) LM -> 0 < a.

Theorem free2_null_A : hiA_free2_null_ty A4L J ASA HEAPA top.
Proof.
unfold hiA_free2_null_ty. intros until errv. intros -> HP _ ST LO LOS SPA HT ERR TP GP A0 K. subst a0.
cbn [hl_free2 hla_base A4L A4H hl_segs]. apply (aj_evt J).
step. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota. step.
apply evt_done.
apply (K _ m c A (Z_to_bv 64 0)).
- unfold ret_state. do 14 eexists. reflexivity.
- apply model_vm_only_refl.
- exact ST.
- apply heap_pres_refl.
- exact ERR.
- rewrite lb_remove_none; [exact HP|]. intros [a n] Hb E. unfold blk_addr in E. cbn [fst] in E. subst a. pose proof (Hpos _ _ _ _ _ _ _ 0 n HP Hb). lia.
Qed.
End F2N.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lb_remove_none : forall p (LB : list blk), (forall b, In b LB -> blk_addr b <> p) -> lb_remove p LB = LB.
Proof.
intros p LB. induction LB as [|b LB IH]; intros Hn; [reflexivity|]. cbn [lb_remove].
destruct (Z.eqb_spec (blk_addr b) p) as [E|E]; [exfalso; exact (Hn b (or_introl eq_refl) E)|].
rewrite IH; [reflexivity|]. intros b' Hb'. apply Hn. right. exact Hb'.
Qed.

Section F2N.
Variable J : aj_base (hl_segs A4L).
Variable ASA : Type.
Variable HEAPA : ASA -> list blk -> list blk -> list frame -> bud -> (word -> option byte) -> config -> Prop.
Variable top : Z.
Hypothesis Hpos : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) LM -> 0 < a.

Theorem free2_null_A : hiA_free2_null_ty A4L J ASA HEAPA top.
Proof.
unfold hiA_free2_null_ty. intros until errv. intros -> HP _ ST LO LOS SPA HT ERR TP GP A0 K. subst a0.
cbn [hl_free2 hla_base A4L A4H hl_segs]. apply (aj_evt J).
step. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota. step.
apply evt_done.
apply (K _ m c A (Z_to_bv 64 0)).
- unfold ret_state. do 14 eexists. reflexivity.
- apply model_vm_only_refl.
- exact ST.
- apply heap_pres_refl.
- exact ERR.
- rewrite lb_remove_none; [exact HP|]. intros [a n] Hb E. unfold blk_addr in E. cbn [fst] in E. subst a. pose proof (Hpos _ _ _ _ _ _ _ 0 n HP Hb). lia.
Qed.
End F2N.
End RC__1.
