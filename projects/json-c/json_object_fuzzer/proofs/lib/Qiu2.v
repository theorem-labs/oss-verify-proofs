(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH Q7UD Qhd4 Qwm6 QgHv QZsi Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import QCcH.
Import Q7UD Qhd4 Qwm6.Mq0 QgHv.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Theorem realloc_nf_of_v6 : forall (H6 : QZsi.heap_iface_A A4L), realloc_nf_stmt (hi5_of_v6 A4L H6).
Proof.
intros H6. unfold realloc_nf_stmt.
intros until u. intros HP HIN BLK0 ST LO LOS SPA HT ERR TP A0 A1 N UW UWK BB BD K.
eapply (s5_hiA_realloc_nf A4L H6) with (p := p) (n0 := n0) (n := n) (u := u) (errv := errv) (lo := lo) (old := old) (junk0 := junk0);
[ exact HP | exact HIN | exact BLK0 | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact A0 | exact A1 | exact N
| exact UW | exact UWK | exact BB | exact BD | exact K ].
Qed.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgHv.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Theorem realloc_nf_of_v6 : forall (H6 : QZsi.heap_iface_A A4L), realloc_nf_stmt (hi5_of_v6 A4L H6).
Proof.
intros H6. unfold realloc_nf_stmt.
intros until u. intros HP HIN BLK0 ST LO LOS SPA HT ERR TP A0 A1 N UW UWK BB BD K.
eapply (s5_hiA_realloc_nf A4L H6) with (p := p) (n0 := n0) (n := n) (u := u) (errv := errv) (lo := lo) (old := old) (junk0 := junk0);
[ exact HP | exact HIN | exact BLK0 | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact A0 | exact A1 | exact N
| exact UW | exact UWK | exact BB | exact BD | exact K ].
Qed.
End RC__1.
