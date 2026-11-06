(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWQV.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1oC.Mq2.
Import ListNotations.
Import SX2.
Open Scope Z_scope.

Definition STOPS1 : list Z := [0x5046c]%Z.
Definition run1 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS1 scr ss [].

Definition ssB1 : sym_state := SS 0x5eae4 srB0 [] knA NV0.
Definition rB1 := Eval vm_compute in run1 scr0 ssB1.
Definition srB1 : list expr := Eval vm_compute in s_regs (fst (fst rB1)).
Definition knB1 : list kentry := Eval vm_compute in kn_after rB1 knA.
Definition logB1 : list sentry := Eval vm_compute in s_log (fst (fst rB1)).
Definition pcB1 : Z := Eval vm_compute in s_pc (fst (fst rB1)).
Definition scsB1 := Eval vm_compute in snd (fst rB1).

