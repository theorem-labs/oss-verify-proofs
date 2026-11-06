(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u Qc6I QJFf QCiC Qpj5 QvDJ Q6sh QKTr QzgH QlES QCrt QBzu Qsn5 QBrp Q6q3 QZzg QFQR QWRO Q5bV QKBN QNQk Qu3b QUYN QdWK QzRg Q6iK QtQx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u Qc6I QJFf.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 QCiC.Mq0 Q6sh QKTr QzgH.
Import QlES.
Import QCrt.
Import QBzu.

Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module AHI := QtQx.Mq0.

Section T2.
Context {RC__ : Q6q3.RunConsts}.
Variable guard : word.
Variable LV : Qsn5.lvp.
Notation asegs := QZzg.asegs.
Notation BANDj := (Band_RC guard).

Definition jo_SD : Z := 0x4fdd8.
Definition jo_SD_stack : Z := 3312.
Definition jo_RL : Z := 0x636a8.
Definition jo_RL_stack : Z := 3376.

Lemma DT2_jo :
forall (OBL_RT_REPLACE_STR : ltac:(let T := type of (@AHI.strdup_jo BANDj LV) in match T with ?A -> _ => exact A end))
(OBL_RT_GOT_MEMCPY : ltac:(let T := type of (@AHI.realloc_jo BANDj LV) in match T with ?A -> _ => exact A end))
(OBL_MEMCPY : ltac:(let T := type of (@AHI.realloc_jo BANDj LV) in match T with _ -> ?A -> _ => exact A end)),
donor_t2 Q6q3.alloc_ceiling asegs (QBrp.at_nodeA LV asegs) (@DL_AR BANDj) (DCo_jo guard LV) jo_SD jo_SD_stack jo_RL jo_RL_stack.
Proof.
intros H1 H2 H3. constructor.
- intros L. unfold astrdupA_stmt. intros.
eapply (@AHI.strdup_jo BANDj LV H1 H2 H3 L) with (RE := toRA RE); eassumption.
- intros L. unfold areallocA_stmt. intros.
eapply (@AHI.realloc_jo BANDj LV H2 H3 L) with (RE := toRA RE); eassumption.
Qed.

Lemma DT2_jo_closed :
donor_t2 Q6q3.alloc_ceiling asegs (QBrp.at_nodeA LV asegs) (@DL_AR BANDj) (DCo_jo guard LV) jo_SD jo_SD_stack jo_RL jo_RL_stack.
Proof.
apply DT2_jo.
- exact (@QNQk.Mq5.rt_replace_str BANDj).
- exact (@QNQk.Mq5.rt_got_memcpy BANDj).
- intros. eapply evt_mono; [eapply Qu3b.Mq5.memcpy_spec; eassumption| intros ms' Hpost; exact Hpost].
Qed.
End T2.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuLP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuLP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5bV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUYN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdWK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzRg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6iK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtQx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module AHI := QtQx.

Section T2.
Context {RC__ : Q6q3.RunConsts}.
Variable guard : word.
Variable LV : Qsn5.lvp.
Notation asegs := QvG1.asegs.
Notation BANDj := (Band_RC guard).

Definition jo_SD : Z := 0x4fa00.
Definition jo_SD_stack : Z := 3312.
Definition jo_RL : Z := 0x632d0.
Definition jo_RL_stack : Z := 3376.

Lemma DT2_jo :
forall (OBL_RT_REPLACE_STR : ltac:(let T := type of (@AHI.strdup_jo BANDj LV) in match T with ?A -> _ => exact A end))
(OBL_RT_GOT_MEMCPY : ltac:(let T := type of (@AHI.realloc_jo BANDj LV) in match T with ?A -> _ => exact A end))
(OBL_MEMCPY : ltac:(let T := type of (@AHI.realloc_jo BANDj LV) in match T with _ -> ?A -> _ => exact A end)),
donor_t2 Q6q3.alloc_ceiling asegs (QBrp.at_nodeA LV asegs) (@DL_AR BANDj) (DCo_jo guard LV) jo_SD jo_SD_stack jo_RL jo_RL_stack.
Proof.
intros H1 H2 H3. constructor.
- intros L. unfold astrdupA_stmt. intros.
eapply (@AHI.strdup_jo BANDj LV H1 H2 H3 L) with (RE := toRA RE); eassumption.
- intros L. unfold areallocA_stmt. intros.
eapply (@AHI.realloc_jo BANDj LV H2 H3 L) with (RE := toRA RE); eassumption.
Qed.

Lemma DT2_jo_closed :
donor_t2 Q6q3.alloc_ceiling asegs (QBrp.at_nodeA LV asegs) (@DL_AR BANDj) (DCo_jo guard LV) jo_SD jo_SD_stack jo_RL jo_RL_stack.
Proof.
apply DT2_jo.
- exact (@QNQk.Mq0.rt_replace_str BANDj).
- exact (@QNQk.Mq0.rt_got_memcpy BANDj).
- intros. eapply evt_mono; [eapply Qu3b.Mq1.memcpy_spec; eassumption| intros ms' Hpost; exact Hpost].
Qed.
End T2.
