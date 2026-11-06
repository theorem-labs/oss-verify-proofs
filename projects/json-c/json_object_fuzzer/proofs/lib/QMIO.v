(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkRc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkRc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qh1B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qh1B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Q5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Q5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMt2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMt2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Link.
Variable segs : list Segment.

#[using="Type"] Theorem evn : EVN segs KL vm_only FEAS (fun e => ACC (ecost e)).
Proof.
intros e L pbrk md ms1 EK HK PRE HAT.
destruct e as [req|a len prot flags|a len|a len prot|p c h|w|a ol nl fl]; cbn in EK; try discriminate; cbn in PRE; unfold ev_at in HAT; cbn [ev_node] in HAT.
-
destruct PRE as [[-> Hph] | [(cur & Hph & Hreq) | (b & l & Hph & Hreg & Hreq)]].
+ eapply evn_brk0; eauto.
+ eapply evn_brk_grow1; eauto.
+ eapply evn_brk_grow2; eauto.
-
destruct PRE as [(Hq & -> & -> & Hprot & Hlen) | (cur & Hph & -> & -> & -> & ->)].
+ eapply evn_mmap_anon; eauto.
+ eapply evn_mmap_fixed; eauto.
-
destruct PRE as (Hq & l & Hin & Hlen). eapply evn_munmap; eauto.
-
destruct PRE as (Hq & -> & -> & b & l & k & Hin & Ha & Hk). eapply evn_mprotect; eauto.
Qed.

Definition membed_realizes_strong_KL {R : Type} (isS : R -> bool) (P : R -> Prop) (Wf : Z) (Df : nat) :=
@membed_realizes_strong RC__ segs KL vm_only vm_only_refl vm_only_trans KL_model_ok
BUD FEAS (fun e => ACC (ecost e)) BUD_feas BUD_step BUD_mono evn R isS P Wf Df.

End Link.

End RC__1.
