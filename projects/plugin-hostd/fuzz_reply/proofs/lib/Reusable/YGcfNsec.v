(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfNsec.v, sha256 02dcfe855f9116d7cf6331ccc466eadea98f12c2902a9fb354f740dab4b2bda5 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: the five lemmas are derived from YGcfSecsStep.v's posts through cfx_ipost_of_ipost. *)
(* Theorem Labs, 2026-10-30: the model-level step lemmas for nsec_cf (YG0ncf.v), the number of USER st_secs entries
   (sec_user_cf, YGcfNames.v: 0 <= sm_size), on every path of the cf model's operations, in YGcfXs.v's cfx_ipost form:
   - nsec_malloc_cf: malloc_cf adds at most one user entry, and none when the request is primary (from_primary);
   - nsec_free_cf: free_cf adds none;
   - nsec_errb_append_cf / nsec_errb_report_cf: the errbuf steps keep it exactly (they append, re-tag or update in
     place only CONTROL entries, whose sm_size is negative: YG00cf.v:57-65);
   - nsec_sec_alloc_cf: cgif's sec_alloc appends one entry, so at most one more.
   ONE proof per fact (Main 2026-10-30): the paths are walked once, by preset row A14's YGcfSecsStep.v over YGcfAmx.v's
   ipost (secs_malloc, secs_free, secs_errb_append, secs_errb_report, secs_sec_alloc_entry, which state both counts
   nsec_cf and sec_T_cf). ipost and cfx_ipost are the same fixpoint (YGcfXs.v restates YGcfAmx.v's), so
   cfx_ipost_of_ipost bridges them and each lemma below is A14's post through that bridge. YGcfCount.v states the
   same counts over the state shapes only. No function is proved here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YGcfNames YG00cf YG0ncf YGcfXs YGcfAmx
YGcfCount YGcfSecsStep.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The bridge: YGcfAmx.v's ipost gives YGcfXs.v's cfx_ipost (the same fixpoint). *)
Lemma cfx_ipost_of_ipost {A : Type} : forall (t : itree astate A) (P : A -> Prop), ipost t P -> cfx_ipost t P.
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [ipost cfx_ipost]; intros P H.
- exact H.
- intros z. exact (IH z P (H z)).
- exact I.
- exact I.
Qed.

Section N. Context {ci : CfImg}.

Lemma nsec_malloc_cf : forall n tr s,
cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Proof.
intros n tr s. apply cfx_ipost_of_ipost. eapply ipost_mono; [|exact (secs_malloc n tr s)].
intros [q s'] H. unfold secs_call_post, secs_step in H. cbn [fst snd] in H |- *. destruct H as [HN _].
unfold secs_call_d in HN. destruct q; destruct (from_primary n); lia.
Qed.

Lemma nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
Proof.
intros p tr s. apply cfx_ipost_of_ipost. eapply ipost_mono; [|exact (secs_free p tr s)].
intros r [HN _]. lia.
Qed.

Lemma nsec_errb_append_cf : forall len s, cfx_ipost (errb_append_cf len s) (fun r => nsec_cf (snd r) = nsec_cf s).
Proof.
intros len s. apply cfx_ipost_of_ipost. eapply ipost_mono; [|exact (secs_errb_append len s)].
intros r [HN _]. exact HN.
Qed.

Lemma nsec_errb_report_cf : forall c s, cfx_ipost (errb_report_cf c s) (fun r => nsec_cf (snd r) = nsec_cf s).
Proof.
intros c s. apply cfx_ipost_of_ipost. eapply ipost_mono; [|exact (secs_errb_report c s)].
intros r [HN _]. exact HN.
Qed.

Lemma nsec_sec_alloc_cf : forall n s, cfx_ipost (sec_alloc n s) (fun r => nsec_cf (snd r) <= nsec_cf s + 1).
Proof.
intros n s. apply cfx_ipost_of_ipost. eapply ipost_mono; [|exact (secs_sec_alloc_entry n s)].
intros r [[_ E] | [_ E]]; unfold nsec_cf; rewrite E; [lia|].
rewrite (cfa_fold_app1 (fun sm acc => (if sec_user_cf sm then 1 else 0) + acc) (fun sm => if sec_user_cf sm then 1 else 0))
  by (intros; reflexivity).
cbv beta. destruct (sec_user_cf _); lia.
Qed.

(* The count at the start state: init_state has no st_secs entry (YG00.v:169-171). *)
Lemma nsec_cf_init : nsec_cf init_state = 0.
Proof. reflexivity. Qed.

End N.
