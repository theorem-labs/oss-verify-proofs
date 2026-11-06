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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkRc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyuL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyuL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOnw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOnw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Q5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Q5.Mq0.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma KL_model_ok : forall L pbrk md, KL L pbrk md -> model_ok md.
Proof. intros L pbrk md HK. split; [exact (kl_halt _ _ _ HK)| exact (kl_lazy _ _ _ HK)]. Qed.

#[using="Type"] Lemma reserved_top_ge : forall maps e, In e maps -> ehi e <= reserved_top maps.
Proof.
induction maps as [|[a sz] maps IH]; intros e Hin; [destruct Hin|].
cbn [reserved_top]. destruct Hin as [<-|Hin]; [rewrite ehi_pair; lia|]. pose proof (IH e Hin). lia.
Qed.

#[using="Type"] Lemma KL_init : forall md pbrk,
m_halted md = None -> m_vm_lazy md = [] ->
vm_maps (m_vmmaps md) = [] -> vm_noaccess (m_vmmaps md) = [] ->
vm_brk (m_vmmaps md) = vm_start_brk (m_vmmaps md) ->
reserved_top (vm_reserved (m_vmmaps md)) <= bv_unsigned (vm_start_brk (m_vmmaps md)) ->
0 < bv_unsigned (vm_start_brk (m_vmmaps md)) ->
bv_unsigned (vm_start_brk (m_vmmaps md)) mod PGSZ = 0 ->
bv_unsigned (vm_start_brk (m_vmmaps md)) + 4 * PGSZ <= alloc_ceiling ->
alloc_top (m_vmmaps md) = alloc_ceiling ->
KL (led_init (map wwZ (vm_reserved (m_vmmaps md)))) pbrk md.
Proof.
intros md pbrk Hh Hl Hm Hn Hb Htop S1 S2 S4 Hceil. pose proof alloc_ceiling_small as Hcl.
pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps md))) as R. unfold bv_modulus in R.
constructor; cbn [led_init ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?Hm, ?Hn; auto.
- split; [intros e []| constructor].
- intros e He. pose proof (reserved_top_ge _ _ He). change (2 ^ Z.of_N 64) with (2^64) in R. lia.
- intros e He. pose proof (reserved_top_ge _ _ He). lia.
- rewrite Hb. splits; auto; lia.
- intros b l [].
- intros b l k [].
- constructor.
- intros e [].
- intros b l E. discriminate.
Qed.

Section Link.
Variable segs : list Segment.

#[using="Type"] Theorem ev_ok : EV_OK segs KL vm_only.
Proof.
intros e L pbrk md ms1 J KE HJ HK PRE HAT HC.
destruct e as [req|a len prot flags|a len|a len prot|p c h|w|a ol nl fl]; cbn in KE; try discriminate; cbn in PRE; unfold ev_at in HAT; cbn [ev_node] in HAT.
-
destruct PRE as [[-> Hph] | [(cur & Hph & Hreq) | (b & l & Hph & Hreg & Hreq)]].
+ eapply ev1_brk0; eauto.
+ eapply ev1_brk_grow1; eauto.
+ eapply ev1_brk_grow2; eauto.
-
destruct PRE as [(Hq & -> & -> & Hprot & Hlen) | (cur & Hph & -> & -> & -> & ->)].
+ eapply ev1_mmap_anon; eauto.
+ eapply ev1_mmap_fixed; eauto.
-
destruct PRE as (Hq & l & Hin & Hlen). eapply ev1_munmap; eauto.
-
destruct PRE as (Hq & -> & -> & b & l & k & Hin & Ha & Hk). eapply ev1_mprotect; eauto.
-
destruct PRE as (Hq & Hfl & Hnl & Hal & l & Hin & Hol & Hne). eapply ev1_mremap; eauto.
Qed.

Definition membed_realizes_KL {R : Type} :=
@membed_realizes RC__ segs KL vm_only vm_only_refl vm_only_trans KL_model_ok ev_ok R.

End Link.

End RC__1.
