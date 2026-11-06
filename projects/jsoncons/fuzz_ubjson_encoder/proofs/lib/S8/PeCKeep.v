(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStep PmKeep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECKP.
Section Keep.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable EE : pe_addrs.
Variable L : heap_layout.
Hypothesis KL : PMK.klayout segs L.
Hypothesis SF : PMKP.sfoot A L.
Variables (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LB sp scr W M M'.

Lemma err_ok_keep b : (forall a, pa_errcat_guard A <= a < pa_errcat_guard A + 2 -> L5.outside W a) ->
  (forall a, pa_atexit A <= a < pa_atexit A + 544 -> L5.outside W a) ->
  PEST.err_ok segs A EE M b -> PEST.err_ok segs A EE M' b.
Proof.
  intros OG OA (G & AT). pose proof (PMST.aw_errg A (PMKP.sf_wf A L SF)) as Hg. pose proof (PMST.aw_atexit A (PMKP.sf_wf A L SF)) as Ha.
  assert (CG : forall i, pa_errcat_guard A <= i < pa_errcat_guard A + 2 -> PMKP.cstatic L i /\ L5.outside W i).
  { intros i Hi. split; [|apply OG; exact Hi]. apply (PMKP.sf_foot A L SF (pa_errcat_guard A, pa_errcat_guard A + 2)); [|cbn; lia]. unfold pm_foot. cbn. auto. }
  assert (CA : forall i, pa_atexit A <= i < pa_atexit A + 544 -> PMKP.cstatic L i /\ L5.outside W i).
  { intros i Hi. split; [|apply OA; exact Hi]. apply (PMKP.sf_foot A L SF (pa_atexit A, pa_atexit A + 544)); [|cbn; lia].
    unfold pm_foot. cbn [app]. right. right. apply in_or_app. right. cbn. auto. }
  split.
  - destruct b.
    + apply (L5C.u8_at_agree segs M M'); [|lia|lia|exact G]. apply (PMKP.agree_st segs L KL LB sp scr W M M' E). intros i Hi. apply CG. lia.
    + apply (PMKP.clear_agree M M' _ _); [|exact G]. apply (PMKP.agree_st segs L KL LB sp scr W M M' E). intros i Hi. apply CG. lia.
  - apply (PEST.atexit_agree segs A EE (PMKP.sf_wf A L SF) M M'); [|exact AT]. intros i Hi.
    apply (PMKP.agree_st segs L KL LB sp scr W M M' E (pa_atexit A) 544); [exact CA| lia].
Qed.
End Keep.
End PECKP.
