(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8 MI_GeomS8 KStepS8 MI_Pres4S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Bits.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Bridge Require Import BrResS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeEmptyS8 HeWNtfS8 HeMetaS8 HeWFreeS8 HeWSlotS8 HeWGrpS8 HeWMallocS8 HeResS8 HeIfaceS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMSTEP.
Context {RUNp : RunP}.

Theorem RES_malloc cs L BL LS nreq c n cs' p L' BL' LS' SZ K :
  INVC x0 cs L BL LS -> RES cs SZ K -> Permutation (map fst SZ) (map bslot BL) ->
  MQC cs LS nreq c n (cs', Some p) -> INVC x0 cs' L' BL' LS' -> map bslot BL' = p :: map bslot BL -> Z.of_nat (length BL') <= K ->
  RES cs' ((p, nreq) :: SZ) K /\ c <= Phi cs' - Phi cs /\ Z.of_nat n <= Psi cs' - Psi cs
  /\ Permutation (map fst ((p, nreq) :: SZ)) (map bslot BL')
  /\ (forall b m, hosts cs b m -> hosts cs' b m /\ GEOM (MR cs' m) = GEOM (MR cs m)).
Proof.
  intros INV [E0 NL0 L630 MA0 NM0] SZP MQ INV' EBL HK.
  assert (SZB : forall q k, In (q, k) SZ -> In q (map bslot BL)).
  { intros q k Hin. apply (Permutation_in _ SZP). apply in_map_iff. exists (q, k). auto. }
  destruct (malloc_end cs L BL LS nreq c n cs' p L' BL' LS' SZ INV E0 NL0 L630 SZB MQ INV' EBL) as (E1 & NL1 & L631 & MA1 & HC & HN & CARVE & OLD).
  split; [| split; [exact HC| split; [exact HN| split; [cbn; rewrite EBL; apply perm_skip; exact SZP| exact OLD]]]].
  constructor; [exact E1| exact NL1| exact L631| exact MA1|].
  destruct CARVE as [EQ|EMP]; [rewrite EQ; exact NM0|].
  pose proof INV' as (IR' & IA' & IM' & IL' & IG' & IS').
  assert (ALL : forall m, s_metas cs' !! m <> None -> m_mem (MR cs' m) <> None).
  { intros m Pm. destruct (NL1 m Pm) as [H|Nx]; [exact H|].
    destruct (proj2 (proj1 (il_link _ _ IL' m)) Nx) as [h Hh]. destruct h as [sc|]; [| rewrite EMP in Hh; destruct Hh].
    destruct (il_active _ _ IL' sc m Hh) as (_ & [b Hb] & _). rewrite (hosts_mem x0 cs' LS' IM' b m Hb). discriminate. }
  pose proof (nmeta_le_ngrp cs' L' BL' LS' INV' ALL). pose proof (ngrp_bound cs' L' BL' LS' INV' E1). unfold CM. lia.
Qed.

Theorem RES_free cs L BL LS cs' u nu L' BL' LS' SZ SZ' K :
  INVC x0 cs L BL LS -> RES cs SZ K -> FREL cs LS cs' u nu -> INVC x0 cs' L' BL' LS' ->
  (forall e, In e SZ' -> In e SZ) ->
  RES cs' SZ' K /\ Phi cs' = Phi cs - u /\ Psi cs' = Psi cs - Z.of_nat nu
  /\ (forall b m, hosts cs' b m -> hosts cs b m /\ GEOM (MR cs' m) = GEOM (MR cs m)).
Proof.
  intros INV [E0 NL0 L630 MA0 NM0] FR INV' SUB.
  destruct (free_end cs L BL LS cs' u nu L' BL' LS' SZ INV NL0 L630 MA0 FR INV') as (E1 & NL1 & L631 & MA1 & PH & PS & NM & OLD).
  split; [| split; [exact PH| split; [exact PS| exact OLD]]].
  constructor; [exact E1| exact NL1| exact (L631 SZ' SUB)| exact MA1| rewrite NM; exact NM0].
Qed.

Theorem RES_init secret resv K : 0 <= K -> RES (strip (minit secret resv)) [] K.
Proof.
  intros HK. constructor.
  - constructor; intros until 1; match goal with H : hosts _ _ _ |- _ => destruct H as [ai H]; cbn in H; rewrite lookup_empty in H; discriminate end.
  - intros m H. exfalso. apply H. cbn. apply lookup_empty.
  - intros c n m i [].
  - constructor; cbn.
    + lia.
    + unfold nareas. cbn. lia.
    + unfold nareas. cbn. lia.
    + unfold regsum. cbn. rewrite map_to_list_empty. cbn. unfold PGSZ. lia.
    + intros rid r H. rewrite lookup_empty in H. discriminate.
    + unfold nareas, nmeta. cbn [s_areas s_metas strip minit s_ctx c_avail_meta_count ctx0]. rewrite !map_size_empty. cbn. lia.
  - unfold nmeta, CM. cbn [s_metas strip minit]. rewrite map_size_empty. cbn. lia.
Qed.

Definition NAMAX (K : Z) : Z := (CM K + NSLOTS) / NSLOTS.

Lemma nareas_K cs L BL LS SZ K : INVC x0 cs L BL LS -> RES cs SZ K -> nareas cs <= NAMAX K.
Proof.
  intros INV R. unfold NAMAX. pose proof (nareas_bound cs L BL LS INV (rs_marith _ _ _ R)). pose proof (rs_nmeta _ _ _ R).
  apply Z.div_le_lower_bound; [unfold NSLOTS; lia| lia].
Qed.

Lemma cszR_csz n : cszR n = csz n.
Proof.
  unfold cszR, csz, IB, UNIT, mmap_len, State.page_round_up_Z. rewrite page_size_eq.
  replace (n + 4 + 16) with (n + 20) by lia. replace (n + 20 + 4096 - 1) with (n + 20 + 4095) by lia. reflexivity.
Qed.

End HMSTEP.
