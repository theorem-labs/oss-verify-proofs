(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AQPart.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WfRecp.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (reg : Z -> region) (cache : Z -> pcache) (c0 k0 fa' : Z) (na : Z).   (* [comment removed for export] *)
  Let ks := pk_chunks (cache c0).
  Let pr := cache_push_list ks (max_count c0) k0.
  Hypothesis WC : wf_caches_ reg cache true.
  Hypothesis WR : wf_region c0 (reg c0) na.
  Hypothesis Hc0 : 1 <= c0 <= 30.
  Hypothesis Hk0 : 0 <= k0 < carved_count_ reg c0.
  Hypothesis NK : ~ In k0 ks.
  (* [comment removed for export] *)
  Hypothesis NF : ~ In k0 (rg_free (reg c0)).
  (* [comment removed for export] *)
  Hypothesis CF : forall k, In k ks -> ~ In k (rg_free (reg c0)).
  Hypothesis MC2 : 2 <= max_count c0 /\ max_count c0 mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis FA : Z.of_nat (length ks) = max_count c0 ->
    4 * (Z.of_nat (length (rg_free (reg c0))) + max_count c0 / 2) <= fa' /\ rg_mapped_fa (reg c0) <= fa' /\
    fa' <= kFreeArraySize /\ fa' mod kFreeArrayMapSize = 0 /\
    fa' <= 4 * (rg_allocated_user (reg c0) / class_size c0) + kFreeArrayMapSize (* [comment removed for export] *) /\ (rg_mapped_user (reg c0) = 0 -> False).

  (* [comment removed for export] *)
  Lemma half_facts : exists hq, max_count c0 = 2 * hq /\ 1 <= hq /\ max_count c0 / 2 = hq /\ Z.of_nat (Z.to_nat hq) = hq.
  Proof.
    destruct MC2 as [M2 MM]. exists (max_count c0 / 2).
    pose proof (Z_div_mod_eq_full (max_count c0) 2) as E. rewrite MM in E.
    split; [lia|]. split; [lia|]. split; [reflexivity|]. apply Z2Nat.id. lia.
  Qed.

  Lemma wf_caches_recp : wf_caches_ (recp_reg reg cache c0 k0 fa') (recp_cache cache c0 k0) true.
  Proof.
    destruct half_facts as (hq & MH & H1 & HD & HN).
    assert (CC : forall c, carved_count_ (recp_reg reg cache c0 k0 fa') c = carved_count_ reg c) by (intros; apply recp_carved).
    destruct WC as (W1 & W31 & W0). destruct (W1 c0 ltac:(lia)) as (L & ND & RG & _). cbv zeta in *. fold ks in L, ND, RG.
    unfold recp_cache. split; [| split; [unfold cache_set; destruct (Z.eqb_spec 31 c0); [lia| exact W31] | unfold cache_set; destruct (Z.eqb_spec 0 c0); [lia| exact W0]]].
    intros c Hc. unfold cache_set. destruct (Z.eqb_spec c c0) as [->|NE]; cbn [pk_chunks].
    - cbv zeta. fold ks. fold pr.
      destruct (recp_nodup cache c0 k0 ND NK) as [ND1 _]. fold ks pr in ND1.
      split; [| split; [exact ND1| split; [| intros X; discriminate X]]].
      + subst pr. unfold cache_push_list. rewrite HD. destruct (Z.eqb_spec (Z.of_nat (length ks)) (max_count c0)) as [E|NE2]; cbn [fst].
        * assert (HL : (Z.to_nat hq <= length ks)%nat) by (try (generalize alloc_ceiling_val); clear - E MH H1 HN; lia).
          rewrite length_app, (drain_keep_length ks (Z.to_nat hq) HL). cbn [length]. try (generalize alloc_ceiling_val); clear - E MH HN HL H1. lia.
        * rewrite length_app. cbn [length]. try (generalize alloc_ceiling_val); clear - NE2 L. lia.
      + intros k Hk. rewrite CC. destruct (proj1 (recp_in cache c0 k0 k) (or_introl Hk)) as [H| ->]; [exact (RG k H)| exact Hk0].
    - rewrite CC. exact (W1 c Hc).
  Qed.

  Lemma wf_region_recp : wf_region c0 (recp_reg reg cache c0 k0 fa' c0) na.
  Proof.
    destruct half_facts as (hq & MH & H1 & HD & HN).
    unfold recp_reg. fold ks. destruct (Z.eqb_spec (Z.of_nat (length ks)) (max_count c0)) as [E|NE]; [| exact WR].
    unfold reg_set. rewrite Z.eqb_refl. destruct (FA E) as (F1 & F2 & F3 & F4 & F5 & F6). rewrite HD in F1.
    destruct WR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    destruct WC as (W1 & _ & _). destruct (W1 c0 ltac:(lia)) as (L & ND & RG & _). cbv zeta in *. fold ks in L, ND, RG.
    unfold wf_region, reg_return; cbn [rg_mapped_user rg_allocated_user rg_mapped_fa rg_free].
    unfold cache_push_list. rewrite (proj2 (Z.eqb_eq _ _) E). cbn [snd]. rewrite HD.
    assert (HL : (Z.to_nat hq <= length ks)%nat) by (try (generalize alloc_ceiling_val); clear - E MH H1 HN; lia).
    pose proof (drain_out_length ks (Z.to_nat hq) HL) as OL.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [try (generalize alloc_ceiling_val); clear - F2 F3 R5; lia|]. split; [exact F4|].
    split; [| split; [| split; [| split; [| split; [exact R11| exact F5]]]]].
    - rewrite length_app, OL. try (generalize alloc_ceiling_val); clear - F1 HN H1. lia.
    - destruct (drain_nodup ks (Z.to_nat hq) ND) as (_ & N2 & _).
      apply (proj2 (list.NoDup_app _ _)). split; [exact R8|]. split; [| exact N2].
      intros x Hx Ho. apply list_elem_of_In in Hx. apply list_elem_of_In in Ho.
      apply (CF x); [| exact Hx]. apply (drain_in_iff ks (Z.to_nat hq)). right. exact Ho.
    - intros k Hk. apply in_app_iff in Hk as [Hk|Hk]; [exact (R9 k Hk)|].
      apply (RG k). apply (drain_in_iff ks (Z.to_nat hq)). right. exact Hk.
    - intros Z0. exfalso. exact (F6 Z0).
  Qed.
End WfRecp.
