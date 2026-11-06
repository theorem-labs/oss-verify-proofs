(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Export ACells.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Wfp.
Context {Clg : Ceiling}.
  Variable L : alayout.
  Definition wf_dk1 (P : aplace) : Prop := Forall (fun k => (1 <= length k <= 255)%nat) (p_dkeys P).
  Definition wf_dk2 (P : aplace) : Prop := NoDup (map depot_hashC (p_dkeys P)).
  Definition wf_dk3 (P : aplace) : Prop := (length (p_dkeys P) <= 2048)%nat.
  Lemma wf_place_cheap : forall P, wf_place L P ->
    0 <= p_b6 P /\ kHighMemBeg <= p_b6 P /\ p_sb P = space_beg_of (p_b6 P) /\ p_sb P + kSpaceSize + 4096 <= alloc_ceiling /\
    app_rangeA L (p_pa P) kPtrArrayReserve /\ p_pa P + kPtrArrayReserve <= alloc_ceiling /\ p_pa P mod 4096 = 0 /\ app_rangeA L (p_thr P) 4096 /\
    p_thr P + 4096 <= alloc_ceiling /\ p_thr P mod 4096 = 0 /\ app_rangeA L (p_ctx P) 0x10000 /\ p_ctx P + 0x10000 <= alloc_ceiling /\
    p_ctx P mod 4096 = 0 /\ app_rangeA L (p_nodes0 P) kDepotNodesBlock /\ p_nodes0 P + kDepotNodesBlock <= alloc_ceiling /\
    p_nodes0 P mod 4096 = 0 /\ app_rangeA L (p_frames0 P) kStackStoreBlockBytes /\ p_frames0 P + kStackStoreBlockBytes <= alloc_ceiling /\
    p_frames0 P mod 4096 = 0 /\ app_rangeA L (p_fs P) kFakeStackBytes /\ p_fs P + kFakeStackBytes <= alloc_ceiling /\ p_fs P mod 4096 = 0 /\
    app_rangeA L (p_itab P) 0x38e000 /\ p_itab P + 0x38e000 <= alloc_ceiling /\ p_itab P mod 4096 = 0 /\ app_rangeA L (p_m64k P) 0x10000 /\
    p_m64k P + 0x10000 <= alloc_ceiling /\ p_m64k P mod 4096 = 0 /\ app_rangeA L (p_gvec P) 4096 /\ p_gvec P + 4096 <= alloc_ceiling /\
    p_gvec P mod 4096 = 0 /\ app_rangeA L (p_dvec P) 4096 /\ p_dvec P + 4096 <= alloc_ceiling /\ p_dvec P mod 4096 = 0 /\
    app_rangeA L (p_m11 P) 4096 /\ p_m11 P + 4096 <= alloc_ceiling /\ p_m11 P mod 4096 = 0 /\ app_rangeA L (p_dtls P) 4096 /\
    p_dtls P + 4096 <= alloc_ceiling /\ p_dtls P mod 4096 = 0 /\ 0 <= p_tlsb P < 2^64 /\ 0 <= p_tlse P < 2^64 /\ wf_dk1 P /\ wf_dk2 P /\ wf_dk3 P /\
    alloc_ceiling + 0x800000 <= p_sp0 P <= 2^47 /\ 0 <= p_stk_span P <= 0x240000 /\ p_sp0 P mod 16 = 0 /\ p_sp0 P + p_stk_span P <= 2^47 /\
    0 <= p_stk_top P < 2^64 /\ 0 <= p_stk_bot P < 2^64 /\ 0 <= p_eager0 P /\ p_eager0 P <= 2^25.
  Proof. intros P H. exact H. Qed.
  Lemma wf_place_dkeys : forall P, wf_place L P ->
    Forall (fun k => (1 <= length k <= 255)%nat) (p_dkeys P) /\
    NoDup (map depot_hashC (p_dkeys P)) /\
    (length (p_dkeys P) <= 2048)%nat.
  Proof.
    intros P H. apply wf_place_cheap in H.
    do 42 (destruct H as [_ H]). destruct H as (D1 & D2 & D3 & _). exact (conj D1 (conj D2 D3)).
  Qed.
End Wfp.
