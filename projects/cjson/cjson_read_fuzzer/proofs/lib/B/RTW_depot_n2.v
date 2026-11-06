(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma LINV_mem_ext : forall g mo mat (m1 m2 mr : word -> option byte),
  (forall x, m1 x = m2 x) -> LINV bsegs g mo mat m2 mr -> LINV bsegs g mo mat m1 mr.
Proof.
  intros g mo mat m1 m2 mr E (A & B & [MG HID] & [MT VD]).
  split; [exact A|]. split; [exact B|]. split; [split|split; [exact MT|]].
  - intros x. unfold lmem. rewrite (E x). exact (MG x).
  - intros x H1 H2. rewrite (E x). exact (HID x H1 H2).
  - intros x Hx. apply VD. rewrite <- (E x). exact Hx.
Qed.

Lemma lscps_mem_ext : forall (P : machine_state -> Model -> lghost -> Prop) ms (m1 m2 : word -> option byte) mo g,
  (forall x, m1 x = m2 x) -> LSCPS bsegs P (msw ms m1) mo g -> LSCPS bsegs P (msw ms m2) mo g.
Proof.
  intros P ms m1 m2 mo g E H mr mat HI T K. cbn [ms_mem msw] in HI.
  pose proof (LINV_mem_ext _ _ _ m1 m2 mr E HI) as HI'.
  exact (H mr mat HI' T K).
Qed.

(* [comment removed for export] *)
Lemma lzf_add_lazy : forall mo (a : word) n x, LOK bsegs mo ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n) = true ->
  0 <= n < 2^64 ->
  lzf (mm_add_lazy a (Z_to_bv 64 n) mo) x = (in_range (bv_unsigned a) n x || lzf mo x)%bool.
Proof.
  intros mo a n x HO C4 Hn.
  assert (Hun : bv_unsigned (Z_to_bv 64 n : word) = n) by (apply unsigned_lit; lia).
  unfold lzf. rewrite mm_add_lazy_lazy, mm_add_lazy_vmmaps, mm_add_map_vmmaps.
  cbn [vm_noaccess in_rangesb existsb fst snd]. fold (in_rangesb (m_vm_lazy mo) x). fold (in_rangesb (vm_noaccess (m_vmmaps mo)) x).
  rewrite Hun. unfold in_range.
  destruct (Z.leb_spec0 (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (bv_unsigned a + n)); cbn [andb orb];
    try reflexivity.
  destruct (in_rangesb (vm_noaccess (m_vmmaps mo)) x) eqn:Ena; [| reflexivity]. exfalso.
  pose proof (lok_na_maps _ _ HO x Ena) as Hmx. apply in_rangesb_true in Hmx as (b & k & Hin & Hbx).
  assert (Hfm : region_free (vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n) = true).
  { rewrite region_free_app in C4. apply andb_true_iff in C4. exact (proj2 C4). }
  eapply (region_free_false_of _ a (Z_to_bv 64 n) b k x Hfm Hin); [rewrite Hun; lia| exact Hbx].
Qed.

Definition N2OPEN_stmt : Prop :=
  forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R len,
  at_node bsegs (NMmap 0 len mm_prot_rw mm_flags_anon_nr) ms ->
  0 < len -> len + 4096 <= 2^64 ->
  page_round_up_Z len <= R ->
  mmap_placeable mo (page_round_up_Z len) ->
  (forall e, In e mmap_errnos -> evt bsegs (jself bsegs) (nret ms (efferr e))) ->
  (forall a : word, mmap_grant mo a (page_round_up_Z len) ->
     LSCPS bsegs P (nret ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]))
           (mm_add_lazy a (Z_to_bv 64 (page_round_up_Z len)) mo)
           (mkG ((bv_unsigned a, bv_unsigned a + page_round_up_Z len) :: G) (R - page_round_up_Z len))) ->
  LSCPS bsegs P ms mo (mkG G R).

Theorem n2open_proof : N2OPEN_stmt.
Proof.
  intros P ms mo G R len HA Hlen0 Hlen1 HnR HPL Href Hgrant.
  set (n := page_round_up_Z len) in *.
  assert (Hn : len <= n /\ n mod 4096 = 0 /\ n < len + 4096).
  { subst n. unfold page_round_up_Z. rewrite page_size_eq. Z.div_mod_to_equations. lia. }
  apply lscps_assume. intros NWX HOK HBINV.
  eapply lscps_mmap_rw_nr_spin2; [exact HA| exact Hlen0| exact Hlen1| exact HPL| exact Href|].
  intros a GR. fold n in GR |- *.
  pose proof GR as (GA & GP & GC & GF). rewrite page_size_eq in GA.
  pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA. ceilb.
  eapply lscps_open with (lo := bv_unsigned a) (hi := bv_unsigned a + n).
  { unfold win_ok. cbn [fst snd]. repeat split; first [lia | Z.div_mod_to_equations; lia]. }
  { cbn [g_res]. replace (bv_unsigned a + n - bv_unsigned a) with n by lia. Z.div_mod_to_equations. nia. }
  intros mv' Emv' ZNS FRESH. cbn [g_win g_res ms_mem msw] in *.
  replace (R - 4096 * ((bv_unsigned a + n - bv_unsigned a) / 4096)) with (R - n).
  2:{ replace (bv_unsigned a + n - bv_unsigned a) with n by lia. Z.div_mod_to_equations. nia. }
  (* [comment removed for export] *)
  match goal with |- LSCPS _ _ (msw (msw ?X _) _) _ _ => change (msw (msw X (reveal0 G (bv_unsigned a) n (ms_mem ms))) mv') with (msw X mv') end.
  apply (lscps_mem_ext P _ (apply_zeros (ms_mem ms) [(a, Z_to_bv 64 n)]) mv').
  { intros x.
    rewrite <- (Z_to_bv_bv_unsigned a) at 1. change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
    rewrite apply_zeros_spec by lia.
    destruct (in_range (bv_unsigned a) n x) eqn:IR.
    - destruct (in_winb G x) eqn:IW.
      + rewrite Emv'. symmetry. apply open_mem_some. apply reveal0_win; assumption.
      + rewrite (FRESH x); [reflexivity| | | exact IW].
        * unfold in_range in IR. apply andb_true_iff in IR as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. lia.
        * rewrite (lzf_add_lazy mo a n x HOK GF) by lia. rewrite IR. reflexivity.
    - rewrite Emv'. unfold open_mem. rewrite (reveal0_out G _ _ _ x IR).
      destruct (ms_mem ms x); [reflexivity|].
      unfold in_range in IR. rewrite IR. reflexivity. }
  rewrite <- (mem_nret_zeros ms a), msw_nret_self.
  exact (Hgrant a GR).
Qed.


End CeilWrap.
