(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac ITree Nodes SysStep Exec Decode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim Monad MSafeP STree Malloc MallocCtrl Prog KInv MI_Inv AllocTop MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMallocRep MallocSR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma reserved_top_ref : reserved_top (segments_reserved rsegs) = 0x311000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition ref_segments : list (Z * Z) := [(0x10000, 0xcd000); (0xdd000, 0x1a1000); (0x27e000, 0x5e000); (0x2dc000, 0x35000)].
Lemma segments_reserved_ref : segments_reserved rsegs = map (fun p => went (fst p) (snd p)) ref_segments.
Proof. vm_compute. reflexivity. Qed.
Lemma reservedZ_segments : reservedZ rsegs = ref_segments.
Proof. vm_compute. reflexivity. Qed.

Lemma mminv_init : forall tid brk mbase sp lim inp,
  mminv (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
Proof. intros. split; reflexivity. Qed.

Section HC.
Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Theorem KM_init : forall tid brk mbase sp lim inp,
  valid_brk rsegs brk -> valid_sp sp -> BUDCAP <= lim ->
  bv_unsigned sp - stack_max_size = hceil ->
  KM (ps_init (reservedZ rsegs)) (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
Proof.
  intros tid brk mbase sp lim inp (VB1 & VB2 & VB3) VSP LIM HSP.
  rewrite reserved_top_ref in VB1, VB2. unfold brk_aslr_max in VB2. rewrite page_size_eq in VB3.
  pose proof (alloc_top_range sp VSP) as TR. rewrite HSP in TR.
  assert (AT : alloc_top (m_vmmaps (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) = hceil).
  { rewrite alloc_top_with_tid, alloc_top_init. exact HSP. }
  hcb. hsb.
  exists (led_init (rband hceil :: reservedZ rsegs)). split; [| split].
  - unfold ps_init. cbn [ps_m]. apply hreach_init. lia.
  - constructor; rewrite ?AT, ?m_vmmaps_with_tid, ?m_vmmaps_init_model.
    all: cbn [vm_maps vm_noaccess vm_reserved vm_start_brk vm_brk vm_limit ld_groups ld_metas ld_brk ld_brkreg ld_resv led_init ps_brk ps_init].
    + apply mminv_init.
    + autorewrite with model. reflexivity.
    + split; [intros e []| constructor].
    + intros e [].
    + rewrite reservedZ_segments, segments_reserved_ref. reflexivity.
    + exact TR.
    + reflexivity.
    + intros e Hin. rewrite segments_reserved_ref in Hin. unfold ref_segments in Hin. cbn [map fst snd] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; rewrite ehi_went; lia.
    + intros e Hin. rewrite segments_reserved_ref in Hin. unfold ref_segments in Hin. cbn [map fst snd] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; rewrite elo_went, ehi_went; lia.
    + rewrite segments_reserved_ref. cbn. lia.
    + rewrite PGSZ_eq. unfold CEIL_MIN in TR. lia.
    + intros b l [].
    + intros b l k [].
    + constructor.
    + intros b l H. discriminate H.
    + split; reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold BUDCAP in *. lia.
  - unfold BUD. rewrite ?m_vmmaps_with_tid, ?m_vmmaps_init_model. cbn [vm_limit].
    unfold BUDCAP, RESV_MAX, GRID_J in *. change (ltotal _) with 0. change (lcount _) with 0. lia.
Qed.

End HC.
