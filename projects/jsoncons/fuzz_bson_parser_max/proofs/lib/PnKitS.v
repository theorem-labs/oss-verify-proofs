(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PnLayoutS PmModel PmStatics PmSpecs PnSpecsS PmStep PmKeep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMKS.
Import PMS.
Section K.
Variable L : heap_layout.
Hypothesis LY : PMS.layout L.

Lemma klayout_S : PMK.klayout RSEGS L.
Proof.
  constructor.
  - exact (ly_segs L LY).
  - exact (ly_ro L LY).
  - rewrite (ly_img_lo L LY), (ly_img_hi L LY). lia.
  - rewrite (ly_img_lo L LY), (ly_img_hi L LY), (ly_errno L LY). lia.
Qed.

(* [comment removed for export] *)
Lemma cstatic_S a : (0x10000 <= a < 0xc893c \/ 0xc8940 <= a < 0xe8de8) -> PMKP.cstatic L a.
Proof.
  intros H. unfold PMKP.cstatic, in_errno. rewrite (ly_img_lo L LY), (ly_img_hi L LY), (ly_errno L LY).
  split; [lia|]. split; [|lia]. intros S. apply (ly_static L LY) in S. lia.
Qed.

Lemma sfoot_S : PMKP.sfoot AD L.
Proof.
  constructor.
  - exact addrs_wf_S.
  - intros a Ha. apply cstatic_S. cbn in Ha. lia.
  - intros iv a Hin Hr. apply cstatic_S. unfold pm_foot in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia.
  - intros a Ha. apply cstatic_S. cbn in Ha. lia.
  - intros iv a Hin Hr. apply cstatic_S. cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia.
Qed.

(* [comment removed for export] *)
Lemma cwr_foot_S LB iv a : In iv (pm_foot AD) -> fst iv <= a < snd iv -> PMK.cwr L LB a.
Proof.
  intros Hin Hr. right. right. assert (Ha : 0xb6e08 <= a < 0xe8c48).
  { unfold pm_foot in Hin. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }
  rewrite (ly_img_lo L LY), (ly_img_hi L LY). split; [lia|]. split.
  - intros S. apply (ly_static L LY) in S. lia.
  - intros S. apply (ly_ro_foot L LY a S). exact Ha.
Qed.
End K.
End PMKS.
