(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PnLayout PnLayoutS PmModel PmStatics PmSpecs PnSpecsS
     PmStep PmKeep PnKitS PgSrc PnModel PnStatics PnKeep PnRun PnRunS PnOwnerOkS PnBrKit.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNBKS.
Import PMS.
Abbreviation AN := PnLayoutS.NADDR_S.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Lemma kh_S : PNBK.khyps RSEGS AD AN L HI.
Proof.
  constructor.
  - exact (PMKS.klayout_S L LY).
  - exact (PMKS.sfoot_S L LY).
  - exact PNRS.addrs_wf_B.
  - intros iv a Hin H. apply (PMKS.cstatic_S L LY). cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H; lia.
  - exact HIok.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros a Ha. rewrite (ly_img_lo L LY), (ly_img_hi L LY). unfold PNBK.bdom in Ha. cbn in Ha. lia.
  - intros a Ha. rewrite (ly_img_lo L LY), (ly_img_hi L LY). unfold PNKP.edep in Ha. cbn in Ha.
    destruct Ha as [Ha|[Ha|(iv & Hin & Ha)]]; [lia|lia|]. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
  - intros fb s H1 H2 H3 H4. apply (PNOKS.src_owner_ok_S L HI LY HIok). unfold PNOKS.owok_pre. split; [exact H1|]. split; [exact H2|]. split; [exact H3| exact H4].
  - intros a Ha B. unfold PNBK.bdom in B. unfold PNKP.edep in Ha. cbn in Ha, B.
    destruct Ha as [Ha|[Ha|(iv & Hin & Ha)]]; [lia|lia|]. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
  - pose proof (ly_kpm L LY). lia.
  - pose proof (ly_bov L LY). lia.
Qed.

End WithHeap.
End PNBKS.
