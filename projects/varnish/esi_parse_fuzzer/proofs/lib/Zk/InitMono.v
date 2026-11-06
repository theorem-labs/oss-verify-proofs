(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRep MRepAux MTree Mall5lv Mall9rj Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma jinvi_init_done resv m idle st LB : JINVi resv (m :: idle) st LB -> c_init_done (ctx st) = 1.
Proof.
  intros (L & LS & BL & INV & _).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (im_idle _ _ _ IM m ltac:(left; reflexivity)) as [Hm _].
  destruct (ia_metas _ IA m meta0 Hm) as (a & ar & k & Ha & _).
  destruct (ia_secret _ IA) as [_ [(I0 & _ & AE)|[I1 _]]]; [| exact I1].
  exfalso. rewrite AE in Ha. rewrite lookup_empty in Ha. discriminate.
Qed.

Lemma ist_init_done {resv} st0 LB st :
  AREACH_from resv st0 LB -> IST st0 st -> c_init_done (ctx st0) <> 0 -> c_init_done (ctx st) <> 0.
Proof.
  intros AR IS H0. induction IS as [t Ht|o st sc st1 st2 m IS IH Hsc TA AM].
  - exact H0.
  - destruct (ist_jinv resv st0 LB st AR IS) as [idle J].
    destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _].
    rewrite (jinvi_init_done _ _ _ _ _ (jinv_am _ _ _ _ _ _ _ J1 AM)). lia.
Qed.

End CEIL.
