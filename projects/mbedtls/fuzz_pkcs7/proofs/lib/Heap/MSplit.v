(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KStepC
  MI_Inv MI_Contracts KReach MReach MStrat ImplRz.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MSplit () : Init.string Init.list := ["Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.KStep.OWN"; "OSSVerify.KrLib.Heap.MStrat.UND"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.MStrat.shift"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.MStrat.GB"; "OSSVerify.KrLib.Heap.KReach.kres"; "OSSVerify.KrLib.Heap.MStrat.MA"].


Definition is_none_leaf (r : exc (option bptr * PState)) : bool :=
  match r with Ok (Some _, _) => false | _ => true end.

(* [comment removed for export] *)
Definition split_pre (X : list bptr) (G : PState -> Model -> Prop) (n : Z) (s : PState) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_MSplit ()) "(0.(1.O5.O4.O2.O1.)(0.(2.(3.O2.))(0.(0.(4.=(5.(3.O2.)))(4.(5.(3.O2.))+=.))(0.(4.=O3.)(0.(4.(6.O3.+2014.)$7.)(8.#2.(6.$7.$9.)O1.))))))")
(* [comment removed for export] *).

Lemma raw_malloc_reach X G n s mo (Q : mstate * option cptr -> Prop) :
  frame_ok G -> split_pre X G n s mo ->
  sreach Q (GB + MA) 2%nat (cmalloc (ps_m s) n) ->
  reachT (raw_malloc n s) mo (fun p mo' => exists st r, Q (st, r) /\ fst p = match r with Some slot => Some (slot, fresh_off st slot n) | None => None end).
Proof.
  (intros HG dd_H; ddestruct dd_H as (OW & U & SH & Hn & HnB & KR); intros SR).
  dpose OW as [(L & Hc & HK & Hi) [Hnd HGs]].
  unfold raw_malloc. change (mbind mget ?f s) with (f s s).
  eapply reachT_mbind.
  { apply (membed_reach G HG Q (cmalloc (ps_m s) n) (GB + MA) 2%nat L _ s mo SR (cmalloc_contract_proof _ _ _ Hc Hn)).
    split; [exact HK|]. split; [exact HGs| exact KR]. }
  cbn beta. intros [st' r] s1 mo1 (HQ & _). cbn [fst snd] in HQ.
  apply (reachT_ret (A := option bptr * PState)). cbn [fst]. dexists st', r. split; [exact HQ| reflexivity].
Qed.

Theorem raw_malloc_splits X G n s mo :
  frame_ok G -> split_pre X G n s mo -> splits (raw_malloc n s) mo is_none_leaf.
Proof.
  intros HG PRE. dpose PRE as (OW & U & SH & Hn & HnB & KR).
  pose proof (raw_malloc_spec_c X G n HG Hn s mo OW) as W.
  split.
  - destruct (reachT_etwf _ _ _ _ (raw_malloc_reach X G n s mo QF HG PRE (cmalloc_sreach_fail _ _ U SH Hn HnB)) W)
      as ([r s'] & mo' & Hp & (st & r0 & HQ & Hr) & _).
    dexists (Ok (r, s')), mo'. split; [exact Hp|]. cbn [fst] in Hr. unfold QF in HQ. cbn [snd] in HQ. subst r0. subst r. reflexivity.
  - destruct (reachT_etwf _ _ _ _ (raw_malloc_reach X G n s mo QS HG PRE (cmalloc_sreach_ok _ _ U SH Hn HnB)) W)
      as ([r s'] & mo' & Hp & (st & r0 & HQ & Hr) & _).
    dexists (Ok (r, s')), mo'. split; [exact Hp|]. cbn [fst] in Hr. unfold QS in HQ. cbn [snd] in HQ. destruct r0 as [slot|]; [| congruence]. subst r. reflexivity.
Qed.
