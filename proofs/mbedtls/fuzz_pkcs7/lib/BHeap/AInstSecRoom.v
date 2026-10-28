(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AInstDepot AInstPop AVstT AInstGen AInstSec AInstMallocG.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_DepotB AW_DepotTop AW_MallocB HMLib HM HMFrame AHeapR APopSec AW_DepotCfg AW_PoisonBig AW_PoisonBigCfg AInstFree AInstMallocS ARoomL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AInstSecRoom () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstMallocS.Glh"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstMallocS.KsF"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

Section S.
  Variables (h : ahst) (n : Z) (mo0 : Model).
  Hypothesis K0 : HK AL0 h mo0.
  Hypothesis B : bwf h.
  Hypothesis HV : h_havol h <= AVOL_MAX.
  Hypothesis NB : 0 <= n < 2^28.
  Hypothesis FP : from_primary n = false.
  (* [comment removed for export] *)
  Hypothesis HV32 : h_havol h <= 2^32.

  Local Notation nb0 := (d_nb (h_dep h)).
  Local Notation bl0 := (d_bl (h_dep h)).

  #[using="NB FP"] Lemma mszh_range : 2^16 <= mszh n <= 2^28 + 16384 /\ mszh n mod 4096 = 0.
  Proof.
    unfold mszh. dpose (sec_req_facts n NB FP) as (NLO & RZ & N2E & RNB & MS & MAL). split; [| exact MAL]. clear - NLO N2E RNB MS NB. lia.
  Qed.

  #[using="K0 B HV NB FP HV32"] Lemma MS_ROOM_l : ltac2:(CDefT.buildp (gd_tbl_AInstSecRoom ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pm,$2.Pmo,$3.P,(4.Vh,Vn,R4.R3.R2.)P,(5.VhAR,Vh,Vn,Vmo0,R5.R4.(6.(7.Vh,))(8.(7.Vh,))R2.)(9.(:.&40.)La,(:.&40.)(;.VhAR,+22.R5.R4.R1.))")
(* [comment removed for export] *).
  Proof.
    (intros sc r m mo dd_H; ddestruct dd_H as (-> & -> & ->); intros [K _]). unfold Ksh, Ks in K. ddestruct K as (v & BASE & KD).
    assert (EV : v = vst_of h).
    { destruct BASE as [(_ & _ & ->)|(a & E & _)]; [reflexivity| discriminate E]. }
    subst v.
    assert (HKV : HKv AL0 (vst_of h) mo).
    { destruct KD as [(_ & _ & X)|[(x & E & _)|[(y & _ & E & _)|(x & y & E & _)]]]; [exact X| exfalso| exfalso| exfalso];
        apply (f_equal (@length Z)) in E; rewrite length_app in E; cbn in E; lia. }
    pose proof mszh_range as (R1 & R2).
    apply (HKv_room_large AL0 h mo (mszh n) B HKV (proj2 K0) HV32 R1 R2).
    apply (vst_slack h (mszh n) B HV). clear - R1. lia.
  Qed.
End S.

End ARUN_1.
