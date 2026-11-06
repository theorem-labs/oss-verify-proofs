(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil AsanAllocModel AsanAllocCons AsanAllocConsC.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit AS_Refill1 AG_RefillModel AG_ColdModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RefillModel~~~~~~08refilled69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocConsC~~~~~~ke4NUMc69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~p6bkBatchClassp6aas_regionsp66astate37Corelib4Init9Datatypesvb4list37Corelib4Init5Logichha2eqp66region37Corelib7Numbers7BinNumshjd1Zvb4boolvb4truehha3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AllocWf~~~~~~hn08cache_okp6fas_cache_initedp66get_pcp68pc_countp66qbatchvb3nil69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanAllocCons~~~~~~hue5INITQp65as_tqp67qc_listhn02WFke5PINVcke5LIVECke5nlive46Stdlib6ZArith6BinInt1Zim73addim72lep6aget_regionp6h0kFreeArrayOffsetp6ckUserMapSizep6erg_mapped_userim73mulp6cas_space_beghha3andp6bkHighMemBegp6bkHighMemEndp6akSpaceSizeim76modulo" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FreeNum.
  Variable st : ltac2:(zQ "10!v2$0").
  Hypothesis W : ltac2:(zQ "10!ik9@1$0?2st").
  Hypothesis PI : ltac2:(zQ "10!ikf@1$0?2st").
  Hypothesis NAL : ltac2:(zQ "50!t7!il7!ilf!inf!io6@2$4@2$3@2$2?2st$0+1@1$1$0").   (* [comment removed for export] *)
  Hypothesis EMPTY : ltac2:(zQ "50!hie!hl6!hsb!t7!ht4@3$0$1@1$4@2$2?2st$3Z").
  Hypothesis ROOM : ltac2:(zQ "80!ioc!t7!ip9!iqd!irc!inf!io6!isd@2$6@2$5@1$4@2$0?2st$1@2$7+2$3$2").
  Hypothesis HM : ltac2:(zQ "a0!it4!iu3!inf!io6!hie!hl6!iua!iv8!jg6!jh3@2$1@2$3$6@1$0?2st@2$1@2$3@2$2@1$0?2st$8@2$2$7+1@3$4$5@2$9@1$0?2st+hgg0Z").

  Lemma NUM_refilled : ltac2:(zQ "30!k4!of!t7@1$1@2$0?2st$2").
  Proof.
    assert (HC : 1 <= kBatchClass <= 30) by (unfold kBatchClass; lia).
    assert (Hc : 1 <= kBatchClass < kNumClasses) by (unfold kBatchClass, kNumClasses; lia).
    destruct PI as [CO NM].
    ndestruct (gfa_cold st kBatchClass W HC EMPTY ROOM HM) as (stg & evg & EG & SG).
    npose (rf_facts st kBatchClass W HC ROOM) as (Q1 & Q2 & _).
    set (r := get_region st kBatchClass) in *.
    set (fl1 := rf_fl1 kBatchClass (rg_num_freed r) (rg_allocated_user r) (rg_mapped_user r) (rg_free_array r)) in *.
    assert (N1 : 1 <= rf_n kBatchClass) by (vm_compute; discriminate).
    assert (NE : exists cp rest, firstn (Z.to_nat (rf_n kBatchClass)) fl1 = cp :: rest).
    { destruct (firstn (Z.to_nat (rf_n kBatchClass)) fl1) as [|cp rest] eqn:E; [exfalso| exists cp, rest; reflexivity].
      apply (f_equal (@length Z)) in E. rewrite length_firstn in E. cbn [length] in E. unfold zlen in Q2. clear - E Q1 Q2 N1. lia. }
    ndestruct NE as (cp & rest & TAKEN).
    assert (CA : exists st' a, cache_alloc st kBatchClass = Some (st', a, evg) /\ as_regions st' = as_regions stg).
    { unfold cache_alloc. replace ((kBatchClass =? 0) || (kNumClasses <=? kBatchClass)) with false by reflexivity. rewrite EMPTY. cbn [Z.eqb].
      change (max_count kBatchClass / 2) with (rf_n kBatchClass). rewrite EG. cbn [pc_chunks pc_count]. rewrite TAKEN.
      eexists _, _. split; [reflexivity| reflexivity]. }
    ndestruct CA as (st' & a & CA & RG).
    pose proof (WF_region st kBatchClass W ltac:(unfold kNumClasses in *; lia)) as RO.
    assert (TAIL : rg_mapped_user (get_region st kBatchClass) - rg_allocated_user (get_region st kBatchClass) < class_size kBatchClass + kUserMapSize).
    { assert (CSZ : class_size kBatchClass <> 0) by (change (class_size kBatchClass) with 8192; lia).
      pose proof (ro_tail_small _ _ RO CSZ) as T. destruct (rg_allocated_user (get_region st kBatchClass) =? 0); unfold kUserMapSize in *; lia. }
    destruct (cache_alloc_ncarved st noX kBatchClass st' a evg (WF_cons_pre st kBatchClass W Hc) (ro_numfreed _ _ RO) TAIL ltac:(lia) CO CA) as (OTH & NC & _).
    (* [comment removed for export] *)
    assert (RGR : as_regions st' = as_regions (refilled st kBatchClass)).
    { rewrite RG. ndestruct SG as (_ & _ & E & _). rewrite E. reflexivity. }
    assert (NCE : forall c0, ncarved (refilled st kBatchClass) c0 = ncarved st' c0) by (intros c0; unfold ncarved, get_region; rewrite RGR; reflexivity).
    intros c0 Hc0. rewrite NCE. destruct (Z.eq_dec c0 kBatchClass) as [->|NEc].
    - destruct NC as [E|B]; [rewrite E; exact (NM _ Hc)|].
      pose proof (own_chunk_boundc st kBatchClass W Hc) as OC. pose proof (own_batch_bound st kBatchClass W) as OB.
      unfold CAPc, CHBc, NBB. replace (mused kBatchClass =? 0) with false by (vm_compute; reflexivity). replace (zlen (noX kBatchClass)) with 0 in B by reflexivity.
      assert (D0 : 0 <= QTOT / kBatchSize) by (apply Z.div_pos; unfold QTOT, kBatchSize, kQuarantineMaxSize, kMaxCacheSize; lia).
      rewrite Z.eqb_refl in OB |- *. lia.
    - unfold ncarved. rewrite (OTH c0 ltac:(lia) NEc). exact (NM c0 Hc0).
  Qed.
End FreeNum.

(* [comment removed for export] *)
Lemma NUM_regions : ltac2:(zQ "60!of!u5!v2!hh3!hie!hj4>1a$2>1b$2>0@3$4@1$3$5@1$1^2@1$1^1>0@1$0^2@1$0^4").
Proof. intros a b E N c Hc. unfold ncarved, get_region. rewrite E. exact (N c Hc). Qed.

(* [comment removed for export] *)
Lemma inited_of_count : ltac2:(zQ "a0!hie!hl6!hlb!hm2!hm9!hqd!hr9!v2!hsb!ht4>2st$7>1c$1>0@2$5^2^1>0@1$4@3$0$1@1$9@2$8^3^2Z@3$0$2@1$6^4$3").
Proof. intros st c CO NZ. pose proof (co_bound _ _ CO) as B. destruct (as_cache_inited st); [reflexivity| exfalso; exact (NZ B)]. Qed.
(* [comment removed for export] *)
Lemma inited_of_tq : ltac2:(zQ "c0!hie!htf!hlb!hh3!hu8!hm2!hm9!iie!hr9!ij7!v2!ijf>2st$a>0@1$7^1>0@1$6@3$0@1$3$1@1$b@1$9^2@1$4$1@3$0$2@1$8^3$5").
Proof. intros st [I|[T _]] NE; [exact I| exfalso; exact (NE T)]. Qed.
