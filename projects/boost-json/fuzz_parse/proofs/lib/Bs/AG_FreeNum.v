(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil AsanAllocModel BothAllocCons BothAllocConsC.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AllocWf AllocKit AG_MallocModel AG_WFHit AS_Refill1 AG_RefillModel AG_ColdModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~0bkBatchClass69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothAllocConsC~~~~~~ke4NUMc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_RefillModel~~~~~~p68refilled0aas_regions06astate37Corelib4Init9Datatypesv94list37Corelib4Init5Logichh82eq06region37Corelib7Numbers7BinNumshja1Zv94boolv94truehh83not0fas_cache_inited06get_pc08pc_count79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AllocWf~~~~~~hp08cache_ok06qbatchv93nil05as_tq07qc_list69OSSVerify6Proofsaboost_jsonafuzz_parse3libdBothAllocCons~~~~~~hv75INITQhp02WFke5PINVcke5LIVECke5nlive46Stdlib6ZArith6BinInt1Zile3addile2le0aget_region0h0kFreeArrayOffset0ckUserMapSize0erg_mapped_userile3mul0cas_space_beghh83and0bkHighMemBeg0bkHighMemEnd0akSpaceSizeile6modulo" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FreeNum.
  Variable st : ltac2:(zQ "10!v1$0").
  Hypothesis W : ltac2:(zQ "10!ik0@1$0?2st").
  Hypothesis PI : ltac2:(zQ "10!ik6@1$0?2st").
  Hypothesis NAL : ltac2:(zQ "50!k1!ike!il6!in6!ind@2$4@2$3@2$2?2st$0+1@1$1$0").   (* [comment removed for export] *)
  Hypothesis EMPTY : ltac2:(zQ "50!hic!hl3!hne!k1!ho6@3$0$1@1$4@2$2?2st$3Z").
  Hypothesis ROOM : ltac2:(zQ "80!io3!k1!iof!iq2!ir0!in6!ind!is0@2$6@2$5@1$4@2$0?2st$1@2$7+2$3$2").
  Hypothesis HM : ltac2:(zQ "a0!is7!it5!in6!ind!hic!hl3!itc!iu9!iv6!jg2@2$1@2$3$6@1$0?2st@2$1@2$3@2$2@1$0?2st$8@2$2$7+1@3$4$5@2$9@1$0?2st+hgg0Z").

  Lemma NUM_refilled : ltac2:(zQ "30!k1!of!ta@1$1@2$2?2st$0").
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
Lemma NUM_regions : ltac2:(zQ "60!u5!v1!of!hh1!hic!hj2>1a$1>1b$1>0@3$4@1$3$5@1$0^2@1$0^1>0@1$2^2@1$2^4").
Proof. intros a b E N c Hc. unfold ncarved, get_region. rewrite E. exact (N c Hc). Qed.

(* [comment removed for export] *)
Lemma inited_of_count : ltac2:(zQ "a0!hic!hl3!hl8!hlf!hm6!hmd!v1!hne!ho6!hsd>2st$6>1c$1>0@2$9^2^1>0@1$4@3$0$1@1$8@2$7^3^2Z@3$0$2@1$5^4$3").
Proof. intros st c CO NZ. pose proof (co_bound _ _ CO) as B. destruct (as_cache_inited st); [reflexivity| exfalso; exact (NZ B)]. Qed.
(* [comment removed for export] *)
Lemma inited_of_tq : ltac2:(zQ "c0!hic!ht9!hl8!hh1!hu1!hlf!hm6!hmd!hu7!v1!hue!ij7>2st$9>0@1$b^1>0@1$6@3$0@1$3$1@1$a@1$8^2@1$4$1@3$0$2@1$7^3$5").
Proof. intros st [I|[T _]] NE; [exact I| exfalso; exact (NE T)]. Qed.
