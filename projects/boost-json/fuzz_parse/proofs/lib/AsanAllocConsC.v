(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FinFun.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AsanAllocCons.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit CidBits AllocBudget.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3powhc3add69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocConsC~~~~~~k06AK_CAP69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~oaaclass_sizehc3div69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanAllocCons~~~~~~te4QTOTte5musedk05LIVEC37Corelib4Init9Datatypeshj54boolhc3eqbte3NBBk04CHBcoabkBatchClassoackUserMapSizeoa9max_countoa6astatehc2le37Corelib4Init5Logichpf3andte7ncarvedk04CAPcoabkNumClasseshc2lthc3mulk04MUBcoaekFreeArraySize79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAllocBudget~~~~~~hvc4csumk03UBchvc6B_PRIMk03B0coah0kFreeArrayOffsetoah1rg_allocated_useroah4rg_mapped_free_arrayoaerg_mapped_userhvc6pusagek04NUMcoaaget_regionoa6regionhc3subte8COMPLETEte3noXhj54listoacinit_state_qk05PINVcoaainit_statete9same_coreoa5chunkhj54andbte6allocboa8ch_classoaachunk_listoa4zlen36Stdlib5Lists4Listjlb6filterk05nlive79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AllocWf~~~~~~jo02WFte9own_chunkhpf2eqoabcompute_reqhj55falsehj54trueoa8kMaxSizeoa9rq_neededoaarq_primaryhc3ltbhj54prodoa6effecthj54pairoa8class_idhj54Somehj56optionhpf3notoaaCAllocatedoabam_malloc_koa8ch_stateoabch_user_begoa6cstatejlb2Inoacam_free_full" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AK_CAP : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!j4!ja@2$1@2$0+2+hf@2$0+2+hd").
(* [comment removed for export] *)
Definition LIVEC : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "50!h9!o1!sb!ja!t8\1c$0@2$3@2$4$1@1$2^1+1").
(* [comment removed for export] *)
Definition CHBc : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "60!ja!h9!hhe!hi5!hid!t8\1c$1@2$0@2$0@1$4^1+2@2$5$2@2$0@1$3^1+8").
Definition CAPc : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "c0!hkd!ja!h9!hl5!hlb!hi5!hm1!sb!hm8!hn6!ho5!t8\1c$2M0\0$0$2@2$3@1$5^1ZZ@2$1@2$1@2$1@2$1@1$a^1+2@2$b$9@1$7^1@1$6^1M0\0$0$2@2$3^1$8$4Z").
Definition NUMc : ltac2:(zQ "10!hp1>2st$0P") := ltac2:(zQ "80!hpa!hr3!h9!hra!hs4!hp1!hsb!ht9\2st$5>1c$2>0@2$1@2$0+1^1@2$7^1$6@2$0@2$3^3^2@1$4^2").

Definition MUBc : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "60!ja!h9!hs4!sb!hn6!hte\1c$1@2$0@2$5@1$3^1@2$0@1$2^1+2$4").
Definition UBc : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "60!ja!hu4!hub!t8!h9!hte\1c$4@2$0@2$0@1$1^1$2@2$5+qgg0@2$0@2$3@1$1^1+kggg0@2$3$2+kggg0").
Definition B0c : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!ijd!ik5@3$0$1+1Nhf").

Lemma B0c_val : ltac2:(zQ "50!ikb!il5!ja!hpa!j4@2$3@2$2$1@2$4+2+h8$0").
Proof. vm_compute. discriminate. Qed.
Lemma MUBc_room : ltac2:(zQ "b0!hpa!hr3!h9!hi5!hu4!ilb!hsb!hn6!ja!ht9!hte>1c$2>0@2$1@2$0+1^1@2$9^1$6>0@2$0+1@1$3^2@2$0@2$8@1$4^3@2$a+2$7$5").
Proof.
  intros c Hc M. unfold kNumClasses in Hc.
  assert (E : exists k, c = Z.of_nat k /\ (k < 32)%nat) by (exists (Z.to_nat c); split; [lia| lia]).
  ndestruct E as (k & -> & Hk).
  do 32 (destruct k as [|k]; [vm_compute in M |- *; first [lia | discriminate] |]). lia.
Qed.
Lemma CAPc_nonneg : ltac2:(zQ "60!hpa!hr3!h9!hs4!hsb!ht9>1c$2>0@2$1@2$0Z^1@2$5^1$4@2$0Z@1$3^2").
Proof.
  intros c Hc. unfold kNumClasses in Hc.
  assert (E : exists k, c = Z.of_nat k /\ (k < 32)%nat) by (exists (Z.to_nat c); split; [lia| lia]).
  ndestruct E as (k & -> & Hk).
  do 32 (destruct k as [|k]; [vm_compute; first [discriminate | lia] |]). lia.
Qed.

(* [comment removed for export] *)
Theorem pusage_boundc : ltac2:(zQ "h30!hr3!hpa!imf!ht9!sb!io4!ipc!h9!iqd!il5!ir7!hp1!ire!hub!hsb!hn6!isb!ja!it4>2st$b>0@1$a^1>0>1c$7>0@2$0@2$1+1^1@2$3^1$e=1r$h0@2$c^4^2@2$0@2$3Z@1$4^3@2$0@2$0@2$1Z@1$2^1@2$1@1$2^1@1$6^1@2$0@2$3@2$h2@1$6^1@1$2^1@2$h1@1$4^3$f@2$0@2$1Z@1$5^1@2$1@1$5^1$d@2$1@1$8^3$9").
Proof.
  intros st NM SH. unfold pusage, B0c. apply csum_le. intros c Hc. change (1 + Z.of_nat 31) with 32 in Hc.
  pose proof (NM c Hc) as N. ndestruct (SH c Hc) as (Hs & AU & TAIL & MFA). unfold reg_usage, UBc, MUBc. cbv zeta.
  unfold ncarved in N. unfold kUserMapSize, kFreeArraySize in *.
  pose proof (CAPc_nonneg c ltac:(unfold kNumClasses in *; lia)) as CP.
  set (r := get_region st c) in *. set (s := class_size c) in *. set (K := CAPc c) in *.
  assert (MU : rg_mapped_user r <= s * (K + 2) + 262144).
  { pose proof (Z.div_mod (rg_allocated_user r) s ltac:(lia)) as D. pose proof (Z.mod_pos_bound (rg_allocated_user r) s Hs).
    assert (M1 : s * (rg_allocated_user r / s) <= s * K) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (D1 : rg_mapped_user r / 262144 <= (s * (K + 2) + 262144) / 262144) by (apply Z.div_le_mono; lia).
  assert (D2 : rg_mapped_free_array r / 262144 <= 536870912 / 262144) by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PINVc : ltac2:(zQ "10!hp1>2st$0P") := ltac2:(zQ "50!hr3!ita!iu5!ir7!hp1\2st$4@2$0@2$1^1$2@1$3^1").

Lemma NUMc_init_q : ltac2:(zQ "50!h9!hkd!iub!ir7!iv3>2rb$0>2sb$0>2pa$0>3env@1$2$0>2ts$1>2qx$0>2qn$0>2qc$0@1$3@8$4^8^7^6^5^4^3^2^1").
Proof.
  intros. intros c Hc. unfold ncarved, get_region. cbn [as_regions init_state_q]. unfold kNumClasses in Hc.
  pose proof (CAPc_nonneg c ltac:(unfold kNumClasses; lia)) as CP.
  assert (E : exists k, c = Z.of_nat k /\ (k < 32)%nat) by (exists (Z.to_nat c); split; [lia| lia]).
  ndestruct E as (k & -> & Hk). unfold zidx. rewrite Nat2Z.id.
  do 32 (destruct k as [|k]; [cbn -[CAPc]; rewrite Zdiv_0_l; exact CP|]). lia.
Qed.
Theorem PINVc_init_q : ltac2:(zQ "50!h9!hkd!iub!jg2!iv3>2rb$0>2sb$0>2pa$0>3env@1$2$0>2ts$1>2qx$0>2qn$0>2qc$0@1$3@8$4^8^7^6^5^4^3^2^1").
Proof. intros. split; [apply COMPLETE_init_q| apply NUMc_init_q]. Qed.
Theorem PINVc_init : ltac2:(zQ "50!h9!hkd!iub!jg2!jga>2rb$0>2sb$0>2pa$0>3env@1$2$0>2ts$1@1$3@5$4^5^4^3^2^1").
Proof. intros. apply PINVc_init_q. Qed.

Lemma PINVc_core : ltac2:(zQ "30!jg2!hp1!jh7>1a$1>1b$1>0@2$2^2^1>0@1$0^2@1$0^4").
Proof.
  intros a b C [CO NM]. split; [exact (COMPLETE_view b a noX (eq_sym (same_core_cview a b C)) CO)|].
  intros c Hc. rewrite (ncarved_view a b c (same_core_cview a b C)). exact (NM c Hc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nlive : ltac2:(zQ "20!h9!hp1>2st$1>1c$0$0") := ltac2:(zQ "a0!ji3!jib!h9!jj3!hp1!jjc!jk7!jl4!jme!hl5\2st$4\1c$2@2$7$0@3$8$0\2ch$0@2$1@2$9@1$5^1^2@1$3^1@1$6^2").

Lemma nlive_nonneg : ltac2:(zQ "40!h9!jn8!hp1!hpa>2st$2>1c$0@2$3Z@2$1^2^1").
Proof. intros. unfold nlive. apply zlen_nonneg. Qed.

(* [comment removed for export] *)
Theorem own_chunk_boundc : ltac2:(zQ "e0!h9!ja!hpa!hr3!jrd!hhe!hi5!js3!jn8!hp1!hsb!jl4!t8!ht9>2st$9>1c$0>0@1$4^2>0@2$3@2$2+1^2@2$d^2$a@2$2@2$b$0@2$7^4^3@2$1@2$8^4^3@2$c$5@2$1@1$6^3+8").
Proof.
  intros st c W Hc. rewrite own_chunk_split. fold (nlive st c).
  assert (MU : forall ch, In ch (chunk_list st) -> (ch_class ch =? c) = true -> 1 <= mused c <= ch_used ch).
  { intros ch Hin E. apply Z.eqb_eq in E. pose proof (WF_chunk st ch W Hin) as CO. unfold chunk_ok in CO. cbv zeta in CO.
    ndestruct CO as (U1 & _ & _ & _ & REST). unfold ch_primary in REST. rewrite E in REST.
    destruct (Z.eqb_spec c 0) as [C0|C0]; [lia|]. cbn [negb] in REST. ndestruct REST as (PR & CL & _).
    replace c with (fclass (ch_used ch)) by (unfold fclass; symmetry; exact CL). apply mused_ok; [lia| exact PR]. }
  assert (M0 : 0 <= mused c).
  { unfold mused. generalize (Z.to_nat c) as k. intros k. do 32 (destruct k as [|k]; [cbn; lia|]). destruct k; cbn; lia. }
  pose proof (quar_count st (fun ch => ch_class ch =? c) (mused c) W M0 ltac:(intros ch Hin E; apply (MU ch Hin E))) as Q. cbv beta in Q.
  assert (D : zlen (List.filter (fun ch => negb (allocb ch) && (ch_class ch =? c)) (chunk_list st)) <= QTOT / (mused c + 8)).
  { apply Z.div_le_lower_bound; [lia|]. lia. }
  lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma primary_of_needed_small : ltac2:(zQ "a0!hkd!jsf!jt5!ju3!juc!h9!jv4!jvf!kgb!kh8>1n$5>0@3$1$0@2$9$6@1$7@1$2^1$3@3$1$0@1$8@1$2^2$4").
Proof.
  intros n H. unfold compute_req in *. cbn [rq_needed rq_primary] in *.
  destruct (round_up (Z.max n 8) 8 + rz_size n <=? kMaxSize) eqn:E; [reflexivity|].
  apply Z.ltb_ge in H. apply Z.leb_gt in E. pose proof (rz_size_facts n) as [RZ _]. exfalso. lia.
Qed.

Theorem PINVc_am_malloc_k : ltac2:(zQ "hf0!h9!hp1!khe!iub!jsf!ki6!jt5!jvf!kif!jrd!jg2!ji3!kj7!hpa!kk2!hkd!ju3!kka!kl4!hid!jn8!klb!km8!kn6!ko1!jk7!kof!jv4!kp8!ja!kh8>2st$1>1n$0>1k$0>1U$0>3st'$1>2ev@1$3$5>0@1$9^6>0@1$9^3>0@1$a^8>0@2$d+1^8>0>0@3$4$f@2$he$hb@1$7@1$6^9$h0@2$d@2$hd@2$h4^b@1$c@1$7@1$6^a+1@1$h3@1$c@1$7@1$6^a>0>1x$b>0@3$hc$b^1@1$h9^c>0@3$4$ha@1$h7^2$h5@1$h2@3$4$0@1$h8^3^b>0@3$4@1$h1@2$2@2$2$0$1@1$3$5@3$h6^c^b^a@2$e@2$2@2$2$0$1@1$3$5@4$8@2$2$0$1@1$3$5@4$8$0$1^9^8^7@1$a^9").
Proof.
  intros st n k U st' ev W W' PI Hn NL NOLIVE H.
  pose proof (am_malloc_k_fresh st n k U st' ev W W' NOLIVE H) as FR. destruct PI as [CO NM].
  assert (CO' : COMPLETE st' noX) by (exact (am_malloc_k_complete st noX n k U st' ev (fun c Hc => WF_cons_pre st c W Hc) CO H FR)).
  split; [exact CO'|].
  ndestruct (am_malloc_k_frame st n k U st' ev W H) as (st1 & allocated & cls & CORE & EU & CH1 & TQ1 & GQ1 & SB1 & LR1 & LC1 & ARMS).
  assert (RG' : as_regions st' = as_regions st1) by (ndestruct CORE as (_ & _ & E & _); exact E).
  intros c Hc. unfold ncarved. unfold get_region. rewrite RG'. fold (get_region st1 c). fold (ncarved st1 c).
  destruct ARMS as [(LG & -> & RG1)|(LG & -> & HC & evC & CA)].
  - unfold ncarved, get_region. rewrite RG1. apply (NM c Hc).
  - set (c0 := class_id (rq_needed (compute_req n))) in *.
    pose proof (WF_region st c0 W ltac:(unfold kNumClasses in HC; unfold kNumClasses; lia)) as RO.
    npose (class_size_table_facts c0 ltac:(unfold kNumClasses in HC; lia)) as (CS1 & _ & CS3 & _).
    assert (TAIL : rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0) < class_size c0 + kUserMapSize).
    { pose proof (ro_tail_small _ _ RO ltac:(lia)) as T. destruct (rg_allocated_user (get_region st c0) =? 0); unfold kUserMapSize in *; lia. }
    destruct (cache_alloc_ncarved st noX c0 st1 allocated evC (WF_cons_pre st c0 W HC) (ro_numfreed _ _ RO) TAIL ltac:(lia) CO CA) as (OTH & NC & _).
    destruct (Z.eq_dec c c0) as [->|NE].
    + destruct NC as [E|B]; [rewrite E; apply (NM c0 Hc)|].
      pose proof (own_chunk_boundc st c0 W Hc) as OC. pose proof (own_batch_bound st c0 W) as OB.
      (* [comment removed for export] *)
      specialize (NL LG).
      assert (MP : 1 <= mused c0) by (subst c0; exact (mused_class_pos n Hn (primary_of_needed_small n LG))).
      unfold CAPc, CHBc, NBB. replace (mused c0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (zlen (noX c0)) with 0 in B by reflexivity.
      assert (D0 : 0 <= QTOT / kBatchSize) by (apply Z.div_pos; unfold QTOT, kBatchSize, kQuarantineMaxSize, kMaxCacheSize; lia).
      destruct (c0 =? kBatchClass); lia.
    + unfold ncarved. rewrite (OTH c ltac:(lia) NE). apply (NM c Hc).
Qed.

Theorem PINVc_am_free_full : ltac2:(zQ "h10!hp1!iub!ki6!khe!jg2!hm8!kk2!kka!kif!jsf!h9!jrd!hid!jn8!kpe!ja!hpa>2st$0>1p$a>3st'$0>2ev@1$1$2>0@1$b^4>0@1$4^5>0@2$h0@2$f@2$d^6$5+1@1$c$5>0@3$9@1$7@2$3$0@1$1$2@2$e^7^6@2$6@2$3$0@1$1$2@4$8$0@1$1$2^5^4@1$4^6").
Proof.
  intros st p st' ev W [CO NM] NL H.
  assert (HC : 1 <= kBatchClass < kNumClasses) by (unfold kBatchClass, kNumClasses; lia).
  ndestruct (am_free_full_complete st noX p st' ev (WF_free_env st W) (WF_batches_ok st W) (WF_cons_pre st kBatchClass W HC) (WF_cps_ok st kBatchClass W HC) CO H)
    as (CO' & SB' & CASES).
  split; [exact CO'|]. intros c Hc.
  destruct CASES as [RS|(st1 & stc & b & evb & RG1 & CA1 & TQ1 & GQ1 & OC1 & CO1 & CA & RS)].
  - rewrite (ncarved_regs st' st c RS). exact (NM c Hc).
  - rewrite (ncarved_regs st' stc c RS).
    pose proof (WF_region st kBatchClass W ltac:(unfold kNumClasses in HC; unfold kNumClasses; lia)) as RO.
    npose (class_size_table_facts kBatchClass ltac:(unfold kNumClasses in HC; lia)) as (CS1 & _ & CS3 & _).
    assert (GR1 : forall c', get_region st1 c' = get_region st c') by (intros c'; unfold get_region; rewrite RG1; reflexivity).
    assert (PRE1 : cons_pre st1 kBatchClass).
    { npose (WF_cons_pre st kBatchClass W HC) as (L1 & L2 & P3 & P4 & P5 & P6 & P7). unfold cons_pre.
      rewrite RG1, CA1, !GR1. unfold get_pc. rewrite CA1. repeat split; try assumption. exact (proj1 P3). exact (proj2 P3). }
    assert (TAIL : rg_mapped_user (get_region st1 kBatchClass) - rg_allocated_user (get_region st1 kBatchClass) < class_size kBatchClass + kUserMapSize).
    { rewrite GR1. pose proof (ro_tail_small _ _ RO ltac:(lia)) as T. destruct (rg_allocated_user (get_region st kBatchClass) =? 0); unfold kUserMapSize in *; lia. }
    destruct (cache_alloc_ncarved st1 noX kBatchClass stc b evb PRE1 ltac:(rewrite GR1; exact (ro_numfreed _ _ RO)) TAIL ltac:(lia) CO1 CA) as (OTH & NC & _).
    destruct (Z.eq_dec c kBatchClass) as [->|NE].
    + destruct NC as [E|B]; [rewrite E; unfold ncarved; rewrite GR1; apply (NM _ Hc)|].
      pose proof (own_chunk_boundc st kBatchClass W Hc) as OC. pose proof (own_batch_bound st kBatchClass W) as OB.
      assert (OB1 : own_batch st1 kBatchClass = own_batch st kBatchClass) by (unfold own_batch; rewrite TQ1, GQ1; reflexivity). rewrite OB1 in B.
      unfold CAPc, CHBc, NBB. replace (mused kBatchClass =? 0) with false by (vm_compute; reflexivity).
      replace (zlen (noX kBatchClass)) with 0 in B by reflexivity.
      assert (D0 : 0 <= QTOT / kBatchSize) by (apply Z.div_pos; unfold QTOT, kBatchSize, kQuarantineMaxSize, kMaxCacheSize; lia).
      rewrite Z.eqb_refl in OB |- *. lia.
    + unfold ncarved. rewrite (OTH c ltac:(lia) NE), GR1. apply (NM c Hc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem PROOMc_of_PINVc : ltac2:(zQ "80!ikb!iqd!jrd!jg2!hp1!ja!hpa!j4>2st$4>0@1$2^1>0@1$3^2@2$6@2$5@1$1^3@2$7+2+h8$0").
Proof.
  intros st W [_ NM]. pose proof B0c_val as BV.
  assert (PB : pusage st <= B0c); [| lia].
  apply pusage_boundc; [exact NM|]. intros c Hc. unfold kNumClasses in Hc.
  pose proof (WF_region st c W ltac:(unfold kNumClasses; lia)) as RO. npose (class_size_table_facts c ltac:(lia)) as (CS1 & _ & CS3 & _).
  cbv zeta. split; [lia|]. split; [split; [apply (ro_alloc_nonneg _ _ RO)| apply (ro_alloc_le _ _ RO)]|].
  split.
  - pose proof (ro_tail_small _ _ RO ltac:(lia)) as T. destruct (rg_allocated_user (get_region st c) =? 0); unfold kUserMapSize in *; lia.
  - pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_bound _ _ RO). pose proof (ro_numfreed _ _ RO). pose proof (zlen_nonneg (rg_free_array (get_region st c))). lia.
Qed.

Theorem ROOMc_of_PINVc : ltac2:(zQ "f0!hpa!hr3!h9!jrd!hi5!jg2!hp1!ire!ilb!hsb!hn6!ipc!ja!ht9!hte>2st$6>1c$2>0@1$3^2>0@1$5^3>0@2$1@2$0+1^3@2$d^3$9>0@2$0+1@1$4^4@2$0@2$c@1$b@2$7^6^5@2$e+2$a$8").
Proof.
  intros st c W [_ NM] Hc M. pose proof (MUBc_room c Hc M) as MR. pose proof (NM c Hc) as N. unfold kNumClasses in Hc.
  pose proof (WF_region st c W ltac:(unfold kNumClasses; lia)) as RO. npose (class_size_table_facts c ltac:(lia)) as (CS1 & _ & CS3 & _).
  pose proof (ro_tail_small _ _ RO ltac:(lia)) as T. pose proof (ro_alloc_nonneg _ _ RO) as A0.
  pose proof (CAPc_nonneg c ltac:(unfold kNumClasses; lia)) as CP.
  unfold ncarved in N. unfold MUBc in MR. set (K := CAPc c) in *.
  pose proof (Z.div_mod (rg_allocated_user (get_region st c)) (class_size c) ltac:(lia)) as D. rewrite (ro_alloc_mod _ _ RO ltac:(lia)), Z.add_0_r in D.
  assert (M1 : class_size c * (rg_allocated_user (get_region st c) / class_size c) <= class_size c * K) by (apply Z.mul_le_mono_nonneg_l; lia).
  destruct (rg_allocated_user (get_region st c) =? 0); unfold kUserMapSize in *; lia.
Qed.
(* [comment removed for export] *)
