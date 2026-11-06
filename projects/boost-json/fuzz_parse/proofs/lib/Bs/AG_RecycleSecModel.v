(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AG_MallocModel AG_WFHit AG_FreeModel AG_WFFree AG_RepQ AG_RecycleModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~he6schunk03nat37Corelib4Init3Natmd3sub06length37Corelib5Lists7ListDefod6firstnhe4mkSChe7upd_nthhe4znth37Corelib7Numbers7BinNumss51Zhe5chunkhecch_alloc_beghe9kPageSize46Stdlib6ZArith6BinInt1Zhg53subhe6astate06optionhe6as_sec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh2AG_RecycleSecModel~~~~~~hjebsec_map_beghedas_n_reservedhecfind_sec_idxhearemove_maphe7set_sec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsfAG_RecycleModel~~~~~~hsc9del_statehje9secdel_l137Corelib4Init5Logiciib2eq04Someiib3andiib2ex37Corelib4Init5Peanoil82leheasc_map_beg36Stdlib5Lists4Listinf9nth_errorinf2Inod3mapinf5NoDupil82lt04cons36Stdlib7SortingbPermutationis0bPermutationiib3iffiib3nothg52leheanearest_leiib2orhg52lt04Nonehg54landhg56moduloheachunk_list04bool05falseheach_primary79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_MallocModel~~~~~~jl7fsame_but_shadowhebCQuarantinehe8ch_statehe6cstate" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition secdel_l1 : ltac2:(zQ "30!h8!lf!m8>1l@1$0$1>3idx$2@1$0$1") := ltac2:(zQ "90!lf!m8!nf!o5!h8!q4!qd!r4!re\1l@1$4$0\3idx$1=1n$1@2$3$0^2=4last$0@4$8$0^3@2$2^1N1@3$6ZZZ@3$5$0@2$2^2N1@4$7$0^4^3^1").

(* [comment removed for export] *)
Definition sec_map_beg : ltac2:(zQ "20!te!u2>2ch$1$0") := ltac2:(zQ "40!ua!u2!v9!hhd\2ch$1@2$3@1$0^1$2").

(* [comment removed for export] *)
Definition secdel : ltac2:(zQ "20!hi4!u2>2st$0>2ch$1$0") := ltac2:(zQ "c0!m8!hid!hj5!hi4!ho7!hp6!u2!hq6!hr5!hs2!ih1!ihe\2st$3\2ch$6M1\1x@1$1$0$3@3$7@1$2^2@1$4^1N0\3idx$0@2$8@3$9@2$a^3^2@1$5^3@2$b@1$2^3^1@1$4^2^2").

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma find_sec_idx_spec : ltac2:(zQ "e0!lf!m8!ijf!ik5!hid!ikb!te!h8!il2!nf!imc!hq6!in2!ip2>1l@1$7$0>1b$6>1k$1>1i$1>0@3$2@1$4$1@3$b^4^3^2@2$3$1^1@2$5@2$a^3^2@2$8$0\1h$0@2$5@3$2@1$4$0@3$d$0^6@2$9^3^4@2$3$0^1@3$2$6@1$c^1^5").
Proof.
  induction l as [|x l IH]; intros b k i H; cbn [find_sec_idx] in H; [discriminate H|].
  destruct (Z.eqb_spec (sc_map_beg x) b) as [E|NE].
  - injection H as <-. split; [lia|]. exists x. rewrite Nat.sub_diag. split; [reflexivity| exact E].
  - destruct (IH _ _ _ H) as [LE (h & Hh & Eh)]. split; [lia|]. exists h. split; [| exact Eh].
    replace (i - k)%nat with (S (i - S k))%nat by lia. cbn [nth_error]. exact Hh.
Qed.

Lemma find_sec_idx_some : ltac2:(zQ "c0!m8!lf!ijf!il2!te!ik5!h8!hid!ikb!hq6!in2!ipf>1l@1$6$1>1b$4>1k$0>0@2$3$1\1h$1@2$8@3$b$1^1^4@3$2$4@1$a^1^3@2$3$0\1i$0@3$2@1$7$0@3$9^5^4^3@2$5$0^1").
Proof.
  induction l as [|x l IH]; (intros b k nd_i1; ndestruct nd_i1 as (h & Hin & E)); [destruct Hin|]. cbn [find_sec_idx].
  destruct (Z.eqb_spec (sc_map_beg x) b) as [Ex|NE]; [exists k; reflexivity|].
  destruct Hin as [->|Hin]; [exfalso; exact (NE E)|]. apply IH. exists h. split; [exact Hin| exact E].
Qed.

(* [comment removed for export] *)
Lemma nth_error_lt : forall {A} (l : list A) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros A l i x H. apply (proj1 (nth_error_Some l i)). congruence. Qed.

Lemma find_sec_idx_nodup : ltac2:(zQ "c0!lf!te!m8!ijf!ik5!hid!in2!h8!iq5!hq6!iqb!ip2>1l@1$7$0>1b$1>1i$2>1h$0>0@2$a$1@4$8$0$1$6^4>0@3$3@1$5$0@3$b$0^5^3@2$4$0^2>0@3$3$1@1$6^3^5@3$3@1$5$2@3$9^7^6N0@2$4$2^5").
Proof.
  intros l b i h ND Hi E.
  destruct (find_sec_idx_some l b 0%nat ltac:(exists h; split; [eapply nth_error_In; exact Hi| exact E])) as [j Hj].
  destruct (find_sec_idx_spec _ _ _ _ Hj) as [_ (h' & Hh' & E')]. rewrite Nat.sub_0_r in Hh'.
  destruct (Nat.eq_dec i j) as [<-|NE]; [exact Hj|]. exfalso.
  pose proof (proj1 (List.NoDup_nth_error _) ND i j) as U.
  assert (LI : (i < length (map sc_map_beg l))%nat) by (rewrite length_map; exact (nth_error_lt _ _ _ Hi)).
  apply NE. apply U; [exact LI|]. rewrite !nth_error_map, Hi, Hh'. cbn. congruence.
Qed.

Lemma znth_nth_error : forall {A} (l : list A) i d x, nth_error l i = Some x -> znth l i d = x.
Proof. induction l as [|y l IH]; intros [|i] d x H; cbn in H |- *; try discriminate H; [congruence| apply IH; exact H]. Qed.

Lemma upd_nth_length : forall {A} (l : list A) i x, length (upd_nth l i x) = length l.
Proof. induction l as [|y l IH]; intros [|i] x; cbn; [reflexivity| reflexivity| reflexivity| rewrite IH; reflexivity]. Qed.

Lemma secdel_l1_length : ltac2:(zQ "80!lf!o5!m8!h8!ijf!nf!ir4!ihe>1l@1$3$0>3idx$2>0@2$6^1@2$1$0^2@3$4$2@2$1$0@2$7^3^2@2$5@2$1$0^3N1").
Proof. intros l idx H. unfold secdel_l1. rewrite length_firstn, upd_nth_length. lia. Qed.

(* [comment removed for export] *)

Lemma upd_nth_app_l : forall {A} (l1 l2 : list A) i x, (i < length l1)%nat -> upd_nth (l1 ++ l2) i x = upd_nth l1 i x ++ l2.
Proof. induction l1 as [|y l1 IH]; intros l2 [|i] x H; cbn in H |- *; try lia; [reflexivity| rewrite IH by lia; reflexivity]. Qed.

Lemma upd_nth_last : forall {A} (l : list A) x y, upd_nth (l ++ [x]) (length l) y = l ++ [y].
Proof. induction l as [|z l IH]; intros x y; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma znth_last : forall {A} (l : list A) x d, znth (l ++ [x]) (length l) d = x.
Proof. induction l as [|z l IH]; intros x d; cbn; [reflexivity| apply IH]. Qed.

Lemma upd_nth_perm : forall {A} (l : list A) i x y, nth_error l i = Some y -> Permutation (y :: upd_nth l i x) (x :: l).
Proof.
  induction l as [|z l IH]; intros [|i] x y H; cbn in H |- *; try discriminate H.
  - injection H as ->. apply perm_swap.
  - rewrite (perm_swap z y), (IH _ _ _ H). apply perm_swap.
Qed.

(* [comment removed for export] *)
Lemma secdel_l1_perm : ltac2:(zQ "a0!lf!ik5!ira!h8!m8!hid!ijf!ihe!ip2!itc>1l@1$3$0>3idx$4>1h$0>0@3$6@1$5$0@3$8$0^3^2@2$1$0^1@3$9$0@3$2$0^2@2$7^4^3^4").
Proof.
  intros l idx h Hi. unfold secdel_l1. pose proof (nth_error_lt _ _ _ Hi) as LT.
  destruct l as [|z l1]; [cbn in LT; lia|].
  destruct (exists_last (l := z :: l1) ltac:(discriminate)) as [l0 [x E]]. rewrite E in Hi, LT |- *. clear E.
  rewrite length_app. cbn [length]. replace (length l0 + 1 - 1)%nat with (length l0) by lia. rewrite znth_last.
  destruct (Nat.eq_dec idx (length l0)) as [->|NE].
  - rewrite upd_nth_last. rewrite nth_error_app2, Nat.sub_diag in Hi by lia. cbn in Hi. injection Hi as ->.
    rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. rewrite app_nil_r. apply Permutation_cons_append.
  - assert (LT0 : (idx < length l0)%nat) by (rewrite length_app in LT; cbn in LT; lia).
    rewrite nth_error_app1 in Hi by exact LT0. rewrite upd_nth_app_l by exact LT0.
    rewrite firstn_app, upd_nth_length, Nat.sub_diag, firstn_O, app_nil_r, <- (upd_nth_length l0 idx x), firstn_all.
    rewrite (upd_nth_perm _ _ _ _ Hi). apply Permutation_cons_append.
Qed.

Lemma secdel_l1_in : ltac2:(zQ "h00!lf!te!in2!ijf!ipf!ik5!h8!m8!hid!ikb!iub!iv2!iq5!ihe!iqb!ip2>1l@1$6$0>3idx$7>1h$0>1y$0>0@2$e$1@4$c$0$1$2^4>0@3$3@1$8$0@3$f$0^5^4@2$5$0^3@2$a@3$4$0^3@2$d^6^5@2$9@3$4$0^3^6@1$b@3$3$1@1$2^3@1$2^4").
Proof.
  intros l idx h y ND Hi. pose proof (secdel_l1_perm _ _ _ Hi) as P.
  assert (ND1 : List.NoDup (map sc_map_beg (h :: secdel_l1 l idx))).
  { eapply Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_sym. exact P. }
  cbn [map] in ND1. apply List.NoDup_cons_iff in ND1 as [NI _]. split.
  - intros Hy. split; [apply (Permutation_in _ P); right; exact Hy|]. intros E. apply NI. rewrite <- E. apply in_map. exact Hy.
  - intros [Hy NE]. apply (Permutation_in _ (Permutation_sym P)) in Hy. destruct Hy as [<-|Hy]; [exfalso; exact (NE eq_refl)| exact Hy].
Qed.

Lemma secdel_l1_nodup : ltac2:(zQ "c0!lf!te!iq5!in2!iqb!ik5!h8!m8!hid!ijf!ihe!ip2>1l@1$6$0>3idx$7>1h$0>0@2$4$1@4$2$0$1$3^3>0@3$9@1$8$0@3$b$0^4^3@2$5$0^2@2$4$1@4$2$0$1$3@2$a^5^4").
Proof.
  intros l idx h ND Hi.
  assert (ND1 : List.NoDup (map sc_map_beg (h :: secdel_l1 l idx))).
  { eapply Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_sym. apply secdel_l1_perm. exact Hi. }
  cbn [map] in ND1. apply List.NoDup_cons_iff in ND1 as [_ ND1]. exact ND1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DelSec.
  Variables (st : astate) (XC XB : list Z) (ch : chunk).
  Let U := ch_user_beg ch.
  Let m := ch_chunk_beg ch.
  Let p := ch_alloc_beg ch.
  Let map := sec_map_beg ch.
  Let stD := del_state st ch.
  Hypothesis W : WFQ st (m :: XC) XB.
  Hypothesis IN : ltac2:(zQ "30!u2!jj0!ipf@3$2$0?2ch@1$1?2st").
  Hypothesis SEC : ltac2:(zQ "40!jjd!jk3!ijf!jka@3$2$0@1$3?2ch$1").

  Let KEYS : keys_ok (as_chunks st). Proof. exact (WFQ_keys st _ _ W). Qed.
  Let INJ : forall a b, In a (chunk_list st) -> In b (chunk_list st) -> ch_user_beg a = ch_user_beg b -> a = b.
  Proof. exact (WFQ_inj st _ _ W). Qed.
  Let MU : m + kChunkHeaderSize = U. Proof. subst m U. unfold ch_chunk_beg. lia. Qed.
  Let PERM0 : Permutation (chunk_list st) (ch :: chunk_list stD). Proof. apply del_perm0; assumption. Qed.
  Let IN2 : forall y, In y (chunk_list stD) <-> In y (chunk_list st) /\ ch_user_beg y <> U. Proof. apply del_in; assumption. Qed.
  Let COK : chunk_ok st ch. Proof. exact (WFQ_chunk st _ _ ch W IN). Qed.
  Let SND : List.NoDup (List.map sc_map_beg (as_sec st)).
  Proof. pose proof W as WW. ndestruct WW as (_ & _ & _ & _ & _ & W6 & _). exact W6. Qed.

  (* [comment removed for export] *)
  Lemma sec_entry : exists idx h, nth_error (as_sec st) idx = Some h /\ sc_map_beg h = map
    /\ sc_size h = rq_needed (compute_req (ch_used ch)) /\ sc_map_size h = round_up (sc_size h) kPageSize + kPageSize
    /\ find_sec_idx (as_sec st) map 0%nat = Some idx
    /\ rq_primary (compute_req (ch_used ch)) = false /\ in_primary st p = false /\ ch_rz ch = 2048 /\ U = p + 2048 /\ m = p + 2032.
  Proof.
    ndestruct COK as (K1 & K2 & K3 & K4 & K5). rewrite SEC in K5. ndestruct K5 as (NP & NIP & (i & h & Hi & Hb & Hs & Hm)).
    pose proof (secondary_rz _ NP) as RZ. rewrite <- K3 in RZ.
    exists i, h. split; [exact Hi|]. split; [exact Hb|]. split; [exact Hs|]. split; [exact Hm|].
    split; [exact (find_sec_idx_nodup _ _ _ _ SND Hi Hb)|].
    split; [exact NP|]. split; [exact NIP|]. split; [exact RZ|].
    clear - K4 RZ. subst m U p. unfold ch_chunk_beg, kChunkHeaderSize. split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_records_map_inj : forall y, In y (chunk_list st) -> ch_primary y = false -> sec_map_beg y = map -> y = ch.
  Proof.
    intros y Hy SY E. apply INJ; [exact Hy| exact IN|].
    pose proof (WFQ_chunk st _ _ y W Hy) as (_ & _ & R3 & R4 & REST). rewrite SY in REST. destruct REST as (NPy & _).
    ndestruct COK as (_ & _ & K3 & K4 & K5). rewrite SEC in K5. destruct K5 as (NP & _).
    rewrite R4, K4, R3, K3, (secondary_rz _ NPy), (secondary_rz _ NP). unfold sec_map_beg in E. fold map in E. unfold map, sec_map_beg in E. lia.
  Qed.

  (* [comment removed for export] *)
  Let MNEW : ~ In m (flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st))).
  Proof. intros H. pose proof (WFQ_qnodup st _ _ W) as ND. apply (NoDup_remove_2 _ _ _ ND). apply in_or_app. left. exact H. Qed.
  Let OLDQ : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) -> q + kChunkHeaderSize <> U.
  Proof. intros b q Hb Hq E. apply MNEW. apply in_flat_map. exists b. split; [exact Hb|]. replace m with q by (clear - E MU; lia). exact Hq. Qed.
  Let FCB : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) ->
    find_chunk (as_chunks stD) (q + kChunkHeaderSize) = find_chunk (as_chunks st) (q + kChunkHeaderSize).
  Proof.
    intros b q Hb Hq. destruct (Z.le_gt_cases (q + kChunkHeaderSize) 0) as [LE|GT].
    - unfold find_chunk. replace (q + kChunkHeaderSize <=? 0) with true by (symmetry; apply Z.leb_le; exact LE). reflexivity.
    - apply del_find_other; [exact KEYS| exact IN| exact GT| exact (OLDQ b q Hb Hq)].
  Qed.
  Let BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> batch_ok st b -> batch_ok stD b.
  Proof.
    (intros b Hb nd_i2; ndestruct nd_i2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9)). unfold batch_ok. unfold stD, del_state, set_chunks.
    cbn [as_space_beg as_regions as_chunks in_primary class_of_addr region_beg get_region].
    refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj _ _)))))))).
    - rewrite B8. f_equal. apply fold_used_ext. intros q Hq. pose proof (FCB b q Hb Hq) as E. unfold stD, del_state, set_chunks in E. cbn [as_chunks] in E. rewrite E. reflexivity.
    - intros q Hq. pose proof (FCB b q Hb Hq) as E. unfold stD, del_state, set_chunks in E. cbn [as_chunks] in E. rewrite E. apply B9. exact Hq.
  Qed.

  Section WithEntry.
    Variables (idx : nat) (h : schunk).
    Hypothesis HIDX : ltac2:(zQ "60!lf!ik5!hid!ijf!hj5!ip2@3$3@1$2$0@3$5$0@1$4?2st?3idx@2$1$0?1h").
    Hypothesis HMAP : sc_map_beg h = map.
    Let l1 := secdel_l1 (as_sec st) idx.
    Let st2 := remove_map (set_sec stD (as_n_reserved st) l1) map.

    Lemma secdel_eq : secdel st ch = st2.
    Proof. unfold secdel. fold map. rewrite (find_sec_idx_nodup _ _ _ _ SND HIDX HMAP). reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma secdel_fields :
         as_space_beg st2 = as_space_beg st /\ as_ptr_array st2 = as_ptr_array st /\ as_regions st2 = as_regions st
      /\ as_cache_inited st2 = as_cache_inited st /\ as_cache st2 = as_cache st /\ as_n_reserved st2 = as_n_reserved st
      /\ as_sec st2 = l1 /\ as_chunks st2 = remove_chunk (as_chunks st) U /\ as_tq st2 = as_tq st /\ as_gq st2 = as_gq st
      /\ as_internal_init st2 = as_internal_init st /\ as_maps st2 = List.filter (fun mp => negb (mp_base mp =? map)) (as_maps st)
      /\ as_qmax st2 = as_qmax st /\ as_qmin st2 = as_qmin st /\ as_qcache st2 = as_qcache st
      /\ chunk_list st2 = chunk_list stD /\ (forall c, get_region st2 c = get_region st c) /\ (forall c, get_pc st2 c = get_pc st c)
      /\ (forall a, class_of_addr st2 a = class_of_addr st a) /\ (forall a, in_primary st2 a = in_primary st a) /\ (forall c, region_beg st2 c = region_beg st c).
    Proof. unfold st2, stD, del_state, remove_map, set_sec, set_chunks, chunk_list, get_region, get_pc, class_of_addr, in_primary, region_beg; cbn. repeat split; reflexivity. Qed.

    Theorem WFQ_del_sec_at : WFQ st2 XC XB.
    Proof.
      pose proof W as WW.
      ndestruct WW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
      npose secdel_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21).
      npose sec_entry as (i0 & h0 & Hi0 & Hb0 & _ & _ & FX0 & NP & NIP & RZ & UP & MP).
      assert (EI : i0 = idx) by (pose proof (find_sec_idx_nodup _ _ _ _ SND HIDX HMAP) as FX1; congruence). subst i0.
      assert (EH : h0 = h) by congruence. subst h0. clear Hi0 Hb0.
      pose proof (nth_error_lt _ _ _ HIDX) as LT.
      unfold WFQ. rewrite F16, F7, F6, F9, F10, F8, F13, F14, F15, F3, F5.
      split. { intros c Hc. destruct (W1 c Hc) as [R0 C0]. split; [destruct R0; constructor; rewrite ?F17; assumption| destruct C0; constructor; rewrite ?F17, ?F18, ?F4; assumption]. }
      split. { (* [comment removed for export] *)
        unfold carved_addr_list in W2 |- *. rewrite F16, F9, F10.
        replace (flat_map (fun c => List.map (compact_to_addr st2 c) (rg_free_array (get_region st2 c)) ++ List.map (compact_to_addr st2 c) (pc_chunks (get_pc st2 c))) (List.map Z.of_nat (seq 0 32)))
          with (flat_map (fun c => List.map (compact_to_addr st c) (rg_free_array (get_region st c)) ++ List.map (compact_to_addr st c) (pc_chunks (get_pc st c))) (List.map Z.of_nat (seq 0 32))).
        2:{ apply flat_map_ext. intros c. rewrite F17, F18. unfold compact_to_addr. rewrite F21. reflexivity. }
        eapply Permutation_NoDup; [| exact W2]. apply Permutation_app_tail. apply Permutation_app_head. apply Permutation_app_tail.
        rewrite (Permutation_map ch_alloc_beg (Permutation_filter ch_primary _ _ PERM0)). cbn [List.filter]. rewrite SEC. reflexivity. }
      split. { (* [comment removed for export] *)
        intros y Hy. apply IN2 in Hy as [Hy NEy]. pose proof (W3 y Hy) as CO. npose CO as (R1 & R2 & R3 & R4 & REST).
        unfold chunk_ok. rewrite F19, F20, F17, F21. refine (conj R1 (conj R2 (conj R3 (conj R4 _)))).
        destruct (ch_primary y) eqn:PY; [exact REST|]. ndestruct REST as (NPy & NIPy & (iy & hy & Hiy & Hby & Hsy & Hmy)).
        split; [exact NPy|]. split; [exact NIPy|].
        assert (NEh : sc_map_beg hy <> sc_map_beg h).
        { rewrite HMAP. intros E. apply NEy. rewrite (sec_records_map_inj y Hy PY); [reflexivity|]. unfold sec_map_beg. rewrite <- Hby, E. reflexivity. }
        assert (INy : In hy l1) by (apply (proj2 (secdel_l1_in _ _ _ _ SND HIDX)); split; [eapply nth_error_In; exact Hiy| exact NEh]).
        apply In_nth_error in INy as [j Hj]. exists j, hy. split; [exact Hj|]. split; [exact Hby|]. split; [exact Hsy| exact Hmy]. }
      split. { intros a b Ha Hb. apply IN2 in Ha as [Ha _]. apply IN2 in Hb as [Hb _]. exact (W4 a b Ha Hb). }
      split. { (* [comment removed for export] *)
        unfold zlen in W5 |- *. erewrite (Permutation_length (Permutation_filter _ _ _ PERM0)) in W5. cbn [List.filter] in W5. rewrite SEC in W5. cbn [negb length] in W5.
        unfold l1. rewrite secdel_l1_length by exact LT. lia. }
      split; [exact (secdel_l1_nodup _ _ _ SND HIDX)|].
      split. { unfold l1, zlen in *. rewrite secdel_l1_length by exact LT. lia. }
      split; [exact W8|].
      split. { split; [| exact (proj2 W9)]. intros b Hb. pose proof (BOK b ltac:(apply in_or_app; left; exact Hb) (proj1 W9 b Hb)) as BB.
               revert BB. unfold batch_ok. rewrite F20, F19, F21, F17, F8. unfold stD, del_state, set_chunks. cbn. fold U. exact (fun x => x). }
      split. { split; [| exact (proj2 W10)]. intros b Hb. pose proof (BOK b ltac:(apply in_or_app; right; exact Hb) (proj1 W10 b Hb)) as BB.
               revert BB. unfold batch_ok. rewrite F20, F19, F21, F17, F8. unfold stD, del_state, set_chunks. cbn. fold U. exact (fun x => x). }
      split. { eapply NoDup_remove_1. exact W11. }
      split. { intros y Hy Hq. apply IN2 in Hy as [Hy NE]. destruct (W12 y Hy Hq) as [E|[E|E]]; [left; exact E| | right; exact E].
               exfalso. apply NE. rewrite <- MU, E. unfold ch_chunk_beg, kChunkHeaderSize. lia. }
      split; [rewrite F17; exact W13|]. split; [rewrite F17; exact W14|]. split; [rewrite F18; exact W15|]. split; [rewrite F18; exact W16|].
      split; [exact W17|]. split; [exact W18|]. split; [exact W19|]. split; [exact W20|]. split; [exact W21|].
      split. { fold U. exact (del_keys st ch KEYS). }
      split. { intros m' Hm'. unfold xc_ok. rewrite F8. destruct (W23 m' ltac:(right; exact Hm')) as [x [Fx Qx]]. exists x. split; [| exact Qx].
               rewrite find_remove_other; [exact Fx| exact (del_upos st ch KEYS IN)| |].
               - destruct (Z.le_gt_cases (m' + kChunkHeaderSize) 0) as [LE|GT]; [| exact GT]. exfalso. unfold find_chunk in Fx.
                 replace (m' + kChunkHeaderSize <=? 0) with true in Fx by (symmetry; apply Z.leb_le; exact LE). discriminate Fx.
               - intros E. apply (NoDup_remove_2 _ _ _ W11). apply in_or_app. right. replace m with m' by (clear - E MU; lia). exact Hm'. }
      intros B HB. apply (xb_ok_ext _ st); [exact F1| exact F3| exact (W24 B HB)].
    Qed.
  End WithEntry.
End DelSec.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nearest_le_keep : ltac2:(zQ "a0!lf!in2!ik5!iv9!h8!hid!ijf!te!ivf!ipf>1l@1$4$0>1m$7>1x$0>0>1h$0>0@3$9$0^1^4>0@2$3@1$1^2^4@2$3@1$1^3@1$1^4@3$6@1$5$0@3$8^4^3@2$2$0^2@2$2$0^2").
Proof.
  induction l as [|h l IH]; intros m x Hl; cbn [nearest_le]; [reflexivity|].
  destruct (Z.ltb_spec m (sc_map_beg h)) as [LT|GE]; [apply IH; intros hh HH; apply Hl; right; exact HH|].
  pose proof (Hl h ltac:(left; reflexivity) GE) as LE.
  replace (m - sc_map_beg h <? m - sc_map_beg x) with false by (symmetry; apply Z.ltb_ge; lia).
  apply IH. intros hh HH. apply Hl. right. exact HH.
Qed.

Lemma nearest_le_at : ltac2:(zQ "f0!lf!in2!hid!ijf!ik5!jgc!ipf!iv9!jh2!jh8!h8!ikb!il2!te!ivf>1l@1$a$0>1m$d>1x$0>4best@1$2$0>0@3$6$0^2^4>0@2$7@1$1^3^4>0>1h$0>0@3$6$0^1^7>0@2$7@1$1^2^7@2$5@3$3$0^3^7@2$8@1$1^3@1$1^7>0@2$5@3$3@1$2$0^4@1$9$0@2$c$0\1b$0@2$b@3$3@1$2$0^5@2$4$0^1@2$8@1$1^1@1$1^6@3$3@1$2$0@3$e^8^7^5@2$4$0^6").
Proof.
  induction l as [|h l IH]; intros m x best Hin Hx Hl Hb; [destruct Hin|]. cbn [nearest_le].
  assert (HL' : forall hh, In hh l -> sc_map_beg hh <= m -> hh = x \/ sc_map_beg hh < sc_map_beg x) by (intros hh HH; apply Hl; right; exact HH).
  destruct (Z.ltb_spec m (sc_map_beg h)) as [LT|GE].
  - destruct Hin as [->|Hin]; [lia|]. exact (IH m x best Hin Hx HL' Hb).
  - destruct (Hl h ltac:(left; reflexivity) GE) as [->|LTx].
    + assert (KEEP : nearest_le l m (Some x) = Some x) by (apply nearest_le_keep; intros hh HH Hm; destruct (HL' hh HH Hm) as [->|K]; lia).
      destruct Hb as [->|(b & -> & Hbx)]; [exact KEEP|].
      replace (m - sc_map_beg x <? m - sc_map_beg b) with true by (symmetry; apply Z.ltb_lt; lia). exact KEEP.
    + assert (Hin' : In x l) by (destruct Hin as [E|Hin]; [exfalso; rewrite E in LTx; lia| exact Hin]).
      destruct Hb as [->|(b & -> & Hbx)].
      * apply IH; [exact Hin'| exact Hx| exact HL'| right; exists h; split; [reflexivity| exact LTx]].
      * destruct (m - sc_map_beg h <? m - sc_map_beg b);
          (apply IH; [exact Hin'| exact Hx| exact HL'| right; eexists; split; [reflexivity| assumption]]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_pagemask_0 : ltac2:(zQ "60!te!ijf!v9!jhe!ji6!hhd>1x$0>0@3$1$0@2$4^1$2Z@3$1$0@2$3^2@2$5$2+1Z").
Proof. intros x H. unfold kPageSize in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. exact H. Qed.
Lemma land7_of_mod8 : ltac2:(zQ "40!te!ijf!jhe!ji6>1x$0>0@3$1$0@2$3^1+8Z@3$1$0@2$2^2+7Z").
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact H. Qed.

Section RecycleSecEval.
  Variables (stA st : astate) (XC XB : list Z) (ch : chunk) (idx : nat) (h : schunk).
  Let U := ch_user_beg ch.
  Let m := ch_chunk_beg ch.
  Let p := ch_alloc_beg ch.
  Let map := sec_map_beg ch.
  Let msz := sc_map_size h.
  Hypothesis SBS : ltac2:(zQ "10!jpb@2$0?3stA?2st").
  Hypothesis W : WFQ st (m :: XC) XB.
  Hypothesis IN : ltac2:(zQ "30!u2!jj0!ipf@3$2$0?2ch@1$1?2st").
  Hypothesis SEC : ltac2:(zQ "40!jjd!jk3!ijf!jka@3$2$0@1$3?2ch$1").
  Hypothesis QUAR : ltac2:(zQ "40!ijf!jqe!jrc!js7@3$0$3@1$2?2ch$1").
  Hypothesis HIDX : ltac2:(zQ "60!lf!ik5!hid!ijf!hj5!ip2@3$3@1$2$0@3$5$0@1$4?2st?3idx@2$1$0?1h").
  Hypothesis HMAP : sc_map_beg h = map.
  (* [comment removed for export] *)
  Hypothesis ALN : map mod kPageSize = 0 /\ msz mod kPageSize = 0.
  Hypothesis AIM : addr_is_in_mem map = true /\ addr_is_in_mem (map + msz - 8) = true /\ addr_is_in_mem (map + msz) = true.
  Hypothesis NIPM : in_primary st m = false.
  Hypothesis NEAR : forall h', In h' (as_sec st) -> sc_map_beg h' <= m -> h' = h \/ sc_map_beg h' < map.

  Let KEYS : keys_ok (as_chunks st). Proof. exact (WFQ_keys st _ _ W). Qed.
  Let SND : List.NoDup (List.map sc_map_beg (as_sec st)).
  Proof. pose proof W as WW. ndestruct WW as (_ & _ & _ & _ & _ & W6 & _). exact W6. Qed.

  Lemma cb_recycle_sec_eval : exists stA' ev, cb_recycle stA m = Some (stA', ev) /\ same_but_shadow stA' (secdel st ch).
  Proof.
    npose (sec_entry st XC XB ch W IN SEC) as (i0 & h0 & Hi0 & Hb0 & Hs0 & Hm0 & FX0 & NP & NIP & RZ & UP & MP).
    pose proof (find_sec_idx_nodup _ _ _ _ SND HIDX HMAP) as FX1. change map with (sec_map_beg ch) in FX1.
    assert (EI : i0 = idx) by congruence. subst i0.
    assert (EH : h0 = h) by congruence. subst h0. clear Hi0 Hb0.
    fold p in NIP, UP, MP. fold U in UP. fold msz in Hm0.
    pose proof (del_find st ch KEYS IN) as FIND. fold U in FIND.
    pose proof SBS as SB. unfold same_but_shadow in SB. ndestruct SB as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16).
    destruct (WFQ_chunk st _ _ ch W IN) as (K1 & _).
    assert (MSZ : kPageSize + kPageSize <= msz).
    { rewrite Hm0, Hs0. npose (compute_req_facts (ch_used ch) ltac:(clear - K1; lia)) as (R1 & R2 & R3 & R4 & RN & _).
      assert (ND1 : 1 <= rq_needed (compute_req (ch_used ch))) by (rewrite RN; clear - R2 R3 K1; destruct (rq_primary (compute_req (ch_used ch))); lia).
      unfold round_up, kPageSize. set (nd := rq_needed (compute_req (ch_used ch))) in *.
      assert (KQ : 1 <= (nd + 4096 - 1) / 4096) by (apply Z.div_le_lower_bound; clear - ND1; lia). clear - KQ. nia. }
    assert (PMAP : p = map + kPageSize) by (unfold map, sec_map_beg; fold p; lia).
    destruct ALN as [AL1 AL2]. ndestruct AIM as (M1 & M2 & M3).
    assert (MAP0 : 0 <= map).
    { clear - M1. unfold addr_is_in_mem, kHighMemBeg in M1. apply orb_prop in M1.
      destruct M1 as [M1|M1]; apply andb_prop in M1 as [M1 _]; apply Z.leb_le in M1; lia. }
    unfold cb_recycle.
    replace (find_chunk (as_chunks stA) (m + kChunkHeaderSize)) with (Some ch).
    2:{ rewrite E8. replace (m + kChunkHeaderSize) with U by (unfold m, U, ch_chunk_beg; lia). symmetry. exact FIND. }
    rewrite QUAR.
    replace (in_primary stA m) with false by (unfold in_primary; rewrite E1; symmetry; exact NIPM).
    (* [comment removed for export] *)
    replace (large_get_block_begin stA m) with (Some p).
    2:{ unfold large_get_block_begin. rewrite E7.
        rewrite (nearest_le_at (as_sec st) m h None ltac:(eapply nth_error_In; exact HIDX) ltac:(rewrite HMAP; unfold map, sec_map_beg; fold p; clear - MP; unfold kPageSize; lia)).
        - replace (sc_map_beg h + sc_map_size h <=? m) with false by (symmetry; apply Z.leb_gt; rewrite HMAP; fold msz; clear - MP MSZ PMAP; unfold kPageSize in *; lia).
          rewrite HMAP, PMAP. reflexivity.
        - intros h' H' LE. destruct (NEAR h' H' LE) as [->|LT]; [left; reflexivity| right; rewrite HMAP; exact LT].
        - left. reflexivity. }
    replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; clear - MAP0 PMAP; unfold kPageSize in PMAP; lia).
    replace (in_primary stA p) with false by (unfold in_primary; rewrite E1; symmetry; exact NIP).
    change (ch_alloc_beg ch) with p. rewrite Z.eqb_refl. cbn [negb].
    (* [comment removed for export] *)
    unfold large_deallocate.
    rewrite (land_pagemask_0 p) by (rewrite PMAP; destruct ALN as [A _]; unfold kPageSize in *; clear - A; Z.div_mod_to_equations; lia). cbn [negb Z.eqb].
    cbn [as_sec set_chunks]. rewrite E7.
    replace (p - kPageSize) with map by (clear - PMAP; lia).
    rewrite (find_sec_idx_nodup _ _ _ _ SND HIDX HMAP).
    rewrite (znth_nth_error _ _ _ _ HIDX). fold msz.
    assert (AL1' : map mod 8 = 0) by (clear - AL1; unfold kPageSize in AL1; Z.div_mod_to_equations; lia).
    assert (AL2' : msz mod 8 = 0) by (clear - AL2; unfold kPageSize in AL2; Z.div_mod_to_equations; lia).
    lazymatch goal with |- context [poison_shadow ?stX ?aX ?nX 0] =>
      destruct (poison_shadow_some stX aX nX 0 (land7_of_mod8 _ AL1') M1 (land7_of_mod8 _ AL2') M2) as (st2 & ev2 & EPS & SB2); rewrite EPS end.
    rewrite M1, M3. cbn [andb negb].
    neexists 2. split; [reflexivity|].
    (* [comment removed for export] *)
    rewrite (secdel_eq st XC XB ch W idx h HIDX HMAP).
    revert SB2. unfold same_but_shadow. destruct st2, stA, st; cbn in *. subst.
    (intros nd_i3; ndestruct nd_i3 as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->)). cbn. repeat split; reflexivity.
  Qed.
End RecycleSecEval.
(* [comment removed for export] *)
