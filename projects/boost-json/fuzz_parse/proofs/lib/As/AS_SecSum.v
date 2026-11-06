(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AsanAllocCons.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AllocWf AllocKit AllocRepFacts AG_MallocModel AG_WFHit SecGap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6SecGap~~~~~~jb4zsum37Corelib4Init5Logicne2eq36Stdlib7SortingbPermutationp7bPermutationhc4bool69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~s85chunkhc4negbs8ach_primarys89kPageSizes8bcompute_reqs88round_ups89rq_needed46Stdlib6ZArith6BinInt1Zhl63adds8cch_alloc_beghl63subne3ands87ch_useds86schunk36Stdlib5Lists4Listhq42Inhc5falsehc4truene2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AS_SecSum~~~~~~ht13npbht16secmszht13smbs86as_secs8bch_user_begs8achunk_lists8arq_primarys8asc_map_begs8bsc_map_sizehl62lehq46filterne3iff89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AS_SecSum9WithState~~~~~~ioa3NPL37Corelib5Lists7ListDefita3maphc6optionhq44findhl63eqbioa3szk69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanAllocCons~~~~~~jh76allocbs84zlenhl63muljh74QTOThl63powhl62lts86astate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AllocWf~~~~~~jod2WF" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsum_perm : ltac2:(zQ "50!h9!j4!n7!p2!r3>1l@1$1$0>2l'@1$1$0>0@3$4$0^2^1@3$3$0@1$2^3@1$2^2").
Proof. intros l l' P. induction P; cbn [zsum] in *; lia. Qed.

Lemma zsum_map_le {A} : forall (f g : A -> Z) (l : list A), (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof.
  intros f g l H. induction l as [|x l IH]; cbn [zsum map]; [lia|].
  pose proof (H x (or_introl eq_refl)). specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)). lia.
Qed.

Lemma zsum_map_const_le {A} : forall (f : A -> Z) (K : Z) (l : list A), (forall x, In x l -> f x <= K) -> zsum (map f l) <= K * zlen l.
Proof.
  intros f K l H. unfold zlen. induction l as [|x l IH]; cbn [zsum map length]; [lia|].
  rewrite Nat2Z.inj_succ. pose proof (H x (or_introl eq_refl)). specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)). lia.
Qed.

Lemma zsum_map_const_ge {A} : forall (f : A -> Z) (K : Z) (l : list A), (forall x, In x l -> K <= f x) -> K * zlen l <= zsum (map f l).
Proof.
  intros f K l H. unfold zlen. induction l as [|x l IH]; cbn [zsum map length]; [lia|].
  rewrite Nat2Z.inj_succ. pose proof (H x (or_introl eq_refl)). specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)). lia.
Qed.

Lemma zsum_map_nonneg {A} : forall (f : A -> Z) (l : list A), (forall x, In x l -> 0 <= f x) -> 0 <= zsum (map f l).
Proof. intros f l H. pose proof (zsum_map_const_ge f 0 l H). lia. Qed.

(* [comment removed for export] *)
Lemma zsum_map_filter_split {A} : forall (f : A -> Z) (p : A -> bool) (l : list A),
  zsum (map f l) = zsum (map f (List.filter p l)) + zsum (map f (List.filter (fun x => negb (p x)) l)).
Proof.
  intros f p l. induction l as [|x l IH]; [reflexivity|]. cbn [map List.filter]. destruct (p x); cbn [negb map zsum]; lia.
Qed.

Lemma zsum_map_filter_le {A} : forall (f : A -> Z) (p : A -> bool) (l : list A),
  (forall x, In x l -> 0 <= f x) -> zsum (map f (List.filter p l)) <= zsum (map f l).
Proof.
  intros f p l H. rewrite (zsum_map_filter_split f p l).
  pose proof (zsum_map_nonneg f (List.filter (fun x => negb (p x)) l) ltac:(intros x Hx; apply H; apply filter_In in Hx; tauto)). lia.
Qed.
Lemma zlen_filter_le' {A} : forall (p : A -> bool) (l : list A), zlen (List.filter p l) <= zlen l.
Proof. intros p l. unfold zlen. induction l as [|x l IH]; cbn; [lia|]. destruct (p x); cbn; lia. Qed.

(* [comment removed for export] *)
Lemma NoDup_incl_split {A} : forall (l1 l2 : list A), List.NoDup l1 -> List.NoDup l2 -> incl l1 l2 ->
  exists l3, Permutation l2 (l1 ++ l3).
Proof.
  intros l1. induction l1 as [|x l1 IH]; intros l2 N1 N2 INC.
  - exists l2. reflexivity.
  - ndestruct (in_split x l2 (INC x (or_introl eq_refl))) as (la & lb & ->).
    apply NoDup_cons_iff in N1 as [NX N1].
    destruct (IH (la ++ lb) N1 (NoDup_remove_1 _ _ _ N2)) as (l3 & P).
    { intros y Hy. pose proof (INC y (or_intror Hy)) as IN. apply in_app_iff in IN. apply in_app_iff.
      destruct IN as [IN|[<-|IN]]; [left; exact IN| exfalso; exact (NX Hy)| right; exact IN]. }
    exists l3. rewrite <- Permutation_middle. cbn [app]. apply perm_skip. exact P.
Qed.

Lemma filter_and {A} : forall (f g : A -> bool) (l : list A), List.filter f (List.filter g l) = List.filter (fun x => g x && f x) l.
Proof.
  intros f g l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. destruct (g x); cbn [andb List.filter]; [| exact IH].
  destruct (f x); [cbn; rewrite IH; reflexivity| exact IH].
Qed.

(* [comment removed for export] *)
Lemma NoDup_map_key_unique {A} : forall (k : A -> Z) (l : list A) (a b : A),
  List.NoDup (map k l) -> In a l -> In b l -> k a = k b -> a = b.
Proof.
  intros k l. induction l as [|x l IH]; intros a b ND Ha Hb E; [destruct Ha|].
  cbn [map] in ND. apply NoDup_cons_iff in ND as [NI ND].
  destruct Ha as [<-|Ha]; destruct Hb as [<-|Hb].
  - reflexivity.
  - exfalso. apply NI. rewrite E. apply in_map. exact Hb.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Ha.
  - exact (IH a b ND Ha Hb E).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition npb : ltac2:(zQ "20!s1!hg9>2ch$1$0") := ltac2:(zQ "30!hh1!hh8!hg9\2ch$2@1$0@1$1^1").
(* [comment removed for export] *)
Definition secmsz : ltac2:(zQ "10!h9>4size$0$0") := ltac2:(zQ "60!hi5!h9!hj1!hjf!hka!hme\4size$1@2$5@2$3@1$4@1$2^1$0$0").
Definition smb : ltac2:(zQ "20!h9!hg9>2ch$1$0") := ltac2:(zQ "40!hn5!hg9!hi5!ho4\2ch$1@2$3@1$0^1$2").       (* [comment removed for export] *)

Section WithState.
  Variable st : ltac2:(zQ "10!jo4$0").
  Hypothesis W : ltac2:(zQ "10!jsa@1$0?2st").

  Let KEYS : keys_ok (as_chunks st). Proof. exact (WF_keys st W). Qed.
  Let SND : List.NoDup (map sc_map_beg (as_sec st)).
  Proof. pose proof W as WW. ndestruct WW as (_ & _ & _ & _ & _ & W6 & _). exact W6. Qed.
  Let SCNT : zlen (List.filter npb (chunk_list st)) = zlen (as_sec st).
  Proof. pose proof W as WW. ndestruct WW as (_ & _ & _ & _ & W5 & _). exact W5. Qed.
  Let INJ : forall a b, In a (chunk_list st) -> In b (chunk_list st) -> ch_user_beg a = ch_user_beg b -> a = b.
  Proof. pose proof W as WW. ndestruct WW as (_ & _ & _ & W4 & _). exact W4. Qed.

  (* [comment removed for export] *)
  Lemma np_entry : ltac2:(zQ "h80!hob!p2!h9!hp1!hpb!s1!hg9!hr7!hrd!hs5!hsc!ih0!ih7!ii1!ii8!hn5!ij1!ijf!hj1!ikc!il9!im6!hme!in4>2ch$6>0@3$7$6^1@1$h1?2st>0@3$1$5@1$b^2$9@2$a$4\1h$4@2$0@3$7$4^1@1$e?2st@2$0@3$1$2@1$h4^1@1$d^4@2$0@3$1$2@1$h5^1@1$c@1$3^4@2$0@3$1$2@1$h0^4@2$h6@1$f^4+og0@2$0@3$1$5@1$h3@1$h2@1$3^4$8@2$h7+1@1$3^4").
  Proof.
    intros ch Hin NP. pose proof (WF_chunk st ch W Hin) as CO. unfold chunk_ok in CO. cbv zeta in CO.
    ndestruct CO as (U1 & U2 & RZ & UB & REST). unfold npb in NP. destruct (ch_primary ch); [discriminate NP|].
    ndestruct REST as (NPR & _ & (i & h & NTH & HB & HS & HM)).
    exists h. split; [exact (nth_error_In _ _ NTH)|]. split; [rewrite HB; reflexivity|].
    split; [rewrite HM, HS; reflexivity|].
    split; [rewrite UB, RZ, (secondary_rz _ NPR); reflexivity|]. exact (conj NPR U1).
  Qed.

  (* [comment removed for export] *)
  Lemma smb_inj : ltac2:(zQ "90!hg9!p2!s1!hs5!ih0!ii1!ijf!hr7!h9>1a$0>1b$0>0@3$7$0^2@1$6?2st>0@3$7$0^2@1$6?2st>0@3$1$2@1$4^4$3>0@3$1$2@1$4^4$3>0@3$1$8@1$5^6@1$5^5@3$1$0^7^6").
  Proof.
    intros a b Ha Hb Na Nb E. apply INJ; [exact Ha| exact Hb|].
    ndestruct (np_entry a Ha Na) as (_ & _ & _ & _ & Ua & _). ndestruct (np_entry b Hb Nb) as (_ & _ & _ & _ & Ub & _).
    unfold smb in E. rewrite Ua, Ub. lia.
  Qed.

  Definition NPL : ltac2:(zQ "20!j4!hg9@1$0$1") := ltac2:(zQ "40!ih0!hg9!ijf!ina@3$3$1$0@1$2?2st").

  Lemma NPL_in : ltac2:(zQ "a0!hg9!hr7!s1!hs5!hob!p2!io4!it3!ih0!ijf>2ch$0@2$6@3$1$0^1$7@2$4@3$1$0^1@1$9?2st@3$5$2@1$8^1$3").
  Proof. intros ch. unfold NPL. apply filter_In. Qed.

  (* [comment removed for export] *)
  Lemma perm_keys : ltac2:(zQ "90!h9!iv1!it3!ii1!ii8!hg9!il9!hpb!r3@3$8$0@4$1$5$0$3$2@4$1$7$0$6@1$4?2st").
  Proof.
    apply NoDup_Permutation_bis.
    - apply (NoDup_map_NoDup_ForallPairs).
      + intros x y Hx Hy E. apply NPL_in in Hx as [Hx Nx]. apply NPL_in in Hy as [Hy Ny]. exact (smb_inj x y Hx Hy Nx Ny E).
      + unfold NPL. apply NoDup_filter. apply chunk_list_nodup. exact KEYS.
    - rewrite !length_map. pose proof SCNT as C. unfold zlen, NPL in *. lia.
    - intros k Hk. apply in_map_iff in Hk. ndestruct Hk as (ch & <- & Hch). apply NPL_in in Hch as [Hch Nch].
      ndestruct (np_entry ch Hch Nch) as (h & Hh & HB & _). rewrite <- HB. apply in_map. exact Hh.
  Qed.

  (* [comment removed for export] *)
  Definition szk : ltac2:(zQ "10!h9>1k$0$0") := ltac2:(zQ "80!hpb!iv8!h9!ii8!il9!im6!jg1!jg9\1k$2M1\1x@1$1$0$2@3$6$0\1h$0@2$7@1$4^1^2@1$3?2st\1h$0@1$5^1Z").

  Lemma szk_entry : ltac2:(zQ "80!hpb!p2!h9!jh0!ii8!il9!im6!hr7>1h$0>0@3$7$0^1@1$4?2st@3$1$2@1$3@1$5^2@1$6^2").
  Proof.
    intros h Hh. unfold szk. destruct (find (fun h0 => sc_map_beg h0 =? sc_map_beg h) (as_sec st)) as [h'|] eqn:F.
    - apply find_some in F as [Hh' E]. apply Z.eqb_eq in E. rewrite (NoDup_map_key_unique sc_map_beg (as_sec st) h' h SND Hh' Hh E). reflexivity.
    - exfalso. pose proof (find_none _ _ F h Hh) as E. cbn beta in E. rewrite Z.eqb_refl in E. discriminate E.
  Qed.
  Lemma szk_chunk : ltac2:(zQ "90!hg9!p2!h9!it3!jh0!ih7!ii1!hp1!hr7>2ch$0>0@3$8$0^1$3@3$1$2@1$4@1$6^2@1$5@1$7^2").
  Proof.
    intros ch Hch. apply NPL_in in Hch as [Hch Nch]. ndestruct (np_entry ch Hch Nch) as (h & Hh & HB & HS & _).
    rewrite <- HB, (szk_entry h Hh). exact HS.
  Qed.

  (* [comment removed for export] *)
  Theorem sec_sum_eq : ltac2:(zQ "b0!h9!iv1!n7!hg9!p2!it3!ih7!ii8!hp1!im6!hpb@3$4$0@1$2@4$1$a$0$9@1$7?2st@1$2@4$1$3$0\2ch$3@1$6@1$8^1$5").
  Proof.
    transitivity (zsum (map szk (map sc_map_beg (as_sec st)))).
    { rewrite map_map. f_equal. apply map_ext_in. intros h Hh. symmetry. exact (szk_entry h Hh). }
    rewrite <- (zsum_perm _ _ (Permutation_map szk perm_keys)). rewrite map_map. f_equal. apply map_ext_in.
    intros ch Hch. exact (szk_chunk ch Hch).
  Qed.

  (* [comment removed for export] *)
  Theorem sec_sum_bound : ltac2:(zQ "h20!hg9!h9!im6!hpb!in4!iv1!it3!n7!jl7!ii8!ina!hme!hh1!hob!hp1!jm1!hr7!jm8>4AMAX$1>0>2sc$3>0@3$h0$3^1@1$9?2st@2$d@2$4Z@1$2^2@2$4@1$2^2^3@2$4@1$7@4$5$3$1$2@1$9?2st@2$b@1$7@4$5$0$1\2ch$0@2$b@1$e^1+jgg6@3$a$0$8$6@2$h1^2@2$f$0@3$a$0\2ch$0@1$c@1$8^1$6").
  Proof.
    intros AMAX HA. rewrite sec_sum_eq. rewrite (zsum_map_filter_split _ allocb NPL).
    assert (L1 : zsum (map (fun ch => secmsz (ch_used ch)) (List.filter allocb NPL)) <= zsum (map (fun ch => ch_used ch + 12294) (List.filter allocb NPL))).
    { apply zsum_map_le. intros ch Hch. apply filter_In in Hch as [Hch _]. apply NPL_in in Hch as [Hch Nch].
      ndestruct (np_entry ch Hch Nch) as (_ & _ & _ & _ & _ & NPR & U1).
      unfold secmsz. npose (req_shape (ch_used ch) U1) as (_ & _ & ND & _ & RU). pose proof (rz_size_facts (ch_used ch)) as (RZ & _).
      rewrite ND. unfold round_up, kPageSize in *.
      set (rz := rz_size (ch_used ch)) in *. set (b := if rq_primary (compute_req (ch_used ch)) then 0 else rz) in *.
      assert (Hb : 0 <= b <= 2048) by (subst b; destruct (rq_primary _); lia).
      clearbody b rz. Z.div_mod_to_equations. lia. }
    assert (L2 : zsum (map (fun ch => secmsz (ch_used ch)) (List.filter (fun ch => negb (allocb ch)) NPL)) <= AMAX * zlen (List.filter (fun ch => negb (allocb ch)) NPL)).
    { apply zsum_map_const_le. intros ch Hch. apply filter_In in Hch as [Hch _].
      rewrite <- (szk_chunk ch Hch). apply NPL_in in Hch as [Hch Nch]. ndestruct (np_entry ch Hch Nch) as (h & Hh & HB & _).
      rewrite <- HB, (szk_entry h Hh). apply (proj2 (HA h Hh)). }
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zlen_sec_split : ltac2:(zQ "b0!hg9!jm1!it3!jl7!ina!hh1!p2!h9!ii8!hpb!hme@3$6$7@2$1$9@1$8?2st@2$a@2$1$0@3$4$0$3$2@2$1$0@3$4$0\2ch$0@1$5@1$3^1$2").
  Proof.
    rewrite <- SCNT. fold NPL. unfold zlen. clear. induction NPL as [|x l IH]; [reflexivity|].
    cbn [List.filter]. destruct (allocb x); cbn [negb length]; lia.
  Qed.

  Lemma quar_np_count : ltac2:(zQ "90!hg9!hh1!it3!jmf!jl7!jm1!ina!in4!jm8@2$7@2$8+vsg9@2$5$0@3$6$0\2ch$0@1$1@1$4^1$2$3").
  Proof.
    pose proof (quar_count st npb 64513 W ltac:(lia)) as Q.
    specialize (Q ltac:(intros ch Hin E; pose proof (WF_chunk st ch W Hin) as CO; unfold chunk_ok in CO; cbv zeta in CO; ndestruct CO as (U1 & _ & _ & _ & REST);
                      unfold npb in E; destruct (ch_primary ch); [discriminate E|]; destruct REST as (PR & _); exact (nonprimary_used _ U1 PR))).
    cbv beta in Q.
    assert (E : zlen (List.filter (fun ch => negb (allocb ch)) NPL) = zlen (List.filter (fun ch => negb (allocb ch) && npb ch) (chunk_list st))); [| lia].
    unfold NPL. rewrite filter_and.
    pose proof (zlen_filter_implies (fun x => npb x && negb (allocb x)) (fun ch => negb (allocb ch) && npb ch) (chunk_list st)
                  ltac:(intros x _ Hx; apply andb_true_iff in Hx; apply andb_true_iff; tauto)).
    pose proof (zlen_filter_implies (fun ch => negb (allocb ch) && npb ch) (fun x => npb x && negb (allocb x)) (chunk_list st)
                  ltac:(intros x _ Hx; apply andb_true_iff in Hx; apply andb_true_iff; tauto)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_np_used_ge : ltac2:(zQ "70!hg9!it3!jl7!hp1!hr7!ina!in4>2ch$0>0@3$4$0^1@3$5$0$2$1@2$6+vsg1@1$3^2").
  Proof.
    intros ch Hch. apply filter_In in Hch as [Hch _]. apply NPL_in in Hch as [Hch Nch].
    ndestruct (np_entry ch Hch Nch) as (_ & _ & _ & _ & _ & NPR & U1). exact (nonprimary_used _ U1 NPR).
  Qed.
End WithState.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma agap_arith : ltac2:(zQ "80!in4!hme!h9!jn7!hob!jm8!ho4!jne>1K$2>2Kl$2>2Kq$2>2Sl$2>1n$2>1L$2>3msz$2>2hc$2>0@2$0Z^7>0@2$0Z^7>0@2$4@2$0Z^a@2$0^a@2$1^9^8>0@2$0@2$5+vsg1^a@2$6^6^7>0@2$0@2$5+vsg9^a+hghgggg0>0@2$4@2$0+1^9@2$0^9@2$3+2+hf>0@2$4@2$0Z^9@2$0^9@2$1@2$3+2+i0@2$3+2+hc>0@2$4@2$0Z^c@2$0^c@2$1@2$6^a^b@2$5+jgg6^e>0@2$4@2$7Z^a@2$0^a@2$1^c+jgg6>0@2$0+nvvvnvogggg0^a@2$0@2$1@2$1@2$1+hgggnvvvogg0@2$1@2$3+2+i6@2$1^f@2$5@2$1@2$3+2+i0@2$3+2+e^h0@2$5@2$1+i0^h2@2$1^c+hgg0^c^b").
Proof.
  intros K Kl Kq Sl n L msz hc HKl HKq HK HL HQ Hn HLb HS HM Hc.
  set (x := n + 16390).
  set (P := (32 + K) * (msz + 4096)).
  assert (P1 : P <= (32 + K) * x) by (subst P x; apply Z.mul_le_mono_nonneg_l; lia).
  set (Wc := 271564838 + L).
  assert (P2 : 64513 * ((32 + K) * x) <= (Wc - x) * x).
  { replace (64513 * ((32 + K) * x)) with ((64513 * 32 + 64513 * K) * x) by ring.
    apply Z.mul_le_mono_nonneg_r; [subst x; lia|]. subst Wc x. lia. }
  assert (P3 : 4 * ((Wc - x) * x) <= Wc * Wc).
  { assert (E : Wc * Wc - 4 * ((Wc - x) * x) = (Wc - 2 * x) * (Wc - 2 * x)) by ring.
    pose proof (Z.square_nonneg (Wc - 2 * x)). lia. }
  assert (P4 : Wc * Wc <= 4834967590 * 4834967590).
  { apply Z.mul_le_mono_nonneg; subst Wc; lia. }
  assert (P5 : 258052 * P <= 4834967590 * 4834967590) by lia.
  clear P1 P2 P3 P4. clearbody P. subst x Wc. lia.
Qed.
