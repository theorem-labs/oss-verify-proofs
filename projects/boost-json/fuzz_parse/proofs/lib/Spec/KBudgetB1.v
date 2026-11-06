(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Pres3 MI_Pres4.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat37Corelib7Numbers7BinNumsi31Z37Corelib5Lists7ListDefk03mapk03seq46Stdlib6ZArith6BinInt1Zm36of_nat37Corelib4Init5Logico43ando43iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9KBudgetB1~~~~~~q44zseq36Stdlib5Lists4Listuc2Inm32lem32ltuc5NoDup06lengtho42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hi34aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~hm95mslothi36NSLOTSm36to_nathi36mstatehi34areai31N35stdpp7numbers1Nht96eq_dec35stdpp7numbers1Zhv46eq_dec04prod25stdpp9countableih5bN_countableih5bZ_countableih5eprod_countable25stdpp9decidableil6bprod_eq_dec03fstq4aarea_slotshi37s_areasuc8flat_map25stdpp8fin_mapsipebmap_to_list25stdpp4gmapird4gmapird9gmap_fold37Corelib4Init3Natite3mulq49all_slots25stdpp4basejg34sizeipe8map_sizeo42ex04Some06optionjg36lookupirdbgmap_lookuphi34meta37Corelib4Init5Peanojl72lehi3h2c_avail_meta_counthi35s_ctxhi37s_metashi34ghdr02id04pair03sndi32N0hi36g_meta25stdpp6optionjs2bfrom_optionite3add03nilhm96x_idlehm96x_zombhi35LFreehi38s_groups04Nonehm92MRhi35m_memhi37s_slots04boolhi37m_availhi37m_freedhi3am_last_idxhi39mask_uptom33eqbm33lor04true89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9KBudgetB15COUNT~~~~~~knd8allfreebhm97allfreeknd7meta_ofuc6filterknd7af_list04conshm96x_pend03apphi34cptrknd2AFknd9pend_listhm93blkhm95bslotknd5DEPTHknd6leavesknd3upsknd2uphm95hostshi3bm_sizeclass01So42orhi36mkGhdrhm94INVL" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma count_incl {A} (l k : list A) : List.NoDup l -> (forall x, In x l -> In x k) -> (length l <= length k)%nat.
Proof.
  intros ND SUB. apply submseteq_length. apply NoDup_submseteq; [apply NoDup_ListNoDup; exact ND|].
  intros x Hx. apply list_elem_of_In. apply SUB. apply list_elem_of_In. exact Hx.
Qed.

Lemma In_keys `{Countable K} {V} (m : gmap K V) k : In k (map fst (map_to_list m)) <-> m !! k <> None.
Proof.
  split.
  - intros Hin. apply in_map_iff in Hin as ([k' v] & E & Hin). cbn in E. subst k'.
    apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. rewrite Hin. discriminate.
  - intros Hk. destruct (m !! k) as [v|] eqn:E; [| congruence]. apply in_map_iff. exists (k, v). split; [reflexivity|].
    apply list_elem_of_In. apply elem_of_map_to_list. exact E.
Qed.

Lemma keys_nodup `{Countable K} {V} (m : gmap K V) : List.NoDup (map fst (map_to_list m)).
Proof. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list. Qed.

Lemma keys_length `{Countable K} {V} (m : gmap K V) : length (map fst (map_to_list m)) = size m.
Proof. rewrite map_length. apply length_map_to_list. Qed.

(* [comment removed for export] *)
Lemma size_le_cover `{Countable K} {V} (m : gmap K V) (l : list K) :
  (forall k, m !! k <> None -> In k l) -> (size m <= length l)%nat.
Proof.
  intros COV. rewrite <- keys_length. apply count_incl; [apply keys_nodup|]. intros k Hk. apply COV. apply In_keys. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma size_ge_sub `{Countable K} {V} (m : gmap K V) (l : list K) :
  List.NoDup l -> (forall k, In k l -> m !! k <> None) -> (length l <= size m)%nat.
Proof.
  intros ND SUB. rewrite <- keys_length. apply count_incl; [exact ND|]. intros k Hk. apply In_keys. apply SUB. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zseq : ltac2:(zQ "30!h8!he!jc>1n$1@1$0$2") := ltac2:(zQ "50!he!l7!ld!jc!nb\1n$0@4$1$0$3$4@2$2N0^1").
Lemma In_zseq : ltac2:(zQ "90!jc!he!p8!pe!u5!vf!hg4!hg9!nb>1n$1>1z$0@2$3@3$5$0^1@1$4^2@2$2@2$6Z^1@2$7^1@1$8^2").
Proof. intros n z.
  unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Lemma zseq_nodup : ltac2:(zQ "40!he!jc!u5!hge>1n$0@2$3$1@1$2^1").
Proof. intros n. unfold zseq. apply Finite.Injective_map_NoDup; [intros a b; lia| apply seq_NoDup]. Qed.
Lemma zseq_length : ltac2:(zQ "50!he!hh6!hhe!jc!u5>1n$0@3$2$0@2$1$3@1$4^1^1").
Proof. intros n. unfold zseq. rewrite map_length, seq_length. reflexivity. Qed.

Definition area_slots : ltac2:(zQ "20!hm1!h8>1a$0@1$1$0") := ltac2:(zQ "70!hm1!l7!jc!u5!hq7!hr0!hra\1a$0@4$1$2$0@1$4^1@1$3@1$6$5").
Definition all_slots : ltac2:(zQ "30!h8!hm1!hs3>2st$2@1$0$1") := ltac2:(zQ "h30!hm1!hsd!ht5!jc!hua!ig5!igf!ii6!ij5!ik4!im7!in6!inb!hs3!io8!ip3!iqe!is9!it1\2st$d@4$f@2$6$0$1$0\2ar@2$6$0$1@1$c@3$b$0$1^1@5$h0$0$1@4$h1$0@4$a$2$4$3$5@6$9$2$4$7$3$5$8$1@4$h2$0@4$a$2$4$3$5@6$9$2$4$7$3$5$8$1@1$e^1").

Lemma length_all_slots : ltac2:(zQ "h71!ht5!jc!hua!ig5!hm1!hsd!ii6!ij5!ik4!im7!is9!hh6!he!hhe!iv0!iv7!hr0!hs3!io8!hra!jgf!jh7!it1&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5>2st$h1@3$d$c@2$b$4@1$f^1@2$e@3$h4~0@4$h5$4$5~0@4$h6$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5@1$h2^1@1$h3$h0").
Proof. intros st.
  unfold all_slots. rewrite (flat_map_constant_length (c:=Z.to_nat NSLOTS)).
  - rewrite length_map_to_list. reflexivity.
  - intros [a ar] _. unfold area_slots. rewrite map_length, zseq_length. reflexivity.
Qed.

Lemma In_all_slots : ltac2:(zQ "hb0!hm1!hsd!jc!ht5!hua!ig5!p8!ji3!hhe!ii6!ij5!ik4!im7!ji8!jie!pe!iv7!hq7!hr0!hs3!io8!vf!hg4!hg9!jj6!is9!jk0>2st$h3>1x$0@2$f@3$h5$0^1@1$h0^2@2$7$0\1a$0@2$7$1\2ar$1@2$7$2\1k$2@2$6@3$8@1$e$1@6$h8$0$1@4$h9$0@4$c$3$4$2$5@6$b$3$4$9$2$5$a$1@4$ha$0@4$c$3$4$2$5@6$b$3$4$9$2$5$a$1^3@1$h4^5@2$d$1^2@2$6@2$6@2$h6Z^1@2$h7^1$h2@3$8$0^4@2$h1^3^1").
Proof. intros st x.
  unfold all_slots. rewrite in_flat_map. split.
  - intros ([a ar] & Hin & Hx). apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. cbn in Hx.
    unfold area_slots in Hx. apply in_map_iff in Hx as (k & <- & Hk). apply In_zseq in Hk. exists a, ar, k. unfold NSLOTS in *. repeat split; auto; lia.
  - intros (a & ar & k & Ha & Hk & ->). exists (a, ar). split; [apply list_elem_of_In; apply elem_of_map_to_list; exact Ha|].
    cbn. unfold area_slots. apply in_map_iff. exists k. split; [reflexivity|]. apply In_zseq. unfold NSLOTS in *. lia.
Qed.

Section COUNT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : ltac2:(zQ "10!lo4@5$0?1X?2st?1L?2BL?2LS").
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Lemma mslot_inj : ltac2:(zQ "h64!hsd!jc!hm1!ht5!hua!ig5!hhe!ii6!ij5!ik4!im7!p8!ji8!jie!hq7!hr0!io8!hg4!hg9!jj6!is9!jk0&@4$h4$2@4$a$3$4$1$5@6$9$3$4$7$1$5$8$0&@4$h5$2@4$a$3$4$1$5@6$9$3$4$7$1$5$8$0&@6$h3$2$0~0~1^6@1$h0?2st&@3$6@1$d$0~2@2$c$0^2>2a1$2>2a2$2>2k1$1>2k2$1>3ar1$0>3ar2$0>0~3>0~3>0@2$b@2$h1Z^6@2$h2^6$f>0@2$b@2$h1Z^6@2$h2^6$f>0@3$6$2@2$e^a^8@2$e^9^7@2$b@3$6$2^b^a@3$6$1^9^8").
Proof. intros a1 a2 k1 k2 ar1 ar2.
  intros H1 H2 K1 K2 E.
  destruct (ia_areas _ IA _ _ H1) as ((r1 & _ & _ & P1 & _) & _). destruct (ia_areas _ IA _ _ H2) as ((r2 & _ & _ & P2 & _) & _).
  destruct a1 as [rid1 o1], a2 as [rid2 o2]. unfold mslot, aadd in E. cbn in E, P1, P2. injection E as Erid Eo.
  unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *.
  assert (Ho : o1 = o2).
  { pose proof (Z.div_mod o1 4096 ltac:(lia)) as D1. pose proof (Z.div_mod o2 4096 ltac:(lia)) as D2. rewrite P1 in D1. rewrite P2 in D2. nia. }
  subst. split; [reflexivity| lia].
Qed.

Lemma area_slots_nodup : ltac2:(zQ "h30!hsd!hm1!ht5!jc!hua!ig5!ii6!ij5!ik4!im7!ji8!jie!hhe!inb!io8!hge!jj6!is9!jk0>1a$1>2ar$0>0@3$c@1$b$0@6$h0$1$0@4$h1$1@4$9$2$4$3$5@6$8$2$4$6$3$5$7$0@4$h2$1@4$9$2$4$3$5@6$8$2$4$6$3$5$7$0^2@1$e?2st@2$a$0^1@2$f$1@1$d^3").
Proof. intros a ar.
  intros Ha. unfold area_slots. apply Finite.Injective_map_NoDup_in; [| apply zseq_nodup].
  intros k1 k2 H1 H2 E. apply In_zseq in H1. apply In_zseq in H2.
  exact (proj2 (mslot_inj a a k1 k2 ar ar Ha Ha ltac:(unfold NSLOTS in *; lia) ltac:(unfold NSLOTS in *; lia) E)).
Qed.

Lemma all_slots_nodup : ltac2:(zQ "30!iv7!hm1!hge@2$2$1@1$0?2st").
Proof.
  unfold all_slots. pose proof (keys_nodup (s_areas st)) as ND.
  remember (map_to_list (s_areas st)) as l eqn:El.
  assert (SUB : forall a ar, In (a, ar) l -> s_areas st !! a = Some ar).
  { intros a ar Hin. subst l. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
  clear El. induction l as [|[a ar] l IH]; cbn; [constructor|].
  cbn in ND. apply List.NoDup_cons_iff in ND as [NIa ND].
  apply List.NoDup_app.
  - apply (area_slots_nodup a ar). apply SUB. left. reflexivity.
  - apply IH; [exact ND| intros a' ar' H; apply SUB; right; exact H].
  - intros x Hx Hx2. unfold area_slots in Hx. apply in_map_iff in Hx as (k & <- & Hk). apply In_zseq in Hk.
    apply in_flat_map in Hx2 as ([a' ar'] & Hin & Hx2). cbn in Hx2. unfold area_slots in Hx2. apply in_map_iff in Hx2 as (k' & E & Hk'). apply In_zseq in Hk'.
    pose proof (mslot_inj a' a k' k ar' ar (SUB a' ar' ltac:(right; exact Hin)) (SUB a ar ltac:(left; reflexivity))
                  ltac:(unfold NSLOTS in *; lia) ltac:(unfold NSLOTS in *; lia) E) as [-> _].
    apply NIa. apply in_map_iff. exists (a, ar'). split; [reflexivity| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma metas_ge_areas : ltac2:(zQ "h82!jc!ht5!hua!ig5!hm1!ii6!ij5!ik4!im7!hsd!jkf!is9!jgf!jh7!it1!hhe!iv0!jmb!hr0!jn1!io8!jo8!jp1!hra&@4$b$4@4$8$1$2$0$3@6$7$1$2$5$0$3$6$9&@4$b$4@4$8$1$2$0$3@6$7$1$2$5$0$3$6$a>0@3$f$0@1$h3@1$h5?2stZ@2$h1@2$h0@3$c~0@4$d$4$9~0@4$e$4@4$8$1$2$0$3@6$7$1$2$5$0$3$6$9@1$h4?2st@1$h7$h2@3$c~1@4$d$4$a~1@4$e$4@4$8$1$2$0$3@6$7$1$2$5$0$3$6$a@1$h6?2st").
Proof.
  intros HC. rewrite <- length_all_slots. apply size_ge_sub; [apply all_slots_nodup|].
  intros x Hx. apply In_all_slots in Hx as (a & ar & k & Ha & Hk & ->).
  apply (ia_carved _ IA a ar k Ha Hk). intros _. rewrite HC. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition meta_of : ltac2:(zQ "30!hm1!igf!jpc>2bh@2$1$0$2$0") := ltac2:(zQ "b0!igf!ht5!jc!hm1!jpc!jq4!jq8!jqe!jr3!jr8!jt0\2bh@2$0$3$4@5$a@2$0$1$2@2$0$1$2@1$5@2$0$1$2@4$6$1$2$8Z@1$9@3$7$3$4^1").

Lemma metas_le_groups : ltac2:(zQ "ha2!ht5!jc!hm1!hua!ig5!ii6!ij5!ik4!im7!jpc!jkf!is9!hh6!jtf!jgf!jh7!it1!h8!ju6!hhe!jmb!jub!jv5!jvf!kg8!jp1&@4$b$2@4$8$0$3$1$4@6$7$0$3$5$1$4$6$a&@4$b$2@4$8$0$3$1$4@6$7$0$3$5$1$4$6$9>0@3$h3@1$h1$2@1?2LS$h7@1$h2$2@2$h4@3$e~0@4$f$2$a~0@4$h0$2@4$8$0$3$1$4@6$7$0$3$5$1$4$6$a@1$h9?2st@2$d@2$d@3$e~1@4$f$2$9~1@4$h0$2@4$8$0$3$1$4@6$7$0$3$5$1$4$6$9@1$h8?2st@2$c$2@1$h5?1X@2$c$2@1$h6?1X").
Proof.
  intros HF.
  pose proof (size_le_cover (s_metas st) (map meta_of (map_to_list (s_groups st)) ++ x_idle X ++ x_zomb X)) as H.
  rewrite !app_length, map_length, length_map_to_list in H. eapply Nat.le_trans; [apply H| lia]. clear H.
  intros m Hm. rewrite !in_app_iff.
  assert (LG : live_group st m -> In m (map meta_of (map_to_list (s_groups st)))).
  { intros [b [ai Hb]]. apply in_map_iff. exists (b, mkGhdr (Some m) ai). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Hb. }
  destruct (im_all _ _ _ IM m Hm) as [A|[[h Hin]|[A|A]]]; [left; exact (LG A)| | right; left; exact A| right; right; exact A].
  destruct h as [sc|]; [| rewrite HF in Hin; destruct Hin].
  left. apply LG. exact (proj1 (proj2 (il_active _ _ IL sc m Hin))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition up : ltac2:(zQ "20!hm1!jie>1x$0@1$1$0") := ltac2:(zQ "h20!hm1!jc!igf!jie!ht5!hua!ig5!ii6!ij5!ik4!im7!kh4!kha!ki0!ki9!jj6!is9!jk0\1x$0M3\1x@1$3@2$2$0$1@1$3$0@6$f$0@2$2$0$1@4$h0$0@4$a$4$5$1$6@6$9$4$5$7$1$6$8@2$2$0$1@4$h1$0@4$a$4$5$1$6@6$9$4$5$7$1$6$8@2$2$0$1^1@1$e?2st\1y@2$2$0$1M2\1y@2$2$0$1@1$3$0^1\1p$0\2y0$1@1$d@2$c?2st^2@1$b$0").
Fixpoint ups (x : aptr) (n : nat) : list aptr :=
  match n with O => [] | S n' => match up x with Some b => b :: ups b n' | None => [] end end.

Definition allfreeb : ltac2:(zQ "20!kj4!jkf>1r$1$0") := ltac2:(zQ "70!kja!kk5!kl0!kle!jkf!kmb!kn1\1r$4@2$5@2$6@1$0^1@1$1^1@1$3@1$2^1").
Lemma allfreeb_spec : ltac2:(zQ "70!kj4!kn7!hhe!pe!ks4!kt0!jkf>1r$6@2$3@3$2$0@1$4^1$1@1$5^1").
Proof. intros r. unfold allfreeb, allfree. rewrite Z.eqb_eq. tauto. Qed.

Definition af_list : ltac2:(zQ "40!h8!igf!hm1!jpc@1$0@2$1$2$3") := ltac2:(zQ "h30!hm1!jpc!ht5!jc!hua!ig5!igf!ii6!ij5!ik4!im7!ks4!ktb!kha!kg8!ku6!iqe!is9!it1@3$f@2$6$0$1\2bh@2$6$0$1@1$b@2$d?2st@1$c^1@5$h0$0$1@4$h1$0@4$a$2$4$3$5@6$9$2$4$7$3$5$8$1@4$h2$0@4$a$2$4$3$5@6$9$2$4$7$3$5$8$1@1$e?2st").
Definition AF : ltac2:(zQ "20!h8!hm1@1$0$1") := ltac2:(zQ "60!hm1!jpc!in6!igf!l7!kuf@4$4@2$3$0$1$0@2$2$0$1$5").
Definition pend_list : ltac2:(zQ "20!h8!hm1@1$0$1") := ltac2:(zQ "60!hm1!ju6!jie!kva!h8!lg0M2\1x@1$2$0@1$4$0@1$5?1X\1s$0@3$3$0^1@1$1$0@1$1$0").
Definition leaves : ltac2:(zQ "20!h8!hm1@1$0$1") := ltac2:(zQ "80!lga!lgf!l7!lh7!lhd!lia!lj1!hm1@3$0$1@4$2$5$1$6?2BL@3$0$7$4$3").
Definition DEPTH : nat := 49%nat.
Definition gcover : ltac2:(zQ "20!h8!hm1@1$0$1") := ltac2:(zQ "70!hm1!lga!lh7!lja!lk3!lkd!ip3@3$1$0$2@4$6$0$0\1l$0@2$5^1$3$4").

Lemma ups_mono : ltac2:(zQ "50!hm1!he!lkd!vf!jmb>1x$0>1k$1>1n$1>0@2$4^2^1>1b$0>0@3$3$0^1@2$2^5^4@3$3$0^2@2$2^6^4").
Proof. intros x k n.
  revert x n. induction k as [|k IH]; intros x n Hk b Hb; [destruct Hb|].
  destruct n as [|n]; [lia|]. cbn in Hb |- *. destruct (up x) as [b0|]; [| destruct Hb].
  destruct Hb as [<-|Hb]; [left; reflexivity| right]. apply (IH b0 n); [lia| exact Hb].
Qed.

Lemma up_slot : ltac2:(zQ "h60!hm1!jc!igf!ht5!hua!ig5!ji8!jie!hhe!ii6!ij5!ik4!im7!jq8!p8!ji3!ll4!lla!ki9!jj6!is9!jk0>1s$0>1p$0>1i$1>0@3$8@1$7@2$2$0$1@6$h3$0@2$2$0$1@4$h4$0@4$c$3$4$1$5@6$b$3$4$9$1$5$a@2$2$0$1@4$h5$0@4$c$3$4$1$5@6$b$3$4$9$1$5$a@2$2$0$1^3@1$h2?2st@2$6@2$2$0$1@4$d$0$1^2^1@2$f$0\2bp$0@2$e@3$h1?2st^1^4@3$8@1$7$0@1$h0^5@2$6$0^1").
Proof. intros s p i.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _). exists bp. split; [exact Hp|].
  unfold up. rewrite Hs. exact (hosts_mem _ _ _ IM _ _ Hp).
Qed.

(* [comment removed for export] *)
Lemma group_cover_n : ltac2:(zQ "i00!hm1!jc!jpc!ht5!hua!ig5!he!p8!vf!ji8!ji3!jmb!kha!lm3!hg9!ii6!ij5!ik4!im7!ln2!jie!hhe!ln5!lh7!lk3!lkd!lna!kg8!nb!jj6!is9!jk0>1n$6>1b$0>1m$0>2ai$1>0@3$h5@1$h4$2@6$hd$0$2@4$he$0@4$h2$3$4$1$5@6$h1$3$4$f$1$5$h0$2@4$hf$0@4$h2$3$4$1$5@6$h1$3$4$f$1$5$h0$2^3@1$hb?2st@2$9$2@2$ha@2$9$0^2^1>0>0@2$e@1$d@2$c?2st^3+j0@2$e@1$d@2$c?2st^4@1$hc^6@2$h6@3$8$0^5$h7@2$a$0\1l$0@2$a$6\1k$6@2$7@3$8$0^2$h8@2$7@2$7@2$bN1^1@2$b^1@1$h3^8@3$8$0^7@2$h9^2^1").
Proof.
  induction n as [|n IH]; intros b m ai Hb Hn.
  - (* [comment removed for export] *)
    pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
    destruct (g_sc _ _ _ _ _ _ GO) as [[[S0 S48] _]|(E63 & L0 & _)]; [exfalso; specialize (Hn S48); lia|].
    destruct (g_big0 _ _ _ _ _ _ GO E63) as [A0 F0].
    pose proof (is_part _ _ _ IS b m ai 0 Hb ltac:(rewrite L0; lia)) as P. cbn zeta in P.
    unfold one5, tbit in P. rewrite A0, F0, !Z.bits_0 in P.
    destruct P as (P & _). set (s := slot_start' (MR st m) 0) in *.
    assert (Hs : s_slots st !! s = Some (m, 0)) by (apply (is_total _ _ _ IS b); [exists ai; exact Hb| rewrite L0; lia]).
    destruct (up_slot s m 0 Hs) as (bp & Hp & UP). pose proof (hosts_inj _ _ _ IM _ _ _ Hp (ex_intro _ ai Hb)) as ->.
    destruct P as [E|[E|[U|[NG|PE]]]]; [discriminate| discriminate| | |].
    + right. exists s, 1%nat. split; [unfold leaves; rewrite !in_app_iff; left; exact U|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
    + exfalso. destruct (s_groups st !! s) as [[[m'|] ai']|] eqn:Hs'; [| exact (ig_nometa _ _ _ IG _ _ Hs')| exact (NG eq_refl)].
      pose proof (ig_ok _ _ _ IG _ _ _ Hs') as GO'.
      destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [ML|ML].
      * destruct (g_nest _ _ _ _ _ _ GO' ML) as (p & i & Hsp & _ & _ & SC & _). rewrite Hs in Hsp. injection Hsp as <- <-. lia.
      * destruct (g_top _ _ _ _ _ _ GO' ML) as [Z0 _].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & Es). rewrite (slot_start'_eq _ _ _ IM _ _ 0 (ex_intro _ ai Hb)) in Es.
        subst s. rewrite Es in Z0. cbn in Z0. pose proof (sstart0 _ _ _ IM _ _ (ex_intro _ ai Hb)). pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia.
    + right. exists s, 1%nat. split; [unfold leaves, pend_list; rewrite !in_app_iff; right; left; rewrite PE; left; reflexivity|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
  - destruct (allfreeb (MR st m)) eqn:AFm.
    + left. unfold AF, af_list. apply in_map_iff. exists (b, mkGhdr (Some m) ai). split; [reflexivity|].
      apply filter_In. split; [apply list_elem_of_In; apply elem_of_map_to_list; exact Hb|]. cbn. exact AFm.
    + (* [comment removed for export] *)
      pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_li _ _ _ _ _ _ GO) as LI.
      assert (EXI : exists i, 0 <= i <= m_last_idx (MR st m) /\ tbit (m_avail (MR st m)) i = false /\ tbit (m_freed (MR st m)) i = false).
      { destruct (List.Exists_dec (fun i => tbit (m_avail (MR st m)) i = false /\ tbit (m_freed (MR st m)) i = false) (zseq (Z.to_nat (m_last_idx (MR st m) + 1)))) as [EX|NEX].
        - intros i. destruct (tbit (m_avail (MR st m)) i), (tbit (m_freed (MR st m)) i); [right| right| right| left]; try (intros [A B]; discriminate). auto.
        - apply List.Exists_exists in EX as (i & Hi & P). apply In_zseq in Hi. exists i. split; [lia| exact P].
        - exfalso. apply Bool.not_true_iff_false in AFm. apply AFm. apply allfreeb_spec. unfold allfree.
          apply Z.bits_inj'. intros j Hj. rewrite Z.lor_spec, testbit_mask_upto by lia.
          destruct (Z.le_gt_cases j (m_last_idx (MR st m))) as [LE|GT].
          + replace (j <=? m_last_idx (MR st m)) with true by (symmetry; apply Z.leb_le; lia).
            destruct (Z.testbit (m_avail (MR st m)) j) eqn:EA; [reflexivity|]. destruct (Z.testbit (m_freed (MR st m)) j) eqn:EF; [reflexivity|].
            exfalso. apply NEX. apply List.Exists_exists. exists j. split; [apply In_zseq; lia| unfold tbit; auto].
          + replace (j <=? m_last_idx (MR st m)) with false by (symmetry; apply Z.leb_gt; lia).
            destruct (Z.testbit (m_avail (MR st m)) j) eqn:EA; [pose proof (M3 j Hj EA); pose proof (g_ai _ _ _ _ _ _ GO); lia|].
            destruct (Z.testbit (m_freed (MR st m)) j) eqn:EF; [pose proof (M4 j Hj EF); lia|]. reflexivity. }
      destruct EXI as (i & Hi & NA & NF).
      pose proof (is_part _ _ _ IS b m ai i Hb Hi) as P. cbn zeta in P. unfold one5 in P. rewrite NA, NF in P.
      destruct P as (P & _). set (s := slot_start' (MR st m) i) in *.
      assert (Hs : s_slots st !! s = Some (m, i)) by (apply (is_total _ _ _ IS b); [exists ai; exact Hb| exact Hi]).
      destruct (up_slot s m i Hs) as (bp & Hp & UP). pose proof (hosts_inj _ _ _ IM _ _ _ Hp (ex_intro _ ai Hb)) as ->.
      destruct P as [E|[E|[U|[NG|PE]]]]; [discriminate| discriminate| | |].
      * right. exists s, 1%nat. split; [unfold leaves; rewrite !in_app_iff; left; exact U|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
      * destruct (s_groups st !! s) as [[[m'|] ai']|] eqn:Hs'; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hs')| exfalso; exact (NG eq_refl)].
        pose proof (ig_ok _ _ _ IG _ _ _ Hs') as GO'.
        assert (ML : m_maplen (MR st m') = 0).
        { destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [ML|ML]; [exact ML|]. exfalso.
          destruct (g_top _ _ _ _ _ _ GO' ML) as [Z0 _].
          destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & Es). rewrite (slot_start'_eq _ _ _ IM _ _ i (ex_intro _ ai Hb)) in Es.
          subst s. rewrite Es in Z0. cbn in Z0. pose proof (sstart0 _ _ _ IM _ _ (ex_intro _ ai Hb)).
          pose proof (sstart_mono _ _ _ IG _ _ 0 i (ex_intro _ ai Hb) ltac:(lia)). pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia. }
        destruct (g_nest _ _ _ _ _ _ GO' ML) as (p & i' & Hsp & _ & _ & SC & _). rewrite Hs in Hsp. injection Hsp as <- <-.
        destruct (IH s m' ai' Hs' ltac:(lia)) as [AFs|(l & k & Hl & Hk & Hin)].
        -- right. exists s, 1%nat. split; [unfold leaves; rewrite !in_app_iff; right; right; exact AFs|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
        -- right. exists l, (S k). split; [exact Hl|]. split; [lia|].
           clear -Hin UP. revert l Hin. induction k as [|k IHk]; intros l Hin; [destruct Hin|].
           cbn in Hin. cbn. destruct (up l) as [b0|]; [| destruct Hin]. destruct Hin as [<-|Hin].
           ++ right. cbn. rewrite UP. left. reflexivity.
           ++ right. apply IHk. exact Hin.
      * right. exists s, 1%nat. split; [unfold leaves, pend_list; rewrite !in_app_iff; right; left; rewrite PE; left; reflexivity|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
Qed.

Lemma ups_length : ltac2:(zQ "50!hm1!hh6!he!jmb!lkd>1x$0>1n$2@2$3@2$1$0@2$4^2^1^1").
Proof. intros x n. revert x. induction n as [|n IH]; intros x; cbn; [lia|]. destruct (up x); cbn; [| lia]. specialize (IH a). lia. Qed.

(* [comment removed for export] *)
Lemma AF_length : ltac2:(zQ "40!hh6!jmb!lh7!hm1@2$1@2$0$3$2Nj0").
Proof.
  unfold AF.
  assert (ND : List.NoDup (map fst af_list)).
  { unfold af_list. pose proof (keys_nodup (s_groups st)) as ND.
    remember (map_to_list (s_groups st)) as l eqn:El. clear El. revert ND. induction l as [|[b h] l IH]; cbn; intros ND; [constructor|].
    apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (allfreeb (MR st (meta_of (b, h)))); cbn; [| apply IH; exact ND].
    apply List.NoDup_cons; [| apply IH; exact ND]. intros Hin. apply NI. apply in_map_iff in Hin as ([b' h'] & E & Hin). apply filter_In in Hin as [Hin _].
    apply in_map_iff. exists (b', h'). auto. }
  assert (FACTS : forall b h, In (b, h) af_list -> exists m ai, h = mkGhdr (Some m) ai /\ s_groups st !! b = Some h /\ allfree (MR st m) /\ 0 <= m_sizeclass (MR st m) < 48).
  { intros b h Hin. unfold af_list in Hin. apply filter_In in Hin as [Hin AFb]. apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
    destruct h as [[m|] ai]; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hin)]. exists m, ai. cbn in AFb. apply allfreeb_spec in AFb.
    split; [reflexivity|]. split; [exact Hin|]. split; [exact AFb|].
    pose proof (ig_ok _ _ _ IG _ _ _ Hin) as GO. destruct (g_sc _ _ _ _ _ _ GO) as [[S _]|(E63 & L0 & _)]; [exact S|].
    exfalso. destruct (g_big0 _ _ _ _ _ _ GO E63) as [A0 F0]. unfold allfree in AFb. rewrite A0, F0, L0 in AFb. cbn in AFb. discriminate. }
  pose proof (count_incl (map (fun bh => m_sizeclass (MR st (meta_of bh))) af_list) (zseq 48)) as C.
  rewrite map_length, zseq_length in C. rewrite map_length. apply C.
  - (* [comment removed for export] *)
    clear C. revert ND FACTS. generalize af_list. intros afl ND FACTS. induction afl as [|[b h] l IH]; cbn; [constructor|].
    cbn in ND. apply List.NoDup_cons_iff in ND as [NI ND]. apply List.NoDup_cons; [| apply IH; [exact ND| intros b' h' H'; apply FACTS; right; exact H']].
    intros Hin. apply in_map_iff in Hin as ([b' h'] & E & Hin').
    destruct (FACTS b h ltac:(left; reflexivity)) as (m & ai & -> & Hb & AFm & SCm).
    destruct (FACTS b' h' ltac:(right; exact Hin')) as (m' & ai' & -> & Hb' & AFm' & SCm'). cbn in E.
    pose proof (ig_oneempty _ _ _ IG m m' b b' ai ai' Hb Hb' (proj2 SCm) E AFm AFm') as <-.
    pose proof (hosts_inj _ _ _ IM _ _ _ (ex_intro _ ai Hb) (ex_intro _ ai' Hb')) as <-.
    apply NI. apply in_map_iff. exists (b, mkGhdr (Some m) ai'). auto.
  - intros z Hz. apply in_map_iff in Hz as ([b h] & <- & Hin). destruct (FACTS b h Hin) as (m & ai & -> & _ & _ & SC). apply In_zseq. replace (meta_of (b, mkGhdr (Some m) ai)) with m by reflexivity. lia.
Qed.

Lemma groups_le : ltac2:(zQ "h51!ht5!jc!hua!ig5!hm1!jpc!jtf!ii6!ij5!ik4!im7!is9!hh6!iv0!jmb!lja!lia!kg8!jgf!jh7!it1&@4$b$4@4$a$0$2$1$3@6$9$0$2$7$1$3$8$5@2$e@3$h2~0@4$h3$4$5~0@4$h4$4@4$a$0$2$1$3@6$9$0$2$7$1$3$8$5@1$h1?2st@2$6Nj0@2$d$f@2$6@2$6@2$c$h0?2BLN1Nj0").
Proof.
  pose proof AF_length as AFL.
  eapply Nat.le_trans; [apply (size_le_cover (s_groups st) gcover)|].
  - intros b Hb. destruct (s_groups st !! b) as [[[m|] ai]|] eqn:E; [| exfalso; exact (ig_nometa _ _ _ IG _ _ E)| congruence].
    unfold gcover. apply in_app_iff.
    destruct (group_cover_n 48 b m ai E ltac:(intros; lia)) as [A|(l & k & Hl & Hk & Hin)]; [left; exact A| right].
    apply in_flat_map. exists l. split; [exact Hl|]. apply (ups_mono l k); [unfold DEPTH; lia| exact Hin].
  - unfold gcover. rewrite app_length.
    assert (FL : forall ls, (length (flat_map (fun l => ups l DEPTH) ls) <= DEPTH * length ls)%nat).
    { induction ls as [|x ls IH]; [cbn; lia|]. cbn [flat_map]. rewrite app_length. cbn [length]. pose proof (ups_length x DEPTH). lia. }
    pose proof (FL leaves) as FLl. unfold leaves in FLl. rewrite !app_length, map_length in FLl.
    assert (PL : (length pend_list <= 1)%nat) by (unfold pend_list; destruct (x_pend X); cbn; lia).
    unfold leaves. nia.
Qed.

(* [comment removed for export] *)
Theorem carve_count : ltac2:(zQ "hf1!hm1!jc!ht5!hua!ig5!jtf!hsd!hh6!ii6!ij5!ik4!im7!hhe!iv0!is9!h8!ju6!jmb!lja!lia!jub!jv5!jvf!hr0!jn1!io8!jo8!hra!jgf!jh7!it1&@4$e$0@4$b$2$3$1$4@6$a$2$3$8$1$4$9$6>0@3$c@1$f$0@1?2LS$h6@1$h0$0>0@3$c$1@1$h8@1$ha?2stZ@2$h1@2$d@1$hb$h7@3$hc~0@4$hd$0$6~0@4$he$0@4$b$2$3$1$4@6$a$2$3$8$1$4$9$6@1$h9?2st@2$5@2$5@2$5Nj0@2$d$h2@2$5@2$7$h3?2BLNj1@2$7$0@1$h4?1X@2$7$0@1$h5?1X").
Proof.
  intros HF HC. pose proof (metas_ge_areas HC) as A. pose proof (metas_le_groups HF) as B. pose proof groups_le as C. lia.
Qed.

(* [comment removed for export] *)
End COUNT.
