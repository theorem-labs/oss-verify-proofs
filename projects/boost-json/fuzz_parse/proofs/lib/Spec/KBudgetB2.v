(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Pres3 MI_Pres4 MI_Cnt KLink KBudgetB1.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4prodhc4listhc3snd37Corelib4Init5Logick82eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~m18mmap_len79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9KBudgetB2~~~~~~q94sumw79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5KLink~~~~~~v18sum_glenhc3fstv18sum_mlenhc4bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hl16regionhc5falsehl15rkindhc4truehl16r_kind01Nhl16mstate25stdpp9countablehs8bN_countable35stdpp7numbers1Nhu86eq_decq99is_groupbhl19s_regions36Stdlib5Lists4Listihc6filter25stdpp8fin_mapsij9bmap_to_list25stdpp4gmapil84gmapil89gmap_foldq98is_metabhc4Somehc6optionhc4pairk83andk83iffq92RGhl17RKGroupihc2In25stdpp4baseird6lookupil8bgmap_lookupq92RMhl16RKMeta37Corelib5Lists7ListDefiv13mapihc5NoDuphc3nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9KBudgetB1~~~~~~jhe4zseq46Stdlib6ZArith6BinInt1Zjm73addq96zrangejm72lejm72ltjm76of_nathc6lengthjm73powjm73subjm76to_nathl14aptrhc4Nonejhe2upjhe3upsihc4last89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9KBudgetB24FOOT~~~~~~jua5rootshl14ghdr35stdpp7numbers1Zkk16eq_deck82exhs8bZ_countablehs8eprod_countable25stdpp9decidableko2bprod_eq_deck83not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~kq82MRhl18m_maplenhl16mkGhdrhl18s_groups37Corelib4Init3Natlge3add37Corelib4Init5Peanoli72lekq83blkkq85bslotkq85hostshl14cptrhl1bm_sizeclasshl1bslot_start'hl18aptr_eqbhl14optrihc4findjm73eqbjua6bigblkkq85bsizehl15r_lenjm73mulhl14areakq88frontierkq8bis_metakindhl14PGSZhl17s_areasird4sizeij98map_sizehl1h2c_avail_meta_areashl15s_ctxhl1h2c_meta_alloc_shifthl15RKBrkjm73divjm76modulojm74log2jua3jof79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~mn09ld_groupsmn08ld_metasv18lbrk_cntv1albrk_bytesmn04mledkq84INVLkq82x0hl15lheadhl15stripv16lcountv16ltotalkq86x_orphkq86x_pendkq87x_fresh" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sumw {A} (w : A -> Z) (l : list A) : Z := fold_right (fun x acc => w x + acc) 0 l.
Lemma sumw_cons {A} (w : A -> Z) x l : sumw w (x :: l) = w x + sumw w l. Proof. reflexivity. Qed.
Lemma sumw_nil {A} (w : A -> Z) : sumw w [] = 0. Proof. reflexivity. Qed.
Arguments sumw {A} w l : simpl never.

Lemma sumw_app {A} (w : A -> Z) l k : sumw w (l ++ k) = sumw w l + sumw w k.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [app]. rewrite !sumw_cons, IH. lia. Qed.

Lemma sumw_perm {A} (w : A -> Z) l k : Permutation l k -> sumw w l = sumw w k.
Proof. induction 1; rewrite ?sumw_cons in *; try lia. Qed.

Lemma sumw_nonneg {A} (w : A -> Z) l : (forall x, In x l -> 0 <= w x) -> 0 <= sumw w l.
Proof. induction l as [|x l IH]; intros H; [rewrite sumw_nil; lia|]. rewrite sumw_cons. pose proof (H x ltac:(left; reflexivity)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. Qed.

Lemma sumw_le {A} (w v : A -> Z) l : (forall x, In x l -> w x <= v x) -> sumw w l <= sumw v l.
Proof. induction l as [|x l IH]; intros H; [rewrite !sumw_nil; lia|]. rewrite !sumw_cons. pose proof (H x ltac:(left; reflexivity)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. Qed.

Lemma sumw_const {A} (c : Z) (l : list A) : sumw (fun _ => c) l = Z.of_nat (length l) * c.
Proof. induction l as [|x l IH]; [rewrite sumw_nil; cbn; lia|]. rewrite sumw_cons, IH. cbn [length]. rewrite Nat2Z.inj_succ. lia. Qed.

Lemma sumw_map {A B} (f : A -> B) (w : B -> Z) l : sumw w (map f l) = sumw (fun x => w (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !sumw_cons, IH. reflexivity. Qed.

Lemma sumw_add {A} (w v : A -> Z) l : sumw (fun x => w x + v x) l = sumw w l + sumw v l.
Proof. induction l as [|x l IH]; [rewrite !sumw_nil; lia|]. rewrite !sumw_cons, IH. lia. Qed.

Lemma sumw_ext {A} (w v : A -> Z) l : (forall x, In x l -> w x = v x) -> sumw w l = sumw v l.
Proof. intros H. pose proof (sumw_le w v l ltac:(intros x Hx; rewrite (H x Hx); lia)). pose proof (sumw_le v w l ltac:(intros x Hx; rewrite (H x Hx); lia)). lia. Qed.

(* [comment removed for export] *)
Lemma sumw_sub {A} (w : A -> Z) (l k : list A) :
  List.NoDup l -> (forall x, In x l -> In x k) -> (forall x, In x k -> 0 <= w x) -> sumw w l <= sumw w k.
Proof.
  revert k. induction l as [|x l IH]; intros k ND SUB POS.
  - rewrite sumw_nil. apply sumw_nonneg. exact POS.
  - apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (in_split x k (SUB x ltac:(left; reflexivity))) as (k1 & k2 & ->).
    rewrite sumw_app, !sumw_cons. pose proof (IH (k1 ++ k2) ND) as H. rewrite sumw_app in H.
    assert (S' : forall y, In y l -> In y (k1 ++ k2)).
    { intros y Hy. pose proof (SUB y ltac:(right; exact Hy)) as K. apply in_app_iff in K. apply in_app_iff.
      destruct K as [K|[<-|K]]; [left; exact K| exfalso; exact (NI Hy)| right; exact K]. }
    specialize (H S' ltac:(intros y Hy; apply POS; apply in_app_iff in Hy; apply in_app_iff; cbn; tauto)). lia.
Qed.

Lemma sum_glen_sumw : ltac2:(zQ "80!h9!j4!jb!k2!lc!pe!ua!hie>1l@1$2@2$1$0$0@3$4$0@1$7^1@3$6@2$1$0$0\1g@2$1$0$0@1$5@3$3$0$0^1^1").
Proof. intros l. reflexivity. Qed.
Lemma sum_mlen_sumw : ltac2:(zQ "90!h9!j4!hj9!jb!k2!lc!pe!ua!hjf>1l@1$3@2$1@2$1$0$0$0@3$5$0@1$8^1@3$7@2$1@2$1$0$0$0\1m@2$1@2$1$0$0$0@1$6@3$4$0$0@3$2@2$1$0$0$0^1^1").
Proof. intros l. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_groupb : ltac2:(zQ "20!hka!hof>1r$1$0") := ltac2:(zQ "60!hp9!hq1!hka!hqa!hr1!hof\1r$5M1\1x$1$2@1$4^1$0$0$3").
Definition is_metab : ltac2:(zQ "20!hka!hof>1r$1$0") := ltac2:(zQ "60!hp9!hq1!hka!hqa!hr1!hof\1r$5M1\1x$1$2@1$4^1$0$3$0").
Definition RG : ltac2:(zQ "50!jb!j4!hrb!hre!hof>2st$3@1$0@2$1$2$4") := ltac2:(zQ "d0!hrb!hof!j4!ht9!hv9!k2!ig3!hre!igf!iif!ik9!im4!imc\2st$7@3$9@2$2$0$1\2kr@2$2$0$1@1$6@3$5$0$1^1@5$a$0$1@4$b$0$4$3$1@4$c$0$4$3$1@1$8^1").
Definition RM : ltac2:(zQ "50!jb!j4!hrb!hre!hof>2st$3@1$0@2$1$2$4") := ltac2:(zQ "d0!hrb!hof!j4!ht9!hv9!k2!in9!hre!igf!iif!ik9!im4!imc\2st$7@3$9@2$2$0$1\2kr@2$2$0$1@1$6@3$5$0$1^1@5$a$0$1@4$b$0$4$3$1@4$c$0$4$3$1@1$8^1").

Lemma In_RG : ltac2:(zQ "h50!hof!hrb!lc!ht9!hv9!io4!iob!ip4!j4!ipb!iq1!iq7!iqc!hre!hr1!hq1!igf!ir7!is9!im4!it3>2st$d>3rid$1>1r$0@2$a@3$h1@2$8$1$0@4$7$1$0^2^1@1$b^3@2$9@3$2@1$6$0@6$h2$1$0@4$h3$1$4$3$0@4$h4$1$4$3$0^2@1$h0^3@2$5$0^1@3$2$f@1$e^1$c").
Proof. intros st rid r.
  unfold RG. rewrite filter_In. cbn. unfold is_groupb. split.
  - intros [Hin K]. split; [apply elem_of_map_to_list; apply list_elem_of_In; exact Hin| destruct (r_kind r); congruence].
  - intros [H K]. rewrite K. split; [apply list_elem_of_In; apply elem_of_map_to_list; exact H| reflexivity].
Qed.
Lemma In_RM : ltac2:(zQ "h50!hof!hrb!lc!ht9!hv9!io4!iob!ip4!j4!ipb!iq1!iu2!iu7!hre!hr1!hq1!igf!ir7!is9!im4!it3>2st$d>3rid$1>1r$0@2$a@3$h1@2$8$1$0@4$7$1$0^2^1@1$b^3@2$9@3$2@1$6$0@6$h2$1$0@4$h3$1$4$3$0@4$h4$1$4$3$0^2@1$h0^3@2$5$0^1@3$2$f@1$e^1$c").
Proof. intros st rid r.
  unfold RM. rewrite filter_In. cbn. unfold is_metab. split.
  - intros [Hin K]. split; [apply elem_of_map_to_list; apply list_elem_of_In; exact Hin| destruct (r_kind r); congruence].
  - intros [H K]. rewrite K. split; [apply list_elem_of_In; apply elem_of_map_to_list; exact H| reflexivity].
Qed.

Lemma filter_nodup_fst {K V} (f : K * V -> bool) (l : list (K * V)) : List.NoDup (map fst l) -> List.NoDup (map fst (List.filter f l)).
Proof.
  induction l as [|[k v] l IH]; cbn; intros ND; [constructor|]. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct (f (k, v)); cbn; [| apply IH; exact ND]. apply List.NoDup_cons; [| apply IH; exact ND].
  intros Hin. apply NI. apply in_map_iff in Hin as ([k' v'] & E & Hin). apply filter_In in Hin as [Hin _]. apply in_map_iff. exists (k', v'). auto.
Qed.
Lemma RG_nodup : ltac2:(zQ "80!hrb!hof!hj9!j4!jg8!iq7!hre!jgf>2st$6@2$7$0@4$4@2$3$0$1$0@2$2$0$1@1$5^1"). Proof. intros st. apply filter_nodup_fst. apply keys_nodup. Qed.
Lemma RM_nodup : ltac2:(zQ "80!hrb!hof!hj9!j4!jg8!iu2!hre!jgf>2st$6@2$7$0@4$4@2$3$0$1$0@2$2$0$1@1$5^1"). Proof. intros st. apply filter_nodup_fst. apply keys_nodup. Qed.
Lemma NoDup_of_fst {K V} (l : list (K * V)) : List.NoDup (map fst l) -> List.NoDup l.
Proof.
  induction l as [|[k v] l IH]; cbn; intros ND; [constructor|]. apply List.NoDup_cons_iff in ND as [NI ND].
  apply List.NoDup_cons; [| apply IH; exact ND]. intros Hin. apply NI. apply in_map_iff. exists (k, v). auto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint omapl {A B} (f : A -> option B) (l : list A) : list B :=
  match l with [] => [] | x :: l' => match f x with Some b => b :: omapl f l' | None => omapl f l' end end.
Lemma In_omapl {A B} (f : A -> option B) l b : In b (omapl f l) <-> exists x, In x l /\ f x = Some b.
Proof.
  induction l as [|x l IH]; cbn; [split; [intros []| intros (x & [] & _)]|].
  destruct (f x) as [b0|] eqn:E; cbn; rewrite IH; split.
  - intros [<-|(y & Hy & Ey)]; [exists x; auto| exists y; auto].
  - intros (y & [<-|Hy] & Ey); [left; congruence| right; exists y; auto].
  - intros (y & Hy & Ey); exists y; auto.
  - intros (y & [<-|Hy] & Ey); [congruence| exists y; auto].
Qed.
Lemma sumw_omapl {A B} (f : A -> option B) (w : B -> Z) l :
  sumw (fun x => match f x with Some b => w b | None => 0 end) l = sumw w (omapl f l).
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [omapl]. rewrite sumw_cons, IH. destruct (f x); [rewrite sumw_cons; reflexivity| lia]. Qed.
Lemma NoDup_omapl {A B} (f : A -> option B) l :
  List.NoDup l -> (forall x y b, In x l -> In y l -> f x = Some b -> f y = Some b -> x = y) -> List.NoDup (omapl f l).
Proof.
  induction l as [|x l IH]; cbn; intros ND INJ; [constructor|]. apply List.NoDup_cons_iff in ND as [NI ND].
  assert (IH' : List.NoDup (omapl f l)) by (apply IH; [exact ND| intros; eapply INJ; eauto]).
  destruct (f x) as [b|] eqn:E; [| exact IH']. apply List.NoDup_cons; [| exact IH'].
  intros Hin. apply In_omapl in Hin as (y & Hy & Ey). pose proof (INJ x y b ltac:(auto) ltac:(auto) E Ey) as <-. exact (NI Hy).
Qed.
Lemma NoDup_map_inj {A B} (f : A -> B) l x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; cbn; intros ND Hx Hy E; [destruct Hx|]. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | exact (IH ND Hx Hy E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

(* [comment removed for export] *)
Definition zrange : ltac2:(zQ "30!h9!jb!jh8>1a$0>1n$2@1$1$0") := ltac2:(zQ "50!h9!jh8!jg8!jlf!jnf\1a$0\1n$1@4$2$0$0\1z$0@2$4^3^1@1$3^1").
Lemma In_zrange : ltac2:(zQ "a0!h9!jh8!ipb!iq1!jo6!ir7!jnf!jof!jp5!jpb>1a$0>1n$1>1z$0@2$3@3$5$0^1@2$4^3^2@2$2@2$7^3^1@2$8^1@2$6^3@1$9^2").
Proof. intros a n z. unfold zrange. rewrite in_map_iff. split; [intros (y & <- & Hy); apply In_zseq in Hy; lia| intros H; exists (z - a); split; [lia| apply In_zseq; lia]]. Qed.
Lemma zrange_nodup : ltac2:(zQ "40!h9!jh8!jo6!jgf>1a$0>1n$1@2$3$0@2$2^2^1").
Proof. intros a n. unfold zrange. apply Finite.Injective_map_NoDup_in; [intros x y _ _ E; lia| apply zseq_nodup]. Qed.
Lemma zrange_length : ltac2:(zQ "50!jh8!h9!jq5!lc!jo6>1a$1>1n$0@3$3$0@2$2$1@2$4^2^1^1").
Proof. intros a n. unfold zrange. rewrite map_length. apply zseq_length. Qed.
Lemma geo_sum : ltac2:(zQ "90!h9!jqe!lc!ua!jo6!jnf!jof!jr5!jrc>1s$0>0@2$6Z^1@3$2$0@3$3$0\1j$0@2$1+2^1@2$4+1@1$8^2@2$7@2$1+2@2$5^2+1+2").
Proof. intros s.
  intros Hs. rewrite <- (Z2Nat.id s) at 2 by lia. generalize (Z.to_nat s). clear s Hs. intros n.
  unfold zrange, zseq. induction n as [|n IH]; [reflexivity|].
  rewrite seq_S, !map_app, sumw_app, IH. cbn [map]. rewrite sumw_cons, sumw_nil, Nat2Z.inj_succ.
  rewrite Nat.add_0_l. replace (1 + Z.of_nat n) with (Z.succ (Z.of_nat n)) by lia. rewrite !Z.pow_succ_r by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FOOT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : ltac2:(zQ "10!mu5@5$0?1X?2st?1L?2BL?2LS").
Hypothesis HXO : ltac2:(zQ "50!hrb!jse!iob!lc!nh7@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis HXP : ltac2:(zQ "50!js6!jse!iob!lc!ni1@3$3@1$2$0@1$4?1X@1$1$0").
Hypothesis HXF : ltac2:(zQ "50!js6!jse!iob!lc!nib@3$3@1$2$0@1$4?1X@1$1$0").
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Local Notation R := (MR st).
Local Notation cx := (s_ctx st).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma up_base0 : ltac2:(zQ "80!hrb!js6!jse!iob!ip4!lc!h9!jt5>3rid$0@3$5@1$3$1@2$7?2st@4$4$0$6^1Z@1$2$1").
Proof. intros rid.
  unfold up. destruct (_ !! _) as [[p i]|] eqn:E; [| reflexivity]. exfalso.
  destruct (is_valid _ _ _ IS _ _ _ E) as ((b & Hb) & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. injection Es as _ Eo.
  pose proof (sstart_mono _ _ _ IG _ _ 0 i Hb ltac:(lia)). rewrite (sstart0 _ _ _ IM _ _ Hb) in H.
  destruct (hosts_ok _ _ _ IG _ _ Hb) as (ai & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia.
Qed.

Lemma ups_last : ltac2:(zQ "90!js6!lc!jtb!jse!jh8!iob!jt5!ir7!ju2>1x$0>1n$4>1b$0>1d$0>0@3$7$0^2@3$2?2st^4^3>0@3$1@1$5$0@2$6?2st^3@1$3$0@3$1$0^4@3$8$0@3$2?2st^6^5^3").
Proof. intros x n b d.
  revert x. induction n as [|n IH]; intros x Hin U; [destruct Hin|].
  cbn in Hin |- *. destruct (up st x) as [b0|]; [| destruct Hin]. destruct Hin as [<-|Hin].
  - destruct n; cbn; [reflexivity|]. rewrite U. reflexivity.
  - pose proof (IH b0 Hin U) as E. destruct (ups st b0 n) as [|y l] eqn:El; [destruct Hin| exact E].
Qed.

Definition roots : ltac2:(zQ "20!jb!js6@1$0$1") := ltac2:(zQ "80!hrb!j4!hof!h9!hj9!ip4!jg8!iq7@4$6@2$1$0$2@2$1$0$3\2kr@2$1$0$2@4$5$0$3@3$4$0$2^1Z@1$7?2st").

Lemma roots_nodup : ltac2:(zQ "30!kj0!js6!jgf@2$2$1$0").
Proof.
  unfold roots. pose proof (RG_nodup st) as ND. remember (RG st) as l eqn:El. clear El.
  induction l as [|[k r] l IH]; cbn; [constructor|]. cbn in ND. apply List.NoDup_cons_iff in ND as [NI ND].
  apply List.NoDup_cons; [| apply IH; exact ND]. intros Hin. apply NI. apply in_map_iff in Hin as ([k' r'] & E & Hin). cbn in E. injection E as ->.
  apply in_map_iff. exists (k, r'). auto.
Qed.

Lemma roots_top : ltac2:(zQ "ha0!h9!js6!hrb!kj9!hv9!kl2!lc!io4!ipb!klc!ht9!km1!kn0!kp3!iob!k2!kq2!kj0!ku6!kuc!kv8!lg2!ir7!is9!im4!it3>1b$1>0@3$h6$1^1$h1@2$9$1\1m$1@2$9$0\2ai$0@2$8@3$6@1$e$3@6$h7$1$3@4$h8$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b$3@4$h9$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b$3^4@1$h5?2st@2$7$3@2$h4@2$7$1^2^1@2$8@1$h0@3$6$0@1$h3@2$h2?2st^2Z@3$6$0@3$f$2$0^4Z").
Proof. intros b.
  intros Hin. unfold roots in Hin. apply in_map_iff in Hin as ([rid r] & <- & Hin). apply In_RG in Hin as [Hr K].
  destruct (ig_top _ _ _ IG rid r Hr K ltac:(rewrite HXO; discriminate)) as (m & [ai Hb] & ML).
  exists m, ai. cbn. auto.
Qed.

Lemma RG_length : ltac2:(zQ "80!li0!jq5!j4!ljb!hrb!iq7!lk1!hof@2$3@2$1@2$2$4$7@1$5?2st@2$0Nj0@2$0@2$0@2$1$6?2BLN1Nj0").
Proof.
  replace (length (RG st)) with (length roots) by (unfold roots; apply map_length).
  pose proof (AF_length X st L BL LS INV) as AFL.
  eapply Nat.le_trans; [apply (count_incl roots (AF st ++ map (fun l => List.last (ups st l DEPTH) l) (leaves X st BL))); [apply roots_nodup|]|].
  - intros b Hb. destruct (roots_top b Hb) as (m & ai & Hg & ML & B0). apply in_app_iff.
    destruct (group_cover_n X st L BL LS INV 48 b m ai Hg ltac:(intros; lia)) as [A|(l & k & Hl & Hk & Hin)]; [left; exact A| right].
    apply in_map_iff. exists l. split; [| exact Hl]. symmetry. apply ups_last; [eapply ups_mono; [| exact Hin]; unfold DEPTH; lia|].
    destruct b as [rid o]. cbn in B0. subst o. apply up_base0.
  - rewrite app_length, map_length. unfold leaves. rewrite !app_length, map_length.
    assert (PL : (length (pend_list X) <= 1)%nat) by (unfold pend_list; destruct (x_pend X); cbn; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma big_slot_block : ltac2:(zQ "c0!js6!ku6!lc!jg8!h9!lk1!lk8!ll1!lla!lm2!ln1!ir7>1b$0>1m$0>0@3$7?2st^2^1>0@3$2$4@1$9@2$1?2st^2+jf@3$b$0@2$a@2$1?2st^3Z@4$3$5$8$6?2BL").
Proof. intros b m.
  intros Hb S63. destruct (hosts_ok _ _ _ IG _ _ Hb) as (ai & Hg & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[[_ S48] _]|(_ & L0 & ML & _)]; [lia|].
  destruct (g_big0 _ _ _ _ _ _ GO S63) as [A0 F0].
  pose proof (is_part _ _ _ IS b m ai 0 Hg ltac:(rewrite L0; lia)) as P. cbn zeta in P.
  unfold one5, tbit in P. rewrite A0, F0, !Z.bits_0, HXP in P. destruct P as (P & _).
  set (s := slot_start' (R m) 0) in *.
  assert (Hs : s_slots st !! s = Some (m, 0)) by (apply (is_total _ _ _ IS b); [exact Hb| rewrite L0; lia]).
  destruct P as [E|[E|[U|[NG|PE]]]]; [discriminate| discriminate| exact U| | discriminate].
  exfalso. destruct (s_groups st !! s) as [[[m'|] ai']|] eqn:Hs'; [| exact (ig_nometa _ _ _ IG _ _ Hs')| exact (NG eq_refl)].
  pose proof (ig_ok _ _ _ IG _ _ _ Hs') as GO'.
  destruct (Z.eq_dec (m_maplen (R m')) 0) as [ML'|ML'].
  - destruct (g_nest _ _ _ _ _ _ GO' ML') as (p & i & Hsp & _ & _ & SC & _). rewrite Hs in Hsp. injection Hsp as <- <-. lia.
  - destruct (g_top _ _ _ _ _ _ GO' ML') as [Z0 _].
    subst s. rewrite (slot_start'_eq _ _ _ IM _ _ 0 Hb) in Z0. cbn in Z0. rewrite (sstart0 _ _ _ IM _ _ Hb) in Z0.
    pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Definition bigblk : ltac2:(zQ "50!iob!j4!hrb!lk1!hof>2kr@2$1$2$4@1$0$3") := ltac2:(zQ "he0!lk1!iob!hrb!h9!kj9!js6!hv9!kl2!jse!hka!j4!ku6!hof!ht9!km1!kn0!kp3!hj9!ip4!lk8!lo0!lm2!loc!lg2!ln1!lp4!lpc!is9!im4!it3\2kr@2$a$2$cM1\1x@1$1$4@1$1$0@6$hb@2$a$2$3$4@4$hc$5@4$h0$2$6$3$7@6$f$2$6$d$3$7$e$4@4$hd$5@4$h0$2$6$3$7@6$f$2$6$d$3$7$e$4@4$h2$2$3@3$h1$2$c^1Z@1$h7?2st\1y$4M4\1y$4@1$1$0^1\6g_meta$h6\cg_active_idx$3M1\6g_meta@1$1$5@1$1$0^2\1m$5M9\0$9@1$1$0@2$ha@1$h5@2$b?2st^1+jf@3$h9$0\1k$0@2$h4@1$h3^1@2$h8@2$b?2st^2Z?2BL@1$8$0@1$8$0@1$8$0").

Lemma bigblk_some : ltac2:(zQ "d0!hrb!lk1!hj9!lc!hof!io4!iob!j4!ipb!h9!lq3!lk8!ir7>2kr@2$7$0$4>1k$1>0@3$3@1$6$1@1$a^2@2$5$1^1@2$8@3$c$1^2?2BL@3$3$0@3$2$0$9@1$b^2@3$2$0$4^3").
Proof. intros kr k.
  unfold bigblk. intros H. destruct (s_groups st !! (fst kr, 0)) as [[[m|] ai]|] eqn:Hg; try discriminate.
  destruct (Z.eqb_spec (m_sizeclass (R m)) 63) as [S63|]; [| discriminate].
  apply find_some in H as [Hin E]. destruct (aptr_eqb_spec (bslot k) (slot_start' (R m) 0)) as [E2|]; [| discriminate].
  split; [exact Hin|]. rewrite E2, (slot_start'_eq _ _ _ IM _ (fst kr, 0) 0 (ex_intro _ ai Hg)). reflexivity.
Qed.

Lemma RG_cost1 : ltac2:(zQ "h00!hrb!hof!iob!j4!lk1!k2!h9!pe!lq3!iq7!lqd!lr6!ir7!jnf!jof!jqe>2kr@2$3$0$1>0@3$c@2$3$0$1^1@1$9?2st@2$e@1$7@1$b@3$5$0$1^2@2$d@2$f+2+h4M2\1x@1$2$4$6@1$8^2\1k$4@1$a^1Z").
Proof. intros kr.
  intros Hin. destruct kr as [rid r]. apply In_RG in Hin as [Hr K]. cbn [fst snd].
  destruct (ig_top _ _ _ IG rid r Hr K ltac:(rewrite HXO; discriminate)) as (m & Hb & ML).
  destruct (hosts_ok _ _ _ IG _ _ Hb) as (ai & Hg & GO). unfold bigblk. cbn [fst]. rewrite Hg.
  destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r' & Hr' & _ & EQ & _). cbn in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
  rewrite mmap_len_round_up.
  destruct (g_sc _ _ _ _ _ _ GO) as [[[S0 S48] M256]|(S63 & L0 & _ & _)].
  - replace (m_sizeclass (R m) =? 63) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- EQ. lia.
  - rewrite S63. cbn [Z.eqb Pos.eqb].
    pose proof (big_slot_block _ _ Hb S63) as HB.
    destruct (List.find _ BL) as [k|] eqn:F.
    + apply find_some in F as [Hk E]. destruct (aptr_eqb_spec (bslot k) (slot_start' (R m) 0)) as [E2|]; [| discriminate].
      assert (Hs : s_slots st !! (bslot k) = Some (m, 0)) by (rewrite E2; apply (is_total _ _ _ IS _ _ _ Hb); rewrite L0; lia).
      destruct (is_big _ _ _ IS k m 0 Hk Hs S63) as (r2 & Hr2 & _ & LEN).
      rewrite E2, (slot_start'_eq _ _ _ IM _ _ 0 Hb) in Hr2. cbn in Hr2. rewrite Hr in Hr2. injection Hr2 as <-.
      rewrite LEN. destruct (is_blocks _ _ _ IS k Hk) as (_ & _ & _ & _ & B0 & _).
      pose proof (MI_Cnt.round_up_pg_spec (bsize k + IB + UNIT)) as [RS _]. unfold IB, UNIT in *. lia.
    + exfalso. apply in_map_iff in HB as (k & Ek & Hk). pose proof (find_none _ _ F k Hk) as NF. cbn in NF.
      rewrite Ek, aptr_eqb_refl in NF. discriminate.
Qed.

Lemma RG_cost : ltac2:(zQ "h00!hrb!hof!j4!iq7!ua!jq5!k2!pe!lk1!lqd!lr6!jnf!jof!lrf!jpb!jqe@2$c@3$4@2$2$0$1\2kr@2$2$0$1@1$7@1$a@3$6$0$1^1@1$3?2st@2$b@2$d@1$e@2$5@2$2$0$1@1$3?2st@2$f+2+h4@3$4$8$9?2BL").
Proof.
  eapply Z.le_trans; [apply sumw_le; intros kr Hkr; apply (RG_cost1 kr Hkr)|].
  rewrite sumw_add, sumw_const, sumw_omapl. apply Zplus_le_compat_l.
  apply sumw_sub.
  - apply NoDup_omapl; [apply NoDup_of_fst; apply RG_nodup|].
    intros x y b Hx Hy Fx Fy. apply (NoDup_map_inj fst (RG st) x y (RG_nodup st) Hx Hy).
    destruct (bigblk_some _ _ Fx) as [_ <-]. destruct (bigblk_some _ _ Fy) as [_ <-]. reflexivity.
  - intros k Hk. apply In_omapl in Hk as (kr & _ & F). exact (proj1 (bigblk_some _ _ F)).
  - intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (_ & _ & _ & _ & B0 & _). exact B0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pages_areas : ltac2:(zQ "hd1!hrb!hv9!h9!hof!kl2!ht9!js6!ls6!jof!km1!kn0!kp3!im4!io4!iob!lc!lse!lta!lu9!lv1!igf!jnf!lrf!jpb!is9!lvc!mg4!imc!it3&@4$c$6@4$b$0$1$2$4@6$a$0$1$5$2$4$9$7>3rid$0>1r$3>1K$2>0@3$f@1$e$3@6$h8$0$3@4$c$0$1$5$3@4$hc$0$1$5$3^3@1$h4?2st@2$d$3^2>0@1$h1^3>0@2$8Z^3>0@2$8@2$h6@2$h5^4+1$h2@3$h0?2st^6^5@2$8^5@1$h7@3$h9~0@4$ha$6$7~0@4$hb$6@4$b$0$1$2$4@6$a$0$1$5$2$4$9$7@1$h3?2st").
Proof. intros rid r K.
  intros Hr MK K0 FR.
  pose proof (size_ge_sub (s_areas st) (map (fun q => (rid, q * PGSZ)) (zrange 1 (Z.to_nat K)))) as H.
  rewrite map_length, zrange_length in H.
  enough (HH : (Z.to_nat K <= size (s_areas st))%nat) by lia. apply H.
  - apply Finite.Injective_map_NoDup_in; [| apply zrange_nodup]. intros x y _ _ E. injection E as E. unfold PGSZ in E. lia.
  - intros a Ha. apply in_map_iff in Ha as (q & <- & Hq). apply In_zrange in Hq. rewrite Z2Nat.id in Hq by lia.
    apply (ir_pages _ _ _ IR rid r q Hr MK); [lia| unfold PGSZ in *; lia| rewrite HXF; discriminate].
Qed.

Lemma frontier_other : ltac2:(zQ "d0!h9!hrb!lc!io4!ip4!j4!kq2!lse!mh0!loc!lr6!hof!mi7>3rid$1>1r$b>0>3off$0@1$6@3$2$9@1$8@1$c?2st@2$3@2$5$1$0@4$4$1$0^3^1@3$2$0@3$7?2st^3^2@1$a^2").
Proof. intros rid r.
  intros NC. unfold frontier. destruct (c_avail_meta_areas cx) as [[rid0 off0]|] eqn:E; [| reflexivity].
  destruct (N.eqb_spec rid0 rid) as [->|]; [| reflexivity]. exfalso. exact (NC off0 eq_refl).
Qed.

(* [comment removed for export] *)
Lemma meta_full_areas : ltac2:(zQ "i61!hrb!h9!hv9!hof!kl2!ht9!lc!js6!ls6!km1!kn0!kp3!im4!io4!jof!jqe!iob!ip4!j4!kq2!lu9!iu7!mh0!loc!hr1!lr6!hq1!lv1!mi7!igf!lrf!jpb!jr5!is9!lvc!mg4!imc!it3&@4$c$7@4$b$0$2$1$4@6$a$0$2$5$1$4$9$8>3rid$0>1r$3>1j$1>0@3$6@1$h0$3@6$i1$0$3@4$c$0$2$5$3@4$i5$0$2$5$3^3@1$hd?2st@2$d$3^2>0@3$6$ha@1$h8^3$h5>0@2$eZ^3>0@3$6$1@1$h9^5@2$he@2$f+2^4$h4>0>3off$1@1$h3@3$6$h7@1$h6@1$hc?2st@2$d@2$h2$0$1@4$h1$0$1^8^1@2$e@2$i0@2$f+2^6+1@1$hf@3$i2~0@4$i3$7$8~0@4$i4$7@4$b$0$2$1$4@6$a$0$2$5$1$4$9$8@1$hb?2st").
Proof. intros rid r j.
  intros Hr K Hj LEN NC. apply (pages_areas rid r); [exact Hr| right; exact K| pose proof (Z.pow_pos_nonneg 2 j); lia|].
  rewrite (frontier_other rid r NC), LEN. lia.
Qed.

(* [comment removed for export] *)
Lemma shift_areas : ltac2:(zQ "h51!hrb!h9!hv9!kl2!js6!ls6!ht9!km1!kn0!kp3!jr5!im4!mj0!lv1!mi7!jof!jpb!jqe!lvc!mg4!imc&@4$b$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5@2$f@2$a@2$h1+2@2$a@1$c@1$e?2st+1+1@1$h0@3$h2~0@4$h3$4$5~0@4$h4$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5@1$d?2st").
Proof.
  pose proof (ir_shift _ _ _ IR) as [S0 _]. pose proof (ir_mshift _ _ _ IR) as (MA & MB & MC).
  set (sh := c_meta_alloc_shift cx) in *.
  destruct (Z.le_gt_cases sh 1) as [LE|GT].
  { assert (2^(sh - 1) <= 1); [| lia]. destruct (Z.eq_dec sh 1) as [->|NE]; [cbn; lia|]. rewrite Z.pow_neg_r by lia. lia. }
  destruct (MC sh ltac:(lia)) as (ridA & rA & HrA & KA & LA).
  destruct (MC (sh - 1) ltac:(lia)) as (ridB & rB & HrB & KB & LB).
  assert (NAB : ridA <> ridB).
  { intros ->. rewrite HrA in HrB. injection HrB as ->. rewrite LB in LA.
    replace sh with (Z.succ (sh - 1)) in LA at 2 by lia. rewrite Z.pow_succ_r in LA by lia. pose proof (Z.pow_pos_nonneg 2 (sh - 1)). unfold PGSZ in *. lia. }
  destruct (c_avail_meta_areas cx) as [[rid0 off0]|] eqn:EC.
  - destruct (N.eq_dec rid0 ridA) as [->|NE].
    + apply (meta_full_areas ridB rB (sh - 1) HrB KB ltac:(lia) LB). intros off E. rewrite EC in E. injection E as E _. exact (NAB E).
    + eapply Z.le_trans; [| apply (meta_full_areas ridA rA sh HrA KA ltac:(lia) LA); intros off E; rewrite EC in E; injection E as E _; exact (NE E)].
      replace sh with (Z.succ (sh - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. pose proof (Z.pow_pos_nonneg 2 (sh - 1)). lia.
  - eapply Z.le_trans; [| apply (meta_full_areas ridA rA sh HrA KA ltac:(lia) LA); intros off E; rewrite EC in E; discriminate].
    replace sh with (Z.succ (sh - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. pose proof (Z.pow_pos_nonneg 2 (sh - 1)). lia.
Qed.

(* [comment removed for export] *)
Lemma brk_len : ltac2:(zQ "i21!hrb!hv9!h9!hof!kl2!ht9!js6!ls6!lc!lu9!lr6!km1!kn0!kp3!im4!ipb!jof!io4!iob!mk7!hr1!hq1!lv1!igf!ml0!ml7!lrf!jpb!jr5!is9!lvc!mg4!imc!it3&@4$e$6@4$d$0$1$2$4@6$c$0$1$5$2$4$b$7>3rid$0>1r$3>0@3$8@1$h2$3@6$hd$0$3@4$e$0$1$5$3@4$i1$0$1$5$3^2@1$h7?2st@2$h1$3^1>0@3$8$h5@1$h4^2$h3@2$f@3$8$2@2$h9@1$a^3$9Z@2$f@2$h0@2$ha+2$9@1$a^3@2$h0@2$hc@2$h8@1$a^3$9+1@1$hb@3$he~0@4$hf$6$7~0@4$i0$6@4$d$0$1$2$4@6$c$0$1$5$2$4$b$7@1$h6?2st").
Proof. intros rid r.
  intros Hr K. destruct (ir_shape _ _ _ IR rid r Hr) as (_ & _ & _ & _ & _ & MK). specialize (MK ltac:(left; exact K)) as [MOD TWO].
  split; [exact MOD|]. split; [exact TWO|].
  apply (pages_areas rid r); [exact Hr| left; exact K| unfold PGSZ in *; Z.div_mod_to_equations; lia|].
  rewrite (ir_brkfront _ _ _ IR rid r Hr K). unfold PGSZ in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition jof : ltac2:(zQ "40!j4!hrb!h9!hof>2kr@2$0$1$3$2") := ltac2:(zQ "80!hrb!hof!j4!k2!lu9!lr6!ml0!mm1\2kr@2$2$0$1@1$7@2$6@1$5@3$3$0$1^1$4").

Lemma RM_j : ltac2:(zQ "h10!hrb!mm9!hof!j4!ipb!jof!k2!lc!h9!iu2!lu9!mj0!lr6!mi7!ir7!lrf!jqe>2kr@2$3$0$2>0@3$e@2$3$0$2^1@1$9?2st@2$4@2$4@2$5+1@1$1^2@2$5@1$1^2@1$b@1$d?2st@3$7$8@1$c@3$6$0$2^2@2$f@2$h0+2@1$1^2$a").
Proof. intros kr.
  intros Hin. destruct kr as [rid r]. apply In_RM in Hin as [Hr K]. pose proof (ir_mshift _ _ _ IR) as (MA & _ & _).
  destruct (MA rid r Hr K) as (j & Hj & LEN). unfold jof. cbn [snd]. rewrite LEN. unfold PGSZ.
  rewrite Z.div_mul, Z.log2_pow2 by lia. split; [exact Hj| reflexivity].
Qed.

Lemma RM_j_nodup : ltac2:(zQ "80!h9!j4!jg8!hrb!mm9!iu2!hof!jgf@2$7$0@4$2@2$1$3$6$0$4@1$5?2st").
Proof.
  apply Finite.Injective_map_NoDup_in; [| apply NoDup_of_fst; apply RM_nodup].
  intros x y Hx Hy E. apply (NoDup_map_inj fst (RM st) x y (RM_nodup st) Hx Hy).
  destruct (RM_j x Hx) as [_ LX]. destruct (RM_j y Hy) as [_ LY]. rewrite E in LX. rewrite <- LY in LX.
  destruct x as [rx x'], y as [ry y']. cbn in LX |- *. apply In_RM in Hx as [Hx Kx]. apply In_RM in Hy as [Hy Ky].
  pose proof (ir_mshift _ _ _ IR) as (_ & MB & _). exact (MB rx ry x' y' Hx Hy Kx Ky LX).
Qed.

Lemma RM_length : ltac2:(zQ "90!jq5!j4!hrb!iu2!mj0!hof!mi7!jof!jpb@2$7@1$8@2$0@2$1$2$5@1$3?2st@1$4@1$6?2st").
Proof.
  pose proof (ir_shift _ _ _ IR) as [S0 _].
  pose proof (count_incl (map jof (RM st)) (zrange 1 (Z.to_nat (c_meta_alloc_shift cx))) RM_j_nodup) as H.
  rewrite map_length, zrange_length in H. enough ((length (RM st) <= Z.to_nat (c_meta_alloc_shift cx))%nat) by lia.
  apply H. intros j Hj. apply in_map_iff in Hj as (kr & <- & Hkr). apply In_zrange. pose proof (RM_j kr Hkr) as [B _]. lia.
Qed.

Lemma sumw_scale {A} (c : Z) (w : A -> Z) l : sumw (fun x => w x * c) l = sumw w l * c.
Proof. induction l as [|x l IH]; [rewrite !sumw_nil; lia|]. rewrite !sumw_cons, IH. lia. Qed.

Lemma RM_cost : ltac2:(zQ "h00!hrb!hof!j4!k2!pe!iu2!ua!lu9!mj0!lr6!mi7!jnf!jof!lrf!jqe!jr5@2$c@3$6@2$2$0$1\2kr@2$2$0$1@1$4@1$9@3$3$0$1^1@1$5?2st@2$d@2$f@2$e+2@2$b@1$8@1$a?2st+1+2$7").
Proof.
  pose proof (ir_shift _ _ _ IR) as [S0 _].
  rewrite (sumw_ext _ (fun kr => 2^(jof kr) * PGSZ)).
  2:{ intros kr Hkr. destruct (RM_j kr Hkr) as [B LEN]. rewrite LEN. apply mmap_len_of_aligned; [pose proof (Z.pow_pos_nonneg 2 (jof kr)); unfold PGSZ; lia| unfold PGSZ; apply Z_mod_mult]. }
  rewrite <- (sumw_map jof (fun j => 2^j * PGSZ)). rewrite sumw_scale, <- geo_sum by lia. apply Z.mul_le_mono_nonneg_r; [unfold PGSZ; lia|].
  apply sumw_sub; [apply RM_j_nodup| | intros j _; apply Z.pow_nonneg; lia].
  intros j Hj. apply in_map_iff in Hj as (kr & <- & Hkr). apply In_zrange. pose proof (RM_j kr Hkr) as [B _]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ltotal_regions : ltac2:(zQ "h21!j4!hrb!hof!h9!jq5!lc!ipb!jh8!k2!pe!iq7!iu2!ua!mqc!mr9!lr6!hie!hjf&\2kr@2$0$1$2@1$9@1$f@3$8$1$2^1@2$6@3$5$3@1$h0@1$d?1L@3$c@2$0$1$2~0@1$a?2st@2$6@3$5$3@1$h1@1$e?1L@3$c@2$0$1$2~0@1$b?2st@2$6@3$5$7@2$4@2$0$3$3@1$d?1L@2$4@2$0$1$2@1$a?2st@3$5$7@2$4@2$0@2$0$3$3$3@1$e?1L@2$4@2$0$1$2@1$b?2st").
Proof.
  pose proof (ir_groups _ _ _ IR) as PG. pose proof (ir_metas _ _ _ IR) as PM.
  change (List.filter _ _) with (RG st) in PG. change (List.filter _ _) with (RM st) in PM.
  rewrite sum_glen_sumw, sum_mlen_sumw, (sumw_perm _ _ _ PG), (sumw_perm _ _ _ PM), !sumw_map. cbn [fst snd].
  rewrite (Permutation_length PG), (Permutation_length PM), !map_length. auto.
Qed.

Lemma lbrk_bound : ltac2:(zQ "h75!hrb!h9!hv9!kl2!js6!ls6!ht9!km1!kn0!kp3!im4!jof!ipb!ms5!lv1!jpb!lvc!mg4!imc!mt0!lu9!jnf!lrf&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5&@4$h2$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5&@4$h1$4$5~0~1&@3$h0~0~2@1$e?2st&@1$f~3@2$c@2$b@1$h3?1L@2$h6@2$h5~4+1$h4@2$c@2$bZ@1$d?1L@2$b@1$d?1L~4").
Proof.
  assert (NG : match ld_brk L with BPGuard _ => False | _ => True end).
  { pose proof (ir_brk _ _ _ IR) as B. destruct (c_brk cx); [destruct B as [-> _]| rewrite B| destruct B as [-> _]]; exact I. }
  unfold lbrk_bytes, lbrk_cnt. destruct (ld_brk L); try (exfalso; exact NG);
    (destruct (ld_brkreg L) as [[b l]|] eqn:ER; [| unfold PGSZ; lia]);
    (destruct (proj1 (ir_brkreg _ _ _ IR b l) ER) as (rid & r & Hr & K & _ & <-);
     destruct (brk_len rid r Hr K) as (MOD & TWO & CNT); unfold PGSZ in *; Z.div_mod_to_equations; nia).
Qed.

(* [comment removed for export] *)

End FOOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem footprint2 : ltac2:(zQ "i81!jnf!h9!hrb!js6!hv9!kl2!lk1!jof!jb!ls6!ipb!hre!lrf!jpb!ht9!km1!kn0!kp3!jq5!mtd!mu5!mud!lu9!mj0!mv3!mi7!mvc!jqe!im4!lc!ua!ng5!nge!lqd!lv1!jp5!jr5!lvc!mg4!imc&@4$hc$3@4$h1$2$4$1$5@6$h0$2$4$e$1$5$f$9>2st$b>1L$h3>2BL@1$8$6>2LS>0$h8@1$8$3>3st'$b>2L'$h3>3BL'@1$8$6>3LS'>0$h8@1$8$3>4ACAP$1>0@5$h4$h5^9^8^7^6>0@5$h4$h5^6^5^4^3>0@3$hd$b@1$ha^7@1$ha^b>0@2$7@1$d@3$i5~0@4$i6$3$9~0@4$i7$3@4$h1$2$4$1$5@6$h0$2$4$e$1$5$f$9@1$i2^c^4>0@2$i3^5+jvf@2$a@2$7@1$i0^d@2$0@2$0@2$0@2$c@2$0@1$d@2$h2$6^8+m1@2$hb+2+h4@3$he$6$i1^8@2$c@2$i4@2$hb+2+b+2$h6@2$c@2$0^6+1$h6@2$a@2$7@1$hf^d@2$0@2$0@2$0@1$d@2$h2$6^8+m1+a^6@2$a@2$7Z@1$h7@1$h9^e@2$7@1$h7@1$h9^e+a").
Proof. intros st L BL LS st' L' BL' LS' ACAP.
  intros INV INV' ES HA HC.
  assert (ER : s_regions st' = s_regions st) by (apply (f_equal s_regions) in ES; exact ES).
  assert (EG : RG st' = RG st) by (unfold RG; rewrite ER; reflexivity).
  pose proof (ir_shift _ _ _ (proj1 INV)) as [S0 _].
  assert (SH : c_meta_alloc_shift (s_ctx st) <= 10).
  { pose proof (shift_areas x0 st L BL LS INV eq_refl) as SA. destruct (Z.le_gt_cases (c_meta_alloc_shift (s_ctx st)) 10) as [LE|GT]; [exact LE|]. exfalso.
    assert (2^10 <= 2^(c_meta_alloc_shift (s_ctx st) - 1)) by (apply Z.pow_le_mono_r; lia). change (2^10) with 1024 in H. lia. }
  destruct (ltotal_regions x0 st L BL LS INV) as (E1 & E2 & L1 & L2). destruct (lbrk_bound x0 st L BL LS INV eq_refl) as [BB BC].
  pose proof (RG_cost x0 st' L' BL' LS' INV' eq_refl eq_refl) as CG. rewrite EG in CG.
  pose proof (RG_length x0 st' L' BL' LS' INV' eq_refl eq_refl) as NG. rewrite EG in NG.
  pose proof (RM_cost x0 st L BL LS INV) as CM. pose proof (RM_length x0 st L BL LS INV) as NM.
  assert (P11 : 2^(c_meta_alloc_shift (s_ctx st) + 1) <= 2^11) by (apply Z.pow_le_mono_r; lia).
  pose proof (sumw_nonneg bsize BL' ltac:(intros k Hk; destruct (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV')))))) k Hk) as (_ & _ & _ & _ & B0 & _); exact B0)).
  unfold ltotal, lcount. rewrite E1, E2, L1, L2. unfold PGSZ in *. split; [nia| split; [lia| lia]].
Qed.
(* [comment removed for export] *)
