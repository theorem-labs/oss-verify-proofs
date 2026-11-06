(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List MI_Ext.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01N01Z35stdpp7numbers1Nhf6eq_dec35stdpp7numbers1Zj96eq_dec37Corelib4Init5Logicl32eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~mc5inv_M79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~r24aptrr28s_groupsr27s_metas25stdpp9countablehgcbN_countablehgcbZ_countablehgceprod_countable25stdpp9decidablehkdbprod_eq_dec25stdpp4gmaphmd4gmapr24ghdrr24metamc5inv_Lr28get_headr25lheadr24optrr26region37Corelib4Init9Datatypeshra4Somehra6optionhra4prodmc8group_okr29s_regionsr27s_slots25stdpp4baseigd6lookuphmdbgmap_lookuphra3fstr27RKGroupr26r_kindr25rkindl32exmc3blkl33andmc5bslothra4pairr24cptr36Stdlib5Lists4Listinc2Inmc5inv_S89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MI_Ext24EXT2~~~~~~ipdh0blk_regions_keptr26mstatehra4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MI_Ext2~~~~~~jg7h0blk_regions_kept" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Section EXT2.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).

Lemma inv_M_ext : ltac2:(zQ "h00!h9!hc!j0!ka!m7!qa!v0!v7!hg2!hhd!hic!hjb!hle!hn9!ho1!ho8>0@3$4@4$d$6@4$c$0$2$1$3@6$b$0$2$9$1$3$a$f@1$8?3st'@1$8?2st>0@3$4@4$d$6@4$c$0$2$1$3@6$b$0$2$9$1$3$a$e@1$7?3st'@1$7?2st>0@3$5?1X?2st?2LS@3$5?1X?3st'?2LS").
Proof.
  intros HM HG I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5 M6]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
  - intros m Hm. rewrite HM in Hm. rewrite (live_group_ext st st' HG). apply M6. exact Hm.
Qed.

Lemma inv_L_ext : ltac2:(zQ "h30!h9!hc!j0!ka!m7!hof!v0!hp7!v7!hg2!hhd!hic!hjb!hle!hn9!ho1!hq2!ho8!hqa>0@3$4@4$e$6@4$d$0$2$1$3@6$c$0$2$a$1$3$b$h1@1$9?3st'@1$9?2st>0@3$4@4$e$6@4$d$0$2$1$3@6$c$0$2$a$1$3$b$f@1$8?3st'@1$8?2st>0>1h$h0@3$4$h2@2$7?3st'^1@2$7?2st^1>0@2$5?2st?2LS@2$5?3st'?2LS").
Proof.
  intros HM HG HE I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

Lemma group_ok_ext : ltac2:(zQ "ha0!h9!hr1!hc!j0!m7!hhd!v0!hn9!ka!ht2!hta!hu4!huc!hg2!hv7!ig3!ih9!hic!hjb!hle!ii3!ij2!ij9!ho8!ik3!ikc>1m$6>1b@2$b$0$2>2ai$2>0@3$4@4$7$6@4$h3$0$3$2$8@6$h2$0$3$5$2$8$h1$h7@1$d?3st'@1$d?2st>0@3$4@4$7$6@4$h3$0$3$2$8@6$h2$0$3$5$2$8$h1@2$b$6$2@1$f?3st'@1$f?2st>0>3rid$0>1r$1>0@3$4@1$a$1@6$h0$0$1@4$7$0$3$5$1@4$h4$0$3$5$1^2@1$e?2st@2$9$1^1>0@3$4$h9@1$h8^2$h6>0@3$4$0@3$h5$0$2^8^4@3$4@1$a$1@6$h0$0$1@4$7$0$3$5$1@4$h4$0$3$5$1^5@1$e?3st'@2$9$1^4>0@6$c?1X?2st?2LS^6^5^4@6$c?1X?3st'?2LS^7^6^5").
Proof. intros m b ai.
  intros HM HS HR I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HS; try assumption.
  - intros Hml. destruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [| auto]. apply HR; auto.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

(* [comment removed for export] *)
Definition blk_regions_kept : ltac2:(zQ "00P") := ltac2:(zQ "he0!h9!hc!hr1!v0!j0!hhd!hu4!m7!ka!ht2!hta!il4!il9!ih9!hn9!ii3!ilf!im5!hv7!hic!hjb!hle!ij2!imd!ij9!in5!ik3!ikc!ig3!iof>3rid$0>1r$2>0@3$7@1$a$2@6$d$0$2@4$e$0$4$5$2@4$f$0$4$5$2^2@1$h2?2st@2$9$2^1>0@3$7$hb@1$ha^2$h8>0@2$b$c\1k$c@2$b$3\1m$3@2$b$1\1i$1@2$h0@3$hd$c^3?2BL@2$h0@3$7@1$a@2$6$3$1@6$d$h9@2$6$3$1@4$e$3@4$h5$0$4$1$8@6$h4$0$4$5$1$8$h3@2$6$3$1@4$f$3@4$h5$0$4$1$8@6$h4$0$4$5$1$8$h3@2$6$3$1@1$h1^3@1$hc?2st@2$9@2$6$3$1@4$h7$3$1^2^1@3$7$0@3$h6$0$1@1$h1^3^7@3$7@1$a$2@6$d$0$2@4$e$0$4$5$2@4$f$0$4$5$2^5@1$h2?3st'@2$9$2^4").

Lemma inv_S_ext : ltac2:(zQ "h30!hc!h9!j0!ka!v0!m7!hhd!hic!hjb!hle!hn9!ip5!v7!hg2!ig3!hu4!iu1!ho1!ho8>0@3$5@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$h2@1$d?3st'@1$d?2st>0@3$5@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$h1@1$c?3st'@1$c?2st>0@3$5@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7@2$f$4$0@1$e?3st'@1$e?2st>0$h0>0@3$b?1X?2st?2BL@3$b?1X?3st'?2BL").
Proof.
  intros HM HG HS HRK I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6 S7]; constructor.
  - intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
  - intros k m i Hk H1 H2. rewrite HS in H1. rewrite ME in H2. destruct (S7 k m i Hk H1 H2) as (r & Hr & Hkd & Hl).
    exists r. split; [| split; [exact Hkd| exact Hl]]. apply HRK; [exact Hr| exact Hkd|]. exists k, m, i. auto.
Qed.
End EXT2.

(* [comment removed for export] *)
Lemma blk_regions_kept_refl : ltac2:(zQ "b0!iv6!hv7!ivf!m7!h9!jk6!il9!hr1!hhd!hn9!j0>2st$0>3st'$0>2BL@1$2$6>0@3$3@4$9$4$a$8$7@1$1^2@1$1^3@3$5^4^3^2").
Proof. intros st st' BL. intros E rid r Hr _ _. rewrite E. exact Hr. Qed.
