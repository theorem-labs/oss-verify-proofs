(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsDepotInv.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj63addj62lej62lthc2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~m37AIAINITm37AIAINSTm35AINSTm33ast79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~s35depot69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hgbasc_map_beghgb6schunkm34a_sb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~hmb2shhgb9kPageSizehgb6as_sechgbakSpaceSizehgbbsc_map_sizem34a_pam34a_stm35a_thrs34d_nbs34d_sb36Stdlib5Lists4Listig72Inj63mulhc2exhgbh0kPtrArrayReserve89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAG_WriteSet3HCW~~~~~~ik06astatwj63divhmb3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ipc2wa37Corelib4Init9Datatypesitc6optionhc2eqhc3not04Nposik05awritj63pow35stdpp9bitvectorbdefinitionsjhe2bv3h5LinuxProcessSemanticsfLinuxProcessSem5Statejk15Modeljhebbv_unsigneditc4boolitc4truejk18m_vmmapsjk17vm_maps69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~jqeain_rangesb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jvb3ivlitc3fstitc4listitc3sndik06acompljvb5munchitc4prod37Corelib5Lists7ListDefkmf6Forallik04avmxjqeh5same_but_materialized79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kr22wzjk1bregion_freehgb4mkSC" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition astatw : ltac2:(zQ "10!h9>1a$0P") := ltac2:(zQ "90!j0!ke!l4!l9!le!q1!qb!r5!h9\1a$8@2$4@2$0@2$2@2$1$7+n0^1@2$3^1@2$1$7+jp8@2$4@2$0@2$2+iovgk8^1@2$3^1+mpvgn0@2$4@2$0@2$2$5^1@2$3^1@2$1$5+4@2$0@2$2$6^1@2$3^1@2$1$6+ohgj0").
  (* [comment removed for export] *)
  Definition awrit : ltac2:(zQ "30!h9!rd!hg3>1s$1>2s'$1>1d$2>2lo$0>2SP$0>1a$0P") := ltac2:(zQ "hb0!ke!j0!le!l4!l9!hkc!hla!hm4!hq9!h9!hqf!hrc!hs6!ht4!hu3!hua!hv1!rd!hv9!ig0!iha!ii0!ii6!iib!io5!hg3!iof\1s$h1\2s'$h1\1d$h9\2lo$9\2SP$9\1a$9@2$2@2$1@2$3^3^1@2$4^1^2@2$2@2$1@2$3@2$0@1$h0^6+k0^1@2$4^1@2$0@1$h0^6$a@2$2@2$1@2$3@1$7^6^1@2$4^1@2$0@2$0@1$7^6$c$a@2$2@2$1@2$3@1$8@1$7^6^1@2$4^1@1$8@2$0@2$0@1$7^6$c$a@2$2@2$1@2$3@1$e^6^1@2$4^1@2$0@1$e^6$h7@2$2@2$h6$6\2sc$6@2$1@2$2@3$h4$6^1@1$b@1$f^7@3$h4$6^1@1$b@1$f^6@2$2@2$1@2$3@1$5^1^2@2$4^2@2$0@1$5^1@1$d^1@2$1@2$3@1$8@1$5^1^2@2$4^2@2$0@1$8@1$5^1@2$ha@1$d^1+8@2$2@1$h8^1@2$2@2$1@2$3@1$h2^4^1@2$4^1@2$0@1$h2^4@2$h5+h0+hggg0@2$1@2$3@1$h3^4^1@2$4^1@2$0@1$h3^4@2$h5+8+ogg0").

  Definition acompl : ltac2:(zQ "40!h9!rd!ip5!hg3>1s$1>2s'$1>1d$3>2lo$0>2SP$0>1m$2>2m'$2P") := ltac2:(zQ "f0!h9!rd!ip5!it6!iv4!j0!ive!jg3!jg9!jgf!hg3!l4!l9!jh8!jjb\1s$1\2s'$1\1d$a\2lo$0\2SP$0\1m$2\2m'$2>1a$0>0@2$5@2$bZ^1@2$c^1@2$d+2+k0>0@1$7@6$9^9^8^7^6^5^2@3$6@1$4@1$e@1$8#8@1^4@1$3^3@1^5@1$3^3").

  (* [comment removed for export] *)
  Definition avmx : ltac2:(zQ "20!jmf!rd>1s$1>2s'$1>2mo$0>3mo'$0P") := ltac2:(zQ "h80!hla!j0!jg9!hrc!hkc!hua!iha!jn8!jg3!jo7!jof!ive!jmf!jp7!jq3!ht4!rd!jud!ke!l4!l9!ii6!le!jjb\1s$h0\2s'$h0\2mo$c\3mo'$c>1x@1$h7@1$2#k0>0@3$b$9@2$h1^1@1$e@1$d^3$a@2$1@2$h6@3$b$9@2$h1^2@1$e@1$d^3$a@2$h5$0\2sc$0@2$1@3$6$0^1@1$3@1$5^7@2$1@1$8@3$6$0^1@1$3@1$5^6@2$1@2$h3@1$4^1@2$7@1$2#k0^3@2$h4@2$7@1$2#k0^3@2$h2@1$4^1@1$f^1>2sc$0>0@3$6$0^1@1$3@1$5^6>0@1$8@3$6$0^2@1$3@1$5^8@1$8@2$1@2$h3@1$4^3@2$7@1$2#k0^5@2$h4@2$7@1$2#k0^5@2$h2@1$4^3@1$f^3").

  (* [comment removed for export] *)
  Lemma acompl_of_munch : ltac2:(zQ "h11!h9!jg9!jjb!kj7!iv4!rd!kje!kk5!kkd!j0!kl4!jgf!hg3!kle!iha!l4!l9&>0@1$2@1$1#k0@1$4@1$2@1$1#8>1s$5>2s'$5>1d$c>2lo$0>2SP$0>1W@1$7$3>1m~0>2m'~0>0@3$d^3^2^1>0>2iv$3>1a$0>0@3$e$3^2^6>0@2$9@2$f@3$6$0$0^3^2@2$h0^2@3$8$0$0^3@6$b^d^c^b^a^9^3@7$a^a^9^8^7^6^4^3").
  Proof.
    intros s s' d lo SP W m m' MU SUB a Ha NW. pose proof (MU (wa a)) as E. rewrite wa_unsigned in E by exact Ha. apply E. clear E MU.
    induction W as [|[x y] W IH]; [exact I|]. cbn. split.
    - intros R. apply NW. apply (SUB (x, y) a); [left; reflexivity| exact R].
    - apply IH. intros iv b Hiv Hb. apply (SUB iv b); [right; exact Hiv| exact Hb].
  Qed.
  Lemma acompl_of_munchF : ltac2:(zQ "h21!h9!jg9!jjb!iv4!km7!rd!kje!kk5!kkd!j0!ko6!kl4!jgf!hg3!kj7!kle!l4!l9&>0@1$2@1$1#k0@1$3@1$2@1$1#8>1s$5>2s'$5>1d$d>2lo$0>2SP$0>1W@1$7$e>1m~0>2m'~0>0@3$f^3^2^1>0@3$a@2$4$0$0\2iv@2$4$0$0>1a$0>0@2$9@2$h0@3$6$0$0^2^1@2$h1^1@3$8$0$0^2@6$c^c^b^a^9^8^2^4@7$b^a^9^8^7^6^4^3").
  Proof.
    intros s s' d lo SP W m m' MU FA. apply (acompl_of_munch s s' d lo SP W m m' MU).
    intros iv a Hiv Ha. exact (proj1 (Forall_forall _ _) FA iv Hiv a Ha).
  Qed.
  (* [comment removed for export] *)
  Lemma awrit_mono : ltac2:(zQ "90!hla!h9!hrc!hua!rd!iha!jgf!le!hg3>1s$4>2s1$4>2s2$4>1d$8>2lo$1>2SP$1>1a$1>0>2sc$0>0@3$5$0^1@1$2@1$3^7@2$7@3$5$0^2@1$2@1$3^7@3$5$0^2@1$2@1$3^9>0@6$6^8^7^5^4^3^2@6$6^9^7^6^5^4^3").
  Proof.
    intros s s1 s2 d lo SP a SUB W. unfold awrit in *.
    destruct W as [H|[H|[H|[H|[H|[H|H]]]]]]; [tauto|tauto|tauto|tauto|tauto| |tauto].
    right; right; right; right; right; left. ndestruct H as (sc & I & R). exists sc. split; [| exact R].
    destruct I as [I|I]; [left; exact I|]. destruct (SUB sc I); [right| left]; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma acompl_refl : ltac2:(zQ "50!h9!rd!kl4!hg3!ip5>1s$1>2s'$1>1d$3>2lo$0>2SP$0>1m$4@7$2^6^5^4^3^2^1^1").
  Proof. intros s s' d lo SP m a _ _. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma avmx_same : ltac2:(zQ "d0!kk5!ive!jg9!jmf!jp7!jq3!hrc!hua!rd!jjb!km7!hla!kp0>1s$8>2s'$8>2mo$3>3mo'$3>0@3$1@1$0@2$a@1$9@1$2#k0@1$9@1$2#k0@1$5@1$4^1@1$5@1$4^2>0@3$1@1$0$b@1$6@1$7^4@1$6@1$7^5@4$c^6^5^4^3").
  Proof. intros s s' mo mo' EV ES x Hx. rewrite EV, ES. split; [left; exact Hx|]. intros sc A B. exact (False_ind _ (B A)). Qed.
  Lemma avmx_mat_l : ltac2:(zQ "40!jmf!kp0!rd!kp8>1s$2>2s'$2>2mo$0>3mo1$0>3mo'$0>0@2$3^3^2>0@4$1^6^5^3^2@4$1^7^6^5^3").
  Proof. intros s s' mo mo1 mo' SB A x Hx. apply A. rewrite (same_but_materialized_vmmaps mo mo1 SB). exact Hx. Qed.
  Lemma avmx_mat_r : ltac2:(zQ "40!jmf!kp0!rd!kp8>1s$2>2s'$2>2mo$0>3mo1$0>3mo'$0>0@4$1^5^4^3^2>0@2$3^3^2@4$1^7^6^5^3").
  Proof. intros s s' mo mo1 mo' A SB x Hx. rewrite (same_but_materialized_vmmaps mo1 mo' SB). exact (A x Hx). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma avmx_cons : ltac2:(zQ "h80!ive!hla!jo7!jof!h9!jp7!jq3!jmf!hrc!hua!rd!jud!kud!iha!l9!le!jg9!kv3!lg2!kp0!ke!l4!jh8!jjb>1s$a>2s'$a>2mo$7>3mo'$7>1a$4>3msz$4>1z$4>0@2$h5Z^3>0@2$eZ^3>0@2$e@2$h4^5^4@2$h6+2+k0>0@3$0$2@3$h1@1$6@1$5^8@1$c^6@1$c^5$3>0>1x@1$h7@1$h0#k0>0@3$0$2@2$b^1@1$6@1$5^a$3@3$0$2@2$b^2@1$6@1$5^a$3>0>2sc$1>0@3$d$1^1@1$8@1$9^c@2$f@3$d$1^2@1$8@1$9^e@3$0$1^2@3$h2^a^9^8@4$h3^d^c^b^a").
  Proof.
    intros s s' mo mo' a msz z Ha Hm Ham FR INCL SEC x Hx. split; [left; exact (INCL x Hx)|].
    intros sc Hin Hnot R. destruct (SEC sc Hin) as [Old| ->]; [exact (Hnot Old)|]. cbn [sc_map_beg sc_map_size] in R.
    pose proof (region_free_not_in _ _ _ x FR) as NI. unfold wz in NI. rewrite !unsigned_lit in NI by lia.
    rewrite (NI R) in Hx. discriminate Hx.
  Qed.
End HCW.
(* [comment removed for export] *)
