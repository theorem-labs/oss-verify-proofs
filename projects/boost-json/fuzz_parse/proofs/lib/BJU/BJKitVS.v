(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prod46Stdlib6ZArith6BinInt1Zk22lehc3fsthc3snd37Corelib4Init5Logicmb3andmb2or37Corelib5Lists7ListDefoa6Forall69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~qa5hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~ud5blockud8blk_addrud8blk_sizeudcrblock_range36Stdlib5Lists4Listhm52Ink23add89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJKitVS3HCW~~~~~~ho4dX_above_hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7BJFrame~~~~~~ht7dxclient_range79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU5BJRep~~~~~~ii76sdeepsii75vdeepii76vdeepsud3memho4cblocks_belowii7ablocks_jvsii7ablocks_kvsii78blocks_vii72jvii73jvsii73kvsht75xpresii75kdeepii76ideepsii7cblocks_itemsii76vsitemhc6length04Npos35stdpp9bitvectorbdefinitionsjh72bvhc3natmb2eq37Corelib4Init3Natjk53mulii75ihdrs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jm74cellhc4conshc3nilmb2exmb3iffii78items_atjm72CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jt58rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~khc5rsegshc6optionk23muljm72C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kn72wzk26of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ks14bptrhc4pairk22lthc4Somemb3notii74mkVSii75vs_atjm72C1kn72b8k23powk23subk26to_natjm7bcells_bytesjm7acells_sizehc3appii79item_deepii78item_hdrjh77Z_to_bvii74Jscaii74vhdroa3mapii75VSvalhm58flat_mapii7bjvs_of_list37Corelib4Init5Peanolt12leii77jheightii7ajvs_heightii79blocks_vsii76vstack" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition X_above_hceil : ltac2:(zQ "30!h9!j4!jb>1X@1$1@2$2$0$0P") := ltac2:(zQ "a0!h9!jb!la!lf!j4!m5!nf!o5!q1!u5\1X@1$4@2$1$0$0@3$8@2$1$0$0\2iv@2$1$0$0@2$7@2$2@1$9?5HCEIL@3$3$0$0^1@2$6@2$2+hggg0@3$3$0$0^1@2$2@3$5$0$0^1+hjhgg0^1").

  (* [comment removed for export] *)
  Definition blocks_below : ltac2:(zQ "20!j4!hj8>2LB@1$0$1P") := ltac2:(zQ "60!hj8!j4!hk0!hkb!hl6!hn8\2LB@1$1$0>1b$0>0@3$5$0^1^2@3$4?5HCEIL@1$2^2@1$3^2").

  Lemma xclient_range_block : ltac2:(zQ "c0!h9!hk0!hj8!j4!hkb!hne!la!jb!hs6!ih6!hl6!hn8>2LB@1$3$2>2SP$0>1X@1$3@2$7$0$0>1b$2>1A$0>1n$0>0@3$b$2^3^6>0@2$6@1$1^4^3>0@2$6@2$5^4^3@2$5@1$1^5@1$4^5>0@3$a?5HCEIL@1$1^6@1$4^6>0@1$8^8@5$9^b^a^9^7^6").
  Proof.
    (intros LB SP X b A n Hb H1 H2 nd_i1 HX; ndestruct nd_i1 as (R1 & R2 & R3 & R4 & R5)). split.
    - right. right. exists b. split; [exact Hb| lia].
    - unfold X_above_hceil in HX. induction X as [|iv X IH]; [constructor|].
      constructor; [| apply IH; exact (Forall_inv_tail HX)]. pose proof (Forall_inv HX) as K. cbn in K. lia.
  Qed.

  Lemma vdeep_xpres_mut : ltac2:(zQ "h30!hj8!hn8!h9!j4!nf!im3!imd!in6!io0!jb!hs6!io6!ip6!iq4!ir2!ire!is4!isb!it2>2LB@1$3$0>2SP$2>1X@1$3@2$9$2$2>1m$8>2m'$8>0@5$h2^5^4^3^2^1>0@1$a^4>0@1$b^7@2$4>1v$f>0@3$6?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$e^3@3$1$0^2^c@3$6?5HCEIL^7^3@2$4>1l$h0>0@3$7?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$c^3@3$1$0^2^c@3$7?5HCEIL^7^3>1l$h1>0@3$5?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$d^3@3$1$0^2^c@3$5?5HCEIL^7^3").
  Proof.
    intros LB SP X m m' HP HX HB.
    apply jv_mutind.
    - intros k _ _. exact I.
    - intros n _ _. exact I.
    - intros [[p T] sz] n D SUB. cbn in D |- *.
      ndestruct D as (cap & junk & E1 & E2 & E3 & BR & TB). exists cap, junk.
      repeat (split; [assumption|]).
      eapply xpres_rw_cells; [exact HP| exact TB|].
      eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | apply HB; apply SUB; left; reflexivity| exact HX].
      cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. unfold lstr_tbl_size in E1. lia.
    - intros [[[p T] sz]|] cap es IH D SUB; cbn in D |- *; [|exact I].
      ndestruct D as (ebs & junk & E1 & E2 & E3 & BR & TB & HH & DD). exists ebs, junk.
      repeat (split; [assumption|]). split; [| split; [exact HH| apply IH; [exact DD| intros b Hb; apply SUB; right; exact Hb]]].
      eapply xpres_rw_cells; [exact HP| exact TB|].
      eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | apply HB; apply SUB; left; reflexivity| exact HX].
      cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. unfold arr_tbl_size in E1. lia.
    - intros [[[p T] sz]|] cap ss IH D SUB; cbn in D |- *; [|exact I].
      ndestruct D as (salt & sbs & junk & jbk & E1 & E2 & E3 & BR & TB & BK & HH & DD). nexists salt, sbs, junk, jbk.
      repeat (split; [assumption|]).
      assert (SZ : 16 + 40 * cap <= sz /\ (BJ_SMALL_OBJ < cap -> 16 + 44 * cap <= sz)).
      { unfold obj_tbl_size, BJ_SMALL_OBJ in *. destruct (Z.leb_spec cap 18); lia. }
      split; [|split; [| split; [exact HH| apply IH; [exact DD| intros b Hb; apply SUB; right; exact Hb]]]].
      + eapply xpres_rw_cells; [exact HP| exact TB|].
        eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | apply HB; apply SUB; left; reflexivity| exact HX].
        cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
      + intros HC. eapply xpres_rw_cells; [exact HP| exact (BK HC)|].
        eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | apply HB; apply SUB; left; reflexivity| exact HX].
        cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. unfold BJ_SMALL_OBJ in *. lia.
    - intros _ _. exact I.
    - intros v IHv r IHr [Dv Dr] SUB. split; [apply IHv; [exact Dv|]| apply IHr; [exact Dr|]]; intros b Hb; apply SUB; cbn; apply in_app_iff; tauto.
    - intros _ _. exact I.
    - intros [[p K] ksz] v IHv r IHr D SUB. cbn in D |- *. ndestruct D as ((K1 & K2 & kb & KB) & Dv & Dr).
      split; [| split; [apply IHv; [exact Dv|]| apply IHr; [exact Dr|]]].
      + split; [exact K1|]. split; [exact K2|]. exists kb.
        eapply xpres_rw_cells; [exact HP| exact KB|].
        eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | apply HB; apply SUB; left; reflexivity| exact HX].
        cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
      + intros b Hb. apply SUB. right. apply in_app_iff. left. exact Hb.
      + intros b Hb. apply SUB. right. apply in_app_iff. right. exact Hb.
  Qed.

  Lemma vdeep_xpres : ltac2:(zQ "c0!hj8!h9!j4!imd!io0!hn8!jb!hs6!io6!ir2!ire!it2>2LB@1$2$0>2SP$1>1X@1$2@2$6$1$1>1m$4>2m'$4>1v$a>0@5$b^6^5^4^3^2>0@1$7^5>0@1$8^8>0@3$3?5HCEIL^6^4>0>1b$0>0@3$5$0^1@1$9^6@3$5$0^2^c@3$3?5HCEIL^7^6").
  Proof. intros LB SP X m m' v HP HX HB. exact (proj1 (vdeep_xpres_mut LB SP X m m' HP HX HB) v). Qed.

  Lemma kdeep_xpres : ltac2:(zQ "a0!h9!hj8!j4!itb!io0!jb!hs6!io6!it2!hn8>2LB@1$2$1>2SP$0>1X@1$2@2$5$0$0>1m$4>2m'$4>1b$1>0@5$8^6^5^4^3^2>0@1$6^5>0@1$7^8>0@3$3?5HCEIL^6^4>0@3$9$1^5^a@3$3?5HCEIL^7^6").
  Proof.
    (intros LB SP X m m' [[p K] ksz] HP HX HB nd_i2 Hin; ndestruct nd_i2 as (K1 & K2 & kb & KB)). cbn.
    split; [exact K1|]. split; [exact K2|]. exists kb.
    eapply xpres_rw_cells; [exact HP| exact KB|].
    eapply xclient_range_block; [exact Hin| cbn; lia| | apply HB; exact Hin| exact HX].
    cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
  Qed.

  Lemma ideeps_xpres : ltac2:(zQ "c0!hj8!j4!h9!iu4!io0!hn8!jb!hs6!io6!iue!ive!it2>2LB@1$1$0>2SP$2>1X@1$1@2$6$2$2>1m$4>2m'$4>1l@1$1$a>0@5$b^6^5^4^3^2>0@1$7^5>0@1$8^8>0@3$3?5HCEIL^6^4>0>1b$0>0@3$5$0^1@1$9^6@3$5$0^2^c@3$3?5HCEIL^7^6").
  Proof.
    intros LB SP X m m' l HP HX HB. induction l as [|it r IH]; intros D SUB; [exact I|].
    destruct D as [Di Dr]. split.
    - destruct it as [v|b]; cbn in Di |- *.
      + eapply vdeep_xpres; [exact HP| exact HX| exact HB| exact Di|]. intros b Hb. apply SUB. cbn. apply in_app_iff. left. exact Hb.
      + eapply kdeep_xpres; [exact HP| exact HX| exact HB| exact Di|]. apply SUB. cbn. left. reflexivity.
    - apply IH; [exact Dr|]. intros b Hb. apply SUB. cbn. apply in_app_iff. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma ihdrs_length : ltac2:(zQ "90!jg8!j4!jh1!ive!jj4!jja!jk0!jl7!jle>1l@1$1$3>2bs@1$1@1$4@1$2#8>0@2$8^2^1@3$6$5@2$0@1$4@1$2#8^2@2$7Nh8@2$0$3^3").
  Proof.
    induction l as [|it r IH]; intros bs Hh; cbn in Hh.
    - subst bs. reflexivity.
    - ndestruct Hh as (hb & rest & -> & L & _ & Hr). rewrite length_app, L, (IH _ Hr). cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_raw : ltac2:(zQ "h60!jg8!j4!nf!jh1!ive!jj4!jl7!jq3!jqb!jja!jr2!jk0!jr8!jrd!h9!iu4!jle!js3!jsf!kh0!io0!kl9>1m$h4>1a$e>1l@1$1$4@2$d@4$h1?5HCEIL^3^2^1@2$c@1$1@1$5@1$3#8\2bs@1$1@1$5@1$3#8@2$2@3$b$9@2$0@1$5@1$3#8^1@2$6Nh8@2$0$4^2@2$2@4$h3$h5^4^3@3$8$7@2$h2@2$6Nh8@2$0$4^2^1@1$a$7@2$2@2$h0^2^1@3$f?5HCEIL^4^2").
  Proof.
    intros m a l. split.
    - (intros nd_i3; ndestruct nd_i3 as (bs & R & Hh & D)). exists bs. split; [exact (ihdrs_length _ _ Hh)|]. split; [exact R|]. split; assumption.
    - (intros nd_i4; ndestruct nd_i4 as (bs & _ & R & Hh & D)). exists bs. split; [exact R|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_relocate : ltac2:(zQ "h81!jh1!h9!jj4!j4!jq3!hj8!ive!jqb!jg8!jr2!km2!jl7!jsf!kh0!kl9!hn8!jb!hs6!io6!iue!iu4!jle!js3!it2&>0@1$2@1$0#k0@1$a@1$2@1$0#8>2LB@1$3$5>2SP$1>1X@1$3@2$h0$1$1>1m~0>2m'~0>1a$1>2a'$1>1l@1$3$6>2bs@1$3@1$2@1$0#8>0@4$d$e^6^4@3$7$4@2$c@2$bNh8@2$8$6^2^1@1$9$4>0@2$h5^3^2>0@3$h4?5HCEIL^8^4>0@4$d$e^8^6@3$7$4@2$c@2$bNh8@2$8$6^5^4@1$9$4>0@5$h7^d^c^b^a^9>0@1$h1^c>0@1$h2^f>0>1b$5>0@3$f$5^1@1$h3^a@3$f$5^2^h2@4$h6?5HCEIL^d^b^a").
  Proof.
    intros LB SP X m m' a a' l bs R Hh D R' HP HX HB SUB. exists bs. split; [exact R'|]. split; [exact Hh|].
    eapply ideeps_xpres; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma vs_at_some_intro : ltac2:(zQ "i30!jq3!h9!jqb!kmb!kn1!kr2!ive!jg8!hne!kr8!jh1!kvd!la!jj4!j4!jb!jr2!lg5!jsf!kh0!kl9!lgc!lh1!km2!jk0!lh8!js3!lhe!li6!lif!lj5!hl6!ljb!lk1!lk7>1m>0@1$d@1$a#k0@1$h7@1$d@1$a#8>1a$1>1p$b>1B$1>3cap$1>5items@1$e$6>5chars$1>4temp$1>5junk7@1$e@1$d@1$a#8>4junk@1$e@1$d@1$a#8>0@2$cZ^4>0@4$h3$h4^b^a@3$2$0@1$4@1$5Z@3$2$0@1$4@1$5^4@3$2$0@1$4@1$5^8@3$2$0@1$4@1$5@2$8^8@2$3+h8@1$9@2$7$6^6@3$2$0@1$4@1$5@2$8^8@2$3+h8^7@3$2$0@1$4@1$5^5@3$2$0@1$hd@1$he+1@3$2$0@2$h2N7^3@3$2$0@1$4@1$5Z@1$h0$0>0@2$c+h0^8>0@2$c@1$9@2$7$6^8^9>0@2$h5@2$3+h8^a@2$i0+2+i0>0@3$hf?5HCEIL^c@2$3+h8^b>0@1$h9@3$h8$1^d^9>0@4$ha?5HCEIL^h1^e^c>0>0@2$h5Z^c@2$c@2$8@2$3+h8@2$8@1$9@2$7$6^e+1^d@2$3+h8^f>0@4$h3$h4^h3@2$8^h0@2$3+h8@1$9@2$7$6^e@3$2$0@2$h2@1$i2@2$3+h8@2$i1^f@1$9@2$7$6^e^a@1$h0$0@4$hc?5HCEIL^h4^h3@5$hb@2$h6@2$f@2$f$b$1$1@4$h1@2$f$b$1$1@4$h1$b$1^h2^h1@2$3+h8^h0^h0^f^e^d").
  Proof.
    intros m a p B cap items chars temp junk7 junk H0 HD H1 H2 H3 H4 H5 H6 H7 H8.
    unfold vs_at, vs_hdr, vs_top, vs_end, vs_begin, vs_n. cbn [vs_buf vs_cap vs_items vs_chars vs_temp].
    split; [exact H0|]. split; [exists junk7; exact HD|].
    split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split; [exact H6|]. split; [exact H7|]. exists junk. exact H8.
  Qed.

  Lemma vs_at_some_elim : ltac2:(zQ "i51!h9!jq3!jqb!nf!kmb!kn1!kr2!ive!jg8!j4!hne!kr8!jh1!kvd!la!jj4!jb!jr2!lg5!jk0!jr8!jsf!kh0!kl9!lgc!lh1!lh8!js3!lhe!li6!lif!lj5!io0!hl6!ljb!lk1!lk7&@2$a^8@2$4+h8@1$b@2$8$7^5>1m$i0>1a$0>1p$d>1B$0>2sz$0>3cap$0>5items@1$9$7>5chars$0>4temp$0>0@4$hd?5HCEIL^9^8@5$hc@2$h9@2$h0@2$h0$d$0$0@4$h2@2$h0$d$0$0@4$h2$d$0^7^6^5^4^3^2^1@2$3@3$h3$0^6@2$4+h8^5@2$3@2$eZ^3@2$3@2$h4@1$9@1$f@1$c#8\5junk7@1$9@1$f@1$c#8@4$h6$h7^b^a@3$2$1@1$5@1$6Z@3$2$1@1$5@1$6^3@3$2$1@1$5@1$6^8@3$2$1@1$5@1$6~0@3$2$1@1$5@1$6@2$a^8@2$4+h8^6@3$2$1@1$5@1$6^4@3$2$1@1$he@1$hf+1@3$2$1@2$h5N7^1@3$2$1@1$5@1$6Z@1$h1$1@2$3@2$e+h0^5@2$3@2$e@1$b@2$8$7^4^5@2$3@2$h8@2$4+h8^5@2$i2+2+i0@2$3@3$i1?5HCEIL^7@2$4+h8^5@2$3@1$ha@3$h3$0^7^2@2$3@4$hb?5HCEIL^a^7^4@2$3>0@2$h8Z^3@2$e@2$a@2$4+h8@2$a@1$b@2$8$7^5+1^4@2$4+h8^6@2$h4@1$9@1$f@1$c#8\4junk@1$9@1$f@1$c#8@4$h6$h7^b~0@3$2$1@2$h5@1$i4@2$4+h8@2$i3^6@1$b@2$8$7^5^1@1$h1$1").
  Proof.
    intros m a p B sz cap items chars temp V.
    unfold vs_at, vs_hdr, vs_top, vs_end, vs_begin, vs_n in V. cbn [vs_buf vs_cap vs_items vs_chars vs_temp] in V.
    ndestruct V as (H0 & HD & SZ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). subst sz.
    split; [reflexivity|]. repeat (split; [assumption|]). exact H8.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_as_CB : ltac2:(zQ "d0!jq3!jh1!kh0!kl9!jj4!jqb!j4!jr2!km2!h9!jsf!ll0!llf>1m>0@1$4@1$1#k0@1$8@1$4@1$1#8>1A$9>2cs@1$6$0>0@4$2$3^3^2^1@4$2$3^4^3@3$5$0@2$a@1$c^2@1$b^2@1$7$0").
  Proof.
    intros m A cs [[W B] R]. split; [split|].
    - cbn. split; [apply cells_bytes_length; exact W| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
  Qed.

  Lemma ihdrs_app : ltac2:(zQ "60!j4!jh1!jle!ive!jj4!lmd>2l1@1$0$3>2l2@1$0$3>3bs1@1$0@1$4@1$1#8>3bs2@1$0@1$4@1$1#8>0@2$2^4^2>0@2$2^4^2@2$2@3$5$3^6^5@3$5@1$4@1$1#8^4^3").
  Proof.
    induction l1 as [|it r IH]; intros l2 bs1 bs2 H1 H2; cbn in H1 |- *.
    - subst bs1. exact H2.
    - ndestruct H1 as (hb & rest & -> & L & Hh & Hr). exists hb, (rest ++ bs2). rewrite app_assoc.
      split; [reflexivity|]. split; [exact L|]. split; [exact Hh|]. apply IH; assumption.
  Qed.

  Lemma ideeps_app : ltac2:(zQ "50!iu4!ive!j4!lmd!io0>1m$4>2l1@1$2$1>2l2@1$2$1>0@3$0?5HCEIL^3^2>0@3$0?5HCEIL^4^2@3$0?5HCEIL^5@3$3$1^4^3").
  Proof.
    induction l1 as [|it r IH]; intros l2 H1 H2; cbn in H1 |- *; [exact H2|].
    destruct H1 as [D R]. split; [exact D| apply IH; assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_snoc : ltac2:(zQ "h70!ive!jh1!jq3!jj4!jqb!j4!jr2!jg8!jsf!kh0!kl9!lmd!km2!jl7!h9!iu4!jle!ln3!lo0!js3!hne!kmb!kr8>1m>0@1$3@1$1#k0@1$c@1$3@1$1#8>1a$e>1l@1$5$0>2bs@1$5@1$3@1$1#8>2it$0>2hb@1$5@1$3@1$1#8>0@4$9$a^6^5@3$4$2@2$8@2$dNh8@2$7$0^4^3@1$6$2>0@2$h0^5^4>0@3$f?5HCEIL^8^6>0@4$9$a^9@2$h4^8@2$h5+h8@1$h6@2$7$0^7@3$4$2@2$8Nh8^4@1$6$2>0@2$h2^6^5>0@3$h1?5HCEIL^b^7@4$h3?5HCEIL^c^b@3$b$0^a@3$4$0^8@1$6$0").
  Proof.
    intros m a l bs it hb R Hh D R1 Hh1 D1. exists (bs ++ hb).
    split. { rewrite length_app. cbn [length]. replace (24 * (length l + 1))%nat with (24 * length l + 24)%nat by lia.
             apply rw_cells_CB_join; [exact R|]. replace (a + Z.of_nat (24 * length l)) with (a + 24 * Z.of_nat (length l)) by lia. exact R1. }
    split. { apply ihdrs_app; [exact Hh|]. cbn. exists hb, []. rewrite app_nil_r. pose proof R1 as [[W _] _]. cbn in W. destruct W as [L _].
             split; [reflexivity|]. split; [exact L|]. split; [exact Hh1| reflexivity]. }
    apply ideeps_app; [exact D|]. cbn. split; [exact D1| exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells : ltac2:(zQ "h30!jh1!jq3!jj4!jqb!j4!jr2!nf!h9!jsf!kh0!kl9!la!loc!km2!jr8!lp7!lpf!lif!kn1>1m>0@1$2@1$0#k0@1$d@1$2@1$0#8>1a$7>1k$7>3j15@1$4@1$2@1$0#8>0@4$9$a^4^3@3$3$1@1$h2@2$c@1$0#k0Z@3$3$1@1$h1@2$c@1$0#8^2@3$3$1@2$8Nf^1@1$5$1>0@2$6@2$bZ^3@2$b^3+4@2$e@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$6@4$9$a^7^6@3$3$1@2$8Nh8^1@1$5$1@2$h0@1$f^5^1").
  Proof.
    intros m a k j15 R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 15 j15]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists (firstn 7 j15), (skipn 7 j15).
    split; [rewrite firstn_length; lia|]. split; [rewrite skipn_length; lia|].
    cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells8 : ltac2:(zQ "h30!jh1!jq3!jj4!jqb!j4!jr2!nf!h9!kn1!jsf!kh0!kl9!la!loc!km2!jr8!lp7!lpf!lif>1m>0@1$2@1$0#k0@1$e@1$2@1$0#8>1a$7>1k$7>2j7@1$4@1$2@1$0#8>1w@1$2@1$0#k0>0@4$a$b^5^4@3$3$1@1$8@2$d@1$0#k0Z@3$3$1@1$h2@2$d@1$0#8^3@3$3$1@2$9N7^2@3$3$1@1$8^1@1$5$1>0@2$6@2$cZ^4@2$c^4+4@2$f@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$6@4$a$b^8^7@3$3$1@2$9Nh8^1@1$5$1@2$h1@1$h0^6^1").
  Proof.
    intros m a k j7 w R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 7 j7; C8 w]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists j7, (le8 w).
    split; [exact L|]. split; [apply length_le8|].
    cbn [cells_bytes cbytes]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells1 : ltac2:(zQ "h30!jh1!jq3!jj4!jqb!j4!jsf!jr2!nf!h9!lif!kh0!kl9!la!loc!km2!jr8!lp7!lpf!kn1>1m>0@1$2@1$0#k0@1$e@1$2@1$0#8>1a$8>1k$8>2j7@1$4@1$2@1$0#8>1b@1$2@1$0#8>3j7b@1$4@1$2@1$0#8>0@4$a$b^6^5@3$3$1@1$h2@2$d@1$0#k0Z@3$3$1@1$9@2$d@1$0#8^4@3$3$1@2$5N7^3@3$3$1@1$9^2@3$3$1@2$5N7^1@1$6$1>0@2$7@2$cZ^5@2$c^5+4@2$f@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$7@4$a$b^9^8@3$3$1@2$5Nh8^1@1$6$1@2$h1@1$h0^7^1").
  Proof.
    intros m a k j7 b j7b R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _ & Lb & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 7 j7; C1 b; CB 7 j7b]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists j7, (b :: j7b).
    split; [exact L|]. split; [cbn [length]; rewrite Lb; reflexivity|].
    cbn [cells_bytes cbytes]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ihdrs_app_inv : ltac2:(zQ "c0!j4!jh1!jj4!ive!nf!jle!lmd!jg8!jk0!jr8!jja!jl7>2l1@1$0$3>2l2@1$0$3>2bs@1$0@1$2@1$1#8>0@2$5@3$6$3^3^2^1@2$9@1$0@1$2@1$1#8\3bs1@1$0@1$2@1$1#8@2$9@1$0@1$2@1$1#8\3bs2@1$0@1$2@1$1#8@2$4@3$8@1$0@1$2@1$1#8^4@3$6@1$2@1$1#8^2^1@2$4@3$8$a@2$7@1$2@1$1#8^2@2$bNh8@2$7$3^6@2$4@2$5^6^2@2$5^5^1").
  Proof.
    induction l1 as [|it r IH]; intros l2 bs Hh; cbn in Hh.
    - exists [], bs. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity| exact Hh].
    - ndestruct Hh as (hb & rest & -> & L & Hi & Hr). destruct (IH _ _ Hr) as (bs1 & bs2 & -> & L1 & H1 & H2).
      exists (hb ++ bs1), bs2. rewrite app_assoc. split; [reflexivity|]. split; [rewrite length_app, L, L1; cbn [length]; lia|].
      split; [| exact H2]. cbn. exists hb, bs1. split; [reflexivity|]. split; [exact L|]. split; [exact Hi| exact H1].
  Qed.

  Lemma ideeps_app_inv : ltac2:(zQ "60!iu4!ive!j4!lmd!nf!io0>1m$5>2l1@1$2$1>2l2@1$2$1>0@3$0?5HCEIL^3@3$3$1^2^1@2$4@3$0?5HCEIL^4^3@3$0?5HCEIL^4^2").
  Proof.
    induction l1 as [|it r IH]; intros l2 D; cbn in D |- *; [split; [exact I| exact D]|].
    destruct D as [Di Dr]. destruct (IH _ Dr) as [D1 D2]. split; [split; [exact Di| exact D1]| exact D2].
  Qed.

  (* [comment removed for export] *)
  Lemma blocks_items_map : ltac2:(zQ "a0!ire!j4!hj8!jk0!lq7!lqd!iue!ir2!ive!lr6>2es@1$1$0@3$3@1$1$2@1$6@4$4$0$8$5^1@4$9$0$2$7^1").
  Proof. induction es as [|v r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma ideeps_map : ltac2:(zQ "a0!ire!j4!jrd!q1!lq7!lqd!iu4!imd!ive!io0>1m$9>2es@1$1$0@2$2@3$6?5HCEIL^2@4$4$0$8$5^1@3$3$0@2$7?5HCEIL^2^1").
  Proof.
    induction es as [|v r IH]; cbn.
    - split; [intros _; constructor| intros _; exact I].
    - split. { intros [D R]. constructor; [exact D| apply IH; exact R]. }
      intros F. split; [exact (Forall_inv F)| apply IH; exact (Forall_inv_tail F)].
  Qed.
  Lemma blocks_jvs_of_list : ltac2:(zQ "80!j4!ire!hj8!jk0!ip6!ir2!ls2!lr6>2es@1$0$1@3$3@1$0$2@1$4@1$6^1@4$7$1$2$5^1").
  Proof. induction es as [|v r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma vdeeps_of_list : ltac2:(zQ "80!ire!j4!jrd!q1!ls2!imd!in6!io0>1m$7>2es@1$1$0@2$2@3$6?5HCEIL^2@1$4^1@3$3$0@2$5?5HCEIL^2^1").
  Proof.
    induction es as [|v r IH]; cbn.
    - split; [intros _; constructor| intros _; exact I].
    - split. { intros [D R]. constructor; [exact D| apply IH; exact R]. }
      intros F. split; [exact (Forall_inv F)| apply IH; exact (Forall_inv_tail F)].
  Qed.
  Lemma jvs_height_of_list : ltac2:(zQ "80!ire!lu5!j4!jja!q1!lub!lv6!ls2>2es@1$2$0>1h$3>0@3$4$0\1v$0@2$1@1$5^1^2^2@2$1@1$6@1$7^3^2").
  Proof.
    induction es as [|v r IH]; intros h F; cbn; [lia|].
    pose proof (Forall_inv F) as F1. cbv beta in F1. pose proof (IH h (Forall_inv_tail F)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vs_at_xpres : ltac2:(zQ "d0!h9!hj8!j4!li6!io0!hn8!jb!hs6!io6!mg4!mh1!ih6!it2>2LB@1$2$1>2SP$0>1X@1$2@2$6$0$0>1m$4>2m'$4>1a$0>2st$a>0@5$c^7^6^5^4^3>0@1$7^6>0@1$8^9>0>1b$1>0@3$5$1^1@1$9^5@3$5$1^2^c>0@5$b^b^a^9^6+k0>0@4$3?5HCEIL^9^7^6@4$3?5HCEIL^9^8^7").
  Proof.
    intros LB SP X m m' a st HP HX HB SUB HR V.
    destruct st as [buf cap items chars temp]. destruct buf as [[[p B] sz]|].
    - destruct (vs_at_some_elim _ _ _ _ _ _ _ _ _ V) as (SZ & C0 & (junk7 & HDR) & C16 & NLE & C32 & BR & BT & ITEMS & ROOMI & (junk & JK)).
      subst sz.
      assert (INB : In (p, B, 24 * cap) LB) by (apply SUB; left; reflexivity).
      eapply vs_at_some_intro with (junk7 := junk7) (junk := junk); try assumption.
      + eapply xpres_rw_cells; [exact HP| exact HDR| exact HR].
      + apply items_at_raw in ITEMS. ndestruct ITEMS as (bs & L & R & Hh & D).
        eapply items_at_relocate; [exact R| exact Hh| exact D| | exact HP| exact HX| exact HB| ].
        * eapply xpres_rw_cells; [exact HP| exact R|].
          eapply xclient_range_block; [exact INB| cbn [blk_addr fst snd]; lia| | apply HB; exact INB| exact HX].
          cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
        * intros b Hb. apply SUB. right. exact Hb.
      + eapply xpres_rw_cells; [exact HP| exact JK|].
        eapply xclient_range_block; [exact INB| cbn [blk_addr fst snd]; lia| | apply HB; exact INB| exact HX].
        cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
    - unfold vs_at in V |- *. cbn [vs_buf vs_cap vs_items vs_chars vs_temp] in V |- *.
      ndestruct V as (C0 & (junk7 & HDR) & R3). split; [exact C0|]. split; [| exact R3].
      exists junk7. eapply xpres_rw_cells; [exact HP| exact HDR| exact HR].
  Qed.

End HCW.
