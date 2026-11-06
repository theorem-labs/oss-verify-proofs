(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prod46Stdlib6ZArith6BinInt1Zk22lehc3fsthc3snd37Corelib4Init5Logicmb3andmb2or37Corelib5Lists7ListDefoa6Forall69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~qa5hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~ud5blockud8blk_addrud8blk_sizeudcrblock_range36Stdlib5Lists4Listhm42Ink23add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJFrame~~~~~~ho3dxclient_range89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJKitVS3HCW~~~~~~ht1dX_above_hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ5BJRep~~~~~~ii36sdeepsii35vdeepii36vdeepsud3memho35xpresht1cblocks_belowii3ablocks_jvsii3ablocks_kvsii38blocks_vii32jvii33jvsii33kvsii35kdeepii36ideepsii3cblocks_itemsii36vsitemhc6length04Npos35stdpp9bitvectorbdefinitionsjh22bvhc3natmb2eq37Corelib4Init3Natjk03mulii35ihdrs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jm24cellhc4conshc3nilmb2exmb3iffii38items_atjm22CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jt08rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~kh75rsegshc6optionk23muljm22C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kn12wzk26of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~krb4bptrhc4pairk22lthc4Somemb3notii34mkVSii35vs_atjm22C1kn12b8k23powk23subk26to_natjm2bcells_bytesjm2acells_sizehc3appii39item_deepii38item_hdrjh27Z_to_bvii34Jscaii34vhdroa3mapii35VSvalhm48flat_mapii3bjvs_of_list37Corelib4Init5Peanolsb2leii37jheightii3ajvs_heightii39blocks_vsii36vstack" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition X_above_hceil : ltac2:(zQ "30!h9!j4!jb>1X@1$1@2$2$0$0P") := ltac2:(zQ "a0!h9!jb!la!lf!j4!m5!nf!o5!q1!u5\1X@1$4@2$1$0$0@3$8@2$1$0$0\2iv@2$1$0$0@2$7@2$2@1$9?5HCEIL@3$3$0$0^1@2$6@2$2+hggg0@3$3$0$0^1@2$2@3$5$0$0^1+hitgg0^1").

  (* [comment removed for export] *)
  Definition blocks_below : ltac2:(zQ "20!j4!hj7>2LB@1$0$1P") := ltac2:(zQ "60!hj7!j4!hjf!hka!hl5!hn7\2LB@1$1$0>1b$0>0@3$5$0^1^2@3$4?5HCEIL@1$2^2@1$3^2").

  Lemma xclient_range_block : ltac2:(zQ "c0!h9!hjf!hj7!j4!hka!hnd!la!jb!hs0!ih2!hl5!hn7>2LB@1$3$2>2SP$0>1X@1$3@2$7$0$0>1b$2>1A$0>1n$0>0@3$b$2^3^6>0@2$6@1$1^4^3>0@2$6@2$5^4^3@2$5@1$1^5@1$4^5>0@3$a?5HCEIL@1$1^6@1$4^6>0@1$9^8@5$8^b^a^9^7^6").
  Proof.
    (intros LB SP X b A n Hb H1 H2 nd_i1 HX; ndestruct nd_i1 as (R1 & R2 & R3 & R4 & R5)). split.
    - right. right. exists b. split; [exact Hb| lia].
    - unfold X_above_hceil in HX. induction X as [|iv X IH]; [constructor|].
      constructor; [| apply IH; exact (Forall_inv_tail HX)]. pose proof (Forall_inv HX) as K. cbn in K. lia.
  Qed.

  Lemma vdeep_xpres_mut : ltac2:(zQ "h30!hj7!hn7!h9!j4!nf!ile!im8!in1!inb!jb!io1!ih2!ioa!ipa!iq8!ir6!is2!is8!isf>2LB@1$3$0>2SP$2>1X@1$3@2$9$2$2>1m$8>2m'$8>0@5$a^5^4^3^2^1>0@1$b^4>0@1$c^7@2$4>1v$h0>0@3$6?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$f^3@3$1$0^2^c@3$6?5HCEIL^7^3@2$4>1l$h1>0@3$7?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$d^3@3$1$0^2^c@3$7?5HCEIL^7^3>1l$h2>0@3$5?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$e^3@3$1$0^2^c@3$5?5HCEIL^7^3").
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

  Lemma vdeep_xpres : ltac2:(zQ "c0!hj7!h9!j4!im8!inb!hn7!jb!io1!ih2!ioa!ir6!is2>2LB@1$2$0>2SP$1>1X@1$2@2$6$1$1>1m$4>2m'$4>1v$b>0@5$7^6^5^4^3^2>0@1$8^5>0@1$9^8>0@3$3?5HCEIL^6^4>0>1b$0>0@3$5$0^1@1$a^6@3$5$0^2^c@3$3?5HCEIL^7^6").
  Proof. intros LB SP X m m' v HP HX HB. exact (proj1 (vdeep_xpres_mut LB SP X m m' HP HX HB) v). Qed.

  Lemma kdeep_xpres : ltac2:(zQ "a0!h9!hj7!j4!it6!inb!jb!io1!ih2!ioa!hn7>2LB@1$2$1>2SP$0>1X@1$2@2$5$0$0>1m$4>2m'$4>1b$1>0@5$6^6^5^4^3^2>0@1$7^5>0@1$8^8>0@3$3?5HCEIL^6^4>0@3$9$1^5^a@3$3?5HCEIL^7^6").
  Proof.
    (intros LB SP X m m' [[p K] ksz] HP HX HB nd_i2 Hin; ndestruct nd_i2 as (K1 & K2 & kb & KB)). cbn.
    split; [exact K1|]. split; [exact K2|]. exists kb.
    eapply xpres_rw_cells; [exact HP| exact KB|].
    eapply xclient_range_block; [exact Hin| cbn; lia| | apply HB; exact Hin| exact HX].
    cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
  Qed.

  Lemma ideeps_xpres : ltac2:(zQ "c0!hj7!j4!h9!itf!inb!hn7!jb!io1!ih2!ioa!iu9!iv9>2LB@1$1$0>2SP$2>1X@1$1@2$6$2$2>1m$4>2m'$4>1l@1$1$b>0@5$7^6^5^4^3^2>0@1$8^5>0@1$9^8>0@3$3?5HCEIL^6^4>0>1b$0>0@3$5$0^1@1$a^6@3$5$0^2^c@3$3?5HCEIL^7^6").
  Proof.
    intros LB SP X m m' l HP HX HB. induction l as [|it r IH]; intros D SUB; [exact I|].
    destruct D as [Di Dr]. split.
    - destruct it as [v|b]; cbn in Di |- *.
      + eapply vdeep_xpres; [exact HP| exact HX| exact HB| exact Di|]. intros b Hb. apply SUB. cbn. apply in_app_iff. left. exact Hb.
      + eapply kdeep_xpres; [exact HP| exact HX| exact HB| exact Di|]. apply SUB. cbn. left. reflexivity.
    - apply IH; [exact Dr|]. intros b Hb. apply SUB. cbn. apply in_app_iff. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma ihdrs_length : ltac2:(zQ "90!jg3!j4!jgc!iv9!jif!jj5!jjb!jl2!jl9>1l@1$1$3>2bs@1$1@1$4@1$2#8>0@2$8^2^1@3$6$5@2$0@1$4@1$2#8^2@2$7Nh8@2$0$3^3").
  Proof.
    induction l as [|it r IH]; intros bs Hh; cbn in Hh.
    - subst bs. reflexivity.
    - ndestruct Hh as (hb & rest & -> & L & _ & Hr). rewrite length_app, L, (IH _ Hr). cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_raw : ltac2:(zQ "h60!jg3!j4!nf!jgc!iv9!jif!jl2!jpe!jq6!jj5!jqd!jjb!jr3!jr8!h9!itf!jl9!jre!jsa!kgb!inb!kl3>1m$h4>1a$e>1l@1$1$4@2$d@4$h1?5HCEIL^3^2^1@2$c@1$1@1$5@1$3#8\2bs@1$1@1$5@1$3#8@2$2@3$b$9@2$0@1$5@1$3#8^1@2$6Nh8@2$0$4^2@2$2@4$h3$h5^4^3@3$8$7@2$h2@2$6Nh8@2$0$4^2^1@1$a$7@2$2@2$h0^2^1@3$f?5HCEIL^4^2").
  Proof.
    intros m a l. split.
    - (intros nd_i3; ndestruct nd_i3 as (bs & R & Hh & D)). exists bs. split; [exact (ihdrs_length _ _ Hh)|]. split; [exact R|]. split; assumption.
    - (intros nd_i4; ndestruct nd_i4 as (bs & _ & R & Hh & D)). exists bs. split; [exact R|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_relocate : ltac2:(zQ "h81!jgc!h9!jif!j4!jpe!hj7!iv9!jq6!jg3!jqd!klc!jl2!jsa!kgb!kl3!hn7!jb!io1!ih2!ioa!iu9!itf!jl9!jre&>0@1$2@1$0#k0@1$a@1$2@1$0#8>2LB@1$3$5>2SP$1>1X@1$3@2$h0$1$1>1m~0>2m'~0>1a$1>2a'$1>1l@1$3$6>2bs@1$3@1$2@1$0#8>0@4$d$e^6^4@3$7$4@2$c@2$bNh8@2$8$6^2^1@1$9$4>0@2$h6^3^2>0@3$h5?5HCEIL^8^4>0@4$d$e^8^6@3$7$4@2$c@2$bNh8@2$8$6^5^4@1$9$4>0@5$h1^d^c^b^a^9>0@1$h2^c>0@1$h3^f>0>1b$5>0@3$f$5^1@1$h4^a@3$f$5^2^h2@4$h7?5HCEIL^d^b^a").
  Proof.
    intros LB SP X m m' a a' l bs R Hh D R' HP HX HB SUB. exists bs. split; [exact R'|]. split; [exact Hh|].
    eapply ideeps_xpres; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma vs_at_some_intro : ltac2:(zQ "i30!jpe!h9!jq6!km5!kmb!kqc!iv9!jg3!hnd!kr2!jgc!kv7!la!jif!j4!jb!jqd!kvf!jsa!kgb!kl3!lg6!lgb!klc!jjb!lh2!jre!lh8!li0!li9!lif!hl5!lj5!ljb!lk1>1m>0@1$d@1$a#k0@1$h7@1$d@1$a#8>1a$1>1p$b>1B$1>3cap$1>5items@1$e$6>5chars$1>4temp$1>5junk7@1$e@1$d@1$a#8>4junk@1$e@1$d@1$a#8>0@2$cZ^4>0@4$h3$h4^b^a@3$2$0@1$4@1$5Z@3$2$0@1$4@1$5^4@3$2$0@1$4@1$5^8@3$2$0@1$4@1$5@2$8^8@2$3+h8@1$9@2$7$6^6@3$2$0@1$4@1$5@2$8^8@2$3+h8^7@3$2$0@1$4@1$5^5@3$2$0@1$hd@1$he+1@3$2$0@2$h2N7^3@3$2$0@1$4@1$5Z@1$h0$0>0@2$c+h0^8>0@2$c@1$9@2$7$6^8^9>0@2$h5@2$3+h8^a@2$i0+2+i0>0@3$hf?5HCEIL^c@2$3+h8^b>0@1$h9@3$h8$1^d^9>0@4$ha?5HCEIL^h1^e^c>0>0@2$h5Z^c@2$c@2$8@2$3+h8@2$8@1$9@2$7$6^e+1^d@2$3+h8^f>0@4$h3$h4^h3@2$8^h0@2$3+h8@1$9@2$7$6^e@3$2$0@2$h2@1$i2@2$3+h8@2$i1^f@1$9@2$7$6^e^a@1$h0$0@4$hc?5HCEIL^h4^h3@5$hb@2$h6@2$f@2$f$b$1$1@4$h1@2$f$b$1$1@4$h1$b$1^h2^h1@2$3+h8^h0^h0^f^e^d").
  Proof.
    intros m a p B cap items chars temp junk7 junk H0 HD H1 H2 H3 H4 H5 H6 H7 H8.
    unfold vs_at, vs_hdr, vs_top, vs_end, vs_begin, vs_n. cbn [vs_buf vs_cap vs_items vs_chars vs_temp].
    split; [exact H0|]. split; [exists junk7; exact HD|].
    split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split; [exact H6|]. split; [exact H7|]. exists junk. exact H8.
  Qed.

  Lemma vs_at_some_elim : ltac2:(zQ "i51!h9!jpe!jq6!nf!km5!kmb!kqc!iv9!jg3!j4!hnd!kr2!jgc!kv7!la!jif!jb!jqd!kvf!jjb!jr3!jsa!kgb!kl3!lg6!lgb!lh2!jre!lh8!li0!li9!lif!inb!hl5!lj5!ljb!lk1&@2$a^8@2$4+h8@1$b@2$8$7^5>1m$i0>1a$0>1p$d>1B$0>2sz$0>3cap$0>5items@1$9$7>5chars$0>4temp$0>0@4$hd?5HCEIL^9^8@5$hc@2$h9@2$h0@2$h0$d$0$0@4$h2@2$h0$d$0$0@4$h2$d$0^7^6^5^4^3^2^1@2$3@3$h3$0^6@2$4+h8^5@2$3@2$eZ^3@2$3@2$h4@1$9@1$f@1$c#8\5junk7@1$9@1$f@1$c#8@4$h6$h7^b^a@3$2$1@1$5@1$6Z@3$2$1@1$5@1$6^3@3$2$1@1$5@1$6^8@3$2$1@1$5@1$6~0@3$2$1@1$5@1$6@2$a^8@2$4+h8^6@3$2$1@1$5@1$6^4@3$2$1@1$he@1$hf+1@3$2$1@2$h5N7^1@3$2$1@1$5@1$6Z@1$h1$1@2$3@2$e+h0^5@2$3@2$e@1$b@2$8$7^4^5@2$3@2$h8@2$4+h8^5@2$i2+2+i0@2$3@3$i1?5HCEIL^7@2$4+h8^5@2$3@1$ha@3$h3$0^7^2@2$3@4$hb?5HCEIL^a^7^4@2$3>0@2$h8Z^3@2$e@2$a@2$4+h8@2$a@1$b@2$8$7^5+1^4@2$4+h8^6@2$h4@1$9@1$f@1$c#8\4junk@1$9@1$f@1$c#8@4$h6$h7^b~0@3$2$1@2$h5@1$i4@2$4+h8@2$i3^6@1$b@2$8$7^5^1@1$h1$1").
  Proof.
    intros m a p B sz cap items chars temp V.
    unfold vs_at, vs_hdr, vs_top, vs_end, vs_begin, vs_n in V. cbn [vs_buf vs_cap vs_items vs_chars vs_temp] in V.
    ndestruct V as (H0 & HD & SZ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). subst sz.
    split; [reflexivity|]. repeat (split; [assumption|]). exact H8.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_as_CB : ltac2:(zQ "d0!jpe!jgc!kgb!kl3!jif!jq6!j4!jqd!klc!h9!jsa!lka!ll9>1m>0@1$4@1$1#k0@1$8@1$4@1$1#8>1A$9>2cs@1$6$0>0@4$2$3^3^2^1@4$2$3^4^3@3$5$0@2$a@1$c^2@1$b^2@1$7$0").
  Proof.
    intros m A cs [[W B] R]. split; [split|].
    - cbn. split; [apply cells_bytes_length; exact W| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
  Qed.

  Lemma ihdrs_app : ltac2:(zQ "60!j4!jgc!jl9!iv9!jif!lm7>2l1@1$0$3>2l2@1$0$3>3bs1@1$0@1$4@1$1#8>3bs2@1$0@1$4@1$1#8>0@2$2^4^2>0@2$2^4^2@2$2@3$5$3^6^5@3$5@1$4@1$1#8^4^3").
  Proof.
    induction l1 as [|it r IH]; intros l2 bs1 bs2 H1 H2; cbn in H1 |- *.
    - subst bs1. exact H2.
    - ndestruct H1 as (hb & rest & -> & L & Hh & Hr). exists hb, (rest ++ bs2). rewrite app_assoc.
      split; [reflexivity|]. split; [exact L|]. split; [exact Hh|]. apply IH; assumption.
  Qed.

  Lemma ideeps_app : ltac2:(zQ "50!itf!iv9!j4!lm7!inb>1m$4>2l1@1$2$1>2l2@1$2$1>0@3$0?5HCEIL^3^2>0@3$0?5HCEIL^4^2@3$0?5HCEIL^5@3$3$1^4^3").
  Proof.
    induction l1 as [|it r IH]; intros l2 H1 H2; cbn in H1 |- *; [exact H2|].
    destruct H1 as [D R]. split; [exact D| apply IH; assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_snoc : ltac2:(zQ "h70!iv9!jgc!jpe!jif!jq6!j4!jqd!jg3!jsa!kgb!kl3!lm7!klc!jl2!h9!itf!jl9!lmd!lna!jre!hnd!km5!kr2>1m>0@1$3@1$1#k0@1$c@1$3@1$1#8>1a$e>1l@1$5$0>2bs@1$5@1$3@1$1#8>2it$0>2hb@1$5@1$3@1$1#8>0@4$9$a^6^5@3$4$2@2$8@2$dNh8@2$7$0^4^3@1$6$2>0@2$h0^5^4>0@3$f?5HCEIL^8^6>0@4$9$a^9@2$h4^8@2$h5+h8@1$h6@2$7$0^7@3$4$2@2$8Nh8^4@1$6$2>0@2$h2^6^5>0@3$h1?5HCEIL^b^7@4$h3?5HCEIL^c^b@3$b$0^a@3$4$0^8@1$6$0").
  Proof.
    intros m a l bs it hb R Hh D R1 Hh1 D1. exists (bs ++ hb).
    split. { rewrite length_app. cbn [length]. replace (24 * (length l + 1))%nat with (24 * length l + 24)%nat by lia.
             apply rw_cells_CB_join; [exact R|]. replace (a + Z.of_nat (24 * length l)) with (a + 24 * Z.of_nat (length l)) by lia. exact R1. }
    split. { apply ihdrs_app; [exact Hh|]. cbn. exists hb, []. rewrite app_nil_r. pose proof R1 as [[W _] _]. cbn in W. destruct W as [L _].
             split; [reflexivity|]. split; [exact L|]. split; [exact Hh1| reflexivity]. }
    apply ideeps_app; [exact D|]. cbn. split; [exact D1| exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells : ltac2:(zQ "h30!jgc!jpe!jif!jq6!j4!jqd!nf!h9!jsa!kgb!kl3!la!lo6!klc!jr3!lp1!lp9!li9!kmb>1m>0@1$2@1$0#k0@1$d@1$2@1$0#8>1a$7>1k$7>3j15@1$4@1$2@1$0#8>0@4$9$a^4^3@3$3$1@1$h2@2$c@1$0#k0Z@3$3$1@1$h1@2$c@1$0#8^2@3$3$1@2$8Nf^1@1$5$1>0@2$6@2$bZ^3@2$b^3+4@2$e@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$6@4$9$a^7^6@3$3$1@2$8Nh8^1@1$5$1@2$h0@1$f^5^1").
  Proof.
    intros m a k j15 R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 15 j15]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists (firstn 7 j15), (skipn 7 j15).
    split; [rewrite firstn_length; lia|]. split; [rewrite skipn_length; lia|].
    cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells8 : ltac2:(zQ "h30!jgc!jpe!jif!jq6!j4!jqd!nf!h9!kmb!jsa!kgb!kl3!la!lo6!klc!jr3!lp1!lp9!li9>1m>0@1$2@1$0#k0@1$e@1$2@1$0#8>1a$7>1k$7>2j7@1$4@1$2@1$0#8>1w@1$2@1$0#k0>0@4$a$b^5^4@3$3$1@1$8@2$d@1$0#k0Z@3$3$1@1$h2@2$d@1$0#8^3@3$3$1@2$9N7^2@3$3$1@1$8^1@1$5$1>0@2$6@2$cZ^4@2$c^4+4@2$f@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$6@4$a$b^8^7@3$3$1@2$9Nh8^1@1$5$1@2$h1@1$h0^6^1").
  Proof.
    intros m a k j7 w R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 7 j7; C8 w]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists j7, (le8 w).
    split; [exact L|]. split; [apply length_le8|].
    cbn [cells_bytes cbytes]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells1 : ltac2:(zQ "h30!jgc!jpe!jif!jq6!j4!jsa!jqd!nf!h9!li9!kgb!kl3!la!lo6!klc!jr3!lp1!lp9!kmb>1m>0@1$2@1$0#k0@1$e@1$2@1$0#8>1a$8>1k$8>2j7@1$4@1$2@1$0#8>1b@1$2@1$0#8>3j7b@1$4@1$2@1$0#8>0@4$a$b^6^5@3$3$1@1$h2@2$d@1$0#k0Z@3$3$1@1$9@2$d@1$0#8^4@3$3$1@2$5N7^3@3$3$1@1$9^2@3$3$1@2$5N7^1@1$6$1>0@2$7@2$cZ^5@2$c^5+4@2$f@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$7@4$a$b^9^8@3$3$1@2$5Nh8^1@1$6$1@2$h1@1$h0^7^1").
  Proof.
    intros m a k j7 b j7b R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _ & Lb & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 7 j7; C1 b; CB 7 j7b]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists j7, (b :: j7b).
    split; [exact L|]. split; [cbn [length]; rewrite Lb; reflexivity|].
    cbn [cells_bytes cbytes]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ihdrs_app_inv : ltac2:(zQ "c0!j4!jgc!jif!iv9!nf!jl9!lm7!jg3!jjb!jr3!jj5!jl2>2l1@1$0$3>2l2@1$0$3>2bs@1$0@1$2@1$1#8>0@2$5@3$6$3^3^2^1@2$9@1$0@1$2@1$1#8\3bs1@1$0@1$2@1$1#8@2$9@1$0@1$2@1$1#8\3bs2@1$0@1$2@1$1#8@2$4@3$8@1$0@1$2@1$1#8^4@3$6@1$2@1$1#8^2^1@2$4@3$8$a@2$7@1$2@1$1#8^2@2$bNh8@2$7$3^6@2$4@2$5^6^2@2$5^5^1").
  Proof.
    induction l1 as [|it r IH]; intros l2 bs Hh; cbn in Hh.
    - exists [], bs. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity| exact Hh].
    - ndestruct Hh as (hb & rest & -> & L & Hi & Hr). destruct (IH _ _ Hr) as (bs1 & bs2 & -> & L1 & H1 & H2).
      exists (hb ++ bs1), bs2. rewrite app_assoc. split; [reflexivity|]. split; [rewrite length_app, L, L1; cbn [length]; lia|].
      split; [| exact H2]. cbn. exists hb, bs1. split; [reflexivity|]. split; [exact L|]. split; [exact Hi| exact H1].
  Qed.

  Lemma ideeps_app_inv : ltac2:(zQ "60!itf!iv9!j4!lm7!nf!inb>1m$5>2l1@1$2$1>2l2@1$2$1>0@3$0?5HCEIL^3@3$3$1^2^1@2$4@3$0?5HCEIL^4^3@3$0?5HCEIL^4^2").
  Proof.
    induction l1 as [|it r IH]; intros l2 D; cbn in D |- *; [split; [exact I| exact D]|].
    destruct D as [Di Dr]. destruct (IH _ Dr) as [D1 D2]. split; [split; [exact Di| exact D1]| exact D2].
  Qed.

  (* [comment removed for export] *)
  Lemma blocks_items_map : ltac2:(zQ "a0!is2!j4!hj7!jjb!lq1!lq7!iu9!ir6!iv9!lr0>2es@1$1$0@3$3@1$1$2@1$6@4$4$0$8$5^1@4$9$0$2$7^1").
  Proof. induction es as [|v r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma ideeps_map : ltac2:(zQ "a0!is2!j4!jr8!q1!lq1!lq7!itf!im8!iv9!inb>1m$9>2es@1$1$0@2$2@3$6?5HCEIL^2@4$4$0$8$5^1@3$3$0@2$7?5HCEIL^2^1").
  Proof.
    induction es as [|v r IH]; cbn.
    - split; [intros _; constructor| intros _; exact I].
    - split. { intros [D R]. constructor; [exact D| apply IH; exact R]. }
      intros F. split; [exact (Forall_inv F)| apply IH; exact (Forall_inv_tail F)].
  Qed.
  Lemma blocks_jvs_of_list : ltac2:(zQ "80!j4!is2!hj7!jjb!ipa!ir6!lrc!lr0>2es@1$0$1@3$3@1$0$2@1$4@1$6^1@4$7$1$2$5^1").
  Proof. induction es as [|v r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma vdeeps_of_list : ltac2:(zQ "80!is2!j4!jr8!q1!lrc!im8!in1!inb>1m$7>2es@1$1$0@2$2@3$6?5HCEIL^2@1$4^1@3$3$0@2$5?5HCEIL^2^1").
  Proof.
    induction es as [|v r IH]; cbn.
    - split; [intros _; constructor| intros _; exact I].
    - split. { intros [D R]. constructor; [exact D| apply IH; exact R]. }
      intros F. split; [exact (Forall_inv F)| apply IH; exact (Forall_inv_tail F)].
  Qed.
  Lemma jvs_height_of_list : ltac2:(zQ "80!is2!ltf!j4!jj5!q1!lu5!lv0!lrc>2es@1$2$0>1h$3>0@3$4$0\1v$0@2$1@1$5^1^2^2@2$1@1$6@1$7^3^2").
  Proof.
    induction es as [|v r IH]; intros h F; cbn; [lia|].
    pose proof (Forall_inv F) as F1. cbv beta in F1. pose proof (IH h (Forall_inv_tail F)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vs_at_xpres : ltac2:(zQ "d0!h9!hj7!j4!li0!inb!hn7!jb!hs0!io1!ih2!ioa!lve!mgb>2LB@1$2$1>2SP$0>1X@1$2@2$6$0$0>1m$4>2m'$4>1a$0>2st$c>0@5$8^7^6^5^4^3>0@1$9^6>0@1$a^9>0>1b$1>0@3$5$1^1@1$b^5@3$5$1^2^c>0@5$7^b^a^9^6+k0>0@4$3?5HCEIL^9^7^6@4$3?5HCEIL^9^8^7").
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
