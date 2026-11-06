(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface CXXRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AsCXXHeap AsObj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import AXpres.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prod46Stdlib6ZArith6BinInt1Zk22le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~lf6as_FSBhc3fsthc3snd37Corelib4Init5Logicr12orr13andlf8AFS_SIZE79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~tb2shk23add37Corelib5Lists7ListDefhi46Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hk58AIMG_TOPtb5aceillf5blocklfcablock_rangelf7afsb_oklf8blk_addrlf8blk_size36Stdlib5Lists4Listhsb2Ink22lttb6AHI_LOtb9ALOWSH_LOr12eqtb7AAPP_HItb3nshk26modulok23sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6CXXRep~~~~~~ii2dxclient_range89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA7BJKitVS3HCW~~~~~~imfdX_above_hceilimfcblocks_belowlf3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA5BJRep~~~~~~it86sdeepsit85vdeepit86vdeepsii25xpresit8ablocks_jvsit8ablocks_kvsit88blocks_vit82jvit83jvsit83kvsit85kdeepit86ideepsit8cblocks_itemsit86vsitemhc6length04Npos35stdpp9bitvectorbdefinitionsjr22bvhc3nat37Corelib4Init3Natjtb3mulit85ihdrs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jvd4cellhc4conshc3nilr12exr13iffhk55asegsit88items_atjvd2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kn48rw_cellshc6optionk23muljvd2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kt02wzk26of_natlf4bptrhc4pairhc4Somer13nottbbaddressableii2crblock_rangeit84mkVSit85vs_atjvd2C1kt02b8k23powk26to_natjvdbcells_bytesjvdacells_sizehc3appit89item_deepit88item_hdrjr27Z_to_bvit84Jscait84vhdrhi43mapit85VSvalhsb8flat_mapit8bjvs_of_list37Corelib4Init5Peanomg12leit87jheightit8ajvs_heightit89blocks_vsit86vstacklf3asr" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!mkb$0").

  (* [comment removed for export] *)
  Definition X_above_hceil : ltac2:(zQ "30!h9!j4!jb>1X@1$1@2$2$0$0P") := ltac2:(zQ "f0!h9!la!pc!q5!jb!qb!s5!sa!t0!hh9!hhe!j4!hjb!ho0!hoc\1X@1$b@2$4$0$0@3$c@2$4$0$0\2iv@2$4$0$0@2$6@2$1@1$e?5HCEIL@3$3$0$0^1@2$6@2$1@3$5$0$0^1$d@2$6@2$7@2$1@1$2?1H@3$3$0$0^1@2$1@3$5$0$0^1@2$a@1$2?1H$8@2$7@2$1@1$9@1$2?1H@3$3$0$0^1@2$1@3$5$0$0^1@1$9@2$a@1$2?1H$8^1").

  (* [comment removed for export] *)
  Definition blocks_below : ltac2:(zQ "20!j4!hp4>2LB@1$0$1P") := ltac2:(zQ "80!hp4!j4!sa!hpc!hqb!hr5!hs0!hte\2LB@1$1$0@2$2@2$4?5HCEIL?1H>1b$0>0@3$7$0^1^2@4$3?5HCEIL?1H@1$5^2@1$6^2").

  Lemma ablock_facts : ltac2:(zQ "h30!sa!hhe!la!hu4!h9!s5!pc!hu9!hv2!hh9!hve!ho0!t0!hpc!ig3!hoc!igd!ih3!ihc>1A$4>1n$4>0@4$d?5HCEIL?1H^2^1@2$0@2$3Z^3@2$0@3$a$4@2$h1^3+h0Z@2$0@2$2Z^2@2$0@2$2$b^3@2$0@2$2@2$1^3^2@1$f?5HCEIL@2$0@2$5@2$2@2$1@2$1^3^2+h0@1$6?1H@2$2@2$1@1$6?1H$c@2$h2^3+h0@2$0@2$3$8@1$9^3@2$0@2$3@2$1@1$9^3@1$h0^2$7@2$0@2$5@2$2@2$1^3^2$8@2$2$7^3@2$3@2$1^3^2$e").
  Proof.
    (intros A n nd_i1; ndestruct nd_i1 as (R1 & R2 & R3 & R4 & R5 & R6 & R7)). pose proof (aapp_bounds _ _ R7 R3) as (B1 & B2 & B3 & B4 & B5).
    npose (sh_aapp_range A n R7 R3) as (S1 & S2 & S3).
    repeat split; try assumption.
    - assert (E : sh AIMG_TOP = 2148379648) by reflexivity. unfold ALOWSH_LO. clear - S1 E. lia.
    - clear - S2 S3. lia.
    - unfold aapp, aapp_lo, aapp_hi in R7. clear - R7. lia.
  Qed.

  Lemma fsb_sh_band : ltac2:(zQ "a0!pc!sa!hh9!hu4!t0!hqb!hu9!hv2!hhe!la>0@2$5?5HCEIL?1H@2$1@2$3$7@1$2@1$0?1H@2$1@2$3@1$2@2$8@1$0?1H$4$6@2$9Z@1$0?1H").
  Proof.
    (intros nd_i2; ndestruct nd_i2 as (F1 & F2 & F3 & F4)). acb. split; [| split].
    - assert (E : sh AIMG_TOP = 2148379648) by reflexivity. pose proof (sh_mono AIMG_TOP (as_FSB H) F1). unfold ALOWSH_LO. clear - E H0. lia.
    - apply sh_below_app. unfold AFS_SIZE, AAPP_HI, AIMG_TOP in *. lia.
    - unfold AIMG_TOP in *. lia.
  Qed.

  Lemma xclient_range_block : ltac2:(zQ "c0!h9!hp4!j4!hr5!hhe!la!jb!hs0!ile!ir1!is2!hte>2LB@1$2$1>2SP$0>1X@1$2@2$6$0$0>1b$1>1A$0>1n$0>0@3$b$1^3^6>0@2$5@1$3^4^3>0@2$5@2$4^4^3@2$4@1$3^5@1$7^5>0@1$a^9>0@1$9^8@7$8?5HCEIL?1H^b^a^9^7^6").
  Proof.
    intros LB SP X b A n Hb H1 H2 [AF HB] HX. pose proof (ablock_facts _ _ (HB _ Hb)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
    npose (fsb_sh_band AF) as (L1 & L2 & L3). split.
    - right. right. left. exists b. split; [exact Hb| lia].
    - unfold X_above_hceil in HX. induction X as [|iv X IH]; [constructor|].
      constructor; [| apply IH; exact (Forall_inv_tail HX)]. pose proof (Forall_inv HX) as K. cbn in K |- *.
      clear IH HX. unfold AIMG_TOP, ALOWSH_LO, AHI_LO in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xclient_range_block_sh : ltac2:(zQ "c0!h9!hp4!j4!jb!hr5!hs0!igd!hh9!ile!ir1!is2!hte>2LB@1$2$1>2SP$0>1X@1$2@2$3$0$0>1b$1>0@3$b$1^1^4>0@1$a^5>0@1$9^4@7$8?5HCEIL?1H^7^6^5@1$7@1$4^4@1$6@1$5^4").
  Proof.
    intros LB SP X b Hb [AF HB] HX. pose proof (ablock_facts _ _ (HB _ Hb)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
    npose (fsb_sh_band AF) as (L1 & L2 & L3). pose proof (HB _ Hb) as AB. split.
    - right. right. right. left. exists b. split; [exact Hb| lia].
    - unfold X_above_hceil in HX. induction X as [|iv X IH]; [constructor|].
      constructor; [| apply IH; exact (Forall_inv_tail HX)]. pose proof (Forall_inv HX) as K. cbn in K |- *.
      acb. pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(unfold AAPP_HI in *; lia)) as SB.
      assert (SB2 : sh (blk_addr b) + nsh (blk_size b) <= sh (blk_addr b + blk_size b + 8)).
      { unfold sh, nsh. Z.div_mod_to_equations. lia. }
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 AB)))))) as GAP. cbn in GAP.
      assert (D4 : sh (blk_addr b) + nsh (blk_size b) <= sh (as_FSB H) \/ sh (as_FSB H + AFS_SIZE) <= sh (blk_addr b)).
      { destruct GAP as [G|G]; [left| right]; unfold sh, nsh; Z.div_mod_to_equations; lia. }
      ndestruct AF as (F1 & F2 & F3 & F4). unfold aapp, aapp_lo, aapp_hi in F4.
      clear IH HX HB AB Hb. unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AFS_SIZE in *. lia.
  Qed.

  Lemma vdeep_xpres_mut : ltac2:(zQ "h30!hp4!hte!h9!j4!sa!it2!jh4!jhe!ji7!jb!jj1!ir1!is2!jja!jk8!jl6!jm2!jm8!jmf>2LB@1$3$0>2SP$2>1X@1$3@2$9$2$2>1m$5>2m'$5>0@7$a?5HCEIL?1H^5^4^3^2^1>0@1$b^4>0@1$c^7@2$4>1v$h0>0@3$7?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$f^3@3$1$0^2^c@3$7?5HCEIL^7^3@2$4>1l$h1>0@3$8?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$d^3@3$1$0^2^c@3$8?5HCEIL^7^3>1l$h2>0@3$6?5HCEIL^6^1>0>1b$0>0@3$1$0^1@1$e^3@3$1$0^2^c@3$6?5HCEIL^7^3").
  Proof.
    intros LB SP X m m' HP HX HB.
    apply jv_mutind.
    - intros k _ _. exact I.
    - intros n _ _. exact I.
    - intros [[p T] sz] n D SUB. cbn in D |- *.
      ndestruct D as (cap & junk & E1 & E2 & E3 & BR & AD & TB). exists cap, junk.
      repeat (split; [assumption|]). split. { eapply xpres_addressable; [exact HP| exact AD|]. assert (INB : In (p, T, sz) LB) by (apply SUB; left; reflexivity). exact (xclient_range_block_sh LB SP X (p, T, sz) INB HB HX). }
      eapply xpres_rw_cells; [exact HP| exact TB|].
      eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | exact HB| exact HX].
      cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. unfold lstr_tbl_size in E1. lia.
    - intros [[[p T] sz]|] cap es IH D SUB; cbn in D |- *; [|exact I].
      ndestruct D as (ebs & junk & E1 & E2 & E3 & BR & AD & TB & HH & DD). exists ebs, junk.
      repeat (split; [assumption|]). split. { eapply xpres_addressable; [exact HP| exact AD|]. assert (INB : In (p, T, sz) LB) by (apply SUB; left; reflexivity). exact (xclient_range_block_sh LB SP X (p, T, sz) INB HB HX). }
      split; [| split; [exact HH| apply IH; [exact DD| intros b Hb; apply SUB; right; exact Hb]]].
      eapply xpres_rw_cells; [exact HP| exact TB|].
      eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | exact HB| exact HX].
      cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. unfold arr_tbl_size in E1. lia.
    - intros [[[p T] sz]|] cap ss IH D SUB; cbn in D |- *; [|exact I].
      ndestruct D as (salt & sbs & junk & jbk & E1 & E2 & E3 & BR & AD & TB & BK & HH & DD). nexists salt, sbs, junk, jbk.
      repeat (split; [assumption|]). split. { eapply xpres_addressable; [exact HP| exact AD|]. assert (INB : In (p, T, sz) LB) by (apply SUB; left; reflexivity). exact (xclient_range_block_sh LB SP X (p, T, sz) INB HB HX). }
      assert (SZ : 16 + 40 * cap <= sz /\ (BJ_SMALL_OBJ < cap -> 16 + 44 * cap <= sz)).
      { unfold obj_tbl_size, BJ_SMALL_OBJ in *. destruct (Z.leb_spec cap 18); lia. }
      split; [|split; [| split; [exact HH| apply IH; [exact DD| intros b Hb; apply SUB; right; exact Hb]]]].
      + eapply xpres_rw_cells; [exact HP| exact TB|].
        eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | exact HB| exact HX].
        cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
      + intros HC. eapply xpres_rw_cells; [exact HP| exact (BK HC)|].
        eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | exact HB| exact HX].
        cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. unfold BJ_SMALL_OBJ in *. lia.
    - intros _ _. exact I.
    - intros v IHv r IHr [Dv Dr] SUB. split; [apply IHv; [exact Dv|]| apply IHr; [exact Dr|]]; intros b Hb; apply SUB; cbn; apply in_app_iff; tauto.
    - intros _ _. exact I.
    - intros [[p K] ksz] v IHv r IHr D SUB. cbn in D |- *. ndestruct D as ((K1 & K2 & KA & kb & KB) & Dv & Dr).
      split; [| split; [apply IHv; [exact Dv|]| apply IHr; [exact Dr|]]].
      + split; [exact K1|]. split; [exact K2|]. split. { eapply xpres_addressable; [exact HP| exact KA|]. assert (INB : In (p, K, ksz) LB) by (apply SUB; left; reflexivity). exact (xclient_range_block_sh LB SP X (p, K, ksz) INB HB HX). } exists kb.
        eapply xpres_rw_cells; [exact HP| exact KB|].
        eapply xclient_range_block; [apply SUB; left; reflexivity| cbn; lia| | exact HB| exact HX].
        cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
      + intros b Hb. apply SUB. right. apply in_app_iff. left. exact Hb.
      + intros b Hb. apply SUB. right. apply in_app_iff. right. exact Hb.
  Qed.

  Lemma vdeep_xpres : ltac2:(zQ "c0!hp4!h9!j4!it2!jhe!hte!jb!jj1!ir1!is2!jl6!jm2>2LB@1$2$0>2SP$1>1X@1$2@2$6$1$1>1m$3>2m'$3>1v$b>0@7$7?5HCEIL?1H^6^5^4^3^2>0@1$8^5>0@1$9^8>0@3$4?5HCEIL^6^4>0>1b$0>0@3$5$0^1@1$a^6@3$5$0^2^c@3$4?5HCEIL^7^6").
  Proof. intros LB SP X m m' v HP HX HB. exact (proj1 (vdeep_xpres_mut LB SP X m m' HP HX HB) v). Qed.

  Lemma kdeep_xpres : ltac2:(zQ "a0!h9!hp4!j4!it2!jn6!jb!jj1!ir1!is2!hte>2LB@1$2$1>2SP$0>1X@1$2@2$5$0$0>1m$3>2m'$3>1b$1>0@7$6?5HCEIL?1H^6^5^4^3^2>0@1$7^5>0@1$8^8>0@3$4?5HCEIL^6^4>0@3$9$1^5^a@3$4?5HCEIL^7^6").
  Proof.
    (intros LB SP X m m' [[p K] ksz] HP HX HB nd_i3 Hin; ndestruct nd_i3 as (K1 & K2 & KA & kb & KB)). cbn.
    split; [exact K1|]. split; [exact K2|]. split. { eapply xpres_addressable; [exact HP| exact KA|]. exact (xclient_range_block_sh LB SP X (p, K, ksz) Hin HB HX). } exists kb.
    eapply xpres_rw_cells; [exact HP| exact KB|].
    eapply xclient_range_block; [exact Hin| cbn; lia| | exact HB| exact HX].
    cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
  Qed.

  Lemma ideeps_xpres : ltac2:(zQ "c0!hp4!j4!h9!it2!jnf!hte!jb!jj1!ir1!is2!jo9!jp9>2LB@1$1$0>2SP$2>1X@1$1@2$6$2$2>1m$3>2m'$3>1l@1$1$b>0@7$7?5HCEIL?1H^6^5^4^3^2>0@1$8^5>0@1$9^8>0@3$4?5HCEIL^6^4>0>1b$0>0@3$5$0^1@1$a^6@3$5$0^2^c@3$4?5HCEIL^7^6").
  Proof.
    intros LB SP X m m' l HP HX HB. induction l as [|it r IH]; intros D SUB; [exact I|].
    destruct D as [Di Dr]. split.
    - destruct it as [v|b]; cbn in Di |- *.
      + eapply vdeep_xpres; [exact HP| exact HX| exact HB| exact Di|]. intros b Hb. apply SUB. cbn. apply in_app_iff. left. exact Hb.
      + eapply kdeep_xpres; [exact HP| exact HX| exact HB| exact Di|]. apply SUB. cbn. left. reflexivity.
    - apply IH; [exact Dr|]. intros b Hb. apply SUB. cbn. apply in_app_iff. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma ihdrs_length : ltac2:(zQ "90!jq3!j4!jqc!jp9!jsf!jt5!hve!jud!jv4>1l@1$1$3>2bs@1$1@1$4@1$2#8>0@2$8^2^1@3$6$5@2$0@1$4@1$2#8^2@2$7Nh8@2$0$3^3").
  Proof.
    induction l as [|it r IH]; intros bs Hh; cbn in Hh.
    - subst bs. reflexivity.
    - ndestruct Hh as (hb & rest & -> & L & _ & Hr). rewrite length_app, L, (IH _ Hr). cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_raw : ltac2:(zQ "h60!jq3!j4!sa!jqc!jp9!jsf!jud!kj9!kk1!jt5!kk8!hve!kke!kl3!h9!kl9!it2!jnf!jv4!km2!kme!kqf>1m$h0>1a$e>1l@1$1$4@2$d@4$h3?5HCEIL^3^2^1@2$c@1$1@1$5@1$3#8\2bs@1$1@1$5@1$3#8@2$2@3$b$9@2$0@1$5@1$3#8^1@2$6Nh8@2$0$4^2@2$2@4$h5$f^4^3@3$8$7@2$h4@2$6Nh8@2$0$4^2^1@1$a$7@2$2@2$h2^2^1@3$h1?5HCEIL^4^2").
  Proof.
    intros m a l. split.
    - (intros nd_i4; ndestruct nd_i4 as (bs & R & Hh & D)). exists bs. split; [exact (ihdrs_length _ _ Hh)|]. split; [exact R|]. split; assumption.
    - (intros nd_i5; ndestruct nd_i5 as (bs & _ & R & Hh & D)). exists bs. split; [exact R|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_relocate : ltac2:(zQ "h81!jqc!h9!jsf!j4!hp4!kj9!jp9!kk1!jq3!kk8!krb!jud!kl9!kme!kqf!hte!jb!jj1!ir1!is2!jo9!jnf!jv4!km2&>0@1$2@1$0#k0@1$a@1$2@1$0#8>2LB@1$3$4>2SP$1>1X@1$3@2$h0$1$1>1m~0>2m'~0>1a$1>2a'$1>1l@1$3$6>2bs@1$3@1$2@1$0#8>0@4$e$c^6^4@3$7$5@2$d@2$bNh8@2$8$6^2^1@1$9$5>0@2$h6^3^2>0@3$h5?5HCEIL^8^4>0@4$e$c^8^6@3$7$5@2$d@2$bNh8@2$8$6^5^4@1$9$5>0@7$h1?5HCEIL?1H^d^c^b^a^9>0@1$h2^c>0@1$h3^f>0>1b$4>0@3$f$4^1@1$h4^a@3$f$4^2^h2@4$h7?5HCEIL^d^b^a").
  Proof.
    intros LB SP X m m' a a' l bs R Hh D R' HP HX HB SUB. exists bs. split; [exact R'|]. split; [exact Hh|].
    eapply ideeps_xpres; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma vs_at_some_intro : ltac2:(zQ "i40!kj9!h9!kk1!ks4!ksa!lgb!jp9!jq3!hhe!lh1!jqc!lha!la!jsf!j4!jb!kk8!li1!kl9!kme!kqf!hu4!li8!krb!hve!lif!lj5!lk3!km2!ll3!llb!lm4!lma!ln0!ihc!ln6>1m>0@1$d@1$a#k0@1$h7@1$d@1$a#8>1a$1>1p$b>1B$1>3cap$1>5items@1$e$6>5chars$1>4temp$1>5junk7@1$e@1$d@1$a#8>4junk@1$e@1$d@1$a#8>0@2$cZ^4>0@4$h4$h2^b^a@3$2$0@1$4@1$5Z@3$2$0@1$4@1$5^4@3$2$0@1$4@1$5^8@3$2$0@1$4@1$5@2$8^8@2$3+h8@1$9@2$7$6^6@3$2$0@1$4@1$5@2$8^8@2$3+h8^7@3$2$0@1$4@1$5^5@3$2$0@1$hf@1$i0+1@3$2$0@2$h3N7^3@3$2$0@1$4@1$5Z@1$h0$0>0@2$c+h0^8>0@2$c@1$9@2$7$6^8^9>0@2$h5@2$3+h8^a@2$i1+2+i0>0@3$hb?5HCEIL^c@2$3+h8^b>0@1$h9@3$h8$1^d^9>0@3$ha^h1^e@2$3+h8^d>0@4$hc?5HCEIL^h2^f^d>0>0@2$h5Z^d@2$c@2$8@2$3+h8@2$8@1$9@2$7$6^f+1^e@2$3+h8^h0>0@4$h4$h2^h4@2$8^h1@2$3+h8@1$9@2$7$6^f@3$2$0@2$h3@1$i3@2$3+h8@2$i2^h0@1$9@2$7$6^f^b@1$h0$0@4$he?5HCEIL^h5^h4@5$hd@2$h6@2$f@2$f$b$1$1@4$h1@2$f$b$1$1@4$h1$b$1^h3^h2@2$3+h8^h1^h1^h0^f^e").
  Proof.
    intros m a p B cap items chars temp junk7 junk H0 HD H1 H2 H3 H4 H5 HA H6 H7 H8.
    unfold vs_at, vs_hdr, vs_top, vs_end, vs_begin, vs_n. cbn [vs_buf vs_cap vs_items vs_chars vs_temp].
    split; [exact H0|]. split; [exists junk7; exact HD|].
    split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact HA|].
    split; [exact H6|]. split; [exact H7|]. exists junk. exact H8.
  Qed.

  Lemma vs_at_some_elim : ltac2:(zQ "i61!h9!kj9!sa!kk1!ks4!ksa!lgb!jp9!jq3!j4!hhe!lh1!jqc!lha!la!jsf!jb!kk8!li1!hve!kke!kl9!kme!kqf!hu4!li8!lif!it2!lj5!lk3!km2!ll3!llb!lm4!lma!ln0!ihc!ln6&@2$a^8@2$4+h8@1$b@2$8$7^5>1m$hb>1a$0>1p$d>1B$0>2sz$0>3cap$0>5items@1$9$7>5chars$0>4temp$0>0@4$i0?5HCEIL^9^8@5$hf@2$h9@2$h0@2$h0$d$0$0@4$h2@2$h0$d$0$0@4$h2$d$0^7^6^5^4^3^2^1@2$2@3$h3$0^6@2$4+h8^5@2$2@2$eZ^3@2$2@2$h4@1$9@1$f@1$c#8\5junk7@1$9@1$f@1$c#8@4$h7$h5^b^a@3$3$1@1$5@1$6Z@3$3$1@1$5@1$6^3@3$3$1@1$5@1$6^8@3$3$1@1$5@1$6~0@3$3$1@1$5@1$6@2$a^8@2$4+h8^6@3$3$1@1$5@1$6^4@3$3$1@1$i1@1$i2+1@3$3$1@2$h6N7^1@3$3$1@1$5@1$6Z@1$h1$1@2$2@2$e+h0^5@2$2@2$e@1$b@2$8$7^4^5@2$2@2$h8@2$4+h8^5@2$i3+2+i0@2$2@3$hd?5HCEIL^7@2$4+h8^5@2$2@1$ha@3$h3$0^7^2@2$2@3$hc^a^7@2$4+h8^5@2$2@4$he?5HCEIL^a^7^4@2$2>0@2$h8Z^3@2$e@2$a@2$4+h8@2$a@1$b@2$8$7^5+1^4@2$4+h8^6@2$h4@1$9@1$f@1$c#8\4junk@1$9@1$f@1$c#8@4$h7$h5^b~0@3$3$1@2$h6@1$i5@2$4+h8@2$i4^6@1$b@2$8$7^5^1@1$h1$1").
  Proof.
    intros m a p B sz cap items chars temp V.
    unfold vs_at, vs_hdr, vs_top, vs_end, vs_begin, vs_n in V. cbn [vs_buf vs_cap vs_items vs_chars vs_temp] in V.
    ndestruct V as (H0 & HD & SZ & H1 & H2 & H3 & H4 & H5 & HA & H6 & H7 & H8). subst sz.
    split; [reflexivity|]. repeat (split; [assumption|]). exact H8.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_as_CB : ltac2:(zQ "d0!kj9!jqc!kl9!kqf!jsf!kk1!j4!kk8!krb!h9!kme!lnf!loe>1m>0@1$4@1$1#k0@1$8@1$4@1$1#8>1A$9>2cs@1$6$0>0@4$3$2^3^2^1@4$3$2^4^3@3$5$0@2$a@1$c^2@1$b^2@1$7$0").
  Proof.
    intros m A cs [[W B] R]. split; [split|].
    - cbn. split; [apply cells_bytes_length; exact W| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
  Qed.

  Lemma ihdrs_app : ltac2:(zQ "60!j4!jqc!jv4!jp9!jsf!lpc>2l1@1$0$3>2l2@1$0$3>3bs1@1$0@1$4@1$1#8>3bs2@1$0@1$4@1$1#8>0@2$2^4^2>0@2$2^4^2@2$2@3$5$3^6^5@3$5@1$4@1$1#8^4^3").
  Proof.
    induction l1 as [|it r IH]; intros l2 bs1 bs2 H1 H2; cbn in H1 |- *.
    - subst bs1. exact H2.
    - ndestruct H1 as (hb & rest & -> & L & Hh & Hr). exists hb, (rest ++ bs2). rewrite app_assoc.
      split; [reflexivity|]. split; [exact L|]. split; [exact Hh|]. apply IH; assumption.
  Qed.

  Lemma ideeps_app : ltac2:(zQ "50!jnf!jp9!j4!lpc!it2>1m$4>2l1@1$2$1>2l2@1$2$1>0@3$0?5HCEIL^3^2>0@3$0?5HCEIL^4^2@3$0?5HCEIL^5@3$3$1^4^3").
  Proof.
    induction l1 as [|it r IH]; intros l2 H1 H2; cbn in H1 |- *; [exact H2|].
    destruct H1 as [D R]. split; [exact D| apply IH; assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma items_at_snoc : ltac2:(zQ "h70!jp9!jqc!kj9!jsf!kk1!j4!kk8!jq3!kl9!kme!kqf!lpc!krb!jud!h9!jnf!jv4!lq2!lqf!km2!hhe!ks4!lh1>1m>0@1$3@1$1#k0@1$c@1$3@1$1#8>1a$e>1l@1$5$0>2bs@1$5@1$3@1$1#8>2it$0>2hb@1$5@1$3@1$1#8>0@4$a$8^6^5@3$4$2@2$9@2$dNh8@2$7$0^4^3@1$6$2>0@2$h0^5^4>0@3$f?5HCEIL^8^6>0@4$a$8^9@2$h4^8@2$h5+h8@1$h6@2$7$0^7@3$4$2@2$9Nh8^4@1$6$2>0@2$h2^6^5>0@3$h1?5HCEIL^b^7@4$h3?5HCEIL^c^b@3$b$0^a@3$4$0^8@1$6$0").
  Proof.
    intros m a l bs it hb R Hh D R1 Hh1 D1. exists (bs ++ hb).
    split. { rewrite length_app. cbn [length]. replace (24 * (length l + 1))%nat with (24 * length l + 24)%nat by lia.
             apply rw_cells_CB_join; [exact R|]. replace (a + Z.of_nat (24 * length l)) with (a + 24 * Z.of_nat (length l)) by lia. exact R1. }
    split. { apply ihdrs_app; [exact Hh|]. cbn. exists hb, []. rewrite app_nil_r. pose proof R1 as [[W _] _]. cbn in W. destruct W as [L _].
             split; [reflexivity|]. split; [exact L|]. split; [exact Hh1| reflexivity]. }
    apply ideeps_app; [exact D|]. cbn. split; [exact D1| exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells : ltac2:(zQ "h30!jqc!kj9!jsf!kk1!j4!kk8!sa!h9!kl9!kme!kqf!la!lrb!krb!kke!ls6!lse!lm4!ksa>1m>0@1$2@1$0#k0@1$d@1$2@1$0#8>1a$7>1k$7>3j15@1$4@1$2@1$0#8>0@4$a$8^4^3@3$3$1@1$h2@2$c@1$0#k0Z@3$3$1@1$h1@2$c@1$0#8^2@3$3$1@2$9Nf^1@1$5$1>0@2$6@2$bZ^3@2$b^3+4@2$e@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$6@4$a$8^7^6@3$3$1@2$9Nh8^1@1$5$1@2$h0@1$f^5^1").
  Proof.
    intros m a k j15 R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 15 j15]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists (firstn 7 j15), (skipn 7 j15).
    split; [rewrite firstn_length; lia|]. split; [rewrite skipn_length; lia|].
    cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells8 : ltac2:(zQ "h30!jqc!kj9!jsf!kk1!j4!kk8!sa!h9!kl9!ksa!kme!kqf!la!lrb!krb!kke!ls6!lse!lm4>1m>0@1$2@1$0#k0@1$e@1$2@1$0#8>1a$7>1k$7>2j7@1$4@1$2@1$0#8>1w@1$2@1$0#k0>0@4$b$8^5^4@3$3$1@1$9@2$d@1$0#k0Z@3$3$1@1$h2@2$d@1$0#8^3@3$3$1@2$aN7^2@3$3$1@1$9^1@1$5$1>0@2$6@2$cZ^4@2$c^4+4@2$f@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$6@4$b$8^8^7@3$3$1@2$aNh8^1@1$5$1@2$h1@1$h0^6^1").
  Proof.
    intros m a k j7 w R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 7 j7; C8 w]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists j7, (le8 w).
    split; [exact L|]. split; [apply length_le8|].
    cbn [cells_bytes cbytes]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sca_hdr_of_cells1 : ltac2:(zQ "h30!jqc!kj9!jsf!kk1!j4!kme!kk8!sa!h9!kl9!lm4!kqf!la!lrb!krb!kke!ls6!lse!ksa>1m>0@1$2@1$0#k0@1$e@1$2@1$0#8>1a$8>1k$8>2j7@1$4@1$2@1$0#8>1b@1$2@1$0#8>3j7b@1$4@1$2@1$0#8>0@4$b$9^6^5@3$3$1@1$h2@2$d@1$0#k0Z@3$3$1@1$a@2$d@1$0#8^4@3$3$1@2$5N7^3@3$3$1@1$a^2@3$3$1@2$5N7^1@1$6$1>0@2$7@2$cZ^5@2$c^5+4@2$f@1$4@1$2@1$0#8\2hb@1$4@1$2@1$0#8@2$7@4$b$9^9^8@3$3$1@2$5Nh8^1@1$6$1@2$h1@1$h0^7^1").
  Proof.
    intros m a k j7 b j7b R K. pose proof R as [[W _] _]. cbn in W. ndestruct W as (_ & _ & L & _ & Lb & _).
    exists (cells_bytes [C8 (wz 0); C1 (b8 k); CB 7 j7; C1 b; CB 7 j7b]). split; [exact (rw_cells_as_CB _ _ _ R)|].
    cbn [vhdr]. split; [exact K|]. exists j7, (b :: j7b).
    split; [exact L|]. split; [cbn [length]; rewrite Lb; reflexivity|].
    cbn [cells_bytes cbytes]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ihdrs_app_inv : ltac2:(zQ "c0!j4!jqc!jsf!jp9!sa!jv4!lpc!jq3!hve!kke!jt5!jud>2l1@1$0$3>2l2@1$0$3>2bs@1$0@1$2@1$1#8>0@2$5@3$6$3^3^2^1@2$9@1$0@1$2@1$1#8\3bs1@1$0@1$2@1$1#8@2$9@1$0@1$2@1$1#8\3bs2@1$0@1$2@1$1#8@2$4@3$8@1$0@1$2@1$1#8^4@3$6@1$2@1$1#8^2^1@2$4@3$8$a@2$7@1$2@1$1#8^2@2$bNh8@2$7$3^6@2$4@2$5^6^2@2$5^5^1").
  Proof.
    induction l1 as [|it r IH]; intros l2 bs Hh; cbn in Hh.
    - exists [], bs. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity| exact Hh].
    - ndestruct Hh as (hb & rest & -> & L & Hi & Hr). destruct (IH _ _ Hr) as (bs1 & bs2 & -> & L1 & H1 & H2).
      exists (hb ++ bs1), bs2. rewrite app_assoc. split; [reflexivity|]. split; [rewrite length_app, L, L1; cbn [length]; lia|].
      split; [| exact H2]. cbn. exists hb, bs1. split; [reflexivity|]. split; [exact L|]. split; [exact Hi| exact H1].
  Qed.

  Lemma ideeps_app_inv : ltac2:(zQ "60!jnf!jp9!j4!lpc!sa!it2>1m$5>2l1@1$2$1>2l2@1$2$1>0@3$0?5HCEIL^3@3$3$1^2^1@2$4@3$0?5HCEIL^4^3@3$0?5HCEIL^4^2").
  Proof.
    induction l1 as [|it r IH]; intros l2 D; cbn in D |- *; [split; [exact I| exact D]|].
    destruct D as [Di Dr]. destruct (IH _ Dr) as [D1 D2]. split; [split; [exact Di| exact D1]| exact D2].
  Qed.

  (* [comment removed for export] *)
  Lemma blocks_items_map : ltac2:(zQ "a0!jm2!j4!hp4!hve!lt6!ltd!jo9!jl6!jp9!lu6>2es@1$1$0@3$3@1$1$2@1$6@4$4$0$8$5^1@4$9$0$2$7^1").
  Proof. induction es as [|v r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma ideeps_map : ltac2:(zQ "a0!jm2!j4!kl3!hjb!lt6!it2!ltd!jnf!jhe!jp9>1m$5>2es@1$1$0@2$2@3$7?5HCEIL^2@4$4$0$9$6^1@3$3$0@2$8?5HCEIL^2^1").
  Proof.
    induction es as [|v r IH]; cbn.
    - split; [intros _; constructor| intros _; exact I].
    - split. { intros [D R]. constructor; [exact D| apply IH; exact R]. }
      intros F. split; [exact (Forall_inv F)| apply IH; exact (Forall_inv_tail F)].
  Qed.
  Lemma blocks_jvs_of_list : ltac2:(zQ "80!j4!hp4!jm2!hve!jja!jl6!lv2!lu6>2es@1$0$2@3$3@1$0$1@1$4@1$6^1@4$7$2$1$5^1").
  Proof. induction es as [|v r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma vdeeps_of_list : ltac2:(zQ "80!jm2!j4!kl3!hjb!it2!lv2!jhe!ji7>1m$4>2es@1$1$0@2$2@3$7?5HCEIL^2@1$5^1@3$3$0@2$6?5HCEIL^2^1").
  Proof.
    induction es as [|v r IH]; cbn.
    - split; [intros _; constructor| intros _; exact I].
    - split. { intros [D R]. constructor; [exact D| apply IH; exact R]. }
      intros F. split; [exact (Forall_inv F)| apply IH; exact (Forall_inv_tail F)].
  Qed.
  Lemma jvs_height_of_list : ltac2:(zQ "80!jm2!mh5!j4!jt5!hjb!mhb!mi6!lv2>2es@1$2$0>1h$3>0@3$4$0\1v$0@2$1@1$5^1^2^2@2$1@1$6@1$7^3^2").
  Proof.
    induction es as [|v r IH]; intros h F; cbn; [lia|].
    pose proof (Forall_inv F) as F1. cbv beta in F1. pose proof (IH h (Forall_inv_tail F)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vs_at_xpres : ltac2:(zQ "d0!h9!hp4!j4!it2!llb!hte!jb!ile!jj1!ir1!is2!mj4!mk1>2LB@1$2$1>2SP$0>1X@1$2@2$6$0$0>1m$3>2m'$3>1a$0>2st$c>0@7$8?5HCEIL?1H^7^6^5^4^3>0@1$9^6>0@1$a^9>0>1b$1>0@3$5$1^1@1$b^5@3$5$1^2^c>0@7$7?5HCEIL?1H^b^a^9^6+k0>0@4$4?5HCEIL^9^7^6@4$4?5HCEIL^9^8^7").
  Proof.
    intros LB SP X m m' a st HP HX HB SUB HR V.
    destruct st as [buf cap items chars temp]. destruct buf as [[[p B] sz]|].
    - destruct (vs_at_some_elim _ _ _ _ _ _ _ _ _ V) as (SZ & C0 & (junk7 & HDR) & C16 & NLE & C32 & BR & BT & AD & ITEMS & ROOMI & (junk & JK)).
      subst sz.
      assert (INB : In (p, B, 24 * cap) LB) by (apply SUB; left; reflexivity).
      eapply vs_at_some_intro with (junk7 := junk7) (junk := junk); try assumption.
      + eapply xpres_rw_cells; [exact HP| exact HDR| exact HR].
      + eapply xpres_addressable; [exact HP| exact AD|]. exact (xclient_range_block_sh LB SP X (p, B, 24 * cap) INB HB HX).
      + apply items_at_raw in ITEMS. ndestruct ITEMS as (bs & L & R & Hh & D).
        eapply items_at_relocate; [exact R| exact Hh| exact D| | exact HP| exact HX| exact HB| ].
        * eapply xpres_rw_cells; [exact HP| exact R|].
          eapply xclient_range_block; [exact INB| cbn [blk_addr fst snd]; lia| | exact HB| exact HX].
          cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
        * intros b Hb. apply SUB. right. exact Hb.
      + eapply xpres_rw_cells; [exact HP| exact JK|].
        eapply xclient_range_block; [exact INB| cbn [blk_addr fst snd]; lia| | exact HB| exact HX].
        cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia.
    - unfold vs_at in V |- *. cbn [vs_buf vs_cap vs_items vs_chars vs_temp] in V |- *.
      ndestruct V as (C0 & (junk7 & HDR) & R3). split; [exact C0|]. split; [| exact R3].
      exists junk7. eapply xpres_rw_cells; [exact HP| exact HDR| exact HR].
  Qed.

End HCW.
