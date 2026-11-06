(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Frame Arr CellsX TacX Image SysStep SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazySR LazyNodes SReach.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepX AsDepotInv AW_DepotFrame
     SecLazy SecLazy2 AG_MallocModel AG_Malloc2 AG_RepQ AG_WriteSet.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~jb6astate37Corelib4Init5Logico53andjbdclass_of_addrjbaclass_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~rc2sh46Stdlib6ZArith6BinInt1Zvf3addvf2levf2lto52exo52or36Stdlib5Lists4Listhj12Invf3div79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~hl03astjbasc_map_begjb6schunkjb6as_secjbbsc_map_sizehl04a_sto53notrc3mem04Npos35stdpp9bitvectorbdefinitionshtc2bvhc4Nonehc6optiono52eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsih45wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~il45asegs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_RecycleDefs3HCW~~~~~~ip87secgonehtcbbv_unsignedip84avis79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jg25wmonojg23ivlhc3fsthc3snd79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8SecLazy2~~~~~~jla9wmono_outjbbch_user_begjb5chunkjb7ch_usedjbaCAllocatedjb8ch_statejbachunk_listjb6cstaterc3nship8aalive_keptip85alivehl08agree_on79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAG_WriteSet~~~~~~khc5awritkhc6acomplkhc4avmx3h5LinuxProcessSemanticsfLinuxProcessSem5Statekn85Modelih4dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeks05bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~kuf5depothl04a_Zrjbaget_regionjbh1rg_allocated_userhl04a_ALhl03a_Lhl03a_Shl05a_bothl05a_ctxhl05a_fsbhl04a_pahl04a_sbhl05a_thrhl05a_tophc4boolhc4prodhc4true3h5LinuxProcessSemanticsfLinuxProcessSem3Runlsa5mkCfgjbfas_cache_inited79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAG_Malloc2~~~~~~mh1cdepot_placedip85pendz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AG_RepQ~~~~~~mma5AREPQ79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX~~~~~~mr07AMODELXmr08awin_vismr09depot_covmr0aflagsx_repkuf5DEPOT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7SecLazy~~~~~~niaanonvm_same69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~nn58restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~ns04lzokjg23mkRjg23stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ogf2MSogf6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~olc7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~oq17seg_rom" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition pendz : ltac2:(zQ "30!h9!j4!nc>2st$2>2XB@1$1$0>1a$0P") := ltac2:(zQ "e0!h9!p9!pf!qf!va!hh7!hhd!hi2!j4!hi7!hic!nc!hk4!hka\2st$b\2XB@1$8$0\1a$0@2$9$0\1x$0@2$1@3$c$0^1^3@2$a@2$1@2$6^1^2@2$7^2@2$5^1@1$3@2$2^4^1@2$1@2$6@1$4^1^2@2$7^2@2$5@1$4^1@2$d@1$3@2$2^4^1+8").


  (* [comment removed for export] *)
  Definition secgone : ltac2:(zQ "20!hoe!h9>1s$0>2s'$0>1a$1P") := ltac2:(zQ "h00!p9!hp5!hq2!hqb!hr4!hs2!hoe!va!hk4!hh7!hhd!hi2!hi7!hsa!hic!h9\1s$6\2s'$6\1a$f@2$c$2\2sc$2@2$0@3$8$2^1@1$3@1$5^4@2$0@1$d@3$8$2^1@1$3@1$5^3@2$e@2$0@2$a@1$1^1^2@2$b^2@2$9@1$1^1@1$4^1@2$0@2$a@1$7@1$1^1^2@2$b^2@1$7@2$9@1$1^1@1$4^1").
  Definition avis : ltac2:(zQ "20!hoe!ht0>1s$0>2s'$0>1m$1>2m'$1P") := ltac2:(zQ "d0!ht6!hv9!hvf!ig6!igf!hsa!ikb!iof!hoe!ht0!hic!iu0!iub\1s$8\2s'$8\1m$9\2m'$9>1x@1$1@1$0#k0>0@1$5@3$4@1$3@1$1@1$0#8@3$6$7^3^1@1$2@1$1@1$0#8@2$a@1$5@3$4@1$3@1$1@1$0#8@3$6$7^3^2@1$2@1$1@1$0#8@3$b^6^5@2$c@1$0#k0^2").

  Lemma avis_of_wmono : ltac2:(zQ "71!ht6!hv9!ig6!hoe!iva!iof!jje&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1s$3>2s'$3>1m~0>2m'~0>0@3$6$5^2^1@4$4^5^4^3^2").
  Proof. intros s s' m m' WM x V. left. exact (WM x V). Qed.
  Lemma avis_of_wmono_out : ltac2:(zQ "e0!h9!jk7!hoe!ht0!jke!j4!jl4!p9!iva!iu0!jp8!hk4!hhd!hi2>1s$2>2s'$2>1X@1$5$1>1m$3>2m'$3>0@3$a^3^2^1>0>2iv$1>1a$0>0@3$b$1^2^6>0@2$7@2$c@3$4$0$0^3^2@2$d^2@3$6$0$0^3@3$9^a^9^3@4$8^7^6^4^3").
  Proof.
    intros s s' X m m' WM SUB x V.
    assert (D : outside X (bv_unsigned x) \/ secgone s s' (bv_unsigned x)).
    { clear WM V. induction X as [|[lo' hi'] X IH]; [left; exact I|]. cbn.
      destruct (Z.lt_ge_cases (bv_unsigned x) lo') as [L|G]; [| destruct (Z.lt_ge_cases (bv_unsigned x) hi') as [L2|G2]].
      - destruct IH as [O|S]; [intros iv a Hiv Ha; apply (SUB iv a); [right; exact Hiv| exact Ha]| left; split; [lia| exact O]| right; exact S].
      - right. apply (SUB (lo', hi') (bv_unsigned x)); [left; reflexivity| cbn; lia].
      - destruct IH as [O|S]; [intros iv a Hiv Ha; apply (SUB iv a); [right; exact Hiv| exact Ha]| left; split; [lia| exact O]| right; exact S]. }
    destruct D as [O|S]; [left; exact (WM x O V)| right; exact S].
  Qed.

  (* [comment removed for export] *)
  Definition alive : ltac2:(zQ "20!h9!nc>2st$1>1a$0P") := ltac2:(zQ "h30!p9!jq5!jr3!jrb!va!hh7!hhd!hi2!igf!hi7!hic!h9!js5!nc!jt2!jtd!jua!jv3!hk4\2st$d\1a$b@2$9$2\2ch$2@2$0@3$h2$2^1@1$f^3@2$0@3$8$h0@1$e^1$c@2$a@2$0@2$6@1$1^1^2@2$7^2@2$5@1$1^1@1$3^1@2$0@2$6@1$4@1$1^1^2@2$7^2@2$5@1$4@1$1^1@1$h1@1$3^1").
  (* [comment removed for export] *)
  Definition alive_kept : ltac2:(zQ "10!nc>2st$0>3st'$0P") := ltac2:(zQ "80!jr3!nc!jtd!hk4!igf!js5!jt2!jua\2st$1\3st'$1>2ch$0>0@3$3$0^1@1$2^3>0@3$4$7@1$6^2$5@3$3$0^3@1$2^4").
  Lemma alive_kept_refl : ltac2:(zQ "20!nc!jv9>2st$0@2$1^1^1").
  Proof. intros st ch H _. exact H. Qed.
  Lemma alive_kept_trans : ltac2:(zQ "20!nc!jv9>1a$0>1b$0>1c$0>0@2$1^3^2>0@2$1^3^2@2$1^5^3").
  Proof. intros a b c A B ch H E. exact (B ch (A ch H E) E). Qed.
  Lemma alive_mono : ltac2:(zQ "40!nc!kg7!h9!jv9>2st$0>3st'$0>1a$2>0@2$3^3^2>0@2$1^4^2@2$1^4^3").
  Proof. (intros st st' a K nd_i2; ndestruct nd_i2 as (ch & H & E & R)). exists ch. split; [exact (K ch H E)|]. exact (conj E R). Qed.
  Lemma agree_alive_trans : ltac2:(zQ "50!kg7!kh0!ht0!nc!jv9>3st0$3>3st1$3>2m0$2>2m1$2>2m2$2>0@2$4^5^4>0@3$1@1$0^6^4^3>0@3$1@1$0^6^4^3@3$1@1$0^8^6^4").
  Proof. intros st0 st1 m0 m1 m2 K A B a Ha Hr. rewrite (B a (alive_mono _ _ a K Ha) Hr). exact (A a Ha Hr). Qed.

  (* [comment removed for export] *)
  Section Compose.
    Variables (s0 s1 s2 : ast) (d : depot) (lo SP : Z) (m0 m1 m2 : mem) (mo0 mo1 mo2 : Model).
    Hypothesis E1 : ltac2:(zQ "60!igf!h9!p9!lp3!lpb!lq3@2$2@3$0$1@1$5?2s1@1$5?2s0@2$2@3$0$1@1$4?2s1@1$4?2s0@3$0$1@1$3?2s1@1$3?2s0").
    Hypothesis SUB1 : ltac2:(zQ "40!hq2!hqb!hs2!hk4>2sc$0>0@3$3$0^1@1$1@1$2?2s1@3$3$0^2@1$1@1$2?2s0").
    Hypothesis SUB2 : ltac2:(zQ "40!hq2!hqb!hs2!hk4>2sc$0>0@3$3$0^1@1$1@1$2?2s2@3$3$0^2@1$1@1$2?2s1").

    Lemma awrit_01_02 : ltac2:(zQ "20!kld!h9>1a$1>0@6$0?2s0?2s1?1d?2lo?2SP^1@6$0?2s0?2s2?1d?2lo?2SP^2").
    Proof. intros a W. apply (awrit_mono s0 s1 s2 d lo SP a); [| exact W]. intros sc Hsc. right. exact (SUB1 sc Hsc). Qed.
    Lemma awrit_12_02 : ltac2:(zQ "20!kld!h9>1a$1>0@6$0?2s1?2s2?1d?2lo?2SP^1@6$0?2s0?2s2?1d?2lo?2SP^2").
    Proof.
      intros a W. ndestruct E1 as (Et & Es & Ep). unfold awrit in W |- *. rewrite Et, Es, Ep in W.
      destruct W as [H|[H|[H|[H|[H|[H|H]]]]]]; [tauto|tauto|tauto|tauto|tauto| |tauto].
      right; right; right; right; right; left. ndestruct H as (sc & I & R). exists sc. split; [| exact R].
      destruct I as [I|I]; [left; exact (SUB1 sc I)| right; exact I].
    Qed.
    Lemma acompl_trans : ltac2:(zQ "10!km6>0@7$0?2s0?2s1?1d?2lo?2SP?2m0?2m1>0@7$0?2s1?2s2?1d?2lo?2SP?2m1?2m2@7$0?2s0?2s2?1d?2lo?2SP?2m0?2m2").
    Proof.
      intros A B a Ha NW. rewrite (B a Ha) by (intros W; exact (NW (awrit_12_02 a W))). apply (A a Ha). intros W. exact (NW (awrit_01_02 a W)).
    Qed.
    Lemma secgone_01_02 : ltac2:(zQ "20!iu0!h9>1a$1>0@3$0?2s0?2s1^1@3$0?2s0?2s2^2").
    Proof. (intros a nd_i3; ndestruct nd_i3 as (sc & I & NI & R)). exists sc. split; [exact I|]. split; [intros I2; exact (NI (SUB2 sc I2))| exact R]. Qed.
    Lemma secgone_12_02 : ltac2:(zQ "20!iu0!h9>1a$1>0@3$0?2s1?2s2^1@3$0?2s0?2s2^2").
    Proof. (intros a nd_i4; ndestruct nd_i4 as (sc & I & NI & R)). exists sc. split; [exact (SUB1 sc I)|]. split; [exact NI| exact R]. Qed.
    Lemma avis_trans : ltac2:(zQ "10!iva>0@4$0?2s0?2s1?2m0?2m1>0@4$0?2s1?2s2?2m1?2m2@4$0?2s0?2s2?2m0?2m2").
    Proof.
      intros A B x V. destruct (A x V) as [V1|G]; [| right; exact (secgone_01_02 _ G)].
      destruct (B x V1) as [V2|G]; [left; exact V2| right; exact (secgone_12_02 _ G)].
    Qed.
    (* [comment removed for export] *)
    Lemma avmx_trans : ltac2:(zQ "10!kn0>0@4$0?2s0?2s1?3mo0?3mo1>0@4$0?2s1?2s2?3mo1?3mo2@4$0?2s0?2s2?3mo0?3mo2").
    Proof.
      intros A B x Hx. destruct (A x Hx) as [A1 A2]. split.
      - destruct A1 as [H1|(sc & I & NI & R)].
        + destruct (proj1 (B x H1)) as [H2|(sc & I & NI & R)]; [left; exact H2| right]. exists sc. split; [exact (SUB1 sc I)|]. split; [exact NI| exact R].
        + right. exists sc. split; [exact I|]. split; [| exact R]. intros I2. exact (NI (SUB2 sc I2)).
      - intros sc I2 NI. exact (False_ind _ (NI (SUB1 sc (SUB2 sc I2)))).
    Qed.
  End Compose.

  (* [comment removed for export] *)
  Definition rstep_post : ltac2:(zQ "b0!ht6!hv9!h9!j4!kq6!kqf!ku6!nc!hoe!lif!ht0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$8>1d$9>2lo$2>1m$a>2mo$4>3XC'@1$3$2>3XB'@1$3$2>2PZ@1$3$2>5MODEL>0$7P>4msF'$5>3mo'$4P") := ltac2:(zQ "jf0!ht6!hv9!p9!hi7!h9!igf!hs2!iof!j4!hq2!lj8!hoe!ht0!kqf!kq6!hqb!lk0!lkd!lm2!lma!ln1!ln8!lo1!loa!lp3!lpb!lq3!lqc!kh0!hk4!iub!hvf!lr5!lrc!ls3!lv6!ku6!lvf!nc!ml1!kg7!jv9!iva!mm1!mq7!km6!kn0!muf!mva!ng6!nh3!ni1!lif!nm7!nr4!nv9!og1!og8!okc!ol2!op6!ou0!hhd\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$i4@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$b\1d$j4\2lo$4\1m$c\2mo$e\3XC'@1$8$4\3XB'@1$8$4\2PZ@1$8$4\5MODEL>0$i6P\4msF'$d\3mo'$e@2$3$b\2s'$b@2$3@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$3$c\2m'$c@2$2@3$5$4@1$ha^h1@1$ha^hc@2$2@3$5$4@1$h6^h1@1$h6^hc@2$2@3$5$4@1$h7^h1@1$h7^hc@2$2@3$5@1$8@2$i1@1$1@1$0#k0@1$1@1$0#k0@1$a^h1@1$a^hc@2$2@3$5$4@1$hb^h1@1$hb^hc@2$2@3$5$4@1$h5^h1@1$h5^hc@2$2@3$5$4@1$h2^h1@1$h2^hc@2$2@3$5$4@1$h9^h1@1$h9^hc@2$2@3$5$4@1$h8^h1@1$h8^hc@2$2>2sc$9>0@3$hd$9^1@1$f@1$6^h2@3$hd$9^2@1$f@1$6^he@2$2@3$5$i0@1$i5@1$6^h1$i2@2$2>2c0$4>0@2$jeZ^1@3$5$4@1$h1@2$h0@1$6^h3^2@1$h1@2$h0@1$6^he^2@2$2@5$j7$7@1$h3^h1@1$h4^h1@1$a^h1@2$i3^h3^h2@2$2@3$5$d@3$j6@1$h3^h1@1$h4^h1^h3@7$ja@hf$j8^ie^id^ic^ib^h0^f^e^ia^i9^d^c^b^a^9^8^7^6^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^5^4^3^2^he@1$jb^ie^hd@1$hf@1$1@1$0#k0^1@1$jd$7@2$2@5$ic?5HCEIL^h1^h7^h6^1@2$2@2$j0^h1^1@2$2@1$j2^1@2$2@3$if?5HCEIL^h1^h2@2$2@2$j5^h8^h2@2$2@4$ie^hc^h1^h8^h2@2$2@2$j1^hb^h2@2$2@3$j3$7^hb^1@2$2@3$i7?5HCEIL^h1^hb@2$2@2$jc$7^1@2$2@4$j9$7^1^ha@2$he@1$0#k0^id@2$2@7$id^hc^h1^hb^ha@2$he@1$0#k0^id^h9^1@2$2@4$ia^hc^h1^h9^1@2$2@3$hc@2$ib@1$6^hc^h5^h9^1@2$2@2$i9@1$6^hc@1$6^h1@2$2@3$hc@1$i8@1$6^hc^h9^1@1^h4@1$6^h1").
End HCW.
(* [comment removed for export] *)
