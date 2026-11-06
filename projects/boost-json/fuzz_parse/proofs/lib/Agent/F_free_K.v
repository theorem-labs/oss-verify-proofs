(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z01N37Corelib4Init9Datatypeshf4bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~je9cell_readje7cellvaljeaget_shadowhf4andbhf3fsthf3snd37Corelib4Init5Logicr23andr22eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~t18ticks_okje5Knownje4aptrje6mstateje3wr846Stdlib6NArith6BinNat1Nhjc3eqb46Stdlib6ZArith6BinInt1Zhlb3eqbhlb2lehlb2lthf4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~hod5blockje4ghdrr22exhod8blk_slothlb3sub35stdpp7numbers1Nhva6eq_dec35stdpp7numbers1Zih56eq_dechf4prodje2IBhlb3addr22orhod8blk_addrje4concjecget_meta_rec25stdpp9countableimabN_countableimabZ_countableimaeprod_countable25stdpp9decidableiqbbprod_eq_dechf4Somehf6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_B~~~~~~itb5hostsitb9sstart_ofjeam_last_idxje8s_groups36Stdlib5Lists4Listjkf2In25stdpp4basejm86lookup25stdpp4gmapjne4gmapjnebgmap_lookupr23iffitb5is_gmitb9hdr_known79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8F_free_K~~~~~~jrd4PROT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth1MallocFacts_Bpres~~~~~~kg64KINVje4aaddje4wr16jrd6hdr_stje4metaje7s_areasje5s_ctxje7s_metasjeas_next_ridje9s_regionsjeas_reservedje7s_slotsje6s_tickje4areaje4mctxje6regionhf3orbr23notkg64ZINVitb4CINVje4cptrje6r_basehlb6modulo37Corelib5Lists7ListDeflha3map36Stdlib4Bool4Boollj87Is_truejm86filteriqbbIs_true_dec35stdppblist_basics4listlmeblist_filterhf4negbje8aptr_eqbhf4Nonehf4pairitb8ci_slotsitb9slot_freekg64LPREjebm_sizeclassje4optritb8ci_mptrskg63amcje3ctx" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_read_wr8 : ltac2:(zQ "h40!h9!hc!j7!nc!o8!p2!pf!q6!qc!s6!sc!hh3!hhe!hi6!hid!hj6!hl4!hn3!hna!ho0>2st$e>1p$d>1v$0>3rid$1>1o$0>0@1$b^5>0@2$9@2$h2Z^4@2$h3^4+hg0@3$a$4@2$3@2$5@3$f^6^5^7^4^3M2\0$2$4@2$6@2$h0^4@3$7$1$0^6@2$h1^3@3$8$1$0^6@1$c^5@2$3@2$5^7^4^3").
Proof. intros st p v rid o.
  intros TK Hv. destruct (N.eqb_spec rid (fst p)) as [->|NE]; cbn [andb].
  - destruct (Z.eqb_spec o (snd p)) as [->|NEo]; [apply cell_read_wr8_same; assumption| apply cell_read_wr8_other; exact NEo].
  - rewrite get_shadow_wr8_other by exact NE. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PROT : ltac2:(zQ "50!ho6!hc!h9!ht2!hid>2st$4>2LB@1$0$3>3rid$1>1o$2P") := ltac2:(zQ "i72!hc!h9!s6!htb!hu2!hi6!sc!hu7!hv3!qc!ht2!hna!igb!ii6!q6!ij0!ij7!ijc!ik3!ik8!il4!ilb!ho0!inb!ioa!ip9!irc!isb!ho6!it2!ji1!jia!jj7!hid!jk4!jm2!jn4!joa!jp2&@2$8@1$h3^1@2$h4^5@1$7^1&@2$h1@3$9$0$1@1$7^1~0\2st$i1\2LB@1$hc$a\3rid$0\1o$1@2$h2@2$4@2$f$0$1\1b@2$f$0$1@2$4$3\2gh$3@2$2@3$6@1$hd$3@6$i4@2$f$0$1$3@4$i5$5@4$ha$0$c$1$d@6$h9$0$c$h7$1$d$h8$3@4$i6$5@4$ha$0$c$1$d@6$h9$0$c$h7$1$d$h8$3^2@1$i2^6@2$hb$3^1@2$2@3$6$0@3$e$0$1^2^4@2$2@2$b@2$8@3$9$0$1^2$h0^3@2$h6^3@2$h1@3$9$0$1^2+c@2$h2@2$4$5\1b$5@2$4$5\1g$5@2$4$1\1i$1@2$2@3$he^7^3^2@2$2@3$6$0@3$e$0$1^3^5@2$2@2$2@2$bZ^1@2$b^1@1$i0@2$h5^7^2@3$6$1^4@2$8@2$hf@2$h5^7^2^1$h0@2$4$a\3blk$a@2$2@3$i3$a^1^4@2$2@3$6$0@3$e$0$1@1$7^1^3@2$2@2$b@2$8~1$h0^2@2$h6^2~1").

Section KSH.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : ltac2:(zQ "70!kq1!sc!hc!ktb!inb!joa!igb@3$1@4$5$2$6$4$3@1$0?3st'@1$0?2st").
Hypothesis EA : ltac2:(zQ "d0!hc!h9!kn8!igb!ii6!sc!hi6!ksd!inb!ioa!ip9!irc!joa@3$5@4$c$6@4$b$0$3$1$4@6$a$0$3$8$1$4$9$7@1$2?3st'@1$2?2st").
Hypothesis EG : ltac2:(zQ "d0!hc!h9!jk4!igb!ii6!sc!hi6!htb!inb!ioa!ip9!irc!joa@3$5@4$c$6@4$b$0$3$1$4@6$a$0$3$8$1$4$9$7@1$2?3st'@1$2?2st").
Hypothesis ESL : ltac2:(zQ "d0!h9!hc!hi6!kra!igb!ii6!ij0!sc!inb!ioa!ip9!irc!joa@3$7@4$c$2@4$b$1$4$0$5@6$a$1$4$8$0$5$9@2$6$2$0@1$3?3st'@1$3?2st").
Hypothesis EC : ltac2:(zQ "30!ko2!sc!kt4@3$1$2@1$0?3st'@1$0?2st").
Hypothesis EM : ltac2:(zQ "40!ilb!sc!hi6!kn1>1q$2@3$1$3@2$0?3st'^1@2$0?2st^1").
Hypothesis TK' : ltac2:(zQ "10!hh3@1$0?3st'").
Hypothesis SHP : ltac2:(zQ "70!nc!p2!sc!hc!h9!jve!o8>3rid$3>1o$4>0@4$5?2st?2LB^2^1@3$2$6@2$0@2$1?3st'^3^2@2$0@2$1?2st^3^2").

Lemma hosts_sh : ltac2:(zQ "30!ji1!hi6!jq1>1b$1>1q$1@2$2@3$0?3st'^2^1@3$0?2st^2^1").
Proof. intros b q. unfold hosts. rewrite EG. tauto. Qed.
Lemma is_gm_sh : ltac2:(zQ "30!jq7!jq1!hi6>1q$2@2$1@2$0?3st'^1@2$0?2st^1").
Proof. intros q. unfold is_gm. split; intros [b H]; exists b; apply hosts_sh; exact H. Qed.
Lemma conc_sh : ltac2:(zQ "40!il4!sc!h9!hi6>1q$3@3$1$2@2$0?3st'^1@2$0?2st^1").
Proof. intros q. unfold conc, get_region. rewrite ER. reflexivity. Qed.

Lemma hdr_known_sh : ltac2:(zQ "c0!hc!h9!jr0!hna!q6!ij0!qc!s6!sc!jve!hi6!hv3>1p@2$5$0$1>2b1$a>2i1$1>3rid$0>0@3$8$0@3$4$0$1^4^1>0>1k$1>0@2$7@2$3+1^1@2$3^1+3@4$9?2st?2LB^4@2$b@3$6$0$1^7^2>0@4$2?2st^6^5^4@4$2?3st'^7^6^5").
Proof. intros p b1 i1 rid.
  (intros <- HP nd_i1; ndestruct nd_i1 as (v3 & lo & hi & H3 & I3 & H2 & H1 & E)). nexists v3, lo, hi.
  rewrite !SHP by (apply HP; lia). auto 10.
Qed.

Lemma KINV_shadow : ltac2:(zQ "20!kl1!h9>1c$1>0@3$0?2st?2LB^1@3$0?3st'?2LB^2").
Proof. intros c.
  intros K. pose proof (ki_gmetas _ _ _ K) as CG. pose proof (ki_slts _ _ _ K) as CS.
  assert (GMO : forall b g, hosts st b g -> gmeta_ok st' g b).
  { intros b g HB. pose proof (CG b g HB) as GO. constructor; rewrite ?EM, ?ER, ?ESL; try (destruct GO; assumption).
    - unfold meta_slot. rewrite EA. exact (go_slot _ _ _ GO).
    - intros ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
      nexists g1, i1, b1. rewrite ?EM. split; [exact SL|]. split; [apply hosts_sh; exact HB1|]. split; [exact FB|]. split; [exact EQB|].
      split; [exact I1|]. split; [exact NF1|]. split; [exact LT|].
      eapply hdr_known_sh; [reflexivity| | exact HK].
      intros k Hk. left. destruct HB as [ai Hai]. exists b, (mkGhdr (Some g) ai). split; [exact Hai|]. split; [reflexivity|]. unfold IB. lia. }
  constructor.
  - apply (links_ext st st' EA); [intros q; rewrite EM; auto| exact (ki_links _ _ _ K)].
  - apply (heads_lx st st' EG); [intros q; rewrite EM; auto| intros sc; unfold active, ctx; rewrite EC; reflexivity| unfold ctx; rewrite EC; reflexivity| intros q _; rewrite EM; auto| exact (ki_heads _ _ _ K)].
  - apply (homog_lx st st' EG); [intros q; rewrite EM; auto| intros q _; rewrite EM; auto| exact (ki_links _ _ _ K)| exact (ki_hom _ _ _ K)].
  - intros b g HB. apply GMO. apply hosts_sh. exact HB.
  - intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. rewrite EM. auto.
  - intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_sh; assumption.
  - intros s g i Hs. rewrite ESL in Hs. rewrite EM. ndestruct (CS s g i Hs) as (GM & E & I). split; [apply is_gm_sh; exact GM| auto].
  - intros b g i HB Hi. rewrite ESL, EM. apply hosts_sh in HB. rewrite EM in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
  - intros b gh o Hb Ho. rewrite EG in Hb. rewrite SHP; [exact (ki_unk _ _ _ K b gh o Hb Ho)|].
    left. exists b, gh. split; [exact Hb|]. split; [reflexivity|]. unfold IB. lia.
  - intros g b i HB Hi. apply hosts_sh in HB. rewrite EM in Hi |- *. rewrite SHP; [exact (ki_h0 _ _ _ K g b i HB Hi)|].
    right; left. nexists b, g, i. auto.
  - apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
    assert (Hin' : In blk LB) by (first [exact Hin | apply (proj1 (list_elem_of_In _ _)); exact Hin]).
    constructor; [| rewrite EG; exact NG| exact SZ].
    nexists g, i, b. rewrite ESL, EM, conc_sh. split; [exact SL|]. split; [apply hosts_sh; exact HB|]. split; [exact FB|]. split; [exact I|]. split; [exact NFR|].
    exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split.
    + rewrite SHP; [exact OK|]. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|]. rewrite OA. unfold UNIT, IB in *. lia.
    + eapply hdr_known_sh; [reflexivity| | exact HK]. intros k Hk. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|].
      cbn [aadd snd]. rewrite OA. unfold UNIT, IB in *. lia.
  - exact (ki_nodup _ _ _ K).
  - pose proof (ki_cx _ _ _ K) as X. unfold kctx, bounces, unmap_seq, ctx in *. rewrite EC. exact X.
  - intros sc Hsc. unfold usage, ctx. rewrite EC. exact (ki_usage _ _ _ K sc Hsc).
  - intros rid off Hb. unfold ctx in Hb. rewrite EC in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
  - exact TK'.
Qed.
End KSH.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hdr_st : ltac2:(zQ "20!hid!hi6>2st$0>2pf$1$0") := ltac2:(zQ "50!kl9!hi6!hid!km0!hj6\2st$2\2pf$1@3$3@2$0^1-2Z@3$4@2$0^1-3+vf^2").

Lemma hdr_st_tables : ltac2:(zQ "hf0!hc!h9!sc!km7!s6!igb!ii6!hi6!inb!joa!ioa!ip9!irc!ij0!ilb!kn1!kn8!ko2!jk4!koa!kp4!kq1!kqd!kra!ks4!ho6!ksd!htb!kt4!hid!ktb>2st$hd>2pf$7@2$4@3$2@4$9$0$5$8$he@1$h5@2$3^2^1@1$h5^2@2$4@3$2@4$9$7@4$c$0$5$1$6@6$b$0$5$8$1$6$a$ha@1$h0@2$3^2^1@1$h0^2@2$4@3$2@4$9$7@4$c$0$5$1$6@6$b$0$5$8$1$6$a$hb@1$h2@2$3^2^1@1$h2^2@2$4@3$2@4$9$7@4$c$0$5$1$6@6$b$0$5$8$1$6$a@2$d$7$1@1$h7@2$3^2^1@1$h7^2@2$4@3$2@1$h9@2$d$1$1@1$h6@2$3^2^1@1$h6^2@2$4@3$2$hc@1$h1@2$3^2^1@1$h1^2@2$4@3$2$0@1$h8@2$3^2^1@1$h8^2@2$4>1q$7@3$2$f@2$e@2$3^3^2^1@2$e^3^1@2$4@3$2@4$9$7@4$c$0$5$1$6@6$b$0$5$8$1$6$a$f@1$h3@2$3^2^1@1$h3^2@3$2$0@1$h4@2$3^2^1@1$h4^2").
Proof. intros st pf. repeat split; reflexivity. Qed.

Lemma ticks_ok_hdr_st : ltac2:(zQ "40!hh3!km7!hi6!hid>2st$3>2pf$2>0@1$0^2@1$0@2$1^3^2").
Proof. intros st pf. intros TK. unfold hdr_st, wr16. repeat apply ticks_ok_wr8. exact TK. Qed.

Lemma hdr_st_cell_read : ltac2:(zQ "h30!h9!hc!j7!qc!hn3!hv3!ku4!nc!o8!p2!pf!q6!sc!km7!hh3!hhe!hi6!hid!hl4>2st$h1>2pf$h0>3rid$1>1o$0>0@1$e^4@3$c$8@2$7@2$9@2$d^5^4^3^2M2\0$2$8@2$a@2$h2^3@3$b$1$0^4@2$6@2$6@2$4^2@2$5@3$3$1$0^4+1@2$4^2@2$5@3$3$1$0^4+2@2$4^2@2$5@3$3$1$0^4+3@1$fM2\0$2$0@2$4^2@2$5@3$3$1$0^4+3+vfZ@2$7@2$9^5^3^2").
Proof. intros st pf rid o.
  intros TK. unfold hdr_st, wr16. change (Z.shiftr 0 8) with 0.
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 255 rid o) by (first [exact TK | lia]).
  cbn [aadd fst snd].
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf + -2 + 1)); destruct (Z.eqb_spec o (snd pf - 1)); try lia;
  destruct (Z.eqb_spec o (snd pf + -2)); destruct (Z.eqb_spec o (snd pf - 2)); try lia;
  destruct (Z.eqb_spec o (snd pf + -3)); destruct (Z.eqb_spec o (snd pf - 3)); try lia; cbn [orb]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_cell_read_other : ltac2:(zQ "h10!hc!h9!qc!sc!ik3!nc!p2!q6!ij0!kua!km7!hh3!o8!hid!hna!ho0!hv3>2st$d>2pf@2$8$0$1>3rid$0>1o$1>0@1$b^4>0@2$4@1$9@3$3$0^3@3$7$0$1^4@2$4@2$f^2@2$h0@3$2$0$1^4+3@2$e@3$2$0$1^4^2@3$3$c@2$5@2$6@2$a^6^5^4^3@2$5@2$6^6^4^3").
Proof. intros st pf rid o.
  intros TK H. rewrite hdr_st_cell_read by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf - 1)); [lia|]. destruct (Z.eqb_spec o (snd pf - 2)); [lia|]. destruct (Z.eqb_spec o (snd pf - 3)); [lia|].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_known_back : ltac2:(zQ "h10!h9!hc!sc!hhe!nc!o8!p2!hu2!hna!q6!ij0!qc!s6!km7!hh3!hid!hv3>2st$f>2pf@2$a$1$0>3rid$1>1o$0>1v$0>0@1$e^5>0>1k$0>0@2$c@2$8+1^1@2$8^1+3@2$7$0\1w$0@3$2$5@2$4@2$6^9@3$9$1$0^8@2$h0@3$b$1$0^8^3@1$3^1>0@3$2$5@2$4@2$6@2$d^7^6^5^4@1$3^3@2$7$0\1w$0@3$2$5@2$4@2$6^9^7^6@1$3^1").
Proof. intros st pf rid o v.
  intros TK HK H. rewrite hdr_st_cell_read in H by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb] in H; [| exists v; exact H].
  destruct (Z.eqb_spec o (snd pf - 1)); [subst; apply (HK 1); lia|].
  destruct (Z.eqb_spec o (snd pf - 2)); [subst; apply (HK 2); lia|].
  destruct (Z.eqb_spec o (snd pf - 3)); [subst; apply (HK 3); lia|].
  cbn [orb] in H. exists v; exact H.
Qed.

Lemma ZINV_hdr_st : ltac2:(zQ "50!kv0!hi6!ho6!km7!hid>2st$4>2pf$1>2Zs@1$2$1>0@2$0^3^1@2$0@2$3^4^3^2").
Proof. intros st pf Zs. apply ZINV_ext; reflexivity. Qed.

(* [comment removed for export] *)
Lemma KINV_hdr_st : ltac2:(zQ "he0!hc!h9!ht2!ktb!sc!q6!hu7!jm2!ho6!qc!kl1!inb!igb!isb!it2!s6!kua!km7!ik8!kv8!hi6!lg0!hid!lg7!kq1!ijc!lh0!jn4!joa!jp2>2st$h6>2LB@1$8$2>3LB'@1$8$2>1c$1>2pf$h4>3blk$2>1r$3>0@2$h3^7^6>0@3$7$2^3^7>0@3$a^9^7^6>0>2b'$2>0@3$7$2^1^9@2$f@3$7$2^2^b@1$h0@3$4$h5@1$6^2@1$6^7>0@3$4$0@3$5$0$1^7@3$5$0$1@1$6^6>0@3$4@1$e$3@6$hb$0$3@4$hc$0$c$b$3@4$hd$0$c$b$3@3$5$0$1^8@1$h8^c@2$d$3^6>0@3$4$1@2$h9@1$h7^7@3$9$0$1^9@1$h2^8>0@3$4$1@2$ha@3$9$0$1^a+h0Z@3$a@2$h1^f^b^d^c").
Proof. intros st LB LB' c pf blk r.
  intros C Hin K HLB Hfst Hr Hpo PM.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin)) as SZ.
  destruct BC as [(r0 & Hr0 & Kr0 & A16 & AEND & AL & UNK) HD BB].
  rewrite <- Hfst, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  ndestruct (hdr_st_tables st pf) as (ER & EA & EG & ESL & ERS & EC & ET & EM & _).
  apply (KINV_shadow st (hdr_st st pf) LB' ER EA EG ESL EC EM (ticks_ok_hdr_st st pf TK)); [| exact K].
  intros rid o HP. apply hdr_st_cell_read_other; [exact TK|].
  destruct (N.eq_dec rid (fst pf)) as [->|NE]; [right| left; exact NE].
  pose proof (ki_gmetas _ _ _ K) as CG.
  destruct HP as [HP|[HP|HP]].
  - ndestruct HP as (b & gh & Hb & Fb & Ho).
    specialize (HD b gh Hb ltac:(rewrite Fb, Hfst; reflexivity)).
    rewrite (conc_region' st b r) in HD by (rewrite Fb; exact Hr). unfold IB in *. lia.
  - ndestruct HP as (b & g & i & HB & Fb & Hi & ->).
    pose proof (CG b g HB) as GO. destruct (go_region _ _ _ GO) as (rb & Hrb & _ & B0 & B16 & _). pose proof (go_stride _ _ _ GO) as [S16 SM].
    pose proof (go_mem _ _ _ GO) as MEM. unfold sstart_of. rewrite MEM. cbn [default id].
    assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
    { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
    set (si := get_stride (get_meta_rec st g) * i) in *. clearbody si.
    unfold UNIT, IB in *. Z.div_mod_to_equations. lia.
  - ndestruct HP as (blk' & Hin' & Fb' & Ho). destruct (HLB blk' Hin') as [HinL NEs].
    specialize (BB blk' HinL NEs ltac:(rewrite Fb', Hfst; reflexivity)).
    pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as BC'.
    pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL)) as SZ'.
    destruct BC' as [(r1 & Hr1 & _ & A16' & _ & _ & _) _ _]. rewrite Fb', Hr in Hr1. assert (r1 = r) by congruence. subst r1.
    rewrite (conc_region' st (blk_slot blk') r) in Ho by (rewrite Fb'; exact Hr).
    unfold IB in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_filter_iff {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) x :
  In x (filter P l) <-> In x l /\ P x.
Proof.
  rewrite <- list_elem_of_In, list_elem_of_filter.
  pose proof (list_elem_of_In l x) as E. tauto.
Qed.

Lemma NoDup_list_filter {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) :
  List.NoDup l -> List.NoDup (filter P l).
Proof.
  induction l as [|x l IH]; intros ND; [constructor|].
  rewrite filter_cons. inversion ND; subst. destruct (decide (P x)); [| apply IH; assumption].
  constructor; [| apply IH; assumption]. intros Hin. apply In_filter_iff in Hin. tauto.
Qed.

Lemma map_filter_slot : ltac2:(zQ "c0!ht2!lg0!ho6!hu7!hi6!lj1!lka!ll5!llf!lo6!j7!sc>1f>0$4$a>2LB@1$2$0@3$b@1$2$1@4$5$0$1$3@6$7$0@1$2$0@1$9$0\1b$0@1$6@1^3@1$3^1\1x$0@1$8@1^3@1$3^1^1@6$7$4@1$2$1@1$9$1\1x$4@1$6@1^3^1\1x$4@1$8@1^3^1@4$5$0$1$3^1").
Proof. intros f LB.
  induction LB as [|b LB IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
  destruct (decide (f (blk_slot b))); cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma KINV_filter_slot : ltac2:(zQ "c0!ht2!ho6!hu7!kl1!j7!h9!hi6!hid!lka!ll5!llf!lo6>2st$7>2LB@1$1$0>1c$5>1f>0$6$4>0@3$3^4^3^2@3$3^5@6$9$0@1$1$0@1$b$0\1b$0@1$8@1^3@1$2^1\1x$0@1$a@1^3@1$2^1^4^3").
Proof. intros st LB c f.
  intros K. pose proof (ki_blks _ _ _ K) as BL. pose proof (ki_nodup _ _ _ K) as ND. destruct K; constructor; auto.
  - apply List.Forall_forall. intros blk Hin. apply In_filter_iff in Hin. destruct Hin as [Hin _].
    exact (proj1 (List.Forall_forall _ _) BL blk Hin).
  - rewrite map_filter_slot. apply NoDup_list_filter. exact ND.
Qed.

Lemma LPRE_intro : ltac2:(zQ "i80!h9!hi6!hc!igb!ii6!ht2!hu7!ij0!htb!inb!ioa!ip9!irc!ho6!lp5!it2!sc!lpc!lg0!ilb!jn4!joa!jp2!lq7!isb!lqe!kua!lr5!ji1!ls1!lse!lt6!hid!jk4!kra!lka!hna!ll5!llf!lo6>2st$i0>2LB@1$d$5>1c$0>1g$1>1p$1>1i$0>3blk$5>0@1$hb^7>0@3$hc^8^4^5>0@3$h0@1$f@2$7$1$0@6$h4$h2@2$7$1$0@4$h5$1@4$c$2$3$0$4@6$b$2$3$9$0$4$a@2$7$1$0@4$h6$1@4$c$2$3$0$4@6$b$2$3$9$0$4$a@2$7$1$0@1$6^3@1$i2^9@2$h8@2$7$1$0@4$h9$1$0^6^4>0@1$ha@2$hd@2$h3^a^7^5>0@3$h0@1$f$8@6$h4$h2$8@4$h5$1@4$c$2$3$0$4@6$b$2$3$9$0$4$a$8@4$h6$1@4$c$2$3$0$4@6$b$2$3$9$0$4$a$8@1$6^5@1$i1^b@1$h7$8>0@2$i4^a@1$hf@2$h3^c^9@6$he^d@6$i5$5@1$d$5@1$i7$5\1b$5@1$i3@1$e@2$h1@1$6^1@1$6^8\1x$5@1$i6@1$e@2$h1@1$6^1@1$6^8^c^b^a^9^8").
Proof. intros st LB c g p i blk.
  intros CS HB SL NF NG HC. destruct (CS _ _ _ SL) as (GM & E & I).
  constructor; auto.
  - rewrite <- E. exact NG.
  - apply List.Forall_forall. intros b' Hin. apply In_filter_iff in Hin. destruct Hin as [_ Hb'].
    rewrite <- E. intros EQ. rewrite EQ, aptr_eqb_refl in Hb'. exact Hb'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.
End DROP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ci_mptrs_frame : ltac2:(zQ "h50!ij0!h9!lu4!sc!hc!igb!lub!lv7!lve!hid!kn8!kq1!inb!joa!ii6!hi6!ksd!ktb!ioa!ip9!irc>2st$9>3st2$9>0@1$6^2>0@3$3@2$0@2$0@2$0@2$0@2$0@2$0@2$0@2$0$2$2$2$2$1$1$1$1$1@1$7@1$8^2@1$7@1$8^3>0@3$3@4$d$f@4$h4$4$5$1$e@6$h3$4$5$c$1$e$h2$h0@1$a^3@1$a^4>0@3$3@4$d$4$5$c$h1@1$b^4@1$b^5@1$6^5").
Proof. intros st st2.
  (intros nd_i2 EC EA ER; ndestruct nd_i2 as (M1 & M2 & M3 & M4 & M5)).
  assert (NG : forall p, ng_ptr st p -> ng_ptr st2 p) by (intros [q|]; cbn; [rewrite ER|]; auto).
  unfold amc in EC. inversion EC.
  unfold ci_mptrs. rewrite H0, H1, H2, H3, EA. repeat split; auto. intros a ar Ha. apply NG. exact (M5 a ar Ha).
Qed.
