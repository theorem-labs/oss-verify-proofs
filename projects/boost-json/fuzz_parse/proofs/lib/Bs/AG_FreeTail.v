(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AW_Drain AW_Put3 AS_Free1 AS_Free2 AS_Free3 AS_Free4 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_Refill1 AG_Refill2 AG_Frame AG_MallocCold AG_MallocTop
     AG_FreeModel AG_FreeModel2 AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free9 AG_RepQ AG_RepQFacts AG_FreeMid SecLazy
     AG_WriteSet AG_RecycleDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hc4cell37Corelib4Init9Datatypeslf4cons69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~ne5as_tq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~s74a_sthc2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hh12wzne6qbatchne7qc_listlf4list37Corelib5Lists7ListDefhmc3mapne7qb_addrlf3nilne8qc_bytesne4zlen79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AG_RepQ~~~~~~hqc5AREPQ79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hv25asegss75OT_TQs75a_thrs73ast79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~ikc3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ip18rw_cells36Stdlib5Lists4Listit82hdit84last46Stdlib6ZArith6BinInt1Ziv93add3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjh8dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Statejm05Model04Npos37Corelib4Init5Logicjpd3and35stdpp9bitvectorbdefinitionsjr82bvjpd2exjpd2eqjr8bbv_unsignedlf6lengthne6effectiv92lene5as_gqne6astates74a_Zrlf4prod37Corelib4Init5Peanokid2lene6as_secnedkMaxCacheSizeneh2kQuarantineMaxSizenedsyscall_event79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AG_Free2~~~~~~ko69lb_removes74a_ALs73a_Ls73a_Ss75a_bots75a_ctxs75a_fsbs74a_pas74a_sbs75a_toplf4Nonelf3applf3natlf6optionjpd3not37Corelib4Init3Natlj53sub3h5LinuxProcessSemanticsfLinuxProcessSem3Runlke5mkCfgnecam_free_fullneakBatchSizene6qcachene6schunknebsyscalls_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AG_Frame~~~~~~lrf7amframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAG_FreeMid~~~~~~mg87ARHEAPQ79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsdAG_FreeModel2~~~~~~ml3bfree_tail_m89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAG_FreeTail3HCW~~~~~~mq59FREE_COST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAG_Malloc2~~~~~~mv7cdepot_placed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_MallocModel~~~~~~nk7fsame_but_shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAG_WriteSet~~~~~~npe6acomplnpe4avmx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAW_Enqueue1~~~~~~nv18enq_regs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AW_Put1~~~~~~oje9put_frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX~~~~~~oo87AMODELXoo88awin_visoo89depot_covoo8aflagsx_rep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~ov95DEPOT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7SecLazy~~~~~~pk2anonvm_same69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~pod8restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~pt84lzok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~qh96u64arrhc2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~qm23stkqm25wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~qqe2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~qv17mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~rj67seg_romiv96of_nativ93subjr87Z_to_bvit82Inlf4Somelf4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_RecycleDefs~~~~~~rr04aviss76ARHEAPqm23mkRqqe6ret_pc69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~sh66sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~sl9dhunspell_scfg99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAG_FreeTail3HCW9FreeTails~~~~~~sq1bfree_gpostXsq19free_midsnebch_user_begne7ch_used79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsdAW_MallocBase~~~~~~ti4aicpt_chain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsUnwind~~~~~~tn56utraceov95depot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsDepotHash~~~~~~ts6adepot_hashov95d_putikc5aceil" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition FREE_COST : Z := 0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tq_cells_of_arepq : ltac2:(zQ "h91!h9!l8!n7!rf!hg5!hgc!hkc!hl2!hlb!hm5!ho3!hoa!hp4!hpa!hq5!hu9!iid!ij6!ije!ik6!ioa!isc!iub!iv1!jh1&@4$a$7$0$b@1$8@1$3@1$4^5>1s$h3>2XC@1$9$0>2XB@1$9$0>1m$h4>0@5$f?5HCEIL^4^3^2^1@4$h5$h0^2@2$h8@1$h2^5$h1@3$2$1@1$5@1$6@2$e$7@1$8@1$3@1$4^5@3$2$1@1$5@1$6@3$h6$0Z~0@3$2$1@1$5@1$6@3$h7$0~0Z@3$2$1@1$5@1$6@1$d@1$3@1$4^5@1$c$1").
Proof. (intros s XC XB m nd_i1; ndestruct nd_i1 as (_ & _ & _ & _ & T & _)). ndestruct T as (_ & _ & _ & _ & _ & _ & TQ & _). exact TQ. Qed.

Section FreeTails.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk).

  Let st : ltac2:(zQ "10!kh6$0") := ltac2:(zQ "10!hg5@1$0?1s").
  Let TH : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!ije@1$0?1s").
  Let U : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!tgc@1$0?2ch").
  Let size : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!tha@1$0?2ch").
  Let CHI : ltac2:(zQ "30!h9!hm5!ki6@1$1@2$2$0$0") := ltac2:(zQ "40!jp7!ju7!tm7!lga@5$2@2$1@1$0#k0?2ra@2$1@1$0#k0?2s0@2$1@1$0#k0?2sp@1$3?1s?2CH").
  Let T : ltac2:(zQ "20!hm5!h9@1$0$1") := ltac2:(zQ "50!jp7!ku4!lga!tr3!ju7@6$3+pgsk0@2$4@1$0#k0?2sp@1$2?1s@1$1?1s+he?3CHI").
  Let nT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!jv6!h9!ro0@1$2@2$0$1?1T").
  Let d' : ltac2:(zQ "10!trd$0") := ltac2:(zQ "20!ug7!uh5@3$1?1d@1$0?1T?2nT").

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis LO : ltac2:(zQ "20!uhe!kg8@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!jp7!jh1!kg8!ju7@2$2@2$1?2lo+ro0@2$3@1$0#k0?2sp").
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis QSZ : size <= kQuarantineMaxSize.

  (* [comment removed for export] *)
  Definition free_mids : ltac2:(zQ "30!jkf!joe!ik6>2sm$2>4msF2$0>3mo2$1P") := ltac2:(zQ "l91!jp7!jr1!jt5!jtb!ju1!h9!l8!hm5!n7!iid!jh1!hgc!ju7!hg5!hp4!jv6!jvf!kg8!kge!hpa!isc!rf!kh6!khf!hkc!ki6!kk1!jkf!kk7!kl0!km0!hl2!kn6!ks4!kt1!kt8!kte!ku4!kuc!kv4!kvc!lg3!ije!lga!ioa!lh2!lh9!lhf!li5!lie!lk7!ho3!lna!joe!lo3!lp2!hlb!lpf!lq8!lr1!lvd!mk8!mp6!mua!nj7!nob!ntf!nu9!oj2!onb!ik6!os7!ot2!ote!oub!pj9!pnf!psc!qh1!ql3!qld!qpe!qq5!qub!rib!rn5!ro0!roa!rp1&@2$a@2$a@2$c@1$0#k0?2sp-ol0+h0\2sm$k6\4msF2$hb\3mo2$j5@2$3@1$2@1$0#k0\3t0'@1$2@1$0#k0@2$3@1$2@1$0#k0\3t1'@1$2@1$0#k0@2$3@1$2@1$0#k0\3t2'@1$2@1$0#k0@2$3@1$2@1$0#k0\3a1'@1$2@1$0#k0@2$3@1$2@1$0#k0\3a2'@1$2@1$0#k0@2$3@1$2@1$0#k0\3a3'@1$2@1$0#k0@2$3@1$2@1$0#k0\3a4'@1$2@1$0#k0@2$3@1$2@1$0#k0\3a5'@1$2@1$0#k0@2$3@1$2@1$0#k0\3a6'@1$2@1$0#k0@2$3@1$2@1$0#k0\3a7'@1$2@1$0#k0@2$3@1$2@1$0#k0\3t3'@1$2@1$0#k0@2$3@1$2@1$0#k0\3t4'@1$2@1$0#k0@2$3@1$2@1$0#k0\3t5'@1$2@1$0#k0@2$3@1$2@1$0#k0\3t6'@1$2@1$0#k0@2$3@1$7@1$2@1$0#8\2jk@1$7@1$2@1$0#8@2$3@1$7@1$2@1$0#k0\4rest@1$7@1$2@1$0#k0@2$3$ic\2m2$ic@2$1@3$4$5@1$ia^h4@1$ia?1s@2$1@3$4$5@1$i6^h4@1$i6?1s@2$1@3$4$5@1$i7^h4@1$i7?1s@2$1@3$4@1$7@2$h9@1$2@1$0#k0@1$2@1$0#k0@1$h7^h4@1$h7?1s@2$1@3$4$5@1$ib^h4@1$ib?1s@2$1@3$4$5@1$i5^h4@1$i5?1s@2$1@3$4$5@1$i9^h4@1$i9?1s@2$1@3$4$5@1$i8^h4@1$i8?1s@2$1@3$4@1$7$ja@1$hc@1$d^h4@1$hc?2st@2$1@3$4$j9@1$h2@1$d^h4@1$h2?2st@2$1@2$h1@2$l7@1$i2?1s$jf@1$i2^h4@2$1@1$j1@3$4@1$7$hf@1$j8@1$h5@1$d^h4@1$e$hf@2$1@2$1@2$h1Z@1$h3@1$h5@1$d^h4@2$h1@1$h3@1$h5@1$d^h4@2$a@2$a$hd$he$j7@2$1@2$1@2$h1Z@1$h3@1$h2@1$d^h4@2$h1@1$h3@1$h2@1$d^h4$he@2$1@5$ke$9@1$i3^h4@1$i4^h4@1$h7^h4@2$j4^h3^h2@2$1@3$4$hb@3$kd@1$i3^h4@1$i4^h4^h3@7$l3@ha$k4?2sp?2gp?2tp?2s7?2s8?2s9?3s10?3s11?1U?4size?2TH$hd^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4?1F@2$l8@1$0#k0+mtlp4?2fc@1$id@1$2@1$0#k0^1@1$l5$9@2$1@6$jd?5HCEIL^h4@1$e$5@1$e$5@2$i1?1U?2LB^1@2$1@2$k8^h4^1@2$1@1$ka^1@2$1@3$k7?5HCEIL^h4^h2@2$1@2$kc?2mo^h2@2$1@3$kb$9?2d'^1@2$1@3$k0?5HCEIL^h4?2d'@2$1@2$k9?2d'^h2@2$1@2$l4$9^1@2$1@4$l1$9^1?2lo@2$a@2$c@1$0#k0?2sp-oq0@2$1@4$h4$9^1@2$a@2$c@1$0#k0?2sp-oq0@4$k5?2sp?2s6?1U?2TH@2$1@4$h4$9^1@2$a@2$c@1$0#k0?2sp-ol0@3$8$6@1$b@1$h8~0@3$8$6@1$b@1$h8@1$l6@2$f$5?1T@1$e$6@2$1@4$kf$9^1~0@3$ie@1$2@1$0#k0@4$j3$5@1$2@1$0#k0$h8?1T^2@2$1@3$4$if@2$f@1$2@1$0#k0^2@2$j2Nvf@2$f$5?1T@2$1@2$1@2$haN1@2$f$5?1T@2$ha@2$f$5?1TNhe@2$1@4$h4$9^1@2$a@2$c@1$0#k0?2sp-k8@3$8$6@1$b?2sp@1$e$6@2$1@4$h4$9^1@2$a@2$c@1$0#k0?2sp-k0@3$8$6@2$l0N8^3@3$8$6@1$b?2s5@3$8$6@1$b?2s4@3$8$6@1$b?2s3@3$8$6@1$b?2s2@3$8$6@1$b?2s1@3$8$6@1$b?2s0@3$8$6@1$b?2ra@1$e$6@2$1@6$jc?5HCEIL?1s@2$i1?1U?2LB@2$c@1$0#k0?2sp?1m^1@2$1@3$l2$9?1m^1@2$1@7$k2?1s^h4?1d?2lo@2$c@1$0#k0?2sp?1m^1@2$1@4$k3?1s^h4?2mo^h2@2$3$h6\3stX$h6@2$3@1$7$h0\3ev0@1$7$h0@2$3@1$7$h0\3ev2@1$7$h0@2$1@3$4@1$j0@2$h9$h6@1$7$h0@2$j6?2st?1U@5$je?1U?4size^3^2^1@2$1@2$k1^3@1$d^h7@3$4@1$7$i0@1$jb^2@1$e$i0").

  (* [comment removed for export] *)
  Definition free_gpostX : ltac2:(zQ "20!jkf!joe>4msF'$0>3mo'$1P") := ltac2:(zQ "jc0!jp7!jt5!jr1!jtb!ju1!hm5!h9!kh6!jvf!iid!ki6!lq8!khf!hg5!ju7!jkf!kk7!ks4!kt1!kt8!kte!ku4!kuc!kv4!ije!lga!ik6!ioa!rpc!lh2!rq2!li5!rq9!lna!joe!lo3!lvd!mua!nj7!nob!rv4!ntf!nu9!rvc!os7!ot2!ote!oub!pj9!pnf!psc!qh1!sg5!qpe!qub!sgc!rib!rn5!kg8!roa\4msF'$f\3mo'$i2@2$3$ha\2s'$ha@2$3@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$3$hb\2m'$hb@2$2@3$4$6@1$h8^h1@1$h8?1s@2$2@3$4$6@1$h6^h1@1$h6?1s@2$2@3$4$6@1$h7^h1@1$h7?1s@2$2@3$4@1$5@2$a@1$1@1$0#k0@1$1@1$0#k0@1$c^h1@1$c?1s@2$2@3$4$6@1$h9^h1@1$h9?1s@2$2@3$4$6@1$h5^h1@1$h5?1s@2$2>2sc$b>0@3$hc$b^1@1$h0@1$d^h2@3$hc$b^2@1$h0@1$d?1s@2$2@2$ja@2$jb@1$h2?1s$i5@1$h2^h1@2$2@5$j3$9@1$h3^h1@1$h4^h1@1$c^h1@2$i1^h3^h2@2$2@3$4$f@3$j2@1$h3^h1@1$h4^h1^h3@7$j6@hf$j4?2ra?2sp?2gp?2tp^h0^f^e?2s0?2s1^d^c^b^a^9^8^7^6?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^5^4^3^2?1F@1$j7?2ra?2fc@1$hd@1$1@1$0#k0^1@1$j9$9@2$2@4$ib?5HCEIL^h1@2$h1?1U?2LB^1@2$2@2$id^h1^1@2$2@1$if^1@2$2@3$ic?5HCEIL^h1^h2@2$2@2$j1?2mo^h2@2$2@3$j0$9?2d'^1@2$2@3$i6?5HCEIL^h1?2d'@2$2@2$ie?2d'^h2@2$2@2$j8$9^1@2$2@4$j5$9^1?2lo@2$e@1$0#k0?2sp@2$2@6$i4?5HCEIL?1s@2$h1?1U?2LB@2$e@1$0#k0?2sp?1m^1@2$2@4$i8?1s^h1?1m^1@2$2@7$i9?1s^h1?1d?2lo@2$e@1$0#k0?2sp?1m^1@2$2@4$ia?1s^h1?2mo^h2@2$3$7\4st''$7@2$3@1$5$8\2ev@1$5$8@2$2@3$4@1$hf@2$a$7@1$5$8@2$i3?2st?1U@2$he@2$a$7@1$5$8@4$i0$7@1$5$8^2^1@2$i7^2@1$d^h3").

  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  (* [comment removed for export] *)
  Theorem free_tail0 : ltac2:(zQ "e0!jkf!lna!joe!iid!skf!sp0!rf!kl0!hpa!sv0!svf!hg5!ik6!kg8>2sm$c>4msF2$0>3mo2$2>0@3$a^3^2^1>0@2$d@1$8@1$6@1$b^4$7>0>4msF'$0>3mo'$2>0@2$9^2^1@4$4$3$5?1Q@2$1^3^2@4$4$3$5?1Q@2$1^5^4").
  Proof.
    intros sm msF2 mo2 MID LE K.
    ndestruct MID as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & jk & rest & m2 & Ethr & Ectx & Efsb & Ezr & Etop & Ebot & Esb & Epa & Esec & Egq & HAL & TNE & TQB & GQB & OK2 & VIS2 & HQ & AWV & FX & AMX & NVS & DEP & DPL & DCOV & MI2 & ST2 & PFR & ESO & TRB & LR & NR & TFB & F4 & AMF & WM & ACM & AVX & (stX & ev0 & ev2 & EM & SBS & SC0)).
    npose HQ as (RQ & ND & LBs).
    pose proof (tq_cells_of_arepq sm [] [] m2 RQ) as TQ. rewrite Ethr in TQ.
    pose proof (WFQ_consts _ _ _ (AREPQ_WFQ _ _ _ _ RQ)) as (CQmax & CQmin & CQc).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL2. npose PL2 as (_ & _ & _ & _ & _ & _ & T1 & T2 & T3 & _). rewrite Ethr in T2, T3.
    eapply (evt_sreach_lazy_at asegs (a_L sm) (a_S sm) (a_Zr sm) _ msF2 _ mo2 Q OK2 VIS2).
    assert (HI' : lo + 2496 <= bv_unsigned sp) by (clear - HI; lia).
    { eapply (@put_tail _ sp ra s0 s1 s2 s3 s4 s5 gp tp s6 s7 s8 s9 s10 s11 F fc lo T rest jk LO HI' LR NR).
      6: exact TQ.
      - constructor. unfold kPageSize in T2, T3. split; [exact T2| exact T3].   (* [comment removed for export] *)
      - unfold kMaxCacheSize. clear. lia.
      - clear - TQB LE. lia.
      - exact ST2.
      - exact PFR.
      - exact ESO.
      - exact TRB.
      - exact TFB.
      - exact F4. }
    cbv beta. intros msF' mo' OK' SBM _ PO.
    ndestruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & VIS' & ST').
    apply K. unfold free_gpostX. nexists sm, t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2.
    split; [exact Ethr|]. split; [exact Ectx|]. split; [exact Efsb|]. split; [exact Ezr|]. split; [exact Etop|]. split; [exact Ebot|].
    split; [intros sc Hsc; rewrite <- Esec; exact Hsc|]. split; [exact HAL|].
    split; [exact OK'|]. split; [exact VIS'|].
    split. { apply (ARHEAP_of_Q sm _ m2 HQ). split; [rewrite CQc; exact LE| rewrite CQmax; exact (proj2 GQB)]. }
    split; [exact AWV|]. split; [exact FX|]. split; [exact (AMODELX_mat sm mo2 mo' AMX SBM)|].
    split; [exact (nonvm_same_trans _ _ _ NVS (nonvm_same_mat mo2 mo' SBM))|].
    split; [exact DEP|]. split; [exact DPL|].
    split; [unfold depot_cov in DCOV |- *; intros x Hx; rewrite (same_but_materialized_vmmaps mo2 mo' SBM); exact (DCOV x Hx)|].
    split; [exact MI2|]. split; [exact ST'|]. split; [exact AMF|]. split; [exact (avis_of_wmono s sm m m2 WM)|].
    split; [exact ACM|]. split; [exact (avmx_mat_r s sm mo mo2 mo' AVX SBM)|].
    pose proof SBS as SBS0. unfold same_but_shadow in SBS0.
    ndestruct SBS0 as (_ & _ & _ & _ & _ & _ & _ & _ & Etq & _ & _ & _ & _ & _ & _ & Eqc).
    rewrite (free_tail_nodrain U size stX ev0 ev2) in EM by (rewrite Etq, Eqc, CQc; exact LE).
    eexists stX, _. split; [exact EM| exact SBS].
  Qed.
End FreeTails.
End HCW.
