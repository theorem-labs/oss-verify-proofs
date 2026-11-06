(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~05block08lb_bytes37Corelib4Init9Datatypeske4conske4list37Corelib4Init5Logicn42eq37Corelib7Numbers7BinNumsod1Z08blk_size46Stdlib6ZArith6BinInt1Zr43addke4prodke4pair06fframe09lf_remove3h5LinuxProcessSemanticsfLinuxProcessSem3Runv36config05as_SR3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshifdmachine_statev35mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehnf5Model08as_AKREL06as_VIS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hs85asegs08as_MPRES05as_St79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~ihd3evt0h3alloc_ok_of_classes0aalloc_room08as_RHEAP0bas_alloc_ok03mem0bRHEAP_frame0h1RHEAP_block_range0h5RHEAP_blocks_disjoint0h2RHEAP_blocks_nodup0bRHEAP_shvis0brauxv_frame0elb_remove_laws09RFS_frame09RFS_range0cRFS_disjoint09RFS_nodup09RFS_shvis0h1frame_release_lawke3niln43notn42or08as_chain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~jne5aceilr42ler46modulo0bmalloc_stmt0aopnew_stmt0aopdel_stmt0aAFREE_STUB0h1free_null_stmt_at0h3stack_malloc_1_stmt0h3stack_malloc_4_stmt0h2set_shadow_f5_stmt0h0asan_memcpy_stmt0h0asan_memset_stmt0h1asan_memmove_stmt0h3stack_malloc_0_stmt0h3stack_malloc_2_stmt0h3stack_malloc_3_stmt0h0memcmp_icpt_stmt0caclient_addr36Stdlib5Lists4Listkv62Inn43and0daclient_ranger42ltod4Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~lj08bytes_at35stdpp9bitvectorbdefinitionsln62bvke6length05apresr46of_natlj05wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lrb8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~mg24cellmg2acells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~ml45u8arr04bptrjne3nshjne2shjne4SHADjnebaddressable06as_RFSke6optionke3fstke3snd37Corelib5Lists7ListDefmte6Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mvf3ivlmvf5munchmvf5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsConst~~~~~~nl49aconst_ok08AFS_SIZE0h0aclient_write_ok0cafs_write_ok06as_FSB07ff_addr03fsz0caframe_range07afsb_ok08ff_class07ff_flagn42ex89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsCXXHeap2HH~~~~~~ogebfresh_frameoge5fsobjhs88AIMG_TOP07AFS_HDR09AFS_FLAGSjne4aapp04fshnjne7AAPP_HImvfddisjoint_fromogeafs_scratch0aathr_cells03asr0casan_rt_hyps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lb_bytes_cons : ltac2:(zQ "80!jd!k4!m6!md!o8!q6!qa!sc>1b$0>2LB@1$3$0@3$4$5@1$1@3$2$0^2^1@2$7@1$6^2@1$1^1").
Proof. reflexivity. Qed.

Lemma lf_remove_head : ltac2:(zQ "80!q6!t2!md!t9!m6!o8!u0!u8>1k$0>2ff$0>2fp$0>2LF@1$2@2$1@2$1$0$0$0@3$5@1$2$6@2$7^3@3$4@2$1@2$1$0$0$0@4$3@2$1$0$0$0@4$3$0$0^4^3^2^1^1").
Proof. intros. cbn. rewrite Z.eqb_refl. reflexivity. Qed.

Section HH.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!osc$0").
  Hypothesis HH : ltac2:(zQ "10!ot1@2$0?5HCEIL?1H").

  Local Ltac hh := pose proof HH as (Lsr & Lakrel & Lmpres & Lalloc & Lcost
                                     & Lrf & Lbr & Lbd & Lnd & Lbsv & Lfsb & Lthr & Laux & Llbr
                                     & Lff & Lfe & Lfr & Lfd & Lfn & Lfsv & Lrel
                                     & Lch & Ltr
                                     & Lmalloc & Lopnew & Lfree & Lopdel & Lopdel2 & Lnull0 & Lnull1 & Lnull2
                                     & Lfs1 & Lfs4 & Lsetf5
                                     & Lmc & Lms & Lmm
                                     & Lperm & LopdelA & LnullA & Lfs0 & Lfs2 & Lfs3 & Lset00 & Lsetf8 & Lmcmp).

  (* [comment removed for export] *)
  Lemma ah_done : ltac2:(zQ "20!hhf!hi8>1Q>0$0P>1c$0>0@1^2^1@3$1?1H^3^2").
  Proof. hh. exact (proj1 Lsr). Qed.
  Lemma ah_mono : ltac2:(zQ "20!hhf!hi8>1Q>0$0P>2Q'>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@1^5^2@3$1?1H^4^3").
  Proof. hh. exact (proj1 (proj2 Lsr)). Qed.
  Lemma ah_seq : ltac2:(zQ "20!hhf!hi8>2Q1>0$0P>2Q2>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@3$1?1H^5^2@3$1?1H^4^3").
  Proof. hh. exact (proj1 (proj2 (proj2 Lsr))). Qed.
  Lemma ah_lift : ltac2:(zQ "c0!hm6!hn7!hqd!hr6!hi8!hs0!o8!hhf!ig3!igc!ih6!il8>1P>0$0P>1Q>0$7P>1s@1$a?1H>3msF$0>2ms$0>2mo$2>0@3$3?1H^4@2$1^3^1>0@3$6$0@3$5?1H^5^4^3>0@3$b$8^8^4>0>4msF'$0>3mo'$2>0@3$3?1H^9@2$1^2^1>0@3$9?1H^7^2>0@1^d@3$5?1H^b^4@3$4?1H^d@2$1^5^4@3$4?1H^9@2$1^7^5").
  Proof. hh. exact (proj2 (proj2 (proj2 Lsr))). Qed.
  Lemma ah_mpres_refl : ltac2:(zQ "20!hqd!igc>2mo$0@3$1?1H^1^1").
  Proof. hh. exact (proj1 Lmpres). Qed.
  Lemma ah_mpres_trans : ltac2:(zQ "20!hqd!igc>3mo1$0>3mo2$0>3mo3$0>0@3$1?1H^3^2>0@3$1?1H^3^2@3$1?1H^5^3").
  Proof. hh. exact (proj2 Lmpres). Qed.
  (* [comment removed for export] *)
  Lemma ah_alloc : ltac2:(zQ "10!ilf@1$0?1H"). Proof. hh. exact Lalloc. Qed.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma alloc_room_ok : ltac2:(zQ "80!md!q6!in5!io1!ih6!iob!jd!ip8>1s@1$4?1H>2LB@1$0$6>1m$7>1n$1>0@4$3?1H^4^3^2>0@3$2?1H^4^2@4$5?1H^6^5^3").
  Proof. (intros s LB m n RH nd_i1; ndestruct nd_i1 as (R1 & R2 & R3 & R4)). eapply ah_alloc; eauto. Qed.
  Lemma ah_costs : cost_laws H. Proof. hh. exact Lcost. Qed.
  Lemma ah_RHEAP_frame : ltac2:(zQ "10!ipd@2$0?5HCEIL?1H"). Proof. hh. exact Lrf. Qed.
  Lemma ah_blocks : ltac2:(zQ "10!iqa@2$0?5HCEIL?1H"). Proof. hh. exact Lbr. Qed.
  Lemma ah_disj : ltac2:(zQ "10!ire@1$0?1H"). Proof. hh. exact Lbd. Qed.
  Lemma ah_nodup : ltac2:(zQ "10!it6@1$0?1H"). Proof. hh. exact Lnd. Qed.
  Lemma ah_blk_shvis : ltac2:(zQ "10!iub@1$0?1H"). Proof. hh. exact Lbsv. Qed.
  Lemma ah_fsb : RHEAP_fsb H. Proof. hh. exact Lfsb. Qed.
  Lemma ah_thr : RHEAP_thr H. Proof. hh. exact Lthr. Qed.
  Lemma ah_rauxv_frame : ltac2:(zQ "10!iv8@2$0?5HCEIL?1H"). Proof. hh. exact Laux. Qed.
  Lemma ah_lb_remove : ltac2:(zQ "10!jg5@1$0?1H"). Proof. hh. exact Llbr. Qed.
  (* [comment removed for export] *)
  Lemma ah_RFS_frame : ltac2:(zQ "10!jh5@1$0?1H"). Proof. hh. exact Lff. Qed.
  Lemma ah_RFS_ext : RFS_ext H. Proof. hh. exact Lfe. Qed.
  Lemma ah_RFS_range : ltac2:(zQ "10!ji0@2$0?5HCEIL?1H"). Proof. hh. exact Lfr. Qed.
  Lemma ah_RFS_disj : ltac2:(zQ "10!jib@1$0?1H"). Proof. hh. exact Lfd. Qed.
  Lemma ah_RFS_nodup : ltac2:(zQ "10!jj9@1$0?1H"). Proof. hh. exact Lfn. Qed.
  Lemma ah_frm_shvis : ltac2:(zQ "10!jk4@1$0?1H"). Proof. hh. exact Lfsv. Qed.
  Lemma ah_release : ltac2:(zQ "10!jkf@1$0?1H"). Proof. hh. exact Lrel. Qed.
  (* [comment removed for export] *)
  Lemma ah_chain_nil : ltac2:(zQ "b0!q6!jm3!t2!o8!jm9!jmf!jn4!ip8!jrc!js5!jsa>1m$7>3cur$0>0@2$5@2$9^1@1$8?5HCEIL@1$4@3$3$0@2$a^1+8Z@4$6?1H^3^2@1$1@2$2$0$0").
  Proof. hh. exact (proj1 Lch). Qed.
  (* [comment removed for export] *)
  Lemma ah_malloc : ltac2:(zQ "10!jt3@2$0?5HCEIL?1H"). Proof. hh. exact Lmalloc. Qed.
  Lemma ah_opnew : ltac2:(zQ "10!ju0@2$0?5HCEIL?1H"). Proof. hh. exact Lopnew. Qed.
  Lemma ah_free : free_stmt H. Proof. hh. exact Lfree. Qed.
  Lemma ah_opdel : ltac2:(zQ "10!juc@2$0?5HCEIL?1H"). Proof. hh. exact Lopdel. Qed.
  Lemma ah_free_null : ltac2:(zQ "20!jv8!kg4@3$1?5HCEIL?1H$0"). Proof. hh. exact Lnull0. Qed.
  Lemma ah_fs1 : ltac2:(zQ "10!kh8@2$0?5HCEIL?1H"). Proof. hh. exact Lfs1. Qed.
  Lemma ah_fs4 : ltac2:(zQ "10!kie@2$0?5HCEIL?1H"). Proof. hh. exact Lfs4. Qed.
  Lemma ah_setf5 : ltac2:(zQ "10!kk4$0"). Proof. hh. exact Lsetf5. Qed.
  Lemma ah_memcpy : ltac2:(zQ "10!kl9@1$0?5HCEIL"). Proof. hh. exact Lmc. Qed.
  Lemma ah_memset : ltac2:(zQ "10!kmc@1$0?5HCEIL"). Proof. hh. exact Lms. Qed.
  Lemma ah_memmove : ltac2:(zQ "10!knf@1$0?5HCEIL"). Proof. hh. exact Lmm. Qed.
  (* [comment removed for export] *)
  Lemma ah_perm : RHEAP_perm H. Proof. hh. exact Lperm. Qed.
  Lemma ah_fs0 : ltac2:(zQ "10!kp3@2$0?5HCEIL?1H"). Proof. hh. exact Lfs0. Qed.
  Lemma ah_fs2 : ltac2:(zQ "10!kq9@2$0?5HCEIL?1H"). Proof. hh. exact Lfs2. Qed.
  Lemma ah_fs3 : ltac2:(zQ "10!krf@2$0?5HCEIL?1H"). Proof. hh. exact Lfs3. Qed.
  Lemma ah_memcmp : ltac2:(zQ "10!kt5@1$0?5HCEIL"). Proof. hh. exact Lmcmp. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ahh_evt : ltac2:(zQ "c0!hm6!hn7!hqd!hr6!hs0!o8!hhf!ig3!igc!hi8!ih6!il8>1P>0$0P>1Q>0$6P>1s@1$a?1H>3msF$0>2ms$0>2mo$2>0@3$3?1H^4@2$1^3^1>0@3$5$0@3$4?1H^5^4^3>0@3$b$7^8^4>0>4msF'$0>3mo'$2>0@3$3?1H^9@2$1^2^1>0@3$8?1H^7^2>0@1^d@3$4?1H^b^4@1^d@2$1^5^4@3$9?1H^9@2$1^7^5").
  Proof.
    intros P Q s msF ms mo K V E W. eapply ah_lift; [exact K| exact V| exact E|].
    intros msF' mo' K' MP HP. apply ah_done. apply W; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ahh_evt_then : ltac2:(zQ "c0!hm6!hn7!hqd!hr6!hi8!hs0!o8!hhf!ig3!igc!ih6!il8>1P>0$0P>1Q>0$7P>1s@1$a?1H>3msF$0>2ms$0>2mo$2>0@3$3?1H^4@2$1^3^1>0@3$6$0@3$5?1H^5^4^3>0@3$b$8^8^4>0>4msF'$0>3mo'$2>0@3$3?1H^9@2$1^2^1>0@3$9?1H^7^2>0@1^d@3$5?1H^b^4@3$4?1H^d@2$1^5^4@3$4?1H^9@2$1^7^5").
  Proof. intros P Q s msF ms mo K V E W. eapply ah_lift; eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma aclient_addr_weaken : ltac2:(zQ "60!jd!q6!md!ku8!lg9!js5>2LB@1$2$0>3LB'@1$2$0>2SP$1>3SP'$1>1a$1>0@5$3?5HCEIL?1H^4^2^1>0@2$5^4^3>0>1b$0>0@3$4$0^1^7@3$4$0^2^9@5$3?5HCEIL?1H^8^6^4").
  Proof.
    intros LB LB' SP SP' a Hc HS HL. unfold aclient_addr in *.
    destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|Hc]]]]; [left; lia| tauto | | | tauto].
    - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
    - right; right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  Qed.

  Lemma aclient_range_addr : ltac2:(zQ "90!q6!md!lgf!ku8!lh5!jd!sc!js5!li4>2LB@1$1$5>2SP$0>1A$0>1n$0>1a$0>0@6$4?5HCEIL?1H^5^4^3^2>0@2$2@2$7^4^2@2$8^2@2$6^4^3@5$3?5HCEIL?1H^7^6^3").
  Proof.
    intros LB SP A n a HR Ha. unfold aclient_range, aclient_addr in *.
    destruct HR as [K|[K|[(b & Hb & K1 & K2)|[(b & Hb & K1 & K2)|[K|[K|K]]]]]]; [left; lia| right; left; apply K; lia | | | right; right; right; right; lia ..].
    - right; right; left. exists b. split; [exact Hb| lia].
    - right; right; right; left. exists b. split; [exact Hb| lia].
  Qed.

  Lemma apres_bytes_at : ltac2:(zQ "c0!md!li9!q6!ig3!ip8!lma!lp3!lp9!lh5!lq2!jd!lq9>2LB@1$0$a>2SP$2>1m$4>2m'$4>1A$2>2bs@1$0@1$6@1$1#8>0@6$9?5HCEIL?1H^6^5^4^3>0@4$5$3^5^3^2>0@6$8?5HCEIL?1H^8^7^4@1$b@2$7@1$6@1$1#8^3@4$5$3^6^5^4").
  Proof.
    (intros LB SP m m' A bs HP nd_i2 HR; ndestruct nd_i2 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR|lia])) as [E _]. rewrite E. reflexivity.
  Qed.

  Lemma apres_wr_at : ltac2:(zQ "80!q6!ig3!ip8!lr2!md!lh5!lq2!jd>2LB@1$4$7>2SP$0>1m$2>2m'$2>1A$0>1n$0>0@6$6?5HCEIL?1H^6^5^4^3>0@4$3$1^5^3^2>0@6$5?5HCEIL?1H^8^7^4^3@4$3$1^6^5^4").
  Proof.
    (intros LB SP m m' A n HP nd_i3 HR; ndestruct nd_i3 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR|lia])) as [_ W]. apply W. apply HW. exact Hi.
  Qed.

  Lemma apres_rw_cells : ltac2:(zQ "b0!md!q6!ig3!ip8!lv6!lh5!lq2!jd!mje!mk6!lq9>2LB@1$0$7>2SP$1>1m$3>2m'$3>1A$1>2cs@1$0$8>0@6$6?5HCEIL?1H^6^5^4^3>0@4$4$2^5^3^2>0@6$5?5HCEIL?1H^8^7^4@1$a@1$9^3@4$4$2^6^5^4").
  Proof.
    intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
    - eapply apres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
    - eapply apres_wr_at; eauto.
  Qed.

  Lemma apres_u8arr : ltac2:(zQ "c0!md!li9!q6!ig3!ip8!moe!lp3!lp9!lh5!lq2!jd!lq9>2LB@1$0$a>2SP$2>1m$4>2m'$4>1A$2>2bs@1$0@1$6@1$1#8>0@6$9?5HCEIL?1H^6^5^4^3>0@4$5$3^5^3^2>0@6$8?5HCEIL?1H^8^7^4@1$b@2$7@1$6@1$1#8^3@4$5$3^6^5^4").
  Proof. intros LB SP m m' A bs HP [HB HW] HR. split; [eapply apres_bytes_at; eauto| eapply apres_wr_at; eauto]. Qed.

  (* [comment removed for export] *)
  Lemma aclient_range_block_sh : ltac2:(zQ "90!q6!t2!mp7!t9!md!lh5!mpd!mq4!lg9>2LB@1$4@2$1@2$1$2$0$0>2SP$0>1p$2>1A$0>1n$0>0@3$8@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0^3^2^1^5@6$5?5HCEIL?1H^6^5@1$7^3@1$6^2").
  Proof. intros LB SP p A n IN. right; right; right; left. exists (p, A, n). split; [exact IN| cbn; lia]. Qed.
  Lemma aclient_range_block : ltac2:(zQ "90!q6!t2!mp7!t9!sc!js5!md!lh5!lg9>2LB@1$6@2$1@2$1$2$0$0>2SP$0>1p$2>1A$0>1n$0>1a$0>1k$0>0@3$8@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0^5^4^3^7>0@2$5^5^3>0@2$5@2$4^4^3@2$4^6^5@6$7?5HCEIL?1H^a^9^5^4").
  Proof. intros LB SP p A n a k IN H1 H2. right; right; left. exists (p, A, n). split; [exact IN| cbn; lia]. Qed.

  Lemma apres_SHAD : ltac2:(zQ "c0!md!li9!q6!ip8!mqa!lp3!lp9!lh5!lq2!jd!mq4!lq9>2LB@1$0$9>2SP$2>1m$3>2m'$3>1A$2>3sbs@1$0@1$5@1$1#8>0@6$8?5HCEIL?1H^6^5^4^3>0@3$4^5^3^2>0@6$7?5HCEIL?1H^8^7@1$a^4@1$b@2$6@1$5@1$1#8^3@3$4^6^5^4").
  Proof. (intros LB SP m m' A sbs HP nd_i5 HR; ndestruct nd_i5 as (A0 & HA & U)). split; [exact A0|]. split; [exact HA|]. eapply apres_u8arr; eauto. Qed.

  Lemma apres_addressable : ltac2:(zQ "a0!q6!mp7!t2!t9!ip8!mr2!md!lq2!jd!lg9>2LB@1$6$8>2SP$0>1m$4>2m'$4>1p$1>1A$0>1n$0>0@6$7?5HCEIL?1H^7^6^5^4>0@3$5^6^3^2>0@3$9@2$2@2$2$1$0$0@4$3@2$2$1$0$0@4$3$1$0^5^4^3^9@3$5^7^5^4").
  Proof.
    intros LB SP m m' p A n HP [Hn SH] IN. split; [exact Hn|]. eapply apres_SHAD; eauto.
    rewrite shadow_of_length by lia. eapply aclient_range_block_sh; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma RFS_via_apres : ltac2:(zQ "70!md!ms1!ip8!q6!lq2!jd!u0>2LF@1$0$6>2LB@1$0$5>2SP$3>1m$2>2m'$2>0@3$1?1H^5^2>0@6$4?5HCEIL?1H^5^4^3^2@3$1?1H^7^3").
  Proof.
    intros LF LB SP m m' R HP. eapply ah_RFS_ext; [exact R|].
    intros a Ha Hr. apply HP; [exact Ha|]. unfold aclient_addr.
    destruct Hr as [Hr|[Hr|Hr]].
    - right; right; right; right; left. exact Hr.
    - right; left. unfold aimg_client. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
    - right; right; right; right; right; left. exact Hr.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma apres_of_munch : ltac2:(zQ "h51!q6!li9!lp3!md!ms9!t2!js5!mt2!mt8!lgf!mv5!ig3!lq2!io1!ih6!jd!ip8!jrc!njb!nk2!nkb&>0@1$2@1$1#k0@1$4@1$2@1$1#8>1s@1$e?1H>2LB@1$3$f>2SP$0>1W@1$3$h2>2m0$h0>1m~0>2m'~0>0@4$d?1H^7^6^3>0@3$h3^5^3^2>0@3$h4$b^4^3>0@3$a@2$5$0$0\2iv@2$5$0$0@2$9@2$6@1$h1?5HCEIL@3$7$0$0^1@2$6@3$8$0$0^1^9^7@6$c?5HCEIL?1H^a^9^6^5").
  Proof.
    intros s LB SP W m0 m m' RH MU WM FW a Ha Hc.
    pose proof (ah_fsb _ _ _ RH) as (F1 & F2 & F3).
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as [H1 H2]. cbn in H1, H2.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      intros K. unfold aclient_addr in Hc.
      destruct Hc as [Hc|Hc]; [lia|].
      assert (LOW : a < aceil); [| lia].
      destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
      - acb; unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      - pose proof (ah_blocks _ _ _ _ RH Hb) as (_ & _ & _ & _ & R & _). lia.
      - pose proof (ah_blocks _ _ _ _ RH Hb) as (_ & _ & R0 & R1 & R & _).
        pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
        unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
      - lia.
      - pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) ltac:(acb; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
        acb; unfold AFS_SIZE in *. lia.
      - acb; unfold AHI_LO in *. lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma stack_window_ok : ltac2:(zQ "e0!q6!t9!md!lgf!jrc!js5!np1!npe!nq8!nrb!ns9!jd!u0!sc>2LB@1$2$b>2LF@1$2$c>3lo'$0>2SP$0>0@2$5@1$4?5HCEIL^2>0@2$5@2$d@1$a?1H$7@1$4?5HCEIL@2$3@4$8?5HCEIL?1H^6@4$1$0$0^4^3@2$3@3$9?1H^5@4$1$0$0^4^3@1$6@4$1$0$0^4^3").
  Proof.
    intros LB LF lo' SP H1 H2. split; [left; cbn; lia|]. split.
    - left. cbn. acb; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. lia.
    - apply aconst_ok_high; [| right; left]; acb; unfold sh, AIMG_TOP, ASHADOW_BASE in *; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fresh_frame : ltac2:(zQ "30!q6!md!u0>2LF@1$1$2>1k$0>2ff$0>2fp$0P") := ltac2:(zQ "h00!q6!lgf!u0!nt1!nta!sc!js5!md!o8!jm9!jmf!ntf!nud!nv6!og0!lg9\2LF@1$7$2\1k$0\2ff$0\2fp$0@2$1@4$b?1H^3^2^1@2$1@2$c?5HCEIL?1H>1f$2>0@3$f$2^1^5@2$1@2$a@2$6@2$5^4@1$4^5@1$3^2@2$6@2$5@1$3^2@1$4@1$d^2^4@1$9@3$8$0^3@1$e^2").

  (* [comment removed for export] *)
  Definition fsobj : ltac2:(zQ "30!q6!md!u0>2LF@1$1$2>1O$0>1n$0P") := ltac2:(zQ "e0!u0!sc!js5!lgf!jmf!q6!ns9!nt1!md!og9!npe!nv6!nta!lg9\2LF@1$8$0\1O$5\1n$5@2$4@2$4@2$2@2$1^2^1@1$6?1H@2$2@2$1@1$6?1H$a^2@2$9$0\1f$0@2$3@3$d$0^1^4@2$3@2$2@1$7^1^3@2$2@2$1^3^2@2$1@1$7^1@1$c@1$b^1").

  Lemma fsz_pos : ltac2:(zQ "30!js5!q6!nta>1k$1>0@2$0Z^1@2$0+k0@1$2^2").
  Proof. intros k Hk. unfold fsz. pose proof (Z.pow_le_mono_r 2 0 k ltac:(lia) Hk). change (2^0) with 1 in H0. nia. Qed.

  Lemma fsz_0 : fsz 0 = 64. Proof. reflexivity. Qed.     (* [comment removed for export] *)
  Lemma fsz_1 : fsz 1 = 128. Proof. reflexivity. Qed.
  Lemma fsz_2 : fsz 2 = 256. Proof. reflexivity. Qed.
  Lemma fsz_3 : fsz 3 = 512. Proof. reflexivity. Qed.
  Lemma fsz_4 : fsz 4 = 1024. Proof. reflexivity. Qed.
  Lemma fshn_1 : fshn 1 = 16. Proof. reflexivity. Qed.

  Lemma fresh_of_RFS : ltac2:(zQ "80!q6!t2!t9!m6!md!ol0!ms1!ip8>2LF@1$4@2$1@2$1$0$0$0>1k$0>2ff$0>2fp$0>1m$7>0@3$6?1H@3$3@2$1@2$1$0$0$0@4$2@2$1$0$0$0@4$2$0$0^4^3^2^5^1@4$5^6^5^4^3").
  Proof.
    intros LF k ff fp m R. pose proof (ah_RFS_range _ _ R) as [AF AR']. pose proof (AR' (k, ff, fp) (or_introl eq_refl)) as AR. cbn in AR.
    split; [exact AR|]. split; [exact AF|]. intros f IN.
    pose proof (ah_RFS_nodup _ _ R) as ND. cbn in ND. inversion ND; subst.
    assert (NE : ff <> ff_addr f). { intros E. apply H2. apply in_map_iff. exists f. split; [symmetry; exact E| exact IN]. }
    destruct (ah_RFS_disj _ _ (k, ff, fp) f R (or_introl eq_refl) (or_intror IN) NE) as [D1 D2]. cbn in D1, D2.
    split; [exact D1| exact D2].
  Qed.

  (* [comment removed for export] *)

  Lemma RFS_fsb : ltac2:(zQ "50!md!nud!ms1!u0!ip8>2LF@1$0$3>1m$4>0@3$2?1H^2^1@2$1?5HCEIL?1H").
  Proof. intros LF m R. exact (proj1 (ah_RFS_range _ _ R)). Qed.

  Lemma fsobj_block : ltac2:(zQ "c0!q6!mp7!t2!md!t9!olf!io1!ih6!jd!u0!ip8!lg9>1s@1$7?1H>2LB@1$3$8>2m0$a>2LF@1$3$9>1p$1>1A$0>1n$0>0@4$6?1H^7^6^5>0@3$b@2$2@2$2$1$0$0@4$4@2$2$1$0$0@4$4$1$0^4^3^2^7@3$5^6^4^3").
  Proof.
    intros s LB m0 LF p A n RH IN. left.
    pose proof (ah_blocks _ _ _ _ RH IN) as (_ & _ & _ & _ & _ & G). cbn in G. lia.
  Qed.

  Lemma fsobj_sub : ltac2:(zQ "60!q6!olf!sc!js5!md!u0>2LF@1$4$5>1O$0>1n$0>2O'$0>2n'$0>0@3$1^5^4^3>0@2$3^5^3>0@2$3@2$2^4^3@2$2^6^5@3$1^8^5^4").
  Proof.
    intros LF O n O' n' D H1 H2. destruct D as [D|(f & IN & D1 & D2)]; [left; lia| right]. exists f. split; [exact IN| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_frame_facts : ltac2:(zQ "h20!lgf!js5!sc!ns9!q6!om8!on4!npe!o8!ond!nta!jrc!jsa!md!ol0!u0!oo8!li4>2LF@1$d$f>1k$4>2ff$4>2fp$4>0@4$e^4^3^2^1@2$0@2$0@2$1Z^4@2$1^4+a@2$0@2$1@2$2$5$6^3@2$0@2$1@2$2^3@1$a^4@1$b?5HCEIL@2$0@3$8$4@2$c^3+k0Z@2$0@3$8$4@2$c^3+8Z@2$0@2$1@2$2$5$9^2@2$0@2$1@2$2^2+1^3@2$0@2$1@2$2@1$3?1H$9^2@2$0@2$h1^2@2$2@1$3?1H$6@2$0@2$1@2$2@1$3?1H$6^3@2$0@2$1@2$2^3@1$a^4@2$2@1$3?1H$7@2$0@2$1$5@1$3?1H@2$0@2$1@2$2@1$3?1H$7@1$b?5HCEIL@3$h0?5HCEIL@1$3?1H$7").
  Proof.
    (intros LF k ff fp nd_i6; ndestruct nd_i6 as ((K & R1 & R2 & R3 & R4) & (F1 & F2 & F3 & F4) & _)).
    assert (M64 : ff mod 64 = 0).
    { unfold fsz in R3. pose proof (fsz_pos k ltac:(lia)) as FP. unfold fsz in FP.
      destruct (Zle_lt_or_eq 0 k ltac:(lia)) as [Kp| <-].
      - assert (E : 64 * 2 ^ k = 64 * (2 * 2 ^ (k - 1))). { rewrite <- Z.pow_succ_r by lia. f_equal. f_equal. lia. }
        rewrite E in R3. pose proof (Z.pow_nonneg 2 (k-1) ltac:(lia)).
        apply Z.mod_divide in R3; [|lia]. apply Z.mod_divide; [lia|]. destruct R3 as [q Hq]. exists (q * (2 * 2 ^ (k-1))). lia.
      - change (64 * 2 ^ 0) with 64 in R3. exact R3. }
    assert (M8 : ff mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof (fsz_pos k ltac:(lia)).
    repeat split; try exact F4; acb; unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fsobj_windows : ltac2:(zQ "h20!js5!sc!q6!jmf!mq4!lgf!ns9!md!ol0!olf!ond!ms1!u0!op0!nta!ip8!op6!mpd>2LF@1$7$c>1O$2>1n$2>1k$2>2ff$2>2fp$2>1m$f>0@3$b?1H^7^1>0@3$9^8^7^6>0@4$8^9^6^5^4>0@2$0Z^9>0@2$0Z^9>0@2$0@2$1^b^a$h0@2$5@2$3@2$0@2$1^c^b^9@2$0@2$1^9@1$e^a^c@2$5@2$3@2$0@2$1@1$4^c@1$h1^b@1$4^9@2$0@2$1@1$4^9@1$d^a@1$4^c@2$5@2$3@2$0@2$1^c^b^8@2$0@2$1^8+1^c@2$3@2$0@2$1^c^b@1$6?1H@2$0@2$1@1$6?1H$a^c").
  Proof.
    intros LF O n k ff fp m R OB FF HO Hn Htop. pose proof (fresh_frame_facts _ _ _ _ FF) as FA.
    ndestruct FA as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    assert (DD : (O + n <= ff \/ ff + fsz k <= O) /\ (O + n <= fp \/ fp + 1 <= O) /\ (O + n <= as_FSB H \/ as_FSB H + AFS_FLAGS <= O)).
    { pose proof (fsz_pos k ltac:(lia)). destruct OB as [OB|(f & IN & D1 & D2)].
      - unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia.
      - ndestruct FF as (_ & _ & D). destruct (D f IN) as [DJ NF].
        pose proof (proj2 (ah_RFS_range _ _ R) f IN) as (K' & Q1 & Q2 & Q3 & Q4). pose proof (fsz_pos (ff_class f) ltac:(lia)).
        unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia. }
    ndestruct DD as (D1 & D2 & D3). split; [exact D1|]. split; [| split; [exact D2| exact D3]].
    destruct D1 as [D1|D1].
    - left. unfold sh, nsh. Z.div_mod_to_equations. nia.
    - right. unfold sh, fshn. unfold fsz in D1. Z.div_mod_to_equations. nia.
  Qed.
  (* [comment removed for export] *)
  Lemma disjoint_from_sub : ltac2:(zQ "60!q6!oq1!sc!js5!md!njb>1W@1$4$5>1O$0>1n$0>1a$0>1k$0>0@3$1^5^4^3>0@2$3^5^3>0@2$3@2$2^4^3@2$2^6^5@3$1^8^5^4").
  Proof.
    induction W as [|[lo hi] W IH]; intros O n a k D H1 H2; cbn in *; [exact I|].
    destruct D as [D1 D2]. split; [lia| exact (IH _ _ _ _ D2 H1 H2)].
  Qed.

  Lemma fshn_nsh : ltac2:(zQ "60!q6!o8!op0!nta!mpd!js5>1k$0>0@2$5Z^1@3$1$0@1$2^2@1$4@1$3^2").
  Proof. intros k Hk. unfold nsh, fsz, fshn. pose proof (Z.pow_nonneg 2 k). Z.div_mod_to_equations. nia. Qed.

  (* [comment removed for export] *)
  Lemma fsobj_disjoint : ltac2:(zQ "h60!q6!t2!sc!m6!t9!js5!ns9!mq4!md!jm3!jmf!ol0!olf!ond!ms1!u0!op0!nta!ip8!op6!oo8!oq1>2LF@1$8$f>1O$0>1n$0>1k$0>2ff$0>2fp$0>1m$h2>3slo$0>3shi$0>0@3$e?1H^9^3>0@3$c^a^9^8>0@4$b^b^8^7^6>0@2$5Z^b>0@2$5Z^b>0@2$5@2$2^d^c$h3>0@3$h4?5HCEIL^e^d>0@2$a@2$5@2$2^f^e^9@2$5^8^f@3$h5@3$3@2$1$0$0@4$4$0$0^a^9@3$3@2$1$0$0@4$4$0$0@1$6?1H@2$2@1$6?1H$d@3$3@2$1$0$0@4$4$0$0^c@2$2^c+1@3$3@2$1$0$0@4$4$0$0^d@2$2^d@1$h1^e@3$3@2$1$0$0@4$4$0$0@1$7^d@2$2@1$7^d@1$h0^e@1$9@2$1$0$0^h0^f").
  Proof.
    intros LF O n k ff fp m slo shi R OB FF HO Hn Htop HHI HS.
    pose proof (fsobj_windows _ _ _ _ _ _ _ R OB FF HO Hn Htop) as (D1 & D2 & D3 & D4).
    pose proof (fresh_frame_facts _ _ _ _ FF) as (K & R1 & R2 & _ & _ & _ & _ & _ & _ & _ & P6 & P7 & P8 & P9).
    pose proof (fsz_pos k ltac:(lia)).
    pose proof (aapp_disjoint_sh O n ff (fsz k) HHI ltac:(acb; unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(acb; unfold AAPP_HI in *; lia) ltac:(lia)) as S2.
    rewrite <- fshn_nsh in S2 by lia.
    cbn. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fsobj_disjoint_sh : ltac2:(zQ "h60!q6!t2!m6!t9!sc!js5!mq4!ns9!md!jm3!ol0!olf!ond!ms1!u0!op0!nta!ip8!op6!jrc!mpd!oq1>2LF@1$8$e>1O$0>1n$0>1k$0>2ff$0>2fp$0>1m$h1>3slo$0>3shi$0>0@3$d?1H^9^3>0@3$b^a^9^8>0@4$a^b^8^7^6>0@2$5Z^b>0@2$5Z^b>0@2$5@2$4^d^c$h2>0@2$5@1$h3?5HCEIL^8@3$h5@3$2@2$1$0$0@4$3$0$0^9^8@3$2@2$1$0$0@4$3$0$0@1$7?1H@2$4@1$7?1H$c@3$2@2$1$0$0@4$3$0$0^b@2$4^b+1@3$2@2$1$0$0@4$3$0$0^c@2$4^c@1$h0^d@3$2@2$1$0$0@4$3$0$0@1$6^c@2$4@1$6^c@1$f^d@1$9@2$1$0$0@1$6^f@1$h4^e").
  Proof.
    intros LF O n k ff fp m slo shi R OB FF HO Hn Htop HS.
    pose proof (fsobj_windows _ _ _ _ _ _ _ R OB FF HO Hn Htop) as (D1 & D2 & D3 & D4).
    pose proof (fresh_frame_facts _ _ _ _ FF) as (K & R1 & R2 & _ & _ & P1 & _ & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    pose proof (fsz_pos k ltac:(lia)).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE O n P9 HO Htop Hn) as S1.
    pose proof (sh_nsh_high O n HO Hn Htop) as S3.
    cbn. acb; unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AHI_LO in *. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Definition fs_scratch : ltac2:(zQ "40!q6!md!t2!u0>2LF@1$1$3>2iv@2$2$0$0P") := ltac2:(zQ "h00!q6!t2!t9!o8!sc!og9!jmf!ns9!mq4!md!lgf!ol0!ond!u0!op0!nta\2LF@1$9$d\2iv@2$1$0$0@2$6@3$3@2$1$0$0^1@4$2$0$0@1$7?1H@2$4@1$7?1H$c@2$5$0\1k$0@2$5$0\2ff$0@2$5$0\2fp$0@2$a@4$b^5^3^2^1@2$6@3$3@2$1$0$0^4@4$2$0$0^2@2$4^2@1$f^3@2$6@3$3@2$1$0$0^4@4$2$0$0^1@2$4^1+1@3$3@2$1$0$0^4@4$2$0$0@1$8^2@2$4@1$8^2@1$e^3").

  Lemma fs_scratch_of_fresh : ltac2:(zQ "h00!q6!t2!m6!t9!sc!ns9!mq4!md!jm3!mv5!ol0!or2!ond!u0!op0!nta>2LF@1$7$d>1k$0>2ff$0>2fp$0>0@4$a^4^3^2^1@3$9@2$1$0$0@1$b^5@3$2@2$1$0$0@4$3$0$0@1$5?1H@2$4@1$5?1H$c@3$2@2$1$0$0@4$3$0$0^2@2$4^2+1@3$2@2$1$0$0@4$3$0$0^3@2$4^3@1$f^4@3$2@2$1$0$0@4$3$0$0@1$6^3@2$4@1$6^3@1$e^4@1$8@2$1$0$0").
  Proof.
    intros LF k ff fp FF. repeat apply Forall_cons; [left; reflexivity| right..| apply Forall_nil]; nexists k, ff, fp; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma fsobj_scratch : ltac2:(zQ "f0!q6!js5!sc!mt2!md!t2!mt8!jmf!or2!olf!ms1!u0!ip8!op6!oo8>2LF@1$4$b>1O$0>1n$0>1m$c>2iv@2$5$0$0>0@3$a?1H^5^2>0@3$9^6^5^4>0@2$1Z^6>0@2$1Z^6>0@2$1@2$2^8^7$d>0@3$e?5HCEIL^9^8>0@2$8^b^7@2$7@2$1@2$2^b^a@3$3$0$0^8@2$1@3$6$0$0^8^b").
  Proof.
    intros LF O n m iv R OB HO Hn Htop HHI [->|(k & ff & fp & FF & E)].
    - cbn. destruct OB as [OB|(f & IN & D1 & D2)]; [unfold AFS_FLAGS, AFS_SIZE in *; lia|].
      pose proof (proj2 (ah_RFS_range _ _ R) f IN) as (K' & Q1 & Q2 & Q3 & Q4). unfold AFS_FLAGS, AFS_HDR in *. lia.
    - pose proof (fsobj_windows _ _ _ _ _ _ _ R OB FF HO Hn Htop) as (D1 & D2 & D3 & D4).
      destruct E as [-> |[-> | ->]]; cbn; [lia| lia|].
      pose proof (fresh_frame_facts _ _ _ _ FF) as (K & R1 & R2 & _).
      pose proof (fsz_pos k ltac:(lia)).
      pose proof (aapp_disjoint_sh O n ff (fsz k) HHI ltac:(acb; unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(acb; unfold AAPP_HI in *; lia) ltac:(lia)) as S2.
      rewrite <- fshn_nsh in S2 by lia. lia.
  Qed.

  Lemma fsobj_scratch_sh : ltac2:(zQ "h00!q6!js5!mq4!sc!mt2!md!t2!mt8!jmf!or2!olf!ms1!u0!ip8!op6!mpd>2LF@1$5$c>1O$0>1n$0>1m$d>2iv@2$6$0$0>0@3$b?1H^5^2>0@3$a^6^5^4>0@2$1Z^6>0@2$1Z^6>0@2$1@2$3^8^7$e>0@2$9^a^6@2$8@2$1@2$3@1$2^a@1$f^9@3$4$0$0^7@2$1@3$7$0$0^7@1$2^a").
  Proof.
    intros LF O n m iv R OB HO Hn Htop [->|(k & ff & fp & FF & E)].
    - cbn. destruct (proj1 (ah_RFS_range _ _ R)) as (F1 & F2 & F3 & F4).
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE O n F4 HO Htop Hn). unfold AFS_FLAGS, AFS_SIZE in *. lia.
    - pose proof (fsobj_windows _ _ _ _ _ _ _ R OB FF HO Hn Htop) as (D1 & D2 & D3 & D4).
      pose proof (fresh_frame_facts _ _ _ _ FF) as (K & R1 & R2 & _ & _ & P1 & _ & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE O n P9 HO Htop Hn) as S1.
      pose proof (fsz_pos k ltac:(lia)).
      destruct E as [-> |[-> | ->]]; cbn; acb; unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma athr_cells_frame : ltac2:(zQ "h00!q6!t2!li9!os0!lp3!mt2!md!ms9!mv5!ig3!ip8!jrc!njb!nk2!nkb!js5>1W@1$6$c>1m$a>2m'>0@1$4@1$2#k0@1$7@1$4@1$2#8>0@2$3?5HCEIL^2>0@3$d^4^3^2>0@3$e$9^4^3>0@3$8@2$1$0$0\2iv@2$1$0$0@2$f@1$b?5HCEIL@3$5$0$0^1^6@2$3?5HCEIL^5").
  Proof.
    (intros W m m' nd_i7 MU WM FW; ndestruct nd_i7 as (ctx & T & D & tb & te & C1 & C2 & C3 & C4 & C5 & R)).
    assert (DJ : forall a n, a + n <= aceil -> disjoint_from W a n).
    { intros a n Hn. clear -FW Hn. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion FW; subst. cbn in *.
      split; [lia| apply IH; assumption]. }
    exists ctx, T, D, tb, te. acb; unfold ATSD0, ATP in *.
    repeat match goal with |- _ /\ _ => split end; try lia;
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply DJ; cbn; lia]).
  Qed.
End HH.
(* [comment removed for export] *)
