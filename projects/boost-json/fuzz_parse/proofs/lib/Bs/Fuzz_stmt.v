(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep CXXLib CXXLib2 AsObj AsStack0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import N8Kit AsClsKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3powhc3addhc3mul37Corelib4Init9Datatypesk64listk64prodk63nilk64cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~n99APC0_FREEn95as_TRn98trace_ok99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9Fuzz_stmt3HCW1W~~~~~~t53ftr37Corelib4Init5Logichi03andt58ftr_dtort56ftr_pot56ftr_pvhc2len95blockk66lengthn9bclass_bytes89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9Fuzz_stmt3HCW~~~~~~hnc9AFUZZ_CLShc6of_natn95as_Cfn95as_Cmn9casan_rt_hypst59fuzz_cost04Npos35stdpp9bitvectorbdefinitionsig62bv3h5LinuxProcessSemanticsfLinuxProcessSem3Runii96config3h5LinuxProcessSemanticsfLinuxProcessSem5Stateilf5Model3h5LinuxProcessSemantics5Riscv7Preludeip65bvmapn95as_Stn96fframen93memhi02ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~iu25asegsig6bbv_unsignedk66optionn95as_AL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jk64cellk64Nonehi02eq37Corelib5Lists7ListDefjp76Forall3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjr8dmachine_stateii99cfg_modelii96cfg_ms79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB5BJRep~~~~~~kh7abj_statics79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsCXXHeap~~~~~~km1afs_scratch79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsConst~~~~~~kqe6ACONSTn98as_AKRELn98as_MPRESn96as_RFSn98as_RHEAPn96as_VISn9bas_rauxv_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsStack0~~~~~~lj66stack079OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6CXXRep~~~~~~lne5xpresjk62C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~ls94frm079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mga3mkRmga3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ml42MSml46ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mq17mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mu67seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~nj08rw_cells36Stdlib7SortingbPermutationnn7bPermutationhc2gehc3subig67Z_to_bvn94bptrk64pairhc6moduloii95mkCfg36Stdlib5Lists4Listnt82Inhc2lt37Corelib4Init3Natnv63add37Corelib4Init5Peanoogf2len9bAFS_MAXLIVEn93ATPn9fas_LIVE_CNT_MAXn9bas_LIVE_MAXn95as_SRn98as_chainn98lb_bytesn95pf_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~oo35aceiloo3baddressablehnc9AFUZZ_CNThncbAFUZZ_EMPTYhncaAFUZZ_LIVEhncbAFUZZ_STACKhnc7PF_FUZZhnccP_FUZZ_ENTRYt59fuzz_postt5afuzz_tr_okmq18bytes_atn93asr" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition P_FUZZ_ENTRY : Z := 0xbf214.
(* [comment removed for export] *)
Definition AFUZZ_STACK : Z := 61440.
(* [comment removed for export] *)
Definition AFUZZ_LIVE : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!j4@2$0+2+i0").
Definition AFUZZ_CNT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!j4!ja@2$1@2$0+2+h9@2$0+2+a").
Definition AFUZZ_CLS : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!k0@2$0+3+hggg0").      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFUZZ_EMPTY : Z := 0x6ef7e0.

(* [comment removed for export] *)
Definition PF_FUZZ : ltac2:(zQ "30!le!h9!m5@1$0@2$2$1@1$0$1") := ltac2:(zQ "40!h9!le!mc!m5@1$2@2$3$0@1$1$0").

Section W.
  Variable H : ltac2:(zQ "10!pl2$0").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ftr : ltac2:(zQ "10!h9>7ra_site$0P") := ltac2:(zQ "60!h9!n2!mc!r6!s2!sa\7ra_site$0@3$5@1$4?1H$3@3$1$0^1@1$2$0").
  (* [comment removed for export] *)
  Definition ftr_dtor : ltac2:(zQ "00P") := ltac2:(zQ "20!hha!hj4@2$1@1$0+smprc@2$1@1$0+ulog8@2$1@1$0+sgnvc@1$0+smqr4").        (* [comment removed for export] *)
  Definition ftr_po : ltac2:(zQ "00P") := ltac2:(zQ "30!hj4!hha!hjb@2$0@1$1+vitm8@2$0$2@2$0@1$1+snon4@1$1+snunc").            (* [comment removed for export] *)
  Definition ftr_pv : ltac2:(zQ "00P") := ltac2:(zQ "40!hj4!hha!hjb!hk6@2$0@1$1+vitm8@2$0$2@2$0$3@2$0@1$1+vjvn0@2$0@1$1+vkjk0@2$0@1$1+vknh0@2$0@1$1+vkqu4@2$0@1$1+vkus0@1$1+vjgt8").   (* [comment removed for export] *)
  Definition fuzz_tr_ok : ltac2:(zQ "00P") := ltac2:(zQ "40!hj4!hjb!hha!hkf@2$0@2$0$3@2$0$1@1$2+uulp0$1").             (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fuzz_class_bytes_cnt : ltac2:(zQ "90!hl8!hld!hm5!le!hj4!h9!hme!hrf!hsc>2LB@1$3$1>1c$5>0@2$4@2$0+1^1@2$0^1+he>0@2$0@1$8@2$2$1^3+3@2$0@2$6^4^3$7").
  Proof.
    intros LB c Hc HL. pose proof (class_bytes_le_len LB c Hc). pose proof (acsize_le c Hc). unfold AFUZZ_CLS. nia.
  Qed.

  Definition fuzz_cost : ltac2:(zQ "10!h9>1N$0$0") := ltac2:(zQ "60!ja!k0!j4!h9!ht5!htd\1N$3@2$0@2$5?1H@2$0@2$1+hg0^1@2$2+2+h0@2$4?1H@2$0@2$1+hg0^1@2$2+2+h0").   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma fuzz_cost_nonneg : ltac2:(zQ "40!hl8!h9!hu5!hv4>0@2$2?5HCEIL?1H>1n$1>0@2$0Z^1@2$0Z@1$3^2").
  Proof.
    intros HH n Hn. npose (ah_costs H HH) as (C1 & C2 & C3 & C4 & _).
    unfold fuzz_cost. pose proof (C1 (256 * n + 2^16) ltac:(lia)). pose proof (C3 (256 * n + 2^16) ltac:(lia)). lia.
  Qed.
  Lemma fuzz_cost_mono : ltac2:(zQ "50!hl8!h9!hv4!hj4!hu5>0@2$4?5HCEIL?1H>1n$1>2n'$1>0@2$3@2$0Z^2@2$0^2^1@2$0@1$2^3@1$2^2").
  Proof.
    intros HH n n' Hn. npose (ah_costs H HH) as (C1 & C2 & C3 & C4 & _).
    unfold fuzz_cost. pose proof (C2 (256 * n + 2^16) (256 * n' + 2^16) ltac:(lia)). pose proof (C4 (256 * n + 2^16) (256 * n' + 2^16) ltac:(lia)). lia.
  Qed.

  Definition fuzz_post : ltac2:(zQ "b0!ig0!ii3!h9!le!il5!iod!irc!is5!hld!isd!it6>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$7?1H>2LB@1$3$8>2LF@1$3$9>1N$2>2lo$2>1B$2>3shi$2>1m$a>2mo$5>0$4P") := ltac2:(zQ "j51!ig0!ii3!itc!hj4!h9!le!jhd!hld!m5!irc!is5!ji6!jj5!jje!jo2!joa!n2!mc!jp1!jqe!juf!kg0!kgd!il5!iod!kl3!kq0!kub!kv5!lg0!lgb!lh4!lhf!li8!isd!it6!ln4!lra!hv4!ls3!mg2!mk6!mkd!mp1!mp7!mtb!ni5!nmb!np3!ja!nq2!nq7!nqd&>0@1$1@1$0#k0@1$c@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$9@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$a?1H\2LB@1$5$7\2LF@1$5$i2\1N$4\2lo$4\1B$4\3shi$4\1m$i3\2mo$h8\1c$h7@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2@1$a?1H\2s'@1$a?1H@2$2@1$5$7\3LB'@1$5$7@2$2@1$5@2$8$4$4\2XS@1$5@2$8$4$4@2$2@2$9@1$0#5@1$1@1$0#k0\2F'@2$9@1$0#5@1$1@1$0#k0@2$2@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@3$h2$h4@3$i0?1H^5@1$h6^h6@7$ib@hf$i9^j1^j0^if^ie^h5^h4^h3^id^ic@2$j4@1$0#k0Z^h2^h1^h0^f^e^d^c^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^b^a^9^8^2@1$ic^j1^1@1$f@1$1@1$0#k0^7@1$ie$6@2$3@1$i8^1@2$3@3$hc?1H^5^h6@2$3@3$hd?1H^h7@1$h5^h6@2$3@2$id$6^7@2$3@4$ia$6^7^hb@2$b@1$0#k0^j0@2$3@4$if$6^7@2$j1@2$b@1$0#k0^ie-q4@3$h0$e@1$i7^6@1$h1$e@2$3@3$i1?1H^7^ha@2$3@4$hf?1H^5^4^7@2$3@3$j0$7^4^he@2$3@3$h3@2$8$4$4@3$ha?5HCEIL?1H^hd^3@2$3@7$i5?5HCEIL?1H^he@2$b@1$0#k0^j0^3^h8^7@2$3@3$he?1H^hd^7@2$3@1$hb^7@2$3@1$h9^7@2$3@4$i4?5HCEIL^7^hb^h9@2$j2@2$d?1H^5@2$j3@2$d?1H^hf@1$i6^hc").

  Definition fuzz_stmt : ltac2:(zQ "00P") := ltac2:(zQ "kc1!ig0!ii3!h9!hl8!jp1!ji6!m5!jhd!nr8!le!ja!nqd!hm5!nrf!ns6!juf!nsf!hld!isd!jo2!nub!nv1!hsc!j4!joa!n2!mc!hj4!itc!og8!oi3!iod!irc!kl3!kub!oi9!oj7!kv5!jje!ojd!okf!lgb!lh4!old!is5!s2!lhf!om5!li8!hme!on0!it6!onb!os1!osa!ln4!hrf!ot9!ou6!ov5!pg3!ph2!phd!hv4!pid!pj9!ls3!mg2!mk6!mkd!mp1!pk6!mtb!ni5!nmb!nq7&@3$4@1$1@1$0#k0^i8@2$b@1$0#k0^9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$f>1m$j3>2mo$hf>1s@1$ic?1H>2LB@1$9$h1>2LF@1$9$h2>2CH@1$9@2$6$2$2>1D$2>1N$2>2lo$2>1B$2>3shi$2>2ds@1$9@1$1@1$0#8>4errv@1$1@1$0#k0>0@3$4$f@3$ie?1H^b^e@7$k6@hf$k4^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0@2$b@1$0#k0$je^f@1$h8@1$1@1$0#k0^d@1$k9$7>0@1$k3^h0>0~0>0~0>0@4$k7$7^h1^b^6>0@3$4$2@1$h6@2$c@1$1@1$0#8^7^b>0@2$h5^c@2$h7+2+ha>0@3$4$2@2$e^e+h0Z>0>0@2$3+1^e@2$hc$8\2pD$8@3$h4@2$6@2$6$8$2$2@4$d@2$6$8$2$2@4$d$8$2^1^h1^h0^h4>0>0@3$4$2^fZ@3$4$2^h1$ja>0@4$ia?1H^h5^h4^h7>0@3$i5?1H^h6@2$h0^h9^h7>0@2$3@2$a@1$j2^h6$jb@1$i8?1H>0@2$3@2$a@1$h6@2$c$h1^h7$j9@1$i7?1H>0>1c$2>0@2$hb@2$3+1^1@2$3^1+he@2$3@2$j1^ha^2$j8>0@3$j0?1H^hc^h3>0@2$3@2$5@1$0#k0^je^h4>0@2$h5^h5@2$h7+2+k0>0@3$4$2@2$e@2$5@1$0#k0^k0+h0Z>0@4$k5$7^i0^h8@2$5@1$0#k0^k1>0@2$3@1$j5?5HCEIL^h9>0@2$3^ha@2$kb@2$5@1$0#k0^k3$jc>0@4$ka$7^i3@2$a@2$5@1$0#k0^k2-q4@3$h9$h3@1$k2^h7@1$ha$h3>0@2$k8$7^i4>0@3$4@1$1@1$0#k0^k4@2$b@1$0#k0$i4>0@1$i1^i6>0@3$4$2@2$e@2$5@1$0#k0^k9+2Z>0@1$i2^i8>0>0@2$3+1^i2@3$j6^ia^i4^i3>0@3$i9?1H^i6^ia>0@2$he@2$hd@2$c$h2^i7N3$i3>0@4$j7?5HCEIL^ic^i4^i2>0@2$3@2$5@1$0#k0^ke^i3>0@4$if?1H^ie@2$5@1$0#k0^k9^i9>0@4$j4@1$id?1H$jd@2$5@1$0#k0^l1^ia>0>3fp'$2>3ra'$2>0@3$h4@2$6$2$2@4$d$2$2^2^1^id@2$3@2$a@2$5@1$0#k0^l4+h0^3>0$k1>0@2$3@1$jf^ib@2$i6?1H^j0@3$ib?1H@hb$k0^l5^l4^l3^l2^ke^kd^k4^k3^k2^k1^k0^jf^je^jd^jc^jb^j6^j5^j1^j0^if^ic^ib^ia^i9^j3^j2@2$h0^j4^j2").
End W.

End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
