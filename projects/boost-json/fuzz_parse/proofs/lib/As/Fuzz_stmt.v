(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep CXXLib CXXLib2 AsObj AsStack0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import N8Kit AsClsKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3powhc3addhc3mul37Corelib4Init9Datatypesk64listk64prodk63nilk64cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~n99APC0_FREEn95as_TRn98trace_ok99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9Fuzz_stmt3HCW1W~~~~~~t53ftr37Corelib4Init5Logichi03andt58ftr_dtorhc2len95blockk66lengthn9bclass_bytes89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9Fuzz_stmt3HCW~~~~~~hma9AFUZZ_CLShc6of_natn95as_Cfn95as_Cmn9casan_rt_hypst59fuzz_cost04Npos35stdpp9bitvectorbdefinitionshv42bv3h5LinuxProcessSemanticsfLinuxProcessSem3Runih76config3h5LinuxProcessSemanticsfLinuxProcessSem5Stateikd5Model3h5LinuxProcessSemantics5Riscv7Preludeio45bvmapn95as_Stn96fframen93memhi02ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~it05asegshv4bbv_unsignedk66optionn95as_AL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jj44cellk64Nonehi02eq37Corelib5Lists7ListDefjo56Forall3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjq6dmachine_stateih79cfg_modelih76cfg_ms79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsCXXHeap~~~~~~kg5afs_scratch79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsConst~~~~~~kl26ACONSTn98as_AKRELn98as_MPRESn96as_RFSn98as_RHEAPn96as_VISn9bas_rauxv_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsStack0~~~~~~kta6stack079OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6CXXRep~~~~~~li25xpres79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA5BJRep~~~~~~lm7abj_staticsjj42C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~lr74frm079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~lv83mkRlv83stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mk22MSmk26ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mof7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mt47seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~nhe8rw_cells36Stdlib7SortingbPermutationnm5bPermutationhc2gehc3subhv47Z_to_bvn94bptrk64pairhc6moduloih75mkCfg36Stdlib5Lists4Listns62Inhc2lt37Corelib4Init3Natnu43add37Corelib4Init5Peanonvd2len9bAFS_MAXLIVEn93ATPn9fas_LIVE_CNT_MAXn9bas_LIVE_MAXn95as_SRn98as_chainn98lb_bytesn95pf_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~on15aceilon1baddressablehma9AFUZZ_CNThmabAFUZZ_EMPTYhmaaAFUZZ_LIVEhmabAFUZZ_STACKhma7PF_FUZZhmacP_FUZZ_ENTRYt59fuzz_postt5afuzz_tr_okmof8bytes_atn93asr" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition P_FUZZ_ENTRY : Z := 0xbf378.
(* [comment removed for export] *)
Definition AFUZZ_STACK : Z := 61440.
(* [comment removed for export] *)
Definition AFUZZ_LIVE : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!j4@2$0+2+i0").
Definition AFUZZ_CNT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!j4!ja@2$1@2$0+2+h9@2$0+2+a").
Definition AFUZZ_CLS : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!k0@2$0+3+hggg0").      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFUZZ_EMPTY : Z := 0x6f28a0.

(* [comment removed for export] *)
Definition PF_FUZZ : ltac2:(zQ "30!le!h9!m5@1$0@2$2$1@1$0$1") := ltac2:(zQ "40!h9!le!mc!m5@1$2@2$3$0@1$1$0").

Section W.
  Variable H : ltac2:(zQ "10!pk0$0").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ftr : ltac2:(zQ "10!h9>7ra_site$0P") := ltac2:(zQ "60!h9!n2!mc!r6!s2!sa\7ra_site$0@3$5@1$4?1H$3@3$1$0^1@1$2$0").
  Definition ftr_dtor : ltac2:(zQ "00P") := ltac2:(zQ "20!hha!hj4@2$1@1$0+uplo8@2$1@1$0+upnrc@2$1@1$0+upok4@1$0+upot0").        (* [comment removed for export] *)
  Definition fuzz_tr_ok : ltac2:(zQ "00P") := ltac2:(zQ "30!hj4!hha!hjb@2$0@2$0@2$0@1$1+vhuhc@2$0$2@2$0@2$0@1$1+vhuhc@2$0$2@2$0@1$1+sopg4@1$1+sovo8@2$0@1$1+vjvn8@2$0@1$1+vkjk8@2$0@1$1+vknh8@2$0@1$1+vkquc@2$0@1$1+vkus8@2$0@1$1+viku4@2$0@1$1+vjms4@2$0@1$1+viohc@1$1+vitm0@2$0@2$0$2@1$1+vhmm8@1$1+tgrg4$2").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fuzz_class_bytes_cnt : ltac2:(zQ "90!hk6!hkb!hl3!le!hj4!h9!hlc!hqd!hra>2LB@1$3$1>1c$5>0@2$4@2$0+1^1@2$0^1+he>0@2$0@1$8@2$2$1^3+3@2$0@2$6^4^3$7").
  Proof.
    intros LB c Hc HL. pose proof (class_bytes_le_len LB c Hc). pose proof (acsize_le c Hc). unfold AFUZZ_CLS. nia.
  Qed.

  Definition fuzz_cost : ltac2:(zQ "10!h9>1N$0$0") := ltac2:(zQ "60!ja!k0!j4!h9!hs3!hsb\1N$3@2$0@2$5?1H@2$0@2$1+hg0^1@2$2+2+h0@2$4?1H@2$0@2$1+hg0^1@2$2+2+h0").   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma fuzz_cost_nonneg : ltac2:(zQ "40!hk6!h9!ht3!hu2>0@2$2?5HCEIL?1H>1n$1>0@2$0Z^1@2$0Z@1$3^2").
  Proof.
    intros HH n Hn. npose (ah_costs H HH) as (C1 & C2 & C3 & C4 & _).
    unfold fuzz_cost. pose proof (C1 (256 * n + 2^16) ltac:(lia)). pose proof (C3 (256 * n + 2^16) ltac:(lia)). lia.
  Qed.
  Lemma fuzz_cost_mono : ltac2:(zQ "50!hk6!h9!hu2!hj4!ht3>0@2$4?5HCEIL?1H>1n$1>2n'$1>0@2$3@2$0Z^2@2$0^2^1@2$0@1$2^3@1$2^2").
  Proof.
    intros HH n n' Hn. npose (ah_costs H HH) as (C1 & C2 & C3 & C4 & _).
    unfold fuzz_cost. pose proof (C2 (256 * n + 2^16) (256 * n' + 2^16) ltac:(lia)). pose proof (C4 (256 * n + 2^16) (256 * n' + 2^16) ltac:(lia)). lia.
  Qed.

  Definition fuzz_post : ltac2:(zQ "b0!hue!ih1!h9!le!ik3!inb!iqa!ir3!hkb!irb!is4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s@1$7?1H>2LB@1$3$8>2LF@1$3$9>1N$2>2lo$2>1B$2>3shi$2>1m$a>2mo$5>0$4P") := ltac2:(zQ "j51!hue!ih1!isa!hj4!h9!le!jgb!hkb!m5!iqa!ir3!jh4!ji3!jic!jn0!jn8!n2!mc!jnf!jpc!jtd!jue!jvb!ik3!inb!kk4!kof!kp9!kq4!kqf!kr8!ks3!ksc!irb!is4!lh8!lle!hu2!lq3!lr1!lv0!mj4!mjb!mnf!mo5!ms9!nh3!nl9!no1!ja!np0!np5!npb&>0@1$1@1$0#k0@1$c@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$9@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s@1$a?1H\2LB@1$5$7\2LF@1$5$i1\1N$4\2lo$4\1B$4\3shi$4\1m$i2\2mo$h8\1c$h7@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2@1$a?1H\2s'@1$a?1H@2$2@1$5$7\3LB'@1$5$7@2$2@1$5@2$8$4$4\2XS@1$5@2$8$4$4@2$2@2$9@1$0#5@1$1@1$0#k0\2F'@2$9@1$0#5@1$1@1$0#k0@2$2@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@3$h2$h4@3$hf?1H^5@1$h6^h6@7$ib@hf$i9^j1^j0^if^ie^h5^h4^h3^id^ic@2$j4@1$0#k0Z^h2^h1^h0^f^e^d^c^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^b^a^9^8^2@1$ic^j1^1@1$f@1$1@1$0#k0^7@1$ie$6@2$3@1$i8^1@2$3@3$hb?1H^5^h6@2$3@3$hc?1H^h7@1$h5^h6@2$3@2$id$6^7@2$3@4$ia$6^7^hb@2$b@1$0#k0^j0@2$3@4$if$6^7@2$j1@2$b@1$0#k0^ie-q4@3$h0$e@1$i7^6@1$h1$e@2$3@3$i0?1H^7^ha@2$3@4$he?1H^5^4^7@2$3@3$j0$7^4^he@2$3@3$h3@2$8$4$4@3$h9?5HCEIL?1H^hd^3@2$3@7$i4?5HCEIL?1H^he@2$b@1$0#k0^j0^3^h8^7@2$3@3$hd?1H^hd^7@2$3@1$ha^7@2$3@1$i6^7@2$3@4$i3?5HCEIL^7^hb^h9@2$j2@2$d?1H^5@2$j3@2$d?1H^hf@1$i5^hc").

  Definition fuzz_stmt : ltac2:(zQ "00P") := ltac2:(zQ "kc1!hue!ih1!h9!hk6!jnf!jh4!m5!jgb!nq6!le!ja!npb!hl3!nqd!nr4!jtd!nrd!hkb!irb!jn0!nt9!ntf!hra!j4!jn8!n2!mc!hj4!isa!nv6!oh1!inb!iqa!kof!oh7!oi5!kp9!jic!oib!ojd!kqf!kr8!okb!ir3!s2!ks3!ol3!ksc!hlc!ole!is4!om9!oqf!or8!lh8!hqd!os7!ot4!ou3!ov1!pg0!pgb!hu2!phb!pi7!lq3!lr1!lv0!mj4!mjb!mnf!pj4!ms9!nh3!nl9!np5&@3$4@1$1@1$0#k0^i8@2$b@1$0#k0^9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$i0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$f>1m$j2>2mo$hf>1s@1$ib?1H>2LB@1$9$h1>2LF@1$9$h2>2CH@1$9@2$6$2$2>1D$2>1N$2>2lo$2>1B$2>3shi$2>2ds@1$9@1$1@1$0#8>4errv@1$1@1$0#k0>0@3$4$f@3$id?1H^b^e@7$k6@hf$k4^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0@2$b@1$0#k0$jd^f@1$h8@1$1@1$0#k0^d@1$k9$7>0@1$k3^h0>0~0>0~0>0@4$k7$7^h1^b^6>0@3$4$2@1$h6@2$c@1$1@1$0#8^7^b>0@2$h5^c@2$h7+2+ha>0@3$4$2@2$e^e+h0Z>0>0@2$3+1^e@2$hc$8\2pD$8@3$h4@2$6@2$6$8$2$2@4$d@2$6$8$2$2@4$d$8$2^1^h1^h0^h4>0>0@3$4$2^fZ@3$4$2^h1$j9>0@4$i9?1H^h5^h4^h7>0@3$i4?1H^h6@2$h0^h9^h7>0@2$3@2$a@1$j1^h6$ja@1$i7?1H>0@2$3@2$a@1$h6@2$c$h1^h7$j8@1$i6?1H>0>1c$2>0@2$hb@2$3+1^1@2$3^1+he@2$3@2$j0^ha^2$j7>0@3$if?1H^hc^h3>0@2$3@2$5@1$0#k0^je^h4>0@2$h5^h5@2$h7+2+k0>0@3$4$2@2$e@2$5@1$0#k0^k0+h0Z>0@4$k5$7^i0^h8@2$5@1$0#k0^k1>0@2$3@1$j4?5HCEIL^h9>0@2$3^ha@2$kb@2$5@1$0#k0^k3$jb>0@4$ka$7^i3@2$a@2$5@1$0#k0^k2-q4@3$h9$h3@1$k2^h7@1$ha$h3>0@2$k8$7^i4>0@3$4@1$1@1$0#k0^k4@2$b@1$0#k0$i3>0@1$k1^i6>0@3$4$2@2$e@2$5@1$0#k0^k9+2Z>0@1$i1^i8>0>0@2$3+1^i2@3$j5^ia^i4^i3>0@3$i8?1H^i6^ia>0@2$he@2$hd@2$c$h2^i7N3$i2>0@4$j6?5HCEIL^ic^i4^i2>0@2$3@2$5@1$0#k0^ke^i3>0@4$ie?1H^ie@2$5@1$0#k0^k9^i9>0@4$j3@1$ic?1H$jc@2$5@1$0#k0^l1^ia>0>3fp'$2>3ra'$2>0@3$h4@2$6$2$2@4$d$2$2^2^1^id@2$3@2$a@2$5@1$0#k0^l4+h0^3>0$k0>0@2$3@1$je^ib@2$i5?1H^j0@3$ia?1H@hb$jf^l5^l4^l3^l2^ke^kd^k4^k3^k2^k1^k0^jf^je^jd^jc^jb^j6^j5^j1^j0^if^ic^ib^ia^i9^j3^j2@2$h0^j4^j2").
End W.

End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
