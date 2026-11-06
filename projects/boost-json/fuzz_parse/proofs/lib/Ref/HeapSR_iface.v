(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hcdRMALLOC_STACK46Stdlib6ZArith6BinInt1Zn63add37Corelib4Init9Datatypesp44listhc5blockhc8blk_size36Stdlib5Lists4Lists6afold_right3h5LinuxProcessSemanticsfLinuxProcessSem3Runu66config79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefcHeapSR_iface~~~~~~hhb5hs_SR04Npos35stdpp9bitvectorbdefinitionshmd2bv37Corelib4Init5Logichp03andhp02eqp44prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshr8dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Stateig05Modelp44Nonep43nilp46optionu69cfg_modelu66cfg_msu65mkCfgig08m_haltedig09m_vm_lazy79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~io33evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~is55rsegshhb7hs_KREL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~jh56PStatehhb8hs_MPRESn62lep46lengthhhbfhs_LIVE_CNT_MAXhhbbhs_LIVE_MAXhhb8hs_RHEAPhhbbhs_alloc_okhhb8lb_byteshc3memn66of_nathch0RHEAP_frame_stmthch6RHEAP_block_range_stmthchaRHEAP_blocks_disjoint_stmthch7RHEAP_blocks_nodup_stmthhbbhs_rauxv_okhch3rauxv_ok_frame_stmtjh54bptrhhbchs_lb_removep44conss62Inp44pairhp03nothc6blk_id37Corelib5Lists7ListDefkp53map3h5LinuxProcessSemantics5Riscv7Preludekr35bvmaphp02ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ku84cellhmdbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ljb8rw_cellsku82C4ku82CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~loe3mkRloe3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lt82MSlt86ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mi57mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mma7seg_romhccrblock_rangehcarheap_presn66to_nathmd7Z_to_bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~mu45hceil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefcHeapSR_iface5Iface~~~~~~ni8emalloc_sr_posthc4RATPn62ltn63pown63subni8h1malloc_sr_stmt_athcbRMALLOC_SYMhhb6ROPNEWhhbcROPNEW_STACKni8cfree_sr_posthcbRFREE_STACKni8ffree_sr_stmt_athc9RFREE_SYMhhb6ROPDELhhb7ROPDEL2ni8fopdel_null_postni8h5opdel_null_sr_stmt_atni89KREL_lawsni8aMPRES_lawsni8h1RHEAP_block_rangeni8h5RHEAP_blocks_disjointni8h2RHEAP_blocks_nodupni8bRHEAP_frameni87SR_lawsni8h0alloc_ok_of_liveni8cfree_sr_stmtni8elb_remove_lawsni8emalloc_sr_stmtni8eopdel2_sr_stmtni8dopdel_sr_stmtni8dopnew_sr_stmtni8brauxv_framehhb3hsr" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROPNEW   : Z := 0xf00d0.   (* [comment removed for export] *)
Definition ROPDEL   : Z := 0x94490.   (* [comment removed for export] *)
Definition ROPDEL2  : Z := 0x94494.   (* [comment removed for export] *)
Definition ROPNEW_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!m6!oe@2$1+h0$0").   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lb_bytes : ltac2:(zQ "30!qc!h9!r3>2LB@1$0$2$1") := ltac2:(zQ "60!r3!h9!qc!rb!t9!oe\2LB@1$2$0@5$4$1$0\1b$0\3acc$1@2$5@1$3^2^1Z^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Record hsr := {
  hs_SR       : (config -> Prop) -> config -> Prop ;
  hs_KREL     : PState -> Model -> Prop ;
  hs_MPRES    : Model -> Model -> Prop ;
  hs_RHEAP    : PState -> list block -> mem -> Prop ;
  hs_rauxv_ok : mem -> Z -> Prop ;
  hs_lb_remove : bptr -> list block -> list block ;
  hs_alloc_ok : PState -> list block -> Z -> Prop ;
  hs_LIVE_MAX : Z ;          (* [comment removed for export] *)
  hs_LIVE_CNT_MAX : Z       (* [comment removed for export] *)
}.

Section Iface.
  Context {HCEIL : HeapCeil}.   (* [comment removed for export] *)
  Variable H : ltac2:(zQ "10!pm0$0").
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).  Notation rauxv_ok := (hs_rauxv_ok H).  Notation lb_remove := (hs_lb_remove H).
  Notation alloc_ok := (hs_alloc_ok H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition SR_laws : ltac2:(zQ "00P") := ltac2:(zQ "h41!hh2!hle!hm7!hoa!hq4!hqb!hr1!huf!iie!ij7!qc!ije!ik4!ikd!il9!im2!ima!in6!ire!jg1&@2$6@1$3@1$2#k0@1$3@1$2#k0@2$4>1Q>0$0P>1c$0>0@1^2^1@3$1?1H^3^2@2$4>1Q>0$0P>2Q'>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@1^5^2@3$1?1H^4^3@2$4>2Q1>0$0P>2Q2>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@3$1?1H^5^2@3$1?1H^4^3>1P>0$7P>2ms$7>2mo$8>0@3$5@1$c@1$3@1$2#k0@1$h0^1@1$9@1$3@1$2#k0>0@3$5@1$a~0@1$h1^2@1$b~0>0@3$h2$h3^5^4@3$1?1H\1c$0@2$4@1^7@1$e^1@3$5$8@1$d^1^5@2$f^5^4").

  Definition KREL_laws : ltac2:(zQ "00P") := ltac2:(zQ "e1!hm7!hoa!hr1!hqb!ij7!qc!ije!ik4!hq4!iie!ima!in6!jga!jl1&@2$2@1$1@1$0#k0@1$1@1$0#k0>1s$d>2mo$9>0@3$c?1H^2^1@2$8@3$3@1$7@1$1@1$0#k0@1$a^2@1$4@1$1@1$0#k0@3$3@1$5~0@1$b^2@1$6~0").

  Definition MPRES_laws : ltac2:(zQ "00P") := ltac2:(zQ "30!iie!jlb!hq4@2$2>2mo$0@3$1?1H^1^1>3mo1$0>3mo2$0>3mo3$0>0@3$1?1H^3^2>0@3$1?1H^3^2@3$1?1H^5^3").

  (* [comment removed for export] *)
  Definition alloc_ok_of_live : ltac2:(zQ "00P") := ltac2:(zQ "e0!jm7!r3!oe!jmc!qc!h9!jn5!jo8!jp7!jq3!jr2!jre!jl1!js4>1s$c>2LB@1$4$1>1m$b>1n$5>0@4$8?1H^4^3^2>0@2$0Z^2>0@2$0@2$2@1$a^5^3@1$7?1H>0@2$0@2$2@1$d@2$3$1^6+1@1$6?1H@4$9?1H^8^7^5").

  (* [comment removed for export] *)
  Definition RHEAP_frame : ltac2:(zQ "00P") := ltac2:(zQ "20!jp7!jsd@2$1?5HCEIL@1$0?1H").
  Definition RHEAP_block_range : ltac2:(zQ "00P") := ltac2:(zQ "20!jp7!ju1@2$1?5HCEIL@1$0?1H").
  Definition RHEAP_blocks_disjoint : ltac2:(zQ "00P") := ltac2:(zQ "20!jp7!jvb@1$1@1$0?1H").
  Definition RHEAP_blocks_nodup : ltac2:(zQ "00P") := ltac2:(zQ "20!jp7!kh9@1$1@1$0?1H").
  Definition rauxv_frame : ltac2:(zQ "00P") := ltac2:(zQ "20!kj4!kk3@1$1@1$0?1H").
  (* [comment removed for export] *)
  Definition lb_remove_laws : ltac2:(zQ "00P") := ltac2:(zQ "e0!r3!kla!h9!qc!km2!kn2!hr1!hqb!kn9!kne!hq4!ko5!koc!kqc@2$a>1p$1>1A$2>1n$2>2LB@1$3$0>0@1$b@3$8$1^4@4$d$0$1$c^1@3$7@1$3$0@3$4?1H^5@3$5@2$6@2$6$1$2$2@4$9@2$6$1$2$2@4$9$1$2^5^4^3^2^2@2$a>1p$1>1b$0>2LB@1$3$0>0@1$b@3$7$1@1$c^2^3@3$7@1$3$0@3$4?1H^4@3$5$0^3^2@3$5$0^3@3$4?1H^4^2>1p$1>2LB@1$3$0>1b$0>0@3$8$0^1@3$4?1H^3^2@3$8$0^2^3").

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition malloc_sr_post : ltac2:(zQ "a0!hm7!hoa!h9!qc!hh2!iie!kt9!r3!jre!jl1>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$9>2LB@1$3$7>1n$2>2lo$2>1B$2>1m$8>2mo$5>0$4P") := ltac2:(zQ "ic1!hm7!hoa!ku2!hq4!h9!jg1!kla!li4!kn2!qc!hr1!jl1!lic!ije!ik4!kne!ikd!ln6!ij7!hqb!huf!il9!hh2!iie!kt9!lo2!lo8!lsa!lt1!mh5!mhb!mlf!mq9!jga!jlb!jp7!kj4!r3!jre!mr4!ms3!oe!mt0!mt9&>0@1$1@1$0#k0@1$e@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$b\2LB@1$9$i5\1n$4\2lo$4\1B$4\1m$i6\2mo$h7\1c$h6@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2$4\1A$4@2$2@1$9@1$1@1$0#8\4junk@1$9@1$1@1$0#8@2$2$6\1p$6@2$2$b\2s'$b@2$3@3$h3$h4@1$h5^h5@7$hd@hf$hb^ie^id^ic^ib^h4^h3^h2^ia^i9@2$ib@1$0#k0^4^h1^h0^f^e^d^c^b^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^a^9^8^7^he@1$he^ie^hd@1$h2@1$1@1$0#k0^6@1$i0$5@2$3@3$i1?1H^1@1$h0^h5@2$3@3$i2?1H^h6@1$h0^h5@2$3@2$hf$5^6@2$3@4$hc$5^6^h9@2$c@1$0#k0^id@2$3@4$h1$5^6@2$i9@2$c@1$0#k0^ib-q4@3$8$7@1$h9^5@1$d$7@2$3@3$i4?1H^6^h8@2$3@4$i8^hb@2$c@1$0#k0^id^h7^6@2$3@3$i7?5HCEIL^4^ha@2$3@4$i3?1H^1@3$8@2$a@2$a$6$4$4@4$f@2$a$6$4$4@4$f$6$4^2^4^ha^hb^6@4$h1$5^6^4@3$8$7@2$ha@1$ia^ha^3@1$d$7").

  Definition malloc_sr_stmt_at : ltac2:(zQ "10!h9>5entry$0>5stack$0P") := ltac2:(zQ "i70!hm7!hoa!h9!jg1!jm7!lic!mt9!hqb!li4!ij7!kn2!qc!ije!hq4!im2!iie!kt9!nhf!lo2!lsa!lt1!mh5!mlf!mq9!ln6!nn1!jga!jp7!hle!jq3!kj4!no3!r3!jre!jl1!oe!noa!nof!np5\5entry$2\5stack$2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i1>1s$i2>2LB@1$b$i0>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>2mo$f>0@4$hb?1H^7^6^8>0@3$ha?1H^8^2>0@4$hd?1H^9^8^7>0@3$he?1H^b^6>0@2$4@2$5@1$0#k0^ic^7>0@4$h4$3^d^9@2$5@1$0#k0^id>0@2$4@1$h1?5HCEIL^a>0@2$4^b@2$i6@2$5@1$0#k0^if^j1>0@4$h8$3^h0@2$i3@2$5@1$0#k0^ie-q4@3$a$8@1$h2^a@1$c$8>0@2$h6$3^h1>0@3$7@1$1@1$0#k0^j0@2$6@1$0#k0$hf>0@3$7@1$1@1$0#k0^ib@2$6@1$0#k0^h0>0@2$d@2$4+1^h1@2$i4^h1@2$i5+2+i0@3$hc?1H@h9$h9^j6^j5^j4^j3^if^ie^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^h7^h6^h4^h3^h2^h1^h0^h5^e@2$e@7$h5@hf$h3^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7@2$6@1$0#k0^j8^h6@1$9@1$1@1$0#k0^h5@1$h7$3^e").

  Definition malloc_sr_stmt : ltac2:(zQ "00P") := ltac2:(zQ "30!npb!m6!nr1@2$0$2$1").
  (* [comment removed for export] *)
  Definition opnew_sr_stmt : ltac2:(zQ "00P") := ltac2:(zQ "30!npb!nrf!ns9@2$0$1$2").

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition free_sr_post : ltac2:(zQ "b0!hm7!hoa!h9!qc!hh2!iie!kt9!r3!jre!jl1!kla>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$9>2LB@1$3$7>1p$a>2lo$2>1B$2>4errv@1$1@1$0#k0>1m$8>2mo$5>0$4P") := ltac2:(zQ "i71!hm7!hoa!ku2!hq4!jg1!jl1!lic!ik4!h9!ikd!li4!km2!ij7!kn2!qc!ije!hqb!huf!il9!hh2!iie!kt9!lo2!lsa!lt1!mh5!mhb!mlf!mq9!ln6!jga!jlb!jp7!kj4!r3!jre!ms3!kla!oe&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h5@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$5\2LB@1$e$i2\1p$i5\2lo$8\1B$8\4errv@1$1@1$0#k0\1m$i3\2mo$h4\1c$h3@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$5\2s'$5@2$3@3$h0$h1@1$h2^h2@7$h9@hf$h7^ic^ib^ia^i9^h1^h0^f^i8^i7^e^d^c^b^a^9^8^7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^6^5^4^3^hc@1$ha^ic^hb@1$c@1$1@1$0#k0^2@1$hc$4@2$3@3$he?1H^1@1$9^h2@2$3@3$hf?1H^h3@1$9^h2@2$3@2$hb$4^2@2$3@4$h8$4^2^h7@2$6@1$0#k0^ib@2$3@4$hd$4^2@2$i6@2$6@1$0#k0^i9-q4@3$d$a@1$h6^h5@1$f$a@2$3@3$i1?1H^2^h6@2$3@4$i4@3$b?1H^h8^h9@2$6@1$0#k0^ib^h4^2@4$i0?1H^1@3$b?1H^h8^h9^2").

  Definition free_sr_stmt_at : ltac2:(zQ "10!h9>5entry$0P") := ltac2:(zQ "i80!hm7!hoa!h9!jg1!kla!lic!hr1!jm7!mt9!kne!hqb!li4!ij7!kn2!qc!ije!im2!iie!kt9!nhf!lo2!lsa!lt1!mh5!mlf!mq9!ln6!nt9!jga!jp7!hle!kj4!no3!nu9!r3!jre!jl1!kn9!oe!np5\5entry$2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h2@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i3>1s$i4>2LB@1$e$i2>1p$4>1A$2>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>2mo$h1>0@4$hd?1H^9^8^a>0@3$hc?1H^a^2>0@3$i5@2$6@2$6$4$2$2@4$9@2$6$4$2$2@4$9$4$2^9^8^7^a>0@3$hf?1H^d^6>0@2$7@2$5@1$0#k0^ie^7>0@4$h6$3^f^9@2$5@1$0#k0^if>0@2$7@1$h3?5HCEIL^a>0@2$7^b@2$i7@2$5@1$0#k0^j1$i1>0@4$ha$3^h2@2$i6@2$5@1$0#k0^j0-q4@3$d$b@1$h4^a@1$f$b>0@2$h8$3^h3>0@3$a@1$1@1$0#k0^j2@2$8@1$0#k0$i0>0@3$a@1$1@1$0#k0^id@2$8@1$0#k0^h1@3$he?1H@ha$hb^j7^j6^j5^j4^j0^if^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^h8^h7^h5^h4^h3^h0^f^e^h6^d@2$h0@7$h7@hf$h5^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@2$8@1$0#k0^j8^h7@1$c@1$1@1$0#k0^h6@1$h9$3^d").

  Definition free_sr_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!nv7!oga@1$0$1").
  Definition opdel_sr_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!nv7!oh6@1$0$1").       (* [comment removed for export] *)
  Definition opdel2_sr_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!nv7!oi0@1$0$1").     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition opdel_null_post : ltac2:(zQ "60!hm7!hoa!hh2!iie!kt9!jre>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$5>2mo$3>0$2P") := ltac2:(zQ "h10!hm7!hoa!hqb!iie!ij7!hq4!huf!ikd!il9!hh2!kt9!lsa!mh5!mhb!mq9!jre!jg1\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2t0@1$1@1$0#k0\2t1@1$1@1$0#k0\2t2@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2a0@1$1@1$0#k0\2a1@1$1@1$0#k0\2a2@1$1@1$0#k0\2a3@1$1@1$0#k0\2a4@1$1@1$0#k0\2a5@1$1@1$0#k0\2a6@1$1@1$0#k0\2a7@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2t3@1$1@1$0#k0\2t4@1$1@1$0#k0\2t5@1$1@1$0#k0\2t6@1$1@1$0#k0\1F@2$a@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$f\2mo$3\1c$9@2$5@3$2$6@1$8^1@7$c@hf$b^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5@1$d^i4^4@1$4@1$1@1$0#k0^3@1$e$h0@3$2$3@1$7^1^2").
  Definition opdel_null_sr_stmt_at : ltac2:(zQ "10!h9>5entry$0P") := ltac2:(zQ "h61!hm7!hoa!mt9!ij7!hr1!hqb!qc!ije!ik4!h9!im2!iie!ima!in6!kt9!lsa!mh5!mq9!oib!hle!jre!jg1&@2$4@1$1@1$0#k0@1$1@1$0#k0\5entry$9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$e@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h4>2mo$b>0@3$5@1$8@1$1@1$0#k0@1$c^1@1$3@1$1@1$0#k0>0@3$5@1$6~0@1$d^2@1$7~0@3$h3?1H@i3$h2^i4^i3^i2^i1^i0^hf^he^hd^hc@2$2@1$0#k0Z^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3@2$a@7$h0@hf$f^i4^i3^i2^i1^i0^hf^he^hd^hc@2$2@1$0#k0Z^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6@2$2@1$0#k0^i5^5@1$3@1$1@1$0#k0^4@1$h1$h5^3").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heap_sr_hyps : ltac2:(zQ "00P") := ltac2:(zQ "h30!hq4!oje!ol8!om5!on3!oo9!oq3!ora!os9!ot4!ou9!ov9!pgb!phd!pif!pk0!pl1!oh6!oi0@2$0$8@2$0$2@2$0$3@2$0$9@2$0$7@2$0$4@2$0$5@2$0$6@2$0$h0@2$0$b@2$0$c@2$0$f@2$0$a@2$0$e@2$0$d@2$0@1$1$h1@1$1$h2").
End Iface.

(* [comment removed for export] *)
