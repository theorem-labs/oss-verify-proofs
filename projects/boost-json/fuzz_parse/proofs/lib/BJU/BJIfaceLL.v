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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJIface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44list3h5LinuxProcessSemanticsfLinuxProcessSem3Runm36config3h5LinuxProcessSemanticsfLinuxProcessSem5Statep85Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~se5blockse3mem37Corelib4Init5Logichi72exhi73andk46optionm39cfg_model3h5LinuxProcessSemantics5Riscv7Preludehld5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hoc6PStatek44Nonehi72eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshtfdmachine_statem36cfg_ms79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJIface~~~~~~ij0bbj_env_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~ind4frm079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ire3mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jg12MSjg16ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jke7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~jp82wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7BJFrame~~~~~~jt95xpres79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~ki16EH_IVSki17hs_KRELki18hs_MPRESki18hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~kp25rsegshfbbv_unsignedm35mkCfgij0aRLLVM_FUZZij0h0RLLVM_FUZZ_STACKij06bj_envij08input_ok89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU9BJIfaceLL5Iface~~~~~~li7fllvm_fuzz_post2ki1aeh_base_okki15frameki15hs_SR46Stdlib6ZArith6BinInt1Zlq02ltlq06modulolq03powlq03subki13hmfki13ehk" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!lt6$0").
  Variable E : ltac2:(zQ "10!ltd$0").
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).

  Definition llvm_fuzz_post2 : ltac2:(zQ "80!h9!jc!k1!lc!of!s6!hh9!hi1>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$6>2lo$2>1B$2>1m$7>2mo$5>0$4P") := ltac2:(zQ "i01!h9!jc!hjb!hk1!hk8!k1!hl1!ho3!hs8!ht2!lc!ht9!ih6!ii7!of!s6!ime!ir6!iva!jje!jk4!jod!jt3!kh8!km5!kmf!kna!ko6!hh9!hi1!ksf!kt8&>0@1$1@1$0#k0@1$4@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$a$hc\2lo$5\1B$5\1m$hd\2mo$f\1c$e@2$2@1$1@1$0#k0\3gp'@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$8\2s'$8@2$2@2$7@1$0#5@1$1@1$0#k0\2F'@2$7@1$0#5@1$1@1$0#k0@2$2@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@3$b$c@1$d^h4@7$h3@hf$h2^i9^i8^h3^i7^h2^h1^h0^i6^i5@1$h6Z^f^e^d^c^b^a^9^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^8^7^6^5^2@1$h4^i9^1@1$9@1$1@1$0#k0^4@1$h5$he@2$3@1$h1^1@2$3@3$h9?1H^3@1$6^h4@2$3@3$ha?1H^h5@1$6^h4@2$3@4$hb?1H^3^h9^4@2$3@7$h0?1H?1E^4^i8^i7^h8^h7@5$h7^h9@2$hf@1$0#k0^i8$h8^h6^4").

  Definition llvm_fuzz_stmt2 : ltac2:(zQ "00P") := ltac2:(zQ "i00!h9!jc!kt8!k1!ht2!lc!ht9!ku6!s6!ho3!kue!kvc!lh1!lhb!lmd!iva!jje!jod!jt3!lo0!loe!kmf!ko6!lp7!hh9!hi1!ksf!hs8!lr8!lre!ls8!lsf>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h9>1s$hb>4REST@1$5$h8>2lo$3>1B$3>4errv@1$1@1$0#k0>2mo$8>3top$h4>0@4$h6?1H^7^6^8>0@3$h5?1H^8^3>0@b$c?5HCEIL?1H?1E^a^ia^i8^7^6@1$b?1E^5^b>0@5$d^9^ib^b@2$2@1$0#k0^i3@2$2@1$0#k0^i2>0@2$hc@2$2@1$0#k0^i3@2$he+2+ha>0@2$h3?1E@2$hf@2$2@1$0#k0^id+h0>0@3$6$3@2$hd@2$2@1$0#k0^ie+h0Z@3$h7?1H@h5$e^j0^if^id^i9^i8^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h0^d^c^b^f^9@2$7@7$h0@hf$f^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1@1$h2$a^h0@1$4@1$1@1$0#k0^f@1$h1$ha^9").
End Iface.
