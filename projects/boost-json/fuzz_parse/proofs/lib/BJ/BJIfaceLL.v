(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJIface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44list3h5LinuxProcessSemanticsfLinuxProcessSem3Runm36config3h5LinuxProcessSemanticsfLinuxProcessSem5Statep85Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~se5blockse3mem37Corelib4Init5Logichi62exhi63andk46optionm39cfg_model3h5LinuxProcessSemantics5Riscv7Preludehlc5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hob6PStatek44Nonehi62eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshtedmachine_statem36cfg_ms79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJFrame~~~~~~iif5xpres79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJIface~~~~~~in5bbj_env_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~is16EH_IVSis17hs_KRELis18hs_MPRESis18hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~jj04frm079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jn13mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jr42MSjr46ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kg17seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kkb2wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~koc5rsegshfbbv_unsignedm35mkCfgin5aRLLVM_FUZZin5h0RLLVM_FUZZ_STACKin56bj_envin58input_ok89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ9BJIfaceLL5Iface~~~~~~li0fllvm_fuzz_post2is1aeh_base_okis15frameis15hs_SR46Stdlib6ZArith6BinInt1Zlp82ltlp83powlp83subis13hmfis13ehk" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!ls4$0").
  Variable E : ltac2:(zQ "10!lsb$0").
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).

  Definition llvm_fuzz_post2 : ltac2:(zQ "80!h9!jc!k1!lc!of!s6!hh8!hi0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$6>2lo$2>1B$2>1m$7>2mo$5>0$4P") := ltac2:(zQ "i01!h9!jc!hja!hk0!hk7!k1!hl0!ho2!hs7!ht1!lc!ht8!ih5!ii6!of!s6!imc!ir2!jg3!jgd!jh8!ji4!jm9!jqd!jv1!jv7!kk0!ko6!hh8!hi0!ks8!kt1&>0@1$1@1$0#k0@1$4@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$a$hc\2lo$5\1B$5\1m$hd\2mo$f\1c$e@2$2@1$1@1$0#k0\3gp'@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$8\2s'$8@2$2@2$7@1$0#5@1$1@1$0#k0\2F'@2$7@1$0#5@1$1@1$0#k0@2$2@1$1@1$0#i0\3fc'@1$1@1$0#i0@2$3@3$b$c@1$d^h4@7$h8@hf$h7^i9^i8^h3^i7^h2^h1^h0^i6^i5@1$hbZ^f^e^d^c^b^a^9^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^8^7^6^5^2@1$h9^i9^1@1$9@1$1@1$0#k0^4@1$ha$he@2$3@1$h6^1@2$3@3$h3?1H^3@1$6^h4@2$3@3$h4?1H^h5@1$6^h4@2$3@4$h5?1H^3^h9^4@2$3@7$h1?1H?1E^4^i8^i7^h8^h7@5$h0^h9@2$hf@1$0#k0^i8$h2^h6^4").

  Definition llvm_fuzz_stmt2 : ltac2:(zQ "00P") := ltac2:(zQ "he0!h9!jc!kt1!k1!ht1!lc!ktf!s6!ho2!ku7!kv5!lga!lh4!lm5!ln8!lo6!jgd!ji4!lof!jqd!jv1!kk0!ko6!hh8!hi0!ks8!hs7!lr0!lr6!lrd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$8@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h8>1s$ha>4REST@1$5$h7>2lo$3>1B$3>4errv@1$1@1$0#k0>2mo$7>3top$f>0@4$h1?1H^7^6^8>0@3$h0?1H^8^3>0@b$b?5HCEIL?1H?1E^a^ia^i8^7^6@1$a?1E^5^b>0@5$c^9^ib^b@2$2@1$0#k0^i3@2$2@1$0#k0^i2>0@2$hb@2$2@1$0#k0^i3@2$hc+2+ha>0@2$e?1E@2$hd@2$2@1$0#k0^id+h0@3$h2?1H@h5$d^if^ie^ic^i8^i7^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^f^c^b^a^e^8@2$6@7$h4@hf$h3^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0@1$h6$9^f@1$4@1$1@1$0#k0^e@1$h5$h9^8").
End Iface.
