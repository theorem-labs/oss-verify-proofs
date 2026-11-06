(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge Frame TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsWalk.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44list3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm3dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeqa5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~t83mem37Corelib4Init5Logichhb2exhhb3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hjc5asegsk44consk44prodk43nilk46optionk44pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hq44cellhf7Z_to_bvk44Nonehhb2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsConst~~~~~~hvf6ACONSThq42CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ikc3mkRikc5munchikc3stkikc5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~iq82MSiq86ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~iv58bytes_ativ57mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jk67seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jp08rw_cells46Stdlib6ZArith6BinInt1Zjt73addjt73subjt76to_nat" s.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition amove_post : ltac2:(zQ "70!h9!jc!k1!lc!pa!t0!hh5>2ra@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2SP$2>3Dst$2>3Src$2>1N$2>3src@1$3@1$1@1$0#8>2lo$2>1m$6>0$4P") := ltac2:(zQ "i21!h9!jc!hif!k1!hj5!hn7!ho0!ho7!hoe!hp4!hpd!pa!hu0!hu8!hv2!lc!hv9!t0!ijc!hh5!ik6!io8!iof!ip8!ipf!iu5!iub!jif!jjb!jo5!jsb!juf!jv6!jvd&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h1@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2SP$3\3Dst$3\3Src$3\1N$3\3src@1$f@1$1@1$0#8\2lo$3\1m$h3\3ms'$b@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$4@3$h0$b^h0@7$h9@hf$h5^i8@2$d@1$0#k0^h7^i7^i6^f^e^d^i5^i4@2$d@1$0#k0^h6^c^b^a^9^8^7^6^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^5^4^3^2^h9@1$ha^i8^h8@1$e@1$1@1$0#k0^1@1$hd$5@2$4@3$h6@3$6@2$7$3$3@4$a$3$3^h6@2$hf^h6^h4@3$6@2$7$3$3@4$a$3$3@2$i0^h7+hgg0^h7@1$8@2$7$3$3^h1^1@2$4@3$h8$5^h1^1@2$4@2$hc$5^1@2$4@4$h7$5^1^h2^h7@2$4@4$he$5^1^h6@3$6$c@2$h4@1$i1^h4^h3@1$8$c@2$4@4$hb$5^1^h5^h3@1$h2^1").


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CallsZ.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)

End CallsZ.
(* [comment removed for export] *)
