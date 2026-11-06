(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import STRW_tac.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehe7Segment99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegsdAgentMemImage5Agent~~~~~~ldfloaded_segments37Corelib7Numbers7BinNumsrf4Npos35stdpp9bitvectorbdefinitionstf2bv06option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshg9dmachine_state3h5LinuxProcessSemantics5Riscv7Preludehl15bvmap37Corelib4Init5Logicho02exrf1Ztfbbv_unsignedho03and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaF_memcpy_A~~~~~~hr35asegs04cons03nil04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ih04cell04None04pairho02eqih02CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~imc3mkRimc5munchimc5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~is12MSis16ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jge8bytes_atjge7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jlf7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jq98rw_cells46Stdlib6ZArith6BinInt1Zjv03addjv06to_nat" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Definition asegs : ltac2:(zQ "20!h8!l3@1$0$1") := ltac2:(zQ "10!qd$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memcpy_post : ltac2:(zQ "60!t8!vc!h8!hg1!hk0!hn7>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>3src@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>0$4P") := ltac2:(zQ "he1!t8!vc!hp4!hpa!hpe!hqc!hv6!hg1!hvf!ig5!iga!hk0!ikc!il4!h8!ila!im0!hn7!im6!iq8!iqf!ir8!ive!jg4!jk8!jl4!jpe!ju4!kg8!kgf&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h1@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2a0@1$1@1$0#k0\2a1@1$1@1$0#k0\2a2@1$1@1$0#k0\3src@1$e@1$1@1$0#8\1m~0\3ms'$b@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$5@3$h0$b^h0@7$h6@hf$h3^i7^i6^i5^i4^f^e^d^i3^i2^h5^c^b^a^9^8^7^6^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^5^4^3^2^h7@1$h7^i7^h6@1$d@1$1@1$0#k0^1@1$ha$6@2$5@3$h4@3$8@2$a$3$3@4$f$3$3@2$4@1$0#k0^h5@2$hc@2$4@1$0#k0^h5@2$4@1$0#k0^h3@1$9@2$a$3$3^h1^1@2$5@3$h5$6^h1^1@2$5@2$h9$6^1@2$5@4$hb$6^1@2$4@1$0#k0^h5@3$8$c@2$h2@1$hd@2$4@1$0#k0^h3^h2@1$9$c@4$h8$6^1@2$4@1$0#k0^h4^h2").

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation INV := (mc_inv asegs S D src W m).
  Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
(* [comment removed for export] *)


End Proofs.
(* [comment removed for export] *)
