(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep ITree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~hcdRMALLOC_STACK46Stdlib6ZArith6BinInt1Zn73add04Npos35stdpp9bitvectorbdefinitionspb2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~rd6PState37Corelib4Init9Datatypeshg24listhg26option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshicdmachine_state3h5LinuxProcessSemantics5Riscv7Preludehn45bvmaphc5blockhc3memrd4bptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hr84cellhg24conshg23nil37Corelib4Init5Logicigb3andhic6ms_memhr82C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ij68rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh5RF_aligned_alloc_stmt~~~~~~indh0RMALLOC_REPLACEDhccrmalloc_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~iuf5rsegspb7Z_to_bvn72lepbbbv_unsignedigb2eqhg24None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~jm05hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jq43mkRjq43stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jue2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kj17mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kn67seg_rom99OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh5RF_aligned_alloc_stmt2HC5Iface~~~~~~ks0fraligned16_postindh2RALIGNED_ALLOC_SYMindeRALIGNED_STACKhc4RATP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~lla5implMrdaraw_mallocn72ltn73pown73sub" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RALIGNED_ALLOC_SYM : Z := 0xdfc08.     (* [comment removed for export] *)
    (* [comment removed for export] *)
Definition RALIGNED_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!m7!of@2$1$0+i0").
Definition RMALLOC_REPLACED : Z := 0x12f3a8.      (* [comment removed for export] *)

Section HC.
  Context {HCEIL : HeapCeil}.

Section Iface.
  Context (RHEAP : PState -> list block -> mem -> Prop)
          (rauxv_ok : mem -> Z -> Prop)
          (raddr_exposed : PState -> Z -> Prop).

Definition raligned16_post : ltac2:(zQ "b0!p5!r8!h9!v9!hha!hi2!hm3!hpa!hq3!hqb!hr1>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$3>2LB@1$4$8>1n$2>2lo$2>1B$2>1m$9>1r@1$5$a>2s'$3>0$6P") := ltac2:(zQ "h60!p5!r8!h9!hv4!v9!hvc!hha!ig4!hi2!ihf!hm3!ii6!hpa!ij0!in1!isb!hq3!hqb!iu0!jic!hr1!jj5\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$c@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$4\2LB@1$6$h0\1n$2\2lo$2\1B$2\1m$h1\1r@1$8$h4\2s'$4\3ms'$a@2$9@hf$h2?5HCEIL?5RHEAP?8rauxv_ok?draddr_exposed^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@4$e$h3@1$b^1$f@3$5$3@1$d@2$h5@1$0#k0Z@1$7$3").

Definition raligned16_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i70!p5!r8!jic!jj5!hv4!jjf!jk4!jl2!h9!hvc!ig4!ij0!in1!v9!jl8!hha!hi2!ihf!hpa!jpb!ju0!ju7!kib!kmb!kr5!lh7!lia!lk1!isb!ll3!hq3!hqb!lp7!hr1!lq0!of!lqd!lr2!lr8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h2@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$hf>1s$d>2LB@1$f$he>1n$8>2lo$8>1B$8>4errv@1$1@1$0#k0>0@3?5RHEAP^6^5^7>0@2?8rauxv_ok^8^3>0@2$5@2$6@1$0#k0^i9^4>0@4$h5$2^a^6@2$6@1$0#k0^ia>0@2$5@1$h3?5HCEIL^7>0@2$5^8@2$i6@2$6@1$0#k0^ic$hb>0@4$c$2^d@2$i3@2$6@1$0#k0^ib-q4@3$9$4@1$b^7@1$a$4>0@4$c$2^e$hc@3$9$4@1$b@2$3@1$0#k0Z@1$a$4>0@2$h7$2^f>0@3$7@1$1@1$0#k0^ie@2$3@1$0#k0$hd>0@3$7@1$1@1$0#k0^i9@2$3@1$0#k0+h0>0@3$7@1$1@1$0#k0^i9@2$3@1$0#k0^f>0@2$h1@2$5Z^h0@2$i4^h0@2$i5+2+i0@7$i0$d$2@1$h0$i1@2$i2?5HCEIL^h1^h3@h8$h9^j5^j4^j3^j2^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^h6^h5^h3^h2^h1^h0^f^h4@7$h6@hf$h4^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6@2$3@1$0#k0$ha^h5@1$e@1$1@1$0#k0^h4@1$h8$2").
End Iface.
End HC.
(* [comment removed for export] *)
