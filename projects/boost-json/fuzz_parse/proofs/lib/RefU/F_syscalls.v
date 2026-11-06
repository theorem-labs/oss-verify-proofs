(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ITree Nodes SysStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Export RSegs.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm5dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeqc5bvmap37Corelib4Init5Logicta2exhfbbv_unsignedta3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hg75rsegs46Stdlib6ZArith6BinInt1Zhkd3addk14consk14prodk13nilk14pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ho74cellk14Noneta2eqho72C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~htd3mkRhtd5munchhtd3stkhtd5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ij92MSij96ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~io67mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~isb7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jh58rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib7SysStep~~~~~~jlccsysret_errnojlcasysret_valhkd3subhkd2leta2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jsa3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaF_syscalls~~~~~~kgcbsysret_posthf7Z_to_bv" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post : ltac2:(zQ "60!h9!jc!l9!m2!pc!t2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1r@1$1@1$0#k0>4errv@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2lo$3>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>0$4P") := ltac2:(zQ "hf1!h9!jc!ue!m2!v3!hg1!hk4!hm5!hmc!l9!hn3!hna!ho0!pc!hs3!hsb!ht2!t2!ht7!ih9!ii0!ii9!ij0!in6!inc!is0!jga!jl0!jpa!jqa!jr8&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1r@1$1@1$0#k0\4errv@1$1@1$0#k0\1F@2$h1@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2lo$3\1m~0\3ms'$d@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$5@3$h0$d^h0@7$h7@hf$h3^i6^i5^i4^i3^f^e^d^i2^i1@1$hd^h6^c^b^a^9^8^7^6^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^5^4^3^2^h4@1$h8^i6^h3@1$f@1$1@1$0#k0^1@1$ha$6@2$5@3$h4@3$8@2$a$3$3@4$c$3$3@2$he@2$4@1$0#k0^i5+h0@2$4@1$0#k0^i5@3$8@2$a$3$3@4$c$3$3@2$7@2$4@1$0#k0^i3-q4@2$7@2$7@2$4@1$0#k0^i3-q4+4@1$b@2$a$3$3^h1^1@2$5@3$h6$6^h1^1@2$5@2$h9$6^1@2$5@4$h5$6^1^h2@2$4@1$0#k0^i5@4$hb$6^1@2$7@2$4@1$0#k0^i3-q4@3$8$e@1$h2@2$hc^h6^h5@1$b$e").

Lemma sysret_spec : ltac2:(zQ "h90!h9!jc!v3!hk4!hm5!jrf!hs3!jr8!hsb!hmc!hna!l9!js5!m2!t2!ht7!kg5!ih9!ii9!in6!is0!jga!jl0!kke!kld>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$e@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>4errv@1$1@1$0#k0>2lo$d>0@4$h2$3^3^1@2$2@1$0#k0^i3>0@4$h6$3^4@2$4@2$2@1$0#k0^i2-q4@3$9$6@1$f^3@1$a$6>0@2$h4$3^5>0@2$5^4@2$7@2$2@1$0#k0^i6+h0>0@2$c@2$5@2$4@2$4@2$2@1$0#k0^i5-q4+4@2$7@2$2@1$0#k0^i7+h0@2$5@2$2@1$0#k0^i7@2$4@2$2@1$0#k0^i5-q4>0@2$5+q4@2$2@1$0#k0^i6@3$h0$3@h6$h7^ia^i9^i8^i7^i3^i2^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^i1^8^b^a^7^9@7$h3@hf$h1^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b@2$h8@1$0#k0+tttrc^a@1$8@1$1@1$0#k0^9@1$h5$3").
Proof.
  intros until lo. intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
