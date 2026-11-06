(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~k44cell37Corelib4Init9Datatypeso74cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~q65rsegsi2bbv_unsigned46Stdlib6ZArith6BinInt1Zv83addk42C1k42C8o74Noneo73nil37Corelib4Init5Logichid2eqhid2ex3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshkddmachine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hp53mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ht82MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ihb7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~im58rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~iqc2wzo74listo76optionhid3not3h5LinuxProcessSemantics5Riscv7Preludejg45bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ8W_suspof~~~~~~jj39RP_SUSPOFk42CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jo33evtht86ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jsf7mem_inviqc2b8v82lev83pow" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition RP_SUSPOF : Z := 0x664b0.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma suspof_spec : ltac2:(zQ "i00!hc!jf!o0!pf!u2!ua!hh0!hh6!hhb!hi0!hi7!hk1!hk7!ho4!ht1!ih5!ila!iq0!iu7!iud!iv4!ivd!h9!jia!jn1!jne!jre!js5!kg9!kh4!kha!khf>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$h4@1$1@1$0#8>3ecv@1$1@1$0#k0>3ecc@1$1@1$0#k0>3lcf@1$1@1$0#k0>4done@1$1@1$0#8>5clean@1$1@1$0#8>4pad5@1$h3@1$1@1$0#8>0@2$hc$4^7>0@2$he@2$6@2$5@1$0#k0^i0+hh8@2$hf+2+k0>0@4$h1$4^9@2$6@2$5@1$0#k0^i1+l8@3$3$2@1$8^8@3$3$2@1$8^7@3$3$2@1$8^6@1$a$2>0@1$h5@3$b$h6@2$5@1$0#k0^7+1>0@4$h1$4^b@2$6@2$5@1$0#k0^i3+r0@3$3$2@1$7@1$hdZ@3$3$2@1$7^7@3$3$2@1$7^6@3$3$2@2$h9N5^5@1$a$2@3$ha$4\2ms$d@2$c@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$c@1$1@1$0#k0\3a4'@1$1@1$0#k0@3$b$d^3@7$f@hf$e^j0^if^ie^id^ic^ib^ia^i9^i8@1$h2@2$6@2$5@1$0#k0^i7+1^i6^i5^2^1^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1@1$hb^j0^h0@1$9@1$1@1$0#k0^f@1$h0$4@7$f@hf$e^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e@1$h2$h8^d@1$9@1$1@1$0#k0^c@1$h0$4").
  Proof.
    intros until pad5. intros MI A64 EC LCF MORE. unfold RP_SUSPOF, wz at 2.
    pose proof (bv_unsigned_in_range _ a0) as R0. unfold bv_modulus in R0; cbn in R0.
    pose proof (bv_unsigned_in_range _ lcf) as RL. unfold bv_modulus in RL; cbn in RL.
    st1. st1. st1. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      st1. st1. st1. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; revert K2; cbn; lia].
      st1. st1. apply evt_done. neexists 2. reflexivity.
    - st1. st1. if_cases K3; zify_cond K3.
      + st1. st1. apply evt_done. neexists 2. reflexivity.
      + exfalso. rewrite ?unsigned_lit in K3 by lia. lia.
  Qed.
End HCW.
