(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XSeqExec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm2dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeq95bvmapk14Nonem2h3Build_machine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~v56fp_csrv57fp_regsk14boolhfbbv_unsigned46Stdlib6ZArith6BinInt1Zhlc3eqbk14list3h5LinuxProcessSemantics5Riscv5Instrho25msize02N03h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehr3h0le_bytes_to_wordhfabv_extractq94sextq94zextk15falsek13natho26awidthho23SZ4ho23SZ8ho25amoophr3dZ_to_le_bytes3h5LinuxProcessSemantics5Riscv3Semil27amo_valil25low3237Corelib4Init5Logicio82eq01Zho25instrk14Somek14prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XSymStepR~~~~~~irc5mkstRk14pairio81I3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejh07Segmentm29MachineOkm2afetch_wordm28is_ecallm2emachine_resultm24step3h5LinuxProcessSemantics5Riscv7DecodeCjocadecode_anyho25OpImmho25aluopq96bv_eqbil25alu64v54getrv56regupdv56v_addihf2BVhf4BvWfho28ShiftImmho22Opho27ALU_ADDho27OpImm32il25alu32ho2aShiftImm32ho24Op32ho23Mulho25mulopil27mul_divho25Mul32ho23Luiv55v_luihlc6shiftlhf9bv_signedho25Auipcv57v_auipcho23Jalv54btgtho24Jalr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XSeqExec~~~~~~ks26v_jalrk14trueho26Branchho2bbranch_condil2cbranch_takenho25Fenceho26FenceIho2|41L1o1a1dv53rdnircbload_resultircbmsize_bytesm28store_okm2h0word_to_le_bytesho25Store79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExec~~~~~~lq66wbytesirccresv_inval_who22Lril29amo_bytesirc9amo_msizeircaamo_nbyteshlc6moduloho22Schf7Z_to_bvho23Amoircfamo_store_bytes" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : XPropExec.FPState}.


(* [comment removed for export] *)
Definition mkstR : ltac2:(zQ "51!h9!jc!l9!p9!sf&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$4@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0$3") := ltac2:(zQ "81!h9!jc!l9!t7!te!sf!hj4!hjd&>0@1$1@1$0#k0@1$2@1$1@1$0#8\4regs@2$5@1$0#5@1$1@1$0#k0\2pc@1$1@1$0#k0\3mem~0\3rom~0\2rv@1$2@1$1@1$0#k0@8$4^5@1$7?2fx^4@1$3@1$1@1$0#k0^1@1$6?2fx^3^2").

(* [comment removed for export] *)
Definition resv_inval_w : ltac2:(zQ "30!h9!jc!l9>2rv@1$2@1$1@1$0#k0>1a@1$1@1$0#k0@1$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!l9!t7!hk7!hke!hn4\2rv@1$2@1$1@1$0#k0\1a@1$1@1$0#k0M2\2rv@1$2@1$1@1$0#k0@1$2@1$1@1$0#k0^2\1r@1$1@1$0#k0M4\0$4@1$2@1$1@1$0#k0@2$6@2$5@1$0#k0^1@2$5@1$0#k0^2@1$3@1$1@1$0#k0^3@1$3@1$1@1$0#k0").

(* [comment removed for export] *)
Definition load_result : ltac2:(zQ "50!h9!jc!hk7!hnb!hq6>2sz$4>2sx$2>2bs@1$3@1$1@1$0#8@1$1@1$0#k0") := ltac2:(zQ "a3!h9!hk7!hqf!hu2!hv7!jc!hq6!ig4!igb!hnb&@4$4@1$0#k0$2@1$0#8@1$3^1&@4$4@1$0#k0$2@1$0#h0@1$3^1&@4$4@1$0#k0$2@1$0#i0@1$3^1\2sz$6\2sx$1\2bs@1$9@1$5@1$0#8M6\2sz$6@1$5@1$0#k0^3M1\2sx$1@1$5@1$0#k0^2@3$7@1$0#8@1$0#k0~0@3$8@1$0#8@1$0#k0~0M1\2sx$1@1$5@1$0#k0^2@3$7@1$0#h0@1$0#k0~1@3$8@1$0#h0@1$0#k0~1M1\2sx$1@1$5@1$0#k0^2@3$7@1$0#i0@1$0#k0~2@3$8@1$0#i0@1$0#k0~2@4$4@1$0#k0$2@1$0#k0@1$3^1").

Definition eff_sx : ltac2:(zQ "20!hk7!hq6>2sz$1>2sx$0$0") := ltac2:(zQ "30!hq6!hk7!ih2\2sz$0\2sx$1M0\2sz$0$1^2^1^1^1$2").

Definition msize_bytes : ltac2:(zQ "20!iha!hq6>2sz$1$0") := ltac2:(zQ "20!hq6!iha\2sz$0M0\2sz$0$1^1N1N2N4N8").

(* [comment removed for export] *)
Definition amo_msize : ltac2:(zQ "20!ii0!hq6>2wd$0$1") := ltac2:(zQ "40!ii0!iia!ij1!hq6\2wd$0M0\2wd$0$3^1$1$2").
Definition amo_nbytes : ltac2:(zQ "20!iha!ii0>2wd$1$0") := ltac2:(zQ "20!ii0!iha\2wd$0M0\2wd$0$1^1N4N8").

(* [comment removed for export] *)
Definition amo_store_bytes : ltac2:(zQ "50!h9!jc!hnb!ij8!ii0>2op$3>2wd$4>2bs@1$2@1$1@1$0#8>3src@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "c0!h9!ii0!jc!hnb!hqf!ik1!hu2!in4!hv7!hke!ij8!inf\2op$a\2wd$1\2bs@1$3@1$2@1$0#8\3src@1$2@1$0#k0M1\2wd$1@1$3@1$2@1$0#8^3@2$5N4@2$9@1$0#i0@4$7@1$0#i0^4@4$8@1$0#k0$4@1$0#i0@1$6^2@1$b^1@2$5N8@2$9@1$0#k0@4$7@1$0#k0^4@4$8@1$0#k0$4@1$0#k0@1$6^2^1").
End FPX_1.


Ltac stepR_pipeline Hfetch Hecall Hdecode :=
  unfold mkstR;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.
Section FPX_2. Context {fx : XPropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stepR_opimm_gen : ltac2:(zQ "i11!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!js0!js9!jt2!ig4!jtb!ju4!jub!jv4!jvd!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2op$h8>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^b^9@2$7@1$1@1$0#i0^5>0@3$3$4@1$h3^6$c>0@3$3@1$2@2$8$6$5@1$h6^7@2$7@2$8$6$5@4$e$6$5@4$h7^6^5^4^3+4@3$3@1$h4$9@2$h5^e@6$b?2fx^d^c^b^a^9@2$h1$9@6$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$hf@1$0#5ZKv$f@2$i0@1$0#5Z^d@3$hd^d^6@3$hb^7@2$hc^d^5@3$ha@1$0#c@1$0#k0^4@2$he^c+4^b^a^9").
Proof.
  intros segs regs pc mem rom rv w op rd rs imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm_gen : ltac2:(zQ "i11!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kg9!js9!jt2!igb!jtb!ju4!jub!jv4!jvd!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2op$h8>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#6>0@3$3@1$2@1$1@1$0#i0@2$h2^b^9@2$7@1$1@1$0#i0^5>0@3$3$4@1$h3^6$c>0@3$3@1$2@2$8$6$5@1$h6^7@2$7@2$8$6$5@4$e$6$5@4$h7^6^5^4^3+4@3$3@1$h4$9@2$h5^e@6$b?2fx^d^c^b^a^9@2$h1$9@6$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$hf@1$0#5ZKv$f@2$i0@1$0#5Z^d@3$hd^d^6@3$hb^7@2$hc^d^5@3$ha@1$0#6@1$0#k0^4@2$he^c+4^b^a^9").
Proof.
  intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op_gen : ltac2:(zQ "i01!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ju4!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kh5!js9!jt2!jtb!jub!jv4!jvd!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2op$h9>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^b^9@2$7@1$1@1$0#i0^5>0@3$3$4@1$h4^6$d>0@3$3@1$2@2$8$6$5@1$h7^7@2$7@2$8$6$5@4$f$6$5@4$h8^6^5^4^3+4@3$3@1$h5$9@2$h6^e@6$c?2fx^d^c^b^a^9@2$h2$9@6$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^d@3$hc^d^6@3$hb^7@2$b^d^5@2$b^d^4@2$hd^c+4^b^a^9").
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_opimm32_gen : ltac2:(zQ "i21!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ig4!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!khb!ki6!jt2!kj1!inf!ju4!jub!jv4!jvd!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h3^a^8@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@3$h9^5^4^3+4@3$3@1$h5$9@2$h6^d@6$c?2fx^c^b^a^9^8@2$h2$9@6$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$i0@1$0#5ZKv$h0@2$i1@1$0#5Z^c@3$he^c^6@3$b@1$0#i0@1$0#k0@3$hb$h8@1$hc@2$hd^c^5@3$b@1$0#c@1$0#i0^4@2$hf^b+4^a^9^8").
Proof.
  intros segs regs pc mem rom rv w rd rs imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_shiftimm32_gen : ltac2:(zQ "i31!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kja!js9!jt2!ig4!igb!kj1!inf!ju4!jub!jv4!jvd!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2op$h8>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h2^b^9@2$7@1$1@1$0#i0^5>0@3$3$4@1$h3^6$c>0@3$3@1$2@2$8$6$5@1$h6^7@2$7@2$8$6$5@4$e$6$5@4$h7^6^5^4^3+4@3$3@1$h4$9@2$h5^e@6$b?2fx^d^c^b^a^9@2$h1$9@6$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$i1@1$0#5ZKv$f@2$i2@1$0#5Z^d@3$hf^d^6@3$ha@1$0#i0@1$0#k0@3$hc^7@1$hd@2$he^d^5@3$hb@1$0#5@1$0#i0^4@2$i0^c+4^b^a^9").
Proof.
  intros segs regs pc mem rom rv w op rd rs sh Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_op32_gen : ltac2:(zQ "i21!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!inf!ju4!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kk8!js9!jt2!ig4!kj1!jub!jv4!jvd!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$f$h2>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2op$ha>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h4^b^9@2$7@1$1@1$0#i0^5>0@3$3$4@1$h5^6$e>0@3$3@1$2@2$8$6$5@1$h8^7@2$7@2$8$6$5@4$h0$6$5@4$h9^6^5^4^3+4@3$3@1$h6$9@2$h7^e@6$d?2fx^d^c^b^a^9@2$h3$9@6$d?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$hb@1$0#5^6@3$i0@1$0#5ZKv$h1@2$i1@1$0#5Z^d@3$he^d^6@3$hc@1$0#i0@1$0#k0@3$hd^7@1$b@2$c^d^5@1$b@2$c^d^4@2$hf^c+4^b^a^9").
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul_gen : ltac2:(zQ "i01!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ju4!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kl0!kl7!jt2!km0!jub!jv4!jvd!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2op$h9>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^b^9@2$7@1$1@1$0#i0^5>0@3$3$4@1$h4^6$d>0@3$3@1$2@2$8$6$5@1$h7^7@2$7@2$8$6$5@4$f$6$5@4$h8^6^5^4^3+4@3$3@1$h5$9@2$h6^e@6$c?2fx^d^c^b^a^9@2$h2$9@6$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^d@3$hc^d^6@4$hb@1$0#k0^7@2$b^d^5@2$b^d^4@2$hd^c+4^b^a^9").
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_mul32_gen : ltac2:(zQ "i21!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!inf!ju4!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kmb!kl7!jt2!ig4!km0!jub!jv4!jvd!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$f$h2>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2op$ha>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h4^b^9@2$7@1$1@1$0#i0^5>0@3$3$4@1$h5^6$e>0@3$3@1$2@2$8$6$5@1$h8^7@2$7@2$8$6$5@4$h0$6$5@4$h9^6^5^4^3+4@3$3@1$h6$9@2$h7^e@6$d?2fx^d^c^b^a^9@2$h3$9@6$d?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$hb@1$0#5^6@3$i0@1$0#5ZKv$h1@2$i1@1$0#5Z^d@3$he^d^6@3$hc@1$0#i0@1$0#k0@4$hd@1$0#i0^7@1$b@2$c^d^5@1$b@2$c^d^4@2$hf^c+4^b^a^9").
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma stepR_lui : ltac2:(zQ "i01!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kn4!jt2!jub!jv4!knb!ko3!jvd!kg2!kod&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3imm@1$1@1$0#h4>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^3>0@3$3$4@1$h3^4$c>0@3$3@1$2@2$8$6$5@1$h6^5@2$7@2$8$6$5@4$e$6$5@2$h7^4^3+4@3$3@1$h4$9@2$h5^c@6$b?2fx^b^a^9^8^7@2$h1$9@6$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^5@3$hd@1$0#5ZKv$f@2$he@1$0#5Z^b@3$h9^b^5@1$hb@2$hc@2$hf@1$0#h4^4+c@2$ha^a+4^9^8^7").
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma stepR_auipc : ltac2:(zQ "i01!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kp9!jt2!jub!jv4!kq2!ko3!jvd!kg2!kod&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3imm@1$1@1$0#h4>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^3>0@3$3$4@1$h3^4$c>0@3$3@1$2@2$8$6$5@1$h6^5@2$7@2$8$6$5@4$e$6$5@2$h7^4^3+4@3$3@1$h4$9@2$h5^c@6$b?2fx^b^a^9^8^7@2$h1$9@6$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^5@3$hd@1$0#5ZKv$f@2$he@1$0#5Z^b@3$h9^b^5@2$hb^a@2$hc@2$hf@1$0#h4^4+c@2$ha^a+4^9^8^7").
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma stepR_jal_link : ltac2:(zQ "hf1!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kqc!jt2!kr3!jub!jv4!jvd!kg2!kod&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3imm@1$1@1$0#h5>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^3>0@3$3$4@1$h3^4$c>0@3$3@1$2@2$8$6$5@1$h6^5@2$7@2$8$6$5@4$e$6$5@2$h7^4^3+4@3$3@1$h4$9@2$h5^c@6$b?2fx^b^a^9^8^7@2$h1$9@6$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^5@3$hc@1$0#5ZKv$f@2$hd@1$0#5Z^b@3$ha^b^5@2$hb^a+4@2$h9^a@2$he@1$0#h5^4^9^8^7").
Proof.
  intros segs regs pc mem rom rv w rd imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

Lemma stepR_jalr : ltac2:(zQ "i01!h9!jc!l9!ipc!hk7!iq2!iq5!iqe!ir5!p9!sf!ivb!ih2!hnb!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!kra!jt2!ju4!jub!jv4!lg0!jvd!kg2!kod&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^a^8@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@3$h7^5^4^3+4@3$3@1$h4$9@2$h5^d@6$b?2fx^c^b^a^9^8@2$h1$9@6$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^6@3$hd@1$0#5ZKv$f@2$he@1$0#5Z^c@3$ha^c^6@2$hb^b+4@2$hc@2$h9^c^5@2$hf@1$0#c^4^a^9^8").
Proof.
  intros segs regs pc mem rom rv w rd rs1 imm Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd, v_jalr.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_jalr; reflexivity.
Qed.

Lemma stepR_branch_tk_gen : ltac2:(zQ "hd1!h9!jc!l9!ipc!iq2!iq5!iqe!hk7!ir5!p9!ju4!ivb!ih2!hnb!jg4!lga!jk5!jl0!jlc!jm9!jn4!jo5!jr2!lh1!lhb!sf!lia!kr3!kod&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>1c$h8>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$3@1$2@1$1@1$0#i0@2$h2^b^9@2$6@1$1@1$0#i0^5>0@3$3$7@1$h3^6$c>0@3$3@1$2@2$8$5$4@1$h6^7@2$6@2$8$5$4@4$e$5$4@4$h7^6^5^4^3+4>0@3$3$7@3$ha^7@2$a^d^6@2$a^d^5$f@3$3@1$h4$9@2$h5^f@6$b?2fx^e^d^c^b^a@2$h1$9@6$b?2fx^e@2$hb^d@2$hc@1$0#d^5^c^b^a").
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma stepR_branch_ft_gen : ltac2:(zQ "hb1!h9!jc!l9!ipc!iq2!iq5!iqe!hk7!ih2!ir5!p9!ju4!ivb!hnb!jg4!jk5!jl0!jlc!jm9!jn4!jo5!jr2!lh1!lhb!sf!lia!jv4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>1c$h7>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$3@1$2@1$1@1$0#i0@2$h1^b^9@2$6@1$1@1$0#i0^5>0@3$3$7@1$h2^6$8>0@3$3@1$2@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$e$5$4@4$h6^6^5^4^3+4>0@3$3$7@3$h9^7@2$b^d^6@2$b^d^5$8@3$3@1$h3$a@2$h4^f@6$c?2fx^e^d^c^b^a@2$h0$a@6$c?2fx^e@2$ha^d+4^c^b^a").
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

Lemma stepR_fence : ltac2:(zQ "h81!h9!jc!l9!ipc!iq2!iq5!iqe!ir5!p9!ivb!hk7!ih2!hnb!jg4!jk5!jl0!jlc!jm9!jn4!jo5!jr2!lja!sf!jv4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$c$e>4regs@2$h6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>1a@1$1@1$0#4>1b@1$1@1$0#4>1c@1$1@1$0#4>1d@1$1@1$0#5>1e@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h0^c^a@2$6@1$1@1$0#i0^6>0@3$3$a@1$h1^7$b>0@3$3@1$2@2$7$5$4@1$h4^8@2$6@2$7$5$4@4$d$5$4@5$h5^7^6^5^4^3+4@3$3@1$h2$8@2$h3^f@6$9?2fx^e^d^c^b^a@2$f$8@6$9?2fx^e@2$h7^d+4^c^b^a").
Proof.
  intros segs regs pc mem rom rv w a b c d e Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Lemma stepR_fencei : ltac2:(zQ "h81!h9!jc!l9!ipc!iq2!iq5!iqe!ir5!p9!ivb!hk7!ih2!hnb!jg4!jk5!jl0!jlc!jm9!jn4!jo5!jr2!lk3!sf!jv4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$c$e>4regs@2$h6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>1a@1$1@1$0#5>1b@1$1@1$0#5>1c@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h0^a^8@2$6@1$1@1$0#i0^4>0@3$3$a@1$h1^5$b>0@3$3@1$2@2$7$5$4@1$h4^6@2$6@2$7$5$4@4$d$5$4@3$h5^5^4^3+4@3$3@1$h2$8@2$h3^d@6$9?2fx^c^b^a^9^8@2$f$8@6$9?2fx^c@2$h7^b+4^a^9^8").
Proof.
  intros segs regs pc mem rom rv w a b c Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stepR_load : ltac2:(zQ "i31!h9!jc!l9!ipc!hk7!hnb!iqe!iq2!iq5!ir5!p9!sf!jv4!ivb!ih2!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!lkd!hq6!jt2!ju4!lla!jub!lm0!lmf!jvd!kg2!kod&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$5$h1>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2sz$h9>2sx$4>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>2bs@1$5@1$1@1$0#8>0@3$3@1$2@1$1@1$0#i0@2$h3^d^b@2$6@1$1@1$0#i0^7>0@3$3$4@1$h4^8$e>0@3$3@1$2@2$9$8$7@1$h7^9@2$6@2$9$8$7@4$f$8$7@5$h8^8^7^6^5^4+4>0@3$3@1$2@1$5@1$1@1$0#8@4$hc^h0^d@2$c@2$hb^f^6@2$i2@1$0#c^5@1$hf^9@2$6@1$5@1$1@1$0#8^4@3$3@1$h5$a@2$h6^h1@6$d?2fx^h0^f^e^d^c@2$h2$a@6$d?2fxM4\0$4@2$b@1$0#5@1$1@1$0#k0@3$ha@1$0#5^8@3$i0@1$0#5ZKv$h0@2$i1@1$0#5Z^h0@3$hd^h0^8@3$he^a^9^5@2$c^f+4^e^d^c").
Proof.
  intros segs regs pc mem rom rv w sz sx rd rs imm bs Hfetch Hecall Hdecode Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
    rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc4;
    destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_store : ltac2:(zQ "i12!h9!jc!l9!ipc!ju4!jv4!iq2!iq5!kod!iqe!hk7!ir5!p9!ivb!lmf!ih2!hnb!jg4!lga!jk5!jl0!jlc!jm9!jn4!jo5!lne!lo9!jr2!lpd!hq6!sf!lu4!lue&>0@1$1@1$0#k0@1$2@1$1@1$0#8&@2$5@2$4^e^7@2$8@1$0#c^5>4segs@1$h0$h3>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2sz$hd>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h5^b^9@2$9@1$1@1$0#i0^5>0@3$3$a@1$h6^6$f>0@3$3@1$2@2$b$7$6@1$hb^7@2$9@2$b$7$6@4$h1$7$6@4$hc^6^5^4^3+4>0@3$3$a@4$h9^e^b@2$5@2$4^d^6@2$8@1$0#c^4@1$e^7$h2@3$3@1$h7$c@2$h8^f@6$d?2fx^e^d^c^b^a@2$h4$c@6$d?2fx^e@2$5^d+4@3$hf^c~1@2$ha@1$e^8@2$4^e^6^b@2$i0^a~1").
Proof.
  intros segs regs pc mem rom rv w sz rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite !b_addsext.
  destruct sz; cbn [msize_bytes] in Hok |- *; cbv beta iota delta [store_val];
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?Hsb, ?store_bytes_low16, ?store_bytes_low32, b_npc4;
    (destruct rv as [r|]; cbv beta iota; [|reflexivity]);
    unfold resv_inval_w;
    match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y); cbv beta iota; reflexivity end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepR_lr : ltac2:(zQ "i71!h9!jc!l9!ipc!hk7!iqe!hnb!iq2!iq5!ju4!ir5!p9!sf!ivb!ih2!jg4!lga!jgb!jk5!jl0!jlc!jm9!jn4!jo5!jr2!lve!ii0!jt2!mg4!lla!jub!jv4!mh1!mhe!lm0!mic!jvd!kg2!hke&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$6$h2>4regs@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$2@1$1@1$0#k0>1w@1$1@1$0#i0>2wd$ha>2aq$4>2rl$4>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2bs@1$6@1$1@1$0#8>0@3$3@1$2@1$1@1$0#i0@2$h4^d^b@2$5@1$1@1$0#i0^7>0@3$3$4@1$h5^8$e>0@3$3@1$2@2$a$8$7@1$h8^9@2$5@2$a$8$7@4$f$8$7@5$h9^8^7^6^5^4+4>0@3$3$7@2$i3@2$i6@1$0#k0@2$9^f^5@1$hc^9Z>0@3$3@1$2@1$6@1$1@1$0#8@4$hd^h1^e@2$9^h0^6@1$i1^a@2$5@1$6@1$1@1$0#8^5@3$3@1$h6$b@2$h7^h2@6$d?2fx^h1^h0^f^e^d@2$h3$b@6$d?2fxM4\0$4@2$c@1$0#5@1$1@1$0#k0@3$hb@1$0#5^8@3$i4@1$0#5ZKv$h1@2$i5@1$0#5Z^h1@3$he^h1^8@3$i2@1$i0^b$h0^6@2$hf^h0+4^f^e@2$5@1$1@1$0#k0@2$9^h1^7").
Proof.
  intros segs regs pc mem rom rv w wd aq rl rd rs bs Hfetch Hecall Hdecode Hal Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite b_npc4; unfold regupd;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_sc_ok : ltac2:(zQ "i91!h9!jc!ipc!hk7!ju4!l9!iq2!iqe!iq5!ir5!p9!sf!mhe!ivb!t7!ih2!hnb!jg4!lga!jgb!jk5!jl0!jlc!jm9!jn4!jo5!lne!lo9!jr2!mj6!ii0!jt2!mg4!lu4!jub!jv4!mic!jvd!kg2!mjc!hke&>0@1$1@1$0#k0@1$5@1$1@1$0#8>4segs@1$h0$h4>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2wd$he>2aq$3>2rl$3>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1r@1$1@1$0#k0>0@3$2@1$5@1$1@1$0#i0@2$h6^d^b@2$7@1$1@1$0#i0^8>0@3$2$3@1$h7^9$f>0@3$2@1$5@2$9$8$6@1$hc^a@2$7@2$9$8$6@4$h1$8$6@6$hd^9^8^7^6^5^4+4>0@3$2$6@2$i4@2$i8@1$0#k0@2$4^f^6@1$i0^aZ>0@3$2@1$1@1$0#k0^5@2$4^h0^7>0@3$2$3@4$ha^h2^f@2$4^h1^8@1$c^c$h2@3$2@1$h8$a@2$h9^h3@6$d?2fx^h2^h1^h0^f@2$7@1$1@1$0#k0^7@2$h5$a@6$d?2fxM3\0$3@2$b@1$0#5@1$1@1$0#k0@3$hf@1$0#5^a@3$i5@1$0#5ZKv$h3@2$i6@1$0#5Z^h2@3$i2^h2^a@2$i7@1$0#k0Z@2$i3^h1+4@3$i1^h0@2$4^h2^9@2$hb@1$c^d@2$4^h2^8^f@1$e@1$1@1$0#k0").
Proof.
  intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    subst r; rewrite Z.eqb_refl; cbv beta iota;
    cbn [amo_nbytes] in Hok |- *; rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?store_bytes_low32, b_npc4;
    unfold regupd, word_to_le_bytes;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepR_amo : ltac2:(zQ "ic1!h9!jc!ipc!hk7!l9!ju4!hnb!iq2!iqe!iq5!ir5!lga!p9!sf!mhe!ivb!ih2!jg4!jgb!jk5!jl0!jlc!jm9!jn4!jo5!lne!jr2!mk6!ij8!ii0!jt2!mg4!lu4!lla!jub!jv4!mh1!mkd!lm0!lue!mic!jvd!kg2!hke&>0@1$1@1$0#k0@1$4@1$1@1$0#8>4segs@1$6$h3>4regs@2$d@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2rv@1$4@1$1@1$0#k0>1w@1$1@1$0#i0>2op$hc>2wd$hd>2aq$3>2rl$3>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>2bs@1$6@1$1@1$0#8>0@3$2@1$4@1$1@1$0#i0@2$h5^f^d@2$8@1$1@1$0#i0^9>0@3$2$3@1$h6^a$h0>0@3$2@1$4@2$a$9$7@1$ha^b@2$8@2$a$9$7@4$h1$9$7@7$hb^a^9^8^7^6^5^4+4>0@3$2$7@2$i8@2$ib@1$0#k0@2$5^h1^6@1$hf^aZ>0@3$2@1$4@1$6@1$1@1$0#8@4$i1^h3^h0@2$5^h2^7@1$e^b@2$8@1$6@1$1@1$0#8^5>0@3$2$3@4$h9^h4^h1@2$5^h3^8@1$e^c$b@3$2@1$h7$c@2$h8^h5@6$f?2fx^h4^h3^h2^h1^h0@2$h4$c@6$f?2fxM3\0$3@2$d@1$0#5@1$1@1$0#k0@3$he@1$0#5^a@3$i9@1$0#5ZKv$h2@2$ia@1$0#5Z^h4@3$i2^h4^a@3$i6@1$i4^d$b^7@2$i3^h3+4@3$i0^h2@2$5^h4^9@4$i5^e^d^7@2$5^h4^8^h1@2$i7^h0@2$5^h4^9").
Proof.
  intros segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs Hfetch Hecall Hdecode Hal Hread Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread, Hok |- *; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, b_npc4; unfold regupd, amo_store_bytes;
    (destruct rv as [r|]; cbv beta iota);
    unfold resv_inval_w;
    try match goal with |- context [Z.eqb (bv_unsigned r) ?y] =>
          destruct (Z.eqb (bv_unsigned r) y); cbv beta iota end;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

End FPX_2.
(* [comment removed for export] *)
