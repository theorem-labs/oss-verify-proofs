(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import ExitSim PropExec CatSim CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~k49jalr_tgtZhf7Z_to_bv37Corelib4Init9Datatypesp56option37Corelib4Init5Logicr62eqp54bool3h5LinuxProcessSemantics5Riscv5Instrt65instrp54Somep54prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshh0dmachine_state3h5LinuxProcessSemantics5Riscv7Preludehl85bvmapk44mkstp55falsep54listp54pairr61I3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehq87Segmenthh09MachineOkhh0afetch_wordhh08is_ecallhh0emachine_resulthh04step3h5LinuxProcessSemantics5Riscv7DecodeCii9adecode_anyt63Jalhl86bv_eqbk44btgtk46regupdk46v_addihf2BVhf4BvWfhf9bv_signedt64Jalrk44getr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SeqExec4FPX1~~~~~~iqc6v_jalrp54truehh08store_okhh0h0word_to_le_bytest63SZ8t65Store69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~jib6wbytest67ALU_ADDt65OpImmt62Opk45v_addt67ALU_SUBk45v_subt63Luik45v_lui46Stdlib6ZArith6BinInt1Zjqe6shiftlt65Auipck47v_auipct67OpImm32k47v_addiwt68ALU_SLTUk47v_sltiut67ALU_XORk46v_xorit65M_MULt63Mulk45v_mult67ALU_ANDk46v_andit66ALU_ORk45v_orit67ALU_SLLt68ShiftImmk46v_sllihfbbv_unsignedt67ALU_SRLk46v_srlit67ALU_SRAk46v_sraip56lengthk43rdnjqe3addjqe2lejqe6of_natjqe3pow3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasekt7dbytes_le_to_Zk45c_ltujqe3ltbjqe2ltjqe3mulr63andjibccat_argv_ptrp53natp53nil37Corelib4Init5Peanoll52lt37Corelib5Lists7ListDeflmf3nth3h5LinuxProcessSemanticsfLinuxProcessSem3Runlodavalid_argvlodavalid_envp69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SeqExec~~~~~~lt5h1argv_layout_slacklt56v_jalrjqe3divjqe6modulor63nott66M_DIVU3h5LinuxProcessSemantics5Riscv3Semmkf7mul_div79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SeqExec4FPX3~~~~~~mnc6v_divut66M_REMUmnc6v_remut63SZ1p54consjqe3subkt7dZ_to_le_bytes01Njqe4of_Nhf7bv_wrap02N0hfabv_extractmkf5low32t63SZ4t63SZ2p53app37Corelib4Init3Natnje3addkt7bnat_to_wordhf6bv_addjqe3oppnje3subll52lelmf5skipnlmf6firstn" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition v_jalr : ltac2:(zQ "30!h9!jc!k1>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "50!h9!k1!nf!ob!jc\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_jal_link : ltac2:(zQ "hf1!h9!jc!qd!sa!sf!k1!va!hg2!hg9!hk7!hne!ho7!hoe!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!ild!im3!imd!in4!ind!io6!iob!ip2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3imm@1$1@1$0#h5>0@3$3@1$2@1$1@1$0#i0@2$h2^8^6@2$7@1$1@1$0#i0^3>0@3$3$4@1$h3^4$c>0@3$3@1$2@2$8$6$5@1$h6^5@2$7@2$8$6$5@4$e$6$5@2$h7^4^3+4@3$3@1$h4$9@2$h5^b@5$b?2fx^a^9^8^7@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^5@3$hc@1$0#5ZKv$f@2$hd@1$0#5Z^a@3$ha^a^5@2$hb^9+4@2$h9^9@2$he@1$0#h5^4^8^7").
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr : ltac2:(zQ "i01!h9!jc!qd!sa!sf!k1!va!hg2!hg9!hk7!hne!ho7!hoe!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!ipe!im3!iq5!in4!ind!iub!io6!iob!ip2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@3$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^6@3$hd@1$0#5ZKv$f@2$he@1$0#5Z^b@3$ha^b^6@2$hb^a+4@2$hc@2$h9^b^5@2$hf@1$0#c^4^9^8").
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hf He Hd.
  exact (step_jalr_gen segs regs pc mem rom w rd rs1 imm Hf He Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sd_val : ltac2:(zQ "hf1!h9!jc!sa!qd!k1!va!iq5!ind!hg2!sf!hg9!hk7!ho7!ip2!hoe!hp6!hpd!iv5!htd!hu8!hv5!ig3!igf!ii1!ivc!jg8!ikf!jhd!ji3!hne!jm5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$f$h2>4regs@2$hd@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>0@3$2@1$3@1$1@1$0#i0@2$h4^9^7@2$8@1$1@1$0#i0^4>0@3$2$9@1$h5^5$e>0@3$2@1$3@2$a$5$4@1$ha^6@2$8@2$a$5$4@4$h0$5$4@4$hc$hb^5^4^3+4>0@3$2$9@4$h8^c^9@2$7@2$6^b^6@2$d@1$0#c^4N8$h1@3$2@1$h6$b@2$h7^d@5$c?2fx^c^b^a^9@2$h3$b@5$c?2fx^c@2$7^b+4@3$he^a@2$7@2$6^c^7@2$d@1$0#c^5@2$h9N8@2$6^c^6^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sd_at : ltac2:(zQ "hf1!h9!jc!sa!qd!k1!va!hg2!sf!hg9!hk7!iq5!ho7!ind!hoe!hp6!hpd!iv5!htd!hu8!hv5!ig3!igf!ii1!ivc!jg8!ikf!jhd!ji3!hne!jm5!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$e$h1>4regs@2$hc@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1a@1$1@1$0#k0>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h3^b^9@2$6@1$1@1$0#i0^6>0@3$2$7@1$h4^7$d>0@3$2@1$3@2$8$5$4@1$h9^8@2$6@2$8$5$4@4$f$5$4@4$hb$ha^7^6^5+4>0@3$2@1$1@1$0#k0@2$c@2$a^d^8@2$he@1$0#c^6^5>0@3$2@1$1@1$0#k0@2$a^e^8^5>0@3$2$7@4$h7^h0^d^7N8$h0@3$2@1$h5$9@2$h6^h1@5$b?2fx^h0^f^e^d@2$h2$9@5$b?2fx^h0@2$c^f+4@3$hd^e^8@2$h8N8^7^d").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma step_addi_at : ltac2:(zQ "i01!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!ind!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!jmf!jn9!im3!hne!iq5!in4!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$hd@1$0#5ZKv$f@2$he@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$c@2$hb^d^7@2$hf@1$0#c^6^5@3$2@1$h4$a@2$h5^f@5$b?2fx^e^d^c^b@2$h1$a@5$b?2fx@3$hc^e^9^6@2$c^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_addi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_add_at : ltac2:(zQ "i01!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!iq5!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!jmf!jo1!im3!hne!in4!jo6!ind!io6!iob&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$he@1$0#5ZKv$f@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hc@2$b^d^7@2$b^d^6^5@3$2@1$h4$a@2$h5^f@5$c?2fx^e^d^c^b@2$h1$a@5$c?2fx@3$hb^e^9^6@2$hd^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_add segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sub_at : ltac2:(zQ "i01!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!iq5!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!joe!jo1!im3!hne!in4!ind!jp8!io6!iob&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$he@1$0#5ZKv$f@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$b^d^7@2$b^d^6^5@3$2@1$h4$a@2$h5^f@5$c?2fx^e^d^c^b@2$h1$a@5$c?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_sub segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_lui_at : ltac2:(zQ "i01!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!jq0!im3!hne!in4!ind!jq6!js6!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3imm@1$1@1$0#h4>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h2^5$8>0@3$2@1$3@2$9$5$4@1$h5^6@2$6@2$9$5$4@4$d$5$4@2$h6^5^4+4>0@3$2$7@3$h7@1$0#5^6@3$hd@1$0#5ZKv$e@2$he@1$0#5Z$8>0@3$2@1$1@1$0#k0@1$hb@2$hc@2$hf@1$0#h4^6+c^5@3$2@1$h3$a@2$h4^e@5$b?2fx^d^c^b^a@2$h0$a@5$b?2fx@3$h9^d^8^6@2$ha^c+4^b^a").
Proof.
  intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
  rewrite (step_lui segs regs pc mem rom w rd imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_auipc_at : ltac2:(zQ "i01!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!jt0!im3!hne!in4!ind!jt8!js6!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3imm@1$1@1$0#h4>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h2^5$8>0@3$2@1$3@2$9$5$4@1$h5^6@2$6@2$9$5$4@4$d$5$4@2$h6^5^4+4>0@3$2$7@3$h7@1$0#5^6@3$hd@1$0#5ZKv$e@2$he@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hb^b@2$hc@2$hf@1$0#h4^6+c^5@3$2@1$h3$a@2$h4^e@5$b?2fx^d^c^b^a@2$h0$a@5$b?2fx@3$h9^d^8^6@2$ha^c+4^b^a").
Proof.
  intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
  rewrite (step_auipc segs regs pc mem rom w rd imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_addiw_at : ltac2:(zQ "i01!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!ju2!im3!hne!iq5!in4!ind!juc!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@3$h6^6^5^4+4>0@3$2$7@3$h7@1$0#5^7@3$hd@1$0#5ZKv$e@2$he@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hc@2$h9^d^7@2$hf@1$0#c^6^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$ha^e^9^6@2$hb^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_addiw segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sltiu_at : ltac2:(zQ "i11!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!jv6!jn9!im3!hne!iq5!in4!ind!kg1!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@4$h7$h6^6^5^4+4>0@3$2$7@3$h8@1$0#5^7@3$he@1$0#5ZKv$e@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$ha^d^7@2$i0@1$0#c^6^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_sltiu segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_xori_at : ltac2:(zQ "i11!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!kgb!jn9!im3!hne!iq5!in4!ind!kh5!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@4$h7$h6^6^5^4+4>0@3$2$7@3$h8@1$0#5^7@3$he@1$0#5ZKv$e@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$ha^d^7@2$i0@1$0#c^6^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_xori segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_mul_at : ltac2:(zQ "i01!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!iq5!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!khe!ki6!im3!hne!in4!ind!kic!io6!iob&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$he@1$0#5ZKv$f@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$b^d^7@2$b^d^6^5@3$2@1$h4$a@2$h5^f@5$c?2fx^e^d^c^b@2$h1$a@5$c?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mul segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_andi_at : ltac2:(zQ "i11!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!kj4!jn9!im3!hne!iq5!in4!ind!kje!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@4$h7$h6^6^5^4+4>0@3$2$7@3$h8@1$0#5^7@3$he@1$0#5ZKv$e@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$ha^d^7@2$i0@1$0#c^6^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_andi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_ori_at : ltac2:(zQ "i11!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!kk7!jn9!im3!hne!iq5!in4!ind!kl0!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@4$h7$h6^6^5^4+4>0@3$2$7@3$h8@1$0#5^7@3$he@1$0#5ZKv$e@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$ha^d^7@2$i0@1$0#c^6^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_ori segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_slli_at : ltac2:(zQ "i11!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!kl8!km2!im3!hne!iq5!in4!ind!kmd!io6!iob!kn6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#6>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@4$h7$h6^6^5^4+4>0@3$2$7@3$h8@1$0#5^7@3$he@1$0#5ZKv$e@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$ha^d^7@2$i0@1$0#6^6^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (step_slli segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srli_at : ltac2:(zQ "i11!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!ko4!km2!im3!hne!iq5!in4!ind!koe!io6!iob!kn6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#6>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@4$h7$h6^6^5^4+4>0@3$2$7@3$h8@1$0#5^7@3$he@1$0#5ZKv$e@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$ha^d^7@2$i0@1$0#6^6^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (PropExec.step_srli segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srai_at : ltac2:(zQ "i11!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!kp7!km2!im3!hne!iq5!in4!ind!kq1!io6!iob!kn6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#6>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@4$h7$h6^6^5^4+4>0@3$2$7@3$h8@1$0#5^7@3$he@1$0#5ZKv$e@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$ha^d^7@2$i0@1$0#6^6^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (step_srai segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_wbytes_hit : ltac2:(zQ "f0!h9!jc!hp6!kqa!qd!hg2!sa!htd!jm5!kr3!kr9!ks0!ks6!kt0!kn6>4segs@1$2$7>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>0@2$b@2$a@2$e@1$0#k0^1@1$c@2$3@1$1@1$0#8^3@2$d+2+k0@3$6@1$4@1$2@1$1@1$0#8@4$9^5@3$8^3^2^4^2@2$3@1$1@1$0#8^4@2$5@1$2@1$1@1$0#8^4").
Proof.
  intros segs bs. induction bs as [|b rest IH]; intros m a Hnw; [reflexivity|].
  cbn [length] in Hnw |- *.
  change (wbytes m a (b :: rest))
    with (wbytes (fun x => if bv_eqb x a then Some b else m x) (a+1) rest).
  set (m' := fun x : word => if bv_eqb x a then Some b else m x).
  cbn [rdn].
  destruct rest as [|b' rest'].
  - cbn [wbytes rdn]. unfold m'. rewrite bv_eqb_refl. reflexivity.
  - assert (Hu1 : bv_unsigned (a+1) = (bv_unsigned a + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    assert (Hread : wbytes m' (a+1) (b' :: rest') a = Some b).
    { rewrite (wbytes_below (b' :: rest') m' (a+1) a);
        [ unfold m'; rewrite bv_eqb_refl; reflexivity
        | cbn [length] in *; lia
        | pose proof (u64_range a); lia ]. }
    rewrite Hread.
    rewrite (IH m' (a+1)) by (cbn [length] in *; lia).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_hit8 : ltac2:(zQ "e0!h9!jc!hp6!qd!jg8!hg2!sa!htd!jm5!kr3!kr9!ks0!kt0!kn6>4segs@1$2$7>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1v@1$1@1$0#k0>0@2$b@2$a@2$d@1$0#k0^2+8@2$c+2+k0@3$6@1$3@1$2@1$1@1$0#8@4$9^5@3$8^4^3@2$4N8^2^3N8@2$5@1$2@1$1@1$0#8@2$4N8^2").
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_8 : ltac2:(zQ "70!h9!sa!k1!lg6!jg8!jc!kn6>1v@1$5@1$0#k0@3$1$2@1$3@2$4N8^1@2$6@1$0#k0^1").
Proof.
  intro v. rewrite bytes_le_N.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
  apply Z.mod_small. apply u64_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma c_ltu_ltb : ltac2:(zQ "70!h9!jc!kn6!sf!sa!lh7!lhf>1x@1$1@1$0#k0>1y@1$1@1$0#k0@3$4$3@2$5^2^1@2$6@2$2@1$0#k0^2@2$2@1$0#k0^1").
Proof. reflexivity. Qed.

Lemma v_addiw_small : ltac2:(zQ "a0!h9!kn6!kr9!k1!ks0!sa!juc!li6!kt0!jc>1x@1$9@1$0#k0>3imm$3>0@2$4Z@2$2@2$1@1$0#k0^2^1>0@2$7@2$2@2$1@1$0#k0^3^2@2$8+2+hf>0@2$4Z^3@3$5$3@2$1@1$0#k0@2$6^5^4@2$2@2$1@1$0#k0^5^4").
Proof.
  intros x imm Hlo Hhi _. unfold v_addiw.
  rewrite Z_to_bv_unsigned.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma v_addiw_id : ltac2:(zQ "70!h9!jc!sa!juc!li6!kt0!kn6>1x@1$1@1$0#k0>0@2$4@2$6@1$0#k0^1@2$5+2+hf@3$2@1$1@1$0#k0@2$3^2Z^2").
Proof.
  intros x Hx. apply bv_eq.
  rewrite (v_addiw_small x 0); [lia | pose proof (u64_range x); lia .. ].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition argv_layout_slack : Z := 4300000%Z.
End FPX1.

(* [comment removed for export] *)

Local Lemma argv_struct_arith : ltac2:(zQ "40!kr9!ks0!k1!lic>1a$2>1e$2>0@2$1Z^2>0@2$1^3+kg0>0@2$1Z^3>0@2$1^4+hg0@2$1@2$0@2$0@2$0+8@2$3@2$0^6+1+8@2$3@2$0^5+1+8+q0+ior8").
Proof. intros. lia. Qed.

Local Lemma argv_sum_arith : ltac2:(zQ "30!ks0!k1!kr9>1a$1>1b$1>0@2$0^2+ior8>0@2$0^2+igggg0@2$0@2$2^4^3+igior8").
Proof. intros. lia. Qed.

Local Lemma argv_mod_arith : ltac2:(zQ "60!ks0!kr9!k1!li6!kt0!lj3>1s$2>1m$2>0@2$0Z^2>0@2$0Z^2>0@2$0^3+igior8>0@2$3@2$1^5+khpsu0@2$4+2+k0@2$5@2$0Z@2$1^6^5@2$3@2$1^6^5@2$4+2+k0").
Proof. intros. lia. Qed.

Local Lemma argv_final_arith : ltac2:(zQ "60!kr9!ks0!k1!li6!kt0!lj3>1s$2>1m$2>1l$2>0@2$1Z^2>0@2$1Z^2>0@2$1^4+igior8>0@2$1^4+hvvvf>0@2$3@2$0^7+khpsu0@2$4+2+k0@2$5@2$1^8@2$0^8^7@2$3@2$0@2$0@2$0^8^7^6+1@2$4+2+k0").
Proof. intros. lia. Qed.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma argv_ptr_bounds : ltac2:(zQ "h30!h9!jc!hp6!kn6!kr9!kqa!lj9!li6!kt0!lk9!lkf!lj3!lm9!lo6!lr9!ls7!mgf!ks0!ks6>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>1k$9>0@1$e^3>0@1$f^3>0@2$c^3@2$5@1$2@1$1@1$0#8^5>0@2$7@2$4@2$3@1$0#k0^7$h0@2$8+2+k0@2$b@2$h1@2$3@1$0#k0^8@2$3@1$0#k0@4$6^8^7^6^5@2$7@2$4@2$4@2$3@1$0#k0@4$6^8^7^6^5@1$h2@2$5@1$1@1$0#8@4$d@1$2@1$1@1$0#8^5^7@1$a@1$1@1$0#8+1@2$8+2+k0").
Proof.
  intros sp av ev k Hva Hve Hk Hsp.
  pose proof (valid_argv_len av Hva) as HavZ.
  pose proof (valid_argv_str_len av k Hva Hk) as HnthZ.
  destruct Hva as [Hlen [Htot [Hstr Hnz]]].
  destruct Hve as [Helen _].
  assert (HevZ : (Z.of_nat (length ev) <= 256)%Z) by exact Helen.
  assert (HtotZ : (Z.of_nat (total_arg_bytes_nat (firstn k av)) <= 2097152)%Z).
  { rewrite total_arg_bytes_Z in Htot.
    pose proof (total_arg_bytes_firstn_le k av). lia. }
  assert (HA : (Z.of_nat (cat_struct_size av ev) <= 10424)%Z).
  { unfold cat_struct_size, auxv_size.
    repeat (rewrite !Nat2Z.inj_add || rewrite !Nat2Z.inj_mul).
    change (Z.of_nat 8) with 8%Z. change (Z.of_nat 1) with 1%Z.
    change (Z.of_nat 160) with 160%Z.
    apply argv_struct_arith;
      solve [ exact HavZ | exact HevZ | apply Nat2Z.is_nonneg ]. }
  assert (Hptr : cat_argv_ptr sp av ev k
    = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  { rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
    rewrite nat_to_word_add_merge. reflexivity. }
  set (n := (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))%nat) in *.
  assert (HnZ : (Z.of_nat n <= 2107576)%Z)
    by (unfold n; rewrite Nat2Z.inj_add; exact (argv_sum_arith _ _ HA HtotZ)).
  assert (Hu : bv_unsigned (sp + nat_to_word n) = (bv_unsigned sp + Z.of_nat n)%Z).
  { unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap64_mod.
    apply Z.mod_small.
    pose proof (u64_range sp) as Hu64.
    unfold argv_layout_slack in Hsp.
    exact (argv_mod_arith _ _ (proj1 Hu64) (Nat2Z.is_nonneg n) HnZ Hsp). }
  rewrite Hptr, Hu.
  unfold argv_layout_slack in Hsp.
  exact (argv_final_arith _ _ _ (Nat2Z.is_nonneg n)
           (Nat2Z.is_nonneg (length (nth k av []))) HnZ HnthZ Hsp).
Qed.

(* [comment removed for export] *)
Lemma step_jalr_x0 : ltac2:(zQ "hd1!h9!jc!sa!qd!k1!va!hg2!hg9!hk7!ho7!sf!hoe!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!ipe!hne!iq5!mi5!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h7@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3imm@1$1@1$0#c>3tgt@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$a@1$h2^5$b>0@3$2@1$3@2$7$5$4@1$h5^6@2$6@2$7$5$4@4$d$5$4@3$h6@3$ha@1$0#5ZKv$e@2$hb@1$0#5Z^5^4+4>0@3$2@1$1@1$0#k0@2$h8^b^6^4@3$2@1$h3$8@2$h4^d@5$9?2fx^c^b^a^9@2$h0$8@5$9?2fx^c@2$h9^5@2$hc@1$0#c^6^a^9").
Proof.
  intros segs regs pc mem rom w rs1 imm tgt Hf He Hd Ht.
  rewrite (step_jalr segs regs pc mem rom w 0 rs1 imm Hf He Hd).
  rewrite Ht. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr_link : ltac2:(zQ "i01!h9!jc!sa!qd!k1!va!hg2!sf!hoe!hg9!hk7!ho7!hp6!hpd!hq4!htd!hu8!hv5!ig3!igf!ii1!ikf!ipe!im3!hne!iq5!in4!ind!mi5!io6!iob!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$c$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3imm@1$1@1$0#c>3tgt@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$d$5$4@3$h6^6^5^4+4>0@3$2$7@3$h7@1$0#5^7@3$hd@1$0#5ZKv$e@2$he@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$h9^d^7^5@3$2@1$h3$a@2$h4^f@5$b?2fx^e^d^c^b@2$h0$a@5$b?2fx@3$ha^e^9@2$hb^d+4@2$hc^6@2$hf@1$0#c^7^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 imm tgt Hf He Hd Hrd Ht.
  rewrite (step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd).
  rewrite Ht, Hrd. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_zero : ltac2:(zQ "90!h9!jc!hq4!sa!hne!iq5!io6!iob!ob>4regs@2$4@1$0#5@1$1@1$0#k0@3$3@1$1@1$0#k0@2$5^1@3$6@1$0#5ZKv$2@2$7@1$0#5Z@2$8@1$0#k0Z").
Proof. reflexivity. Qed.
End FPX2.

(* [comment removed for export] *)
Ltac reg_neq_tac :=
  let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.

(* [comment removed for export] *)
Ltac getr_resolve :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero;
  rewrite ?getr_nz by reg_neq_tac.

(* [comment removed for export] *)
Ltac regupd_resolve :=
  repeat first [ rewrite regupd_same
               | rewrite regupd_other by reg_neq_tac ].

(* [comment removed for export] *)
Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Goal forall regs (v : word), getr (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), getr (regupd regs 8 v) 0 = Z_to_bv 64 0.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), reg_get (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. regupd_resolve. reflexivity. Abort.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition v_divu : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!kn6!mif!ob\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_remu : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!kn6!mj6!ob\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").

(* [comment removed for export] *)
Lemma m_divu : ltac2:(zQ "90!h9!jc!sa!mk0!k1!mk6!mn1!mrb!kn6>1a@1$1@1$0#k0>1b@1$1@1$0#k0>0@1$3@3$2$4@2$8@1$0#k0^1Z@3$2@1$1@1$0#k0@4$6@1$0#k0$5^3^2@2$7^3^2").
Proof.
  intros a b Hb.
  change (mul_div M_DIVU a b)
    with (if (bv_unsigned b =? 0)%Z then Z_to_bv 64 (-1) else bv_divu a b).
  rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. unfold v_divu.
  rewrite bv_divu_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range a). pose proof (u64_range b).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (bv_unsigned a); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma m_remu : ltac2:(zQ "90!h9!jc!sa!mk0!k1!ms5!mn1!mse!kn6>1a@1$1@1$0#k0>1b@1$1@1$0#k0>0@1$3@3$2$4@2$8@1$0#k0^1Z@3$2@1$1@1$0#k0@4$6@1$0#k0$5^3^2@2$7^3^2").
Proof.
  intros a b Hb.
  change (mul_div M_REMU a b)
    with (if (bv_unsigned b =? 0)%Z then a else bv_modu a b).
  rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. unfold v_remu.
  rewrite bv_modu_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range a). pose proof (u64_range b).
  pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)).
  lia.
Qed.

Lemma step_divu : ltac2:(zQ "i21!h9!jc!sa!qd!k1!sf!va!iq5!hg2!hg9!hk7!hne!ho7!hoe!hp6!hpd!hq4!mk0!htd!hu8!hv5!ig3!igf!ii1!ikf!mk6!ki6!im3!in4!ind!mrb!io6!iob!kn6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$e$h2>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$2@1$3@1$1@1$0#i0@2$h4^9^7@2$8@1$1@1$0#i0^4>0@3$2$5@1$h5^5$d>0@3$2@1$3@2$9$6$4@1$h8^6@2$8@2$9$6$4@4$f$6$4@4$ha$h9^5^4^3+4>0@1$h1@3$2$4@2$i1@1$0#k0@2$7^b^4Z@3$2@1$h6$a@2$h7^d@5$c?2fx^c^b^a^9@2$h3$a@5$c?2fxM5\0$5@2$b@1$0#5@1$1@1$0#k0@3$hb@1$0#5^7@3$hf@1$0#5ZKv$h0@2$i0@1$0#5Z^c@3$hc^c^7@2$he@2$7^c^6@2$7^c^5@2$hd^b+4^a^9").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
  erewrite step_mul_gen by eassumption.
  rewrite m_divu by exact Hnz. reflexivity.
Qed.

Lemma step_remu : ltac2:(zQ "i21!h9!jc!sa!qd!k1!sf!va!iq5!hg2!hg9!hk7!hne!ho7!hoe!hp6!hpd!hq4!mk0!htd!hu8!hv5!ig3!igf!ii1!ikf!ms5!ki6!im3!in4!ind!mse!io6!iob!kn6&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$e$h2>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$2@1$3@1$1@1$0#i0@2$h4^9^7@2$8@1$1@1$0#i0^4>0@3$2$5@1$h5^5$d>0@3$2@1$3@2$9$6$4@1$h8^6@2$8@2$9$6$4@4$f$6$4@4$ha$h9^5^4^3+4>0@1$h1@3$2$4@2$i1@1$0#k0@2$7^b^4Z@3$2@1$h6$a@2$h7^d@5$c?2fx^c^b^a^9@2$h3$a@5$c?2fxM5\0$5@2$b@1$0#5@1$1@1$0#k0@3$hb@1$0#5^7@3$hf@1$0#5ZKv$h0@2$i0@1$0#5Z^c@3$hc^c^7@2$he@2$7^c^6@2$7^c^5@2$hd^b+4^a^9").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
  erewrite step_mul_gen by eassumption.
  rewrite m_remu by exact Hnz. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sb : ltac2:(zQ "hf1!h9!jc!sa!qd!k1!va!iq5!ind!hg2!sf!hg9!hk7!ho7!ip2!hoe!hp6!hpd!iv5!htd!hu8!hv5!ig3!igf!ii1!ivc!jg8!ikf!mt8!ji3!hne!jm5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$f$h2>4regs@2$hd@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>0@3$2@1$3@1$1@1$0#i0@2$h4^9^7@2$8@1$1@1$0#i0^4>0@3$2$9@1$h5^5$e>0@3$2@1$3@2$a$5$4@1$ha^6@2$8@2$a$5$4@4$h0$5$4@4$hc$hb^5^4^3+4>0@3$2$9@4$h8^c^9@2$7@2$6^b^6@2$d@1$0#c^4N1$h1@3$2@1$h6$b@2$h7^d@5$c?2fx^c^b^a^9@2$h3$b@5$c?2fx^c@2$7^b+4@3$he^a@2$7@2$6^c^7@2$d@1$0#c^5@2$h9N1@2$6^c^6^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, Hsb, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma N_to_le_bytes_1_small : ltac2:(zQ "90!h9!jc!mte!hp6!lkf!sa!jg8!ob!kn6>1v@1$1@1$0#k0@3$5@1$3@1$1@1$0#8@2$6N1^1@3$2@1$1@1$0#8@2$7@1$0#8@2$8@1$0#k0^1@1$4@1$1@1$0#8").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Zmod_pow2_div8 : ltac2:(zQ "70!kt0!k1!mif!mj6!sa!ks0!mu5>1z$1>1m$1>0@2$5+8^1@3$4$1@2$2@2$3^3@2$0+2^2@2$0+2+8@2$3@2$2^3@2$0+2+8@2$0+2@2$6^2+8").
Proof.
  intros z m Hm.
  rewrite <- !Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases i (m - 8)) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_wrap : ltac2:(zQ "d0!muc!hp6!lk9!sa!mvd!h9!k1!ks0!lic!ng0!ks6!jc!ng8>1n$2>1m$4>1z$6>0@2$7@2$8+8@1$a^3@1$9^2@3$3@1$1@1$b@1$5#8@2$0^4@2$c^3^2@2$0^4^2").
Proof.
  induction n as [|n IH]; intros m z Hm; cbn [Z_to_le_bytes]; [reflexivity|].
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned.
    apply bv_wrap_bv_wrap. lia.
  - replace (Z.shiftr (bv_wrap m z) 8) with (bv_wrap (m - 8) (Z.shiftr z 8)).
    + apply IH. lia.
    + unfold bv_wrap, bv_modulus.
      rewrite !Z.shiftr_div_pow2 by lia.
      rewrite Zmod_pow2_div8 by lia.
      do 2 f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_low16 : ltac2:(zQ "90!h9!jc!hp6!sa!nh2!muc!jg8!nh6!kn6>1u@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$5N2@2$8@1$0#h0@4$7@1$0#k0$4@1$0#h0^1@2$6N2^1").
Proof.
  intro u. unfold word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. lia.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_low32 : ltac2:(zQ "80!h9!jc!hp6!sa!muc!jg8!ni3!kn6>1u@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$4N4@2$7@1$0#i0@1$6^1@2$5N4^1").
Proof.
  intro u. unfold low32, word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. lia.
Qed.

(* [comment removed for export] *)
Lemma step_sw_val : ltac2:(zQ "hf1!h9!jc!sa!qd!k1!va!iq5!ind!hg2!sf!hg9!hk7!ho7!ip2!hoe!hp6!hpd!iv5!htd!hu8!hv5!ig3!igf!ii1!ivc!jg8!ikf!nic!ji3!hne!jm5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$f$h2>4regs@2$hd@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>0@3$2@1$3@1$1@1$0#i0@2$h4^9^7@2$8@1$1@1$0#i0^4>0@3$2$9@1$h5^5$e>0@3$2@1$3@2$a$5$4@1$ha^6@2$8@2$a$5$4@4$h0$5$4@4$hc$hb^5^4^3+4>0@3$2$9@4$h8^c^9@2$7@2$6^b^6@2$d@1$0#c^4N4$h1@3$2@1$h6$b@2$h7^d@5$c?2fx^c^b^a^9@2$h3$b@5$c?2fx^c@2$7^b+4@3$he^a@2$7@2$6^c^7@2$d@1$0#c^5@2$h9N4@2$6^c^6^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sw_at : ltac2:(zQ "hf1!h9!jc!sa!qd!k1!va!hg2!sf!hg9!hk7!iq5!ho7!ind!hoe!hp6!hpd!iv5!htd!hu8!hv5!ig3!igf!ii1!ivc!jg8!ikf!nic!ji3!hne!jm5!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$e$h1>4regs@2$hc@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1a@1$1@1$0#k0>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h3^b^9@2$6@1$1@1$0#i0^6>0@3$2$7@1$h4^7$d>0@3$2@1$3@2$8$5$4@1$h9^8@2$6@2$8$5$4@4$f$5$4@4$hb$ha^7^6^5+4>0@3$2@1$1@1$0#k0@2$c@2$a^d^8@2$he@1$0#c^6^5>0@3$2@1$1@1$0#k0@2$a^e^8^5>0@3$2$7@4$h7^h0^d^7N4$h0@3$2@1$h5$9@2$h6^h1@5$b?2fx^h0^f^e^d@2$h2$9@5$b?2fx^h0@2$c^f+4@3$hd^e^8@2$h8N4^7^d").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma step_sh_val : ltac2:(zQ "hf1!h9!jc!sa!qd!k1!va!iq5!ind!hg2!sf!hg9!hk7!ho7!ip2!hoe!hp6!hpd!iv5!htd!hu8!hv5!ig3!igf!ii1!ivc!jg8!ikf!nj2!ji3!hne!jm5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$f$h2>4regs@2$hd@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>0@3$2@1$3@1$1@1$0#i0@2$h4^9^7@2$8@1$1@1$0#i0^4>0@3$2$9@1$h5^5$e>0@3$2@1$3@2$a$5$4@1$ha^6@2$8@2$a$5$4@4$h0$5$4@4$hc$hb^5^4^3+4>0@3$2$9@4$h8^c^9@2$7@2$6^b^6@2$d@1$0#c^4N2$h1@3$2@1$h6$b@2$h7^d@5$c?2fx^c^b^a^9@2$h3$b@5$c?2fx^c@2$7^b+4@3$he^a@2$7@2$6^c^7@2$d@1$0#c^5@2$h9N2@2$6^c^6^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low16, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sh_at : ltac2:(zQ "hf1!h9!jc!sa!qd!k1!va!hg2!sf!hg9!hk7!iq5!ho7!ind!hoe!hp6!hpd!iv5!htd!hu8!hv5!ig3!igf!ii1!ivc!jg8!ikf!nj2!ji3!hne!jm5!ip2&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$e$h1>4regs@2$hc@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1a@1$1@1$0#k0>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h3^b^9@2$6@1$1@1$0#i0^6>0@3$2$7@1$h4^7$d>0@3$2@1$3@2$8$5$4@1$h9^8@2$6@2$8$5$4@4$f$5$4@4$hb$ha^7^6^5+4>0@3$2@1$1@1$0#k0@2$c@2$a^d^8@2$he@1$0#c^6^5>0@3$2@1$1@1$0#k0@2$a^e^8^5>0@3$2$7@4$h7^h0^d^7N2$h0@3$2@1$h5$9@2$h6^h1@5$b?2fx^h0^f^e^d@2$h2$9@5$b?2fx^h0@2$c^f+4@3$hd^e^8@2$h8N2^7^d").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_app : ltac2:(zQ "d0!h9!jc!hp6!qd!hg2!sa!kr3!lk9!nj8!nl0!nl7!htd!nm6>4segs@1$2$b>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2n1$7>2n2$7>1a@1$1@1$0#k0>3bs1@1$2@1$1@1$0#8>3bs2@1$2@1$1@1$0#8>0@3$5@1$3@1$2@1$1@1$0#8@4$6^7^6^3^5@2$4@1$2@1$1@1$0#8^2>0@3$5@1$3@1$2@1$1@1$0#8@4$6^8^7@3$c@1$0#k0^4@1$a^6^5@2$4@1$2@1$1@1$0#8^2@3$5@1$3@1$2@1$1@1$0#8@4$6^9^8^5@2$9^7^6@2$4@1$2@1$1@1$0#8@3$8@1$1@1$0#8^4^3").
Proof.
  intros segs mem n1. induction n1 as [|n1 IH]; intros n2 a bs1 bs2 H1 H2.
  - cbn in H1. injection H1 as <-. cbn [app].
    rewrite word_add_0 in H2. exact H2.
  - change (S n1 + n2)%nat with (S (n1 + n2))%nat.
    cbn [rdn] in H1 |- *.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|]; [|discriminate].
    destruct (rdn segs mem (a+1) n1) as [rest|] eqn:Er; [|discriminate].
    injection H1 as <-.
    rewrite (IH n2 (a+1) rest bs2 Er); [reflexivity|].
    replace (a + 1 + nat_to_word n1) with (a + nat_to_word (S n1))
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    exact H2.
Qed.

Lemma rdn_nth : ltac2:(zQ "h00!h9!jc!hp6!qd!hg2!lk9!sa!kr3!mte!lkf!lm9!lo6!nl7!htd!ob!nm6>4segs@1$2$d>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$5>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>1j$5>0@3$6@1$3@1$2@1$1@1$0#8@4$7^6^5^3^4@2$4@1$2@1$1@1$0#8^2>0@2$a^2^5@3$6@1$3@1$2@1$1@1$0#8@4$7^8^7@3$f@1$0#k0^5@1$c^3N1@2$4@1$2@1$1@1$0#8@3$8@1$1@1$0#8@4$b@1$1@1$0#8^3^4@2$e@1$0#8Z@1$9@1$1@1$0#8").
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
    as [b|] eqn:Eb; [|discriminate].
  destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
  injection H as <-.
  destruct j as [|j].
  - rewrite word_add_0. cbn [rdn nth]. rewrite Eb. reflexivity.
  - cbn [nth].
    replace (a + nat_to_word (S j)) with (a + 1 + nat_to_word j)
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    apply (IH (a+1) rest j Er). lia.
Qed.

(* [comment removed for export] *)
Lemma v_addi_m : ltac2:(zQ "b0!h9!jc!kn6!sa!k1!ind!ks0!li6!nmf!mu5!ob>1x@1$1@1$0#k0>1k$4>0@2$6^1@2$2@1$0#k0^2>0@2$7Z^2@3$3@1$1@1$0#k0@2$5^4@1$8^3@2$a@1$0#k0@2$9@2$2@1$0#k0^4^3").
Proof. intros x k _ _. reflexivity. Qed.

Lemma rdn_skipn : ltac2:(zQ "e0!h9!jc!hp6!qd!hg2!lk9!sa!kr3!nn6!nnd!no3!nl7!htd!nm6>4segs@1$2$c>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$5>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>1k$5>0@3$6@1$3@1$2@1$1@1$0#8@4$7^6^5^3^4@2$4@1$2@1$1@1$0#8^2>0@2$9^2^5@3$6@1$3@1$2@1$1@1$0#8@4$7^8^7@3$d@1$0#k0^5@1$b^3@2$8^6^3@2$4@1$2@1$1@1$0#8@3$a@1$1@1$0#8^3^4").
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0)%nat by lia. subst k. rewrite word_add_0.
    cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct k as [|k].
    + rewrite word_add_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [Nat.sub skipn].
      replace (a + nat_to_word (S k)) with (a + 1 + nat_to_word k)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest k Er). lia.
Qed.

Lemma rdn_firstn : ltac2:(zQ "b0!h9!jc!hp6!qd!hg2!lk9!sa!kr3!nnd!noc!htd>4segs@1$2$a>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$5>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>1k$5>0@3$6@1$3@1$2@1$1@1$0#8@4$7^6^5^3^4@2$4@1$2@1$1@1$0#8^2>0@2$8^2^5@3$6@1$3@1$2@1$1@1$0#8@4$7^8^7^5^3@2$4@1$2@1$1@1$0#8@3$9@1$1@1$0#8^3^4").
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0)%nat by lia. subst k. cbn in H |- *.
    injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct k as [|k]; [reflexivity|].
    cbn [rdn firstn]. rewrite Eb.
    rewrite (IH (a+1) rest k Er) by lia. reflexivity.
Qed.
End FPX3.
(* [comment removed for export] *)
