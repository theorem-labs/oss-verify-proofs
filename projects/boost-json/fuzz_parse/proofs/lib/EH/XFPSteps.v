(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq37Corelib4Init9Datatypesla6optionla4listla4Some01Z3h5LinuxProcessSemantics5Riscv5Instroc5instrla4prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsrfdmachine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~hg64mksthg66v_addila4boolla5falsela4pair02N03h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehn1h0le_bytes_to_word3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehr57Segmentrf9MachineOkrfafetch_wordrf8is_ecallrfemachine_resultrf4step3h5LinuxProcessSemantics5Riscv7DecodeCij1adecode_anyoc|51F1L1o1a1doc5FMT_D3h5LinuxProcessSemantics5Riscv7Preludeinb5bvmapinb9bvmap_sethg67FPStatehg66fp_csrhg67fp_regshg64getrhg64mkFPhg63rdnhfabv_extracthf9bv_signedla4truerf8store_okrfh0word_to_le_bytesoc6FStore3h5LinuxProcessSemantics5Riscv3Semjj67reg_get79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExec~~~~~~jm36wbytesoc7FMV_F_Xoc3Fmv" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac fp_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val Sem.exec_csr
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.fget Sem.fset Sem.with_fregs Sem.with_fcsr Sem.fread Sem.fwrite
     Sem.accrue Sem.resolve_rm Sem.frm_of
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     RiscvSemantics.access_value RiscvSemantics.drop_access_report
     ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst fp_regs fp_csr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fp_step_fld : ltac2:(zQ "i41!h9!jc!l5!n2!nb!o2!o9!r0!r8!v6!hk5!hkd!hl7!hle!hm6!hmd!hq0!hua!hv5!ig1!ige!ih9!iia!il7!im5!in3!iq1!iqa!ir7!is2!isc!it7!itf!iu7!iue!ivb&>0@1$1@1$0#k0@1$3@1$1@1$0#8>2fx$hc>4segs@1$4$h1>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1a@1$1@1$0#k0>2bs@1$4@1$1@1$0#8>0@3$2@1$3@1$1@1$0#i0@2$h3^b^9@2$5@1$1@1$0#i0^6>0@3$2$c@1$h4^7$d>0@3$2@1$3@2$8$7$6@1$h7^8@2$5@2$8$7$6@4$e$7$6@4$h8$h9^7^6^5+4>0@3$2@1$1@1$0#k0@2$b@2$hf^d^7@2$i3@1$0#c^6^5>0@3$2@1$3@1$4@1$1@1$0#8@4$i1^f^c^6N8@2$5@1$4@1$1@1$0#8^5@3$2@1$h5$9@2$h6^h0@5$a^h1^f^e^d^c@2$h2$9@5$a@2$i0@5$hb@1$0#5@1$1@1$0#k0^a@4$i2@1$0#k0$f@1$0#k0@1$h0^6@1$he^h1@1$hd^h1^f@2$b^e+4^d^c").
Proof.
  intros fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr.
  fp_pipeline Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
  rewrite ov_rdn, b_addsext, Ha, Hr. cbv beta iota.
  cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fp_step_fsd : ltac2:(zQ "i21!h9!jc!l5!n2!o9!r0!o2!hl7!r8!v6!hk5!hkd!hle!nb!hm6!jg7!hua!hv5!ig1!ige!ih9!iia!jge!jh9!il7!in3!jid!iq1!jl8!jq1!ir7!isc!it7!ivb&>0@1$1@1$0#k0@1$3@1$1@1$0#8>2fx$he>4segs@1$d$h0>4regs@2$hb@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1a@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$c>0@3$2@1$3@2$8$5$4@1$h8^7@2$6@2$8$5$4@4$e$5$4@4$ha$h9^6^5^4+4>0@3$2@1$1@1$0#k0@2$b@2$i0^c^7@2$i1@1$0#c^5^4>0@3$2$7@4$h6^e^b^5N8$f@3$2@1$h4$9@2$h5^f@5$a^h0^e^d^c^b@2$h1$9@5$a^h0^e@2$b^d+4@3$hd^c^6@2$h7N8@2$hc@1$hf^h0^8^b").
Proof.
  intros fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok.
  fp_pipeline Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
  rewrite b_addsext, Ha, Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4. destruct fx; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fp_step_fmv_d_x : ltac2:(zQ "i01!h9!jc!n2!l5!o9!r0!o2!r8!v6!hk5!hl7!hle!nb!hm6!hua!hv5!ig1!ige!ih9!iia!il7!in3!jqb!jr5!iq1!iqa!ir7!is2!isc!it7!itf!hkd&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2fx$ha>4segs@1$c$e>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h0^8^6@2$6@1$1@1$0#i0^3>0@3$3$a@1$h1^4$b>0@3$3@1$2@2$7$5$4@1$h4^5@2$6@2$7$5$4@4$d$5$4@4$h7$h6$h5^4^3+4@3$3@1$h2$8@2$h3^b@5$9^c^a^9^8^7@2$f$8@5$9@2$he@5$h9@1$0#5@1$1@1$0#k0^5@2$hd^a^4@1$hc^c@1$hb^c^a@2$hf^9+4^8^7").
Proof.
  intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
  fp_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
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
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
