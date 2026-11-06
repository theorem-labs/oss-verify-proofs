(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XHoare XRefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XMemsetLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EhMemcpyBase EhMemcpy EhMemset.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XSumsSpecLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import EhX_plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~07FPState89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX~~~~~~k89copy_spec69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~p6floaded_segments89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~te5two64k89fill_spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~hj79COPY_SPEChj79FILL_SPEC" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma eh_copy_spec_memcpy : ltac2:(zQ "30!jf!oa!sc>2fx$0@3$1^1$2+uqtq8").
Proof.
  intros fx mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : EhMemcpyBase.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  ndestruct (EhMemcpy.ref_memcpy mem0 dst src n bs (seg_rom RSEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 0xeada8) with (0xeada8%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma eh_fill_spec_memset : ltac2:(zQ "40!hi3!jf!hib!sc>2fx$1@4$2^1$3+urji8$0").
Proof.
  intros fx. apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (EhMemset.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

(* [comment removed for export] *)
Theorem eh_copy_spec : ltac2:(zQ "10!hn6$0").
Proof. intros fx. exact (eh_copy_spec_memcpy fx). Qed.
Theorem eh_fill_spec : ltac2:(zQ "10!ho3$0").
Proof. intros fx. exact (eh_fill_spec_memset fx). Qed.
