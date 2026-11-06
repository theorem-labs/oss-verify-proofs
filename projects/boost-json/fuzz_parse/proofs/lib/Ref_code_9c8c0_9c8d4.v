(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libh4Ref_code_9c8c0_9c8d4~~~~~~t67W_9c8c069OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hi8floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn45instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChqfadecode_anyhn45Auipct67W_9c8c4hn47ALU_ADDhn45OpImmt67W_9c8c8t67W_9c8ccm54truehn47AMO_ADDhn42AWhn43Amot67W_9c8d0hn44Jalr" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9c8c0 : bv 32 := 0x0006d517.
Lemma F_9c8c0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hhe!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+psos0Kv$4@2$a@1$0#k0+psos0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9c8c0 : ltac2:(zQ "e0!h9!hn1!hp8!hq1!l5!l9!le!nd!o4!hq8!od!ht5!hu3!hhe@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+aKv$4@2$6@1$0#5+a@3$5@1$0#h4+mdKv$4@2$6@1$0#h4+md+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c8c4 : bv 32 := 0x62850513.
Lemma F_9c8c4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!huc!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+psos4Kv$4@2$a@1$0#k0+psos4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9c8c4 : ltac2:(zQ "f1!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hv6!ig1!huc&@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+mi8Kv$1@2$5@1$0#c+mi8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c8c8 : bv 32 := 0x00100593.
Lemma F_9c8c8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iga!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+psos8Kv$4@2$a@1$0#k0+psos8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9c8c8 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hv6!ig1!iga@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#c+1Kv$1@2$5@1$0#c+1+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c8cc : bv 32 := 0x06b5252f.
Lemma F_9c8cc : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih4!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+psoscKv$4@2$a@1$0#k0+psosc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9c8cc : ltac2:(zQ "h11!h9!l5!hn1!hp8!l9!le!hq1!ihe!nd!o4!hq8!od!ht5!ii5!ij0!ij6!ih4&@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$b@1$9@2$6$3$2@1$c$h0@2$8@2$6$3$2@4$a$3$2@7$f$d$e$7$7~0~0@3$4@1$0#5+bKv$1@2$5@1$0#5+b+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c8d0 : bv 32 := 0x00008067.
Lemma F_9c8d0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ijd!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+psot0Kv$4@2$a@1$0#k0+psot0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9c8d0 : ltac2:(zQ "e0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!ik7!ijd@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.
