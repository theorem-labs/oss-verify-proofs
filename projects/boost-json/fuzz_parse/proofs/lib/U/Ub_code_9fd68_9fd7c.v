(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1Uh3Ub_code_9fd68_9fd7c~~~~~~t67W_9fd6869OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hi9floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn55instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChr0adecode_anyhn55Auipct67W_9fd6chn57ALU_ADDhn55OpImmt67W_9fd70t67W_9fd74m54truehn57AMO_ADDhn52AWhn53Amot67W_9fd78hn54Jalr" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9fd68 : bv 32 := 0x0006d517.
Lemma F_9fd68 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hhf!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+pvtm8Kv$4@2$a@1$0#k0+pvtm8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9fd68 : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!hu4!hhf@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+aKv$4@2$6@1$0#5+a@3$5@1$0#h4+mdKv$4@2$6@1$0#h4+md+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fd6c : bv 32 := 0x6c050513.
Lemma F_9fd6c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hud!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+pvtmcKv$4@2$a@1$0#k0+pvtmc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9fd6c : ltac2:(zQ "f1!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hv7!ig2!hud&@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+ms0Kv$1@2$5@1$0#c+ms0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fd70 : bv 32 := 0x00100593.
Lemma F_9fd70 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!igb!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+pvtn0Kv$4@2$a@1$0#k0+pvtn0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9fd70 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hv7!ig2!igb@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#c+1Kv$1@2$5@1$0#c+1+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fd74 : bv 32 := 0x06b5252f.
Lemma F_9fd74 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih5!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+pvtn4Kv$4@2$a@1$0#k0+pvtn4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9fd74 : ltac2:(zQ "h11!h9!l5!hn2!hp9!l9!le!hq2!ihf!nd!o4!hq9!od!ht6!ii6!ij1!ij7!ih5&@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$b@1$9@2$6$3$2@1$c$h0@2$8@2$6$3$2@4$a$3$2@7$f$d$e$7$7~0~0@3$4@1$0#5+bKv$1@2$5@1$0#5+b+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fd78 : bv 32 := 0x00008067.
Lemma F_9fd78 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ije!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+pvtn8Kv$4@2$a@1$0#k0+pvtn8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_9fd78 : ltac2:(zQ "e0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ik8!ije@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.
