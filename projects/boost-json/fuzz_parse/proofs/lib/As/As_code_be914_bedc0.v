(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash3As_code_be914_bedc0~~~~~~t67W_bea9469OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~hiafloaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn55instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChr0adecode_anyhn55BC_LThn56Brancht67W_bea98hn57ALU_ADDhn55OpImmt67W_bea9chn53Jalt67W_beaa0t67W_beaa4t67W_beaa8t67W_beaachn56BC_LTUt67W_bebe8t67W_bebechn54Jalr" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_bea94 : bv 32 := 0x000ac663.
Lemma F_bea94 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hi0!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqp4Kv$4@2$a@1$0#k0+ruqp4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea94 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!hud!hi0@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+h5Kv$1@2$5@1$0#5+h5@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+cKv$1@2$5@1$0#d+c+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea98 : bv 32 := 0x00050413.
Lemma F_bea98 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hv7!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqp8Kv$4@2$a@1$0#k0+ruqp8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea98 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig1!igc!hv7@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea9c : bv 32 := 0x0780006f.
Lemma F_bea9c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih5!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqpcKv$4@2$a@1$0#k0+ruqpc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea9c : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!ihf!ih5@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5ZKv$4@2$6@1$0#5Z@3$5@1$0#h5+n8Kv$4@2$6@1$0#h5+n8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaa0 : bv 32 := 0x148000ef.
Lemma F_beaa0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ii6!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqq0Kv$4@2$a@1$0#k0+ruqq0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_beaa0 : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!ihf!ii6@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+hk8Kv$4@2$6@1$0#h5+hk8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaa4 : bv 32 := 0x0fb00593.
Lemma F_beaa4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ij0!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqq4Kv$4@2$a@1$0#k0+ruqq4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_beaa4 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig1!igc!ij0@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#c+vbKv$1@2$5@1$0#c+vb+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaa8 : bv 32 := 0x00050413.
Lemma F_beaa8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ija!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqq8Kv$4@2$a@1$0#k0+ruqq8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_beaa8 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig1!igc!ija@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaac : bv 32 := 0x06b56463.
Lemma F_beaac : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ik4!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqqcKv$4@2$a@1$0#k0+ruqqc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_beaac : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ike!hud!ik4@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#d+m8Kv$1@2$5@1$0#d+m8+4").
Proof. vm_refl. Qed.

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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_bebe8 : bv 32 := 0x00000513.
Lemma F_bebe8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!il8!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruru8Kv$4@2$a@1$0#k0+ruru8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bebe8 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig1!igc!il8@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebec : bv 32 := 0x00008067.
Lemma F_bebec : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!im2!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+rurucKv$4@2$a@1$0#k0+ruruc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bebec : ltac2:(zQ "e0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!imc!im2@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

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
