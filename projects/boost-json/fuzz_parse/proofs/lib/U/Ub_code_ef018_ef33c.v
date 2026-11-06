(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1Uh3Ub_code_ef018_ef33c~~~~~~t67W_ef01869OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hi9floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn55instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChr0adecode_anyhn55Auipct67W_ef01cm54truehn5|41L1o1a1dhn53SZ1t67W_ef020hn55BC_EQhn56Brancht67W_ef210hn54Jalrt67W_ef2a0hn53SZ4t67W_ef2a4hn55BC_LTt67W_ef2a8" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ef018 : bv 32 := 0x00040597.
Lemma F_ef018 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hhf!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uvgh8Kv$4@2$a@1$0#k0+uvgh8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ef018 : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!hu4!hhf@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+bKv$4@2$6@1$0#5+b@3$5@1$0#h4+k0Kv$4@2$6@1$0#h4+k0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ef01c : bv 32 := 0xe7358683.
Lemma F_ef01c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hud!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uvghcKv$4@2$a@1$0#k0+uvghc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ef01c : ltac2:(zQ "h00!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!hv7!od!ht6!hve!igb!hud@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#c+un3Kv$1@2$5@1$0#c+un3+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ef020 : bv 32 := 0x1e068863.
Lemma F_ef020 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih2!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uvgi0Kv$4@2$a@1$0#k0+uvgi0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ef020 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ihc!ii5!ih2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hv0Kv$1@2$5@1$0#d+hv0+4").
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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_ef210 : bv 32 := 0x00008067.
Lemma F_ef210 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iif!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uvih0Kv$4@2$a@1$0#k0+uvih0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ef210 : ltac2:(zQ "e0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ij9!iif@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
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
Definition W_ef2a0 : bv 32 := 0x00052583.
Lemma F_ef2a0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ik1!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uviq0Kv$4@2$a@1$0#k0+uviq0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ef2a0 : ltac2:(zQ "h00!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!hv7!od!ht6!hve!ikb!ik1@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ef2a4 : bv 32 := 0x0005c463.
Lemma F_ef2a4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!il2!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uviq4Kv$4@2$a@1$0#k0+uviq4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ef2a4 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ilc!ii5!il2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+8Kv$1@2$5@1$0#d+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ef2a8 : bv 32 := 0x00008067.
Lemma F_ef2a8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!im5!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uviq8Kv$4@2$a@1$0#k0+uviq8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ef2a8 : ltac2:(zQ "e0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ij9!im5@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
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
