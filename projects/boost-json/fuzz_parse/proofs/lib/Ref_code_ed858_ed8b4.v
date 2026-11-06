(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libh4Ref_code_ed858_ed8b4~~~~~~t67W_ed85869OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hi8floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn45instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChqfadecode_anyhn47ALU_ADDhn45OpImmt67W_ed85ct67W_ed860hn44Jalr" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ed858 : bv 32 := 0x00050213.
Lemma F_ed858 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hhe!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+utol8Kv$4@2$a@1$0#k0+utol8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ed858 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!hhe@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+4Kv$1@2$5@1$0#5+4@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed85c : bv 32 := 0x00000513.
Lemma F_ed85c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hv7!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+utolcKv$4@2$a@1$0#k0+utolc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ed85c : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!hv7@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ed860 : bv 32 := 0x00008067.
Lemma F_ed860 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ig1!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+utom0Kv$4@2$a@1$0#k0+utom0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_ed860 : ltac2:(zQ "e0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!igb!ig1@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
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
