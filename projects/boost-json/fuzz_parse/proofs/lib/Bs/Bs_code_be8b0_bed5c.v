(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh3Bs_code_be8b0_bed5c~~~~~~t67W_bea3069OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~hiafloaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhna5instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChr5adecode_anyhna5BC_LThna6Brancht67W_bea34hna7ALU_ADDhna5OpImmt67W_bea38hna3Jalt67W_bea3ct67W_bea40t67W_bea44t67W_bea48hna6BC_LTUt67W_beb84t67W_beb88hna4Jalr" s.
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
Definition W_bea30 : bv 32 := 0x000ac663.
Lemma F_bea30 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hi0!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqj0Kv$4@2$a@1$0#k0+ruqj0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea30 : ltac2:(zQ "f0!h9!l5!hn7!hpe!l9!le!hq7!nd!o4!hqe!od!htb!hu9!hv2!hi0@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+h5Kv$1@2$5@1$0#5+h5@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+cKv$1@2$5@1$0#d+c+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea34 : bv 32 := 0x00050413.
Lemma F_bea34 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hvc!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqj4Kv$4@2$a@1$0#k0+ruqj4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea34 : ltac2:(zQ "f0!h9!l5!hn7!hpe!l9!le!hq7!nd!o4!hqe!od!htb!ig6!ih1!hvc@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea38 : bv 32 := 0x0780006f.
Lemma F_bea38 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iha!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqj8Kv$4@2$a@1$0#k0+ruqj8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea38 : ltac2:(zQ "e0!h9!hn7!hpe!hq7!l5!l9!le!nd!o4!hqe!od!htb!ii4!iha@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5ZKv$4@2$6@1$0#5Z@3$5@1$0#h5+n8Kv$4@2$6@1$0#h5+n8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea3c : bv 32 := 0x148000ef.
Lemma F_bea3c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iib!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqjcKv$4@2$a@1$0#k0+ruqjc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea3c : ltac2:(zQ "e0!h9!hn7!hpe!hq7!l5!l9!le!nd!o4!hqe!od!htb!ii4!iib@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+hk8Kv$4@2$6@1$0#h5+hk8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea40 : bv 32 := 0x0fb00593.
Lemma F_bea40 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ij5!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqk0Kv$4@2$a@1$0#k0+ruqk0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea40 : ltac2:(zQ "f0!h9!l5!hn7!hpe!l9!le!hq7!nd!o4!hqe!od!htb!ig6!ih1!ij5@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#c+vbKv$1@2$5@1$0#c+vb+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea44 : bv 32 := 0x00050413.
Lemma F_bea44 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ijf!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqk4Kv$4@2$a@1$0#k0+ruqk4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea44 : ltac2:(zQ "f0!h9!l5!hn7!hpe!l9!le!hq7!nd!o4!hqe!od!htb!ig6!ih1!ijf@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea48 : bv 32 := 0x06b56463.
Lemma F_bea48 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ik9!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruqk8Kv$4@2$a@1$0#k0+ruqk8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_bea48 : ltac2:(zQ "f0!h9!l5!hn7!hpe!l9!le!hq7!nd!o4!hqe!od!htb!il3!hv2!ik9@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#d+m8Kv$1@2$5@1$0#d+m8+4").
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
Definition W_beb84 : bv 32 := 0x00000513.
Lemma F_beb84 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ild!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruro4Kv$4@2$a@1$0#k0+ruro4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_beb84 : ltac2:(zQ "f0!h9!l5!hn7!hpe!l9!le!hq7!nd!o4!hqe!od!htb!ig6!ih1!ild@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb88 : bv 32 := 0x00008067.
Lemma F_beb88 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!im7!hm4!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ruro8Kv$4@2$a@1$0#k0+ruro8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_beb88 : ltac2:(zQ "e0!h9!l5!hn7!hpe!l9!le!hq7!nd!o4!hqe!od!htb!in1!im7@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
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
