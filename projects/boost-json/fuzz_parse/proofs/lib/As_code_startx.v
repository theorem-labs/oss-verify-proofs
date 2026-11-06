(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAs_code_startx~~~~~~t68W_193a4069OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~hi2floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhmd5instrm54prodm54pairm54true3h5LinuxProcessSemantics5Riscv7DecodeChqfadecode_anyhmd|41L1o1a1dhmd3SZ8t68W_193a44hmd7ALU_ADDhmd5OpImmt68W_193a48hmd5BC_NEhmd6Brancht68W_193afchmd5Storet68W_193b00t68W_193b04m55falsehmd3SZ1t68W_193b08hmd5BC_EQt68W_193b0c" s.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_193a40 : bv 32 := 0x0004b503.
Lemma F_193a40 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hh7!hl7!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpjqk0Kv$4@2$a@1$0#k0+hpjqk0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_193a40 : ltac2:(zQ "h00!h9!l5!hma!hp1!l9!le!hpa!nd!o4!hq1!hq8!od!ht5!hu3!hv0!hh7@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193a44 : bv 32 := 0x00848493.
Lemma F_193a44 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hv7!hl7!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpjqk4Kv$4@2$a@1$0#k0+hpjqk4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_193a44 : ltac2:(zQ "f1!h9!l5!hma!hp1!l9!le!hpa!nd!o4!hq1!od!ht5!ig2!igd!hv7&@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193a48 : bv 32 := 0xfe051ce3.
Lemma F_193a48 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih6!hl7!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpjqk8Kv$4@2$a@1$0#k0+hpjqk8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_193a48 : ltac2:(zQ "f0!h9!l5!hma!hp1!l9!le!hpa!nd!o4!hq1!od!ht5!ii1!iia!ih6@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hvv8Kv$1@2$5@1$0#d+hvv8+4").
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_193afc : bv 32 := 0x00b53023.
Lemma F_193afc : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ij4!hl7!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpjqvcKv$4@2$a@1$0#k0+hpjqvc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_193afc : ltac2:(zQ "f0!h9!l5!hma!hp1!l9!le!hpa!nd!o4!hq1!od!ht5!hv0!ijf!ij4@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193b00 : bv 32 := 0x00158593.
Lemma F_193b00 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ik8!hl7!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpjrg0Kv$4@2$a@1$0#k0+hpjrg0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_193b00 : ltac2:(zQ "f1!h9!l5!hma!hp1!l9!le!hpa!nd!o4!hq1!od!ht5!ig2!igd!ik8&@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+1Kv$1@2$5@1$0#c+1+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193b04 : bv 32 := 0xfff5c683.
Lemma F_193b04 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!il3!hl7!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpjrg4Kv$4@2$a@1$0#k0+hpjrg4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_193b04 : ltac2:(zQ "h00!h9!l5!hma!hp1!l9!le!hpa!nd!ile!o4!hq1!od!ht5!hu3!im6!il3@3$b@1$9@2$6$3$2@1$c$f@2$7@2$6$3$2@4$a$3$2@5$d$e$8@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#c+vvfKv$1@2$5@1$0#c+vvf+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193b08 : bv 32 := 0xfec68ae3.
Lemma F_193b08 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!imd!hl7!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpjrg8Kv$4@2$a@1$0#k0+hpjrg8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_193b08 : ltac2:(zQ "f0!h9!l5!hma!hp1!l9!le!hpa!nd!o4!hq1!od!ht5!in8!iia!imd@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193b0c : bv 32 := 0xfe069ae3.
Lemma F_193b0c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!io1!hl7!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpjrgcKv$4@2$a@1$0#k0+hpjrgc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_193b0c : ltac2:(zQ "f0!h9!l5!hma!hp1!l9!le!hpa!nd!o4!hq1!od!ht5!ii1!iia!io1@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4+4").
Proof. vm_refl. Qed.
