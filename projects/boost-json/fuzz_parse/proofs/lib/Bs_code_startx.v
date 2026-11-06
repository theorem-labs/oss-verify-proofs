(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBs_code_startx~~~~~~t68W_1907b869OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~hi2floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn25instrm54prodm54pairm54true3h5LinuxProcessSemantics5Riscv7DecodeChr4adecode_anyhn2|41L1o1a1dhn23SZ8t68W_1907bchn27ALU_ADDhn25OpImmt68W_1907c0hn25BC_NEhn26Brancht68W_190874hn25Storet68W_190878t68W_19087cm55falsehn23SZ1t68W_190880hn25BC_EQt68W_190884" s.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1907b8 : bv 32 := 0x0004b503.
Lemma F_1907b8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hh7!hlc!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpgnr8Kv$4@2$a@1$0#k0+hpgnr8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_1907b8 : ltac2:(zQ "h00!h9!l5!hmf!hp6!l9!le!hpf!nd!o4!hq6!hqd!od!hta!hu8!hv5!hh7@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1907bc : bv 32 := 0x00848493.
Lemma F_1907bc : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hvc!hlc!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpgnrcKv$4@2$a@1$0#k0+hpgnrc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_1907bc : ltac2:(zQ "f1!h9!l5!hmf!hp6!l9!le!hpf!nd!o4!hq6!od!hta!ig7!ih2!hvc&@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1907c0 : bv 32 := 0xfe051ce3.
Lemma F_1907c0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ihb!hlc!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpgns0Kv$4@2$a@1$0#k0+hpgns0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_1907c0 : ltac2:(zQ "f0!h9!l5!hmf!hp6!l9!le!hpf!nd!o4!hq6!od!hta!ii6!iif!ihb@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hvv8Kv$1@2$5@1$0#d+hvv8+4").
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_190874 : bv 32 := 0x00b53023.
Lemma F_190874 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ij9!hlc!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpgon4Kv$4@2$a@1$0#k0+hpgon4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_190874 : ltac2:(zQ "f0!h9!l5!hmf!hp6!l9!le!hpf!nd!o4!hq6!od!hta!hv5!ik4!ij9@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190878 : bv 32 := 0x00158593.
Lemma F_190878 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ikd!hlc!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpgon8Kv$4@2$a@1$0#k0+hpgon8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_190878 : ltac2:(zQ "f1!h9!l5!hmf!hp6!l9!le!hpf!nd!o4!hq6!od!hta!ig7!ih2!ikd&@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+1Kv$1@2$5@1$0#c+1+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19087c : bv 32 := 0xfff5c683.
Lemma F_19087c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!il8!hlc!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpgoncKv$4@2$a@1$0#k0+hpgonc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_19087c : ltac2:(zQ "h00!h9!l5!hmf!hp6!l9!le!hpf!nd!im3!o4!hq6!od!hta!hu8!imb!il8@3$b@1$9@2$6$3$2@1$c$f@2$7@2$6$3$2@4$a$3$2@5$d$e$8@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#c+vvfKv$1@2$5@1$0#c+vvf+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190880 : bv 32 := 0xfec68ae3.
Lemma F_190880 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!in2!hlc!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpgoo0Kv$4@2$a@1$0#k0+hpgoo0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_190880 : ltac2:(zQ "f0!h9!l5!hmf!hp6!l9!le!hpf!nd!o4!hq6!od!hta!ind!iif!in2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_190884 : bv 32 := 0xfe069ae3.
Lemma F_190884 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!io6!hlc!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+hpgoo4Kv$4@2$a@1$0#k0+hpgoo4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_190884 : ltac2:(zQ "f0!h9!l5!hmf!hp6!l9!le!hpf!nd!o4!hq6!od!hta!ii6!iif!io6@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4+4").
Proof. vm_refl. Qed.
