(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libh4Ref_code_eb9d4_eba18~~~~~~t67W_eb9d469OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hi8floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn45instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChqfadecode_anyhn47ALU_ADDhn45OpImmt67W_eb9d8hn43SZ8hn45Storet67W_eb9dct67W_eb9e0t67W_eb9e4t67W_eb9e8t67W_eb9ect67W_eb9f0t67W_eb9f4hn43Jalt67W_eb9f8hn45BC_EQhn46Brancht67W_eb9fchn47ALU_SUBhn42Opt67W_eba00t67W_eba04m54truehn4|41L1o1a1dt67W_eba08t67W_eba0ct67W_eba10t67W_eba14hn44Jalr" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_eb9d4 : bv 32 := 0xfe010113.
Lemma F_eb9d4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hhe!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpt4Kv$4@2$a@1$0#k0+urpt4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9d4 : ltac2:(zQ "f1!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!hhe&@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+vu0Kv$1@2$5@1$0#c+vu0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9d8 : bv 32 := 0x00113c23.
Lemma F_eb9d8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hv7!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpt8Kv$4@2$a@1$0#k0+urpt8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9d8 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!ig1!ig8!hv7@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#c+h8Kv$1@2$5@1$0#c+h8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9dc : bv 32 := 0x00813823.
Lemma F_eb9dc : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih1!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urptcKv$4@2$a@1$0#k0+urptc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9dc : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!ig1!ig8!ih1@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#c+h0Kv$1@2$5@1$0#c+h0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9e0 : bv 32 := 0x00913423.
Lemma F_eb9e0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ihb!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpu0Kv$4@2$a@1$0#k0+urpu0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9e0 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!ig1!ig8!ihb@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9e4 : bv 32 := 0x00058413.
Lemma F_eb9e4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ii5!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpu4Kv$4@2$a@1$0#k0+urpu4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9e4 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!ii5@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9e8 : bv 32 := 0x00050493.
Lemma F_eb9e8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iif!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpu8Kv$4@2$a@1$0#k0+urpu8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9e8 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!iif@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9ec : bv 32 := 0x00000593.
Lemma F_eb9ec : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ij9!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpucKv$4@2$a@1$0#k0+urpuc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9ec : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!ij9@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9f0 : bv 32 := 0x00040613.
Lemma F_eb9f0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ik3!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpv0Kv$4@2$a@1$0#k0+urpv0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9f0 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!ik3@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9f4 : bv 32 := 0xab8ff0ef.
Lemma F_eb9f4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ikd!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpv4Kv$4@2$a@1$0#k0+urpv4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9f4 : ltac2:(zQ "e0!h9!hn1!hp8!hq1!l5!l9!le!nd!o4!hq8!od!ht5!il7!ikd@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+hvvir8Kv$4@2$6@1$0#h5+hvvir8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9f8 : bv 32 := 0x00050463.
Lemma F_eb9f8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ile!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpv8Kv$4@2$a@1$0#k0+urpv8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9f8 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!im8!in1!ile@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+8Kv$1@2$5@1$0#d+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eb9fc : bv 32 := 0x40950433.
Lemma F_eb9fc : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!inb!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urpvcKv$4@2$a@1$0#k0+urpvc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eb9fc : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!io5!ip0!inb@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+9Kv$1@2$5@1$0#5+9+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eba00 : bv 32 := 0x00040513.
Lemma F_eba00 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ip6!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urqg0Kv$4@2$a@1$0#k0+urqg0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eba00 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!ip6@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eba04 : bv 32 := 0x01813083.
Lemma F_eba04 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iq0!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urqg4Kv$4@2$a@1$0#k0+urqg4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eba04 : ltac2:(zQ "h00!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!iqa!od!ht5!ir1!ig1!iq0@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#c+h8Kv$1@2$5@1$0#c+h8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eba08 : bv 32 := 0x01013403.
Lemma F_eba08 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ire!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urqg8Kv$4@2$a@1$0#k0+urqg8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eba08 : ltac2:(zQ "h00!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!iqa!od!ht5!ir1!ig1!ire@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#c+h0Kv$1@2$5@1$0#c+h0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eba0c : bv 32 := 0x00813483.
Lemma F_eba0c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!is8!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urqgcKv$4@2$a@1$0#k0+urqgc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eba0c : ltac2:(zQ "h00!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!iqa!od!ht5!ir1!ig1!is8@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eba10 : bv 32 := 0x02010113.
Lemma F_eba10 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!it2!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urqh0Kv$4@2$a@1$0#k0+urqh0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eba10 : ltac2:(zQ "f1!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!it2&@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+i0Kv$1@2$5@1$0#c+i0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eba14 : bv 32 := 0x00008067.
Lemma F_eba14 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!itc!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+urqh4Kv$4@2$a@1$0#k0+urqh4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eba14 : ltac2:(zQ "e0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!iu6!itc@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.
