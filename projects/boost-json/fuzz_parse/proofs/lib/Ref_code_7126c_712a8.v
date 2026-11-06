(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libh4Ref_code_7126c_712a8~~~~~~t67W_7126c69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hi8floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn45instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChqfadecode_anyhn47ALU_ADDhn45OpImmt67W_71270hn43SZ8hn45Storet67W_71274t67W_71278hn43Jalt67W_7127chn45Auipct67W_71280t67W_71284hn43SZ4t67W_71288t67W_7128ct67W_71290t67W_71294t67W_71298m54truehn4|41L1o1a1dt67W_7129ct67W_712a0t67W_712a4hn44Jalr" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7126c : bv 32 := 0xff010113.
Lemma F_7126c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hhe!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhimcKv$4@2$a@1$0#k0+nhimc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_7126c : ltac2:(zQ "f1!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!hhe&@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+vv0Kv$1@2$5@1$0#c+vv0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71270 : bv 32 := 0x00113423.
Lemma F_71270 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hv7!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhin0Kv$4@2$a@1$0#k0+nhin0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71270 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!ig1!ig8!hv7@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71274 : bv 32 := 0x00813023.
Lemma F_71274 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih1!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhin4Kv$4@2$a@1$0#k0+nhin4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71274 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!ig1!ig8!ih1@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71278 : bv 32 := 0x6482b0ef.
Lemma F_71278 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ihb!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhin8Kv$4@2$a@1$0#k0+nhin8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71278 : ltac2:(zQ "e0!h9!hn1!hp8!hq1!l5!l9!le!nd!o4!hq8!od!ht5!ii5!ihb@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+irmk8Kv$4@2$6@1$0#h5+irmk8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7127c : bv 32 := 0x00099597.
Lemma F_7127c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iic!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhincKv$4@2$a@1$0#k0+nhinc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_7127c : ltac2:(zQ "e0!h9!hn1!hp8!hq1!l5!l9!le!nd!o4!hq8!od!ht5!ij6!iic@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+bKv$4@2$6@1$0#5+b@3$5@1$0#h4+p9Kv$4@2$6@1$0#h4+p9+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71280 : bv 32 := 0x9e458413.
Lemma F_71280 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ijf!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhio0Kv$4@2$a@1$0#k0+nhio0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71280 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!ijf@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#c+pu4Kv$1@2$5@1$0#c+pu4+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71284 : bv 32 := 0x00a42023.
Lemma F_71284 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ik9!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhio4Kv$4@2$a@1$0#k0+nhio4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71284 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!il3!ig8!ik9@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71288 : bv 32 := 0x6382b0ef.
Lemma F_71288 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ila!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhio8Kv$4@2$a@1$0#k0+nhio8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71288 : ltac2:(zQ "e0!h9!hn1!hp8!hq1!l5!l9!le!nd!o4!hq8!od!ht5!ii5!ila@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+irmj8Kv$4@2$6@1$0#h5+irmj8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7128c : bv 32 := 0x00a42223.
Lemma F_7128c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!im4!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhiocKv$4@2$a@1$0#k0+nhioc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_7128c : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!il3!ig8!im4@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#c+4Kv$1@2$5@1$0#c+4+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71290 : bv 32 := 0x6302b0ef.
Lemma F_71290 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ime!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhip0Kv$4@2$a@1$0#k0+nhip0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71290 : ltac2:(zQ "e0!h9!hn1!hp8!hq1!l5!l9!le!nd!o4!hq8!od!ht5!ii5!ime@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+irmj0Kv$4@2$6@1$0#h5+irmj0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71294 : bv 32 := 0x00a42423.
Lemma F_71294 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!in8!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhip4Kv$4@2$a@1$0#k0+nhip4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71294 : ltac2:(zQ "f0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!il3!ig8!in8@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71298 : bv 32 := 0x00813083.
Lemma F_71298 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!io2!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhip8Kv$4@2$a@1$0#k0+nhip8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_71298 : ltac2:(zQ "h00!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!ioc!od!ht5!ip3!ig1!io2@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7129c : bv 32 := 0x00013403.
Lemma F_7129c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iq0!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhipcKv$4@2$a@1$0#k0+nhipc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_7129c : ltac2:(zQ "h00!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!ioc!od!ht5!ip3!ig1!iq0@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_712a0 : bv 32 := 0x01010113.
Lemma F_712a0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iqa!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhiq0Kv$4@2$a@1$0#k0+nhiq0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_712a0 : ltac2:(zQ "f1!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!hu3!hue!iqa&@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+h0Kv$1@2$5@1$0#c+h0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_712a4 : bv 32 := 0x00008067.
Lemma F_712a4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ir4!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nhiq4Kv$4@2$a@1$0#k0+nhiq4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_712a4 : ltac2:(zQ "e0!h9!l5!hn1!hp8!l9!le!hq1!nd!o4!hq8!od!ht5!ire!ir4@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.
