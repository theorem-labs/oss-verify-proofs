(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1Uh3Ub_code_726ec_72728~~~~~~t67W_726ec69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hi9floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn55instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChr0adecode_anyhn57ALU_ADDhn55OpImmt67W_726f0hn53SZ8hn55Storet67W_726f4t67W_726f8hn53Jalt67W_726fchn55Auipct67W_72700t67W_72704hn53SZ4t67W_72708t67W_7270ct67W_72710t67W_72714t67W_72718m54truehn5|41L1o1a1dt67W_7271ct67W_72720t67W_72724hn54Jalr" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_726ec : bv 32 := 0xff010113.
Lemma F_726ec : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hhf!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nimucKv$4@2$a@1$0#k0+nimuc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_726ec : ltac2:(zQ "f1!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!hhf&@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+vv0Kv$1@2$5@1$0#c+vv0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_726f0 : bv 32 := 0x00113423.
Lemma F_726f0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hv8!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nimv0Kv$4@2$a@1$0#k0+nimv0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_726f0 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig2!ig9!hv8@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_726f4 : bv 32 := 0x00813023.
Lemma F_726f4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih2!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nimv4Kv$4@2$a@1$0#k0+nimv4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_726f4 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig2!ig9!ih2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_726f8 : bv 32 := 0x6702d0ef.
Lemma F_726f8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ihc!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nimv8Kv$4@2$a@1$0#k0+nimv8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_726f8 : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!ii6!ihc@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+itmn0Kv$4@2$6@1$0#h5+itmn0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_726fc : bv 32 := 0x0009b597.
Lemma F_726fc : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iid!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nimvcKv$4@2$a@1$0#k0+nimvc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_726fc : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!ij7!iid@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+bKv$4@2$6@1$0#5+b@3$5@1$0#h4+pbKv$4@2$6@1$0#h4+pb+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72700 : bv 32 := 0xaa458413.
Lemma F_72700 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ik0!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ning0Kv$4@2$a@1$0#k0+ning0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_72700 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!ik0@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#c+qq4Kv$1@2$5@1$0#c+qq4+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72704 : bv 32 := 0x00a42023.
Lemma F_72704 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ika!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ning4Kv$4@2$a@1$0#k0+ning4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_72704 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!il4!ig9!ika@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72708 : bv 32 := 0x6602d0ef.
Lemma F_72708 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ilb!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ning8Kv$4@2$a@1$0#k0+ning8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_72708 : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!ii6!ilb@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+itmm0Kv$4@2$6@1$0#h5+itmm0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7270c : bv 32 := 0x00a42223.
Lemma F_7270c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!im5!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ningcKv$4@2$a@1$0#k0+ningc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_7270c : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!il4!ig9!im5@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#c+4Kv$1@2$5@1$0#c+4+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72710 : bv 32 := 0x6582d0ef.
Lemma F_72710 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!imf!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ninh0Kv$4@2$a@1$0#k0+ninh0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_72710 : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!ii6!imf@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+itml8Kv$4@2$6@1$0#h5+itml8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72714 : bv 32 := 0x00a42423.
Lemma F_72714 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!in9!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ninh4Kv$4@2$a@1$0#k0+ninh4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_72714 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!il4!ig9!in9@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72718 : bv 32 := 0x00813083.
Lemma F_72718 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!io3!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ninh8Kv$4@2$a@1$0#k0+ninh8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_72718 : ltac2:(zQ "h00!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!iod!od!ht6!ip4!ig2!io3@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7271c : bv 32 := 0x00013403.
Lemma F_7271c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iq1!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+ninhcKv$4@2$a@1$0#k0+ninhc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_7271c : ltac2:(zQ "h00!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!iod!od!ht6!ip4!ig2!iq1@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72720 : bv 32 := 0x01010113.
Lemma F_72720 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iqb!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nini0Kv$4@2$a@1$0#k0+nini0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_72720 : ltac2:(zQ "f1!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!iqb&@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+h0Kv$1@2$5@1$0#c+h0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72724 : bv 32 := 0x00008067.
Lemma F_72724 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ir5!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nini4Kv$4@2$a@1$0#k0+nini4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_72724 : ltac2:(zQ "e0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!irf!ir5@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.
