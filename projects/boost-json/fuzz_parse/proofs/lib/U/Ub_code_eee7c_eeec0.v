(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1Uh3Ub_code_eee7c_eeec0~~~~~~t67W_eee7c69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hi9floaded_segments01Z3h5LinuxProcessSemantics5Riscv5Instrhn55instrm54prodm54pair3h5LinuxProcessSemantics5Riscv7DecodeChr0adecode_anyhn57ALU_ADDhn55OpImmt67W_eee80hn53SZ8hn55Storet67W_eee84t67W_eee88t67W_eee8ct67W_eee90t67W_eee94t67W_eee98t67W_eee9chn53Jalt67W_eeea0hn55BC_EQhn56Brancht67W_eeea4hn57ALU_SUBhn52Opt67W_eeea8t67W_eeeacm54truehn5|41L1o1a1dt67W_eeeb0t67W_eeeb4t67W_eeeb8t67W_eeebchn54Jalr" s.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_eee7c : bv 32 := 0xfe010113.
Lemma F_eee7c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hhf!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuncKv$4@2$a@1$0#k0+uuunc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee7c : ltac2:(zQ "f1!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!hhf&@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+vu0Kv$1@2$5@1$0#c+vu0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eee80 : bv 32 := 0x00113c23.
Lemma F_eee80 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hv8!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuo0Kv$4@2$a@1$0#k0+uuuo0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee80 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig2!ig9!hv8@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#c+h8Kv$1@2$5@1$0#c+h8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eee84 : bv 32 := 0x00813823.
Lemma F_eee84 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ih2!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuo4Kv$4@2$a@1$0#k0+uuuo4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee84 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig2!ig9!ih2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#c+h0Kv$1@2$5@1$0#c+h0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eee88 : bv 32 := 0x00913423.
Lemma F_eee88 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ihc!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuo8Kv$4@2$a@1$0#k0+uuuo8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee88 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!ig2!ig9!ihc@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eee8c : bv 32 := 0x00058413.
Lemma F_eee8c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ii6!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuocKv$4@2$a@1$0#k0+uuuoc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee8c : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!ii6@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eee90 : bv 32 := 0x00050493.
Lemma F_eee90 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ij0!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuup0Kv$4@2$a@1$0#k0+uuup0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee90 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!ij0@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eee94 : bv 32 := 0x00000593.
Lemma F_eee94 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ija!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuup4Kv$4@2$a@1$0#k0+uuup4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee94 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!ija@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eee98 : bv 32 := 0x00040613.
Lemma F_eee98 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ik4!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuup8Kv$4@2$a@1$0#k0+uuup8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee98 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!ik4@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eee9c : bv 32 := 0xab8ff0ef.
Lemma F_eee9c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ike!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuupcKv$4@2$a@1$0#k0+uuupc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eee9c : ltac2:(zQ "e0!h9!hn2!hp9!hq2!l5!l9!le!nd!o4!hq9!od!ht6!il8!ike@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@3$5@1$0#h5+hvvir8Kv$4@2$6@1$0#h5+hvvir8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eeea0 : bv 32 := 0x00050463.
Lemma F_eeea0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ilf!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuq0Kv$4@2$a@1$0#k0+uuuq0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eeea0 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!im9!in2!ilf@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+8Kv$1@2$5@1$0#d+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eeea4 : bv 32 := 0x40950433.
Lemma F_eeea4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!inc!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuq4Kv$4@2$a@1$0#k0+uuuq4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eeea4 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!io6!ip1!inc@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+9Kv$1@2$5@1$0#5+9+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eeea8 : bv 32 := 0x00040513.
Lemma F_eeea8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ip7!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuq8Kv$4@2$a@1$0#k0+uuuq8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eeea8 : ltac2:(zQ "f0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!ip7@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eeeac : bv 32 := 0x01813083.
Lemma F_eeeac : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!iq1!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuuqcKv$4@2$a@1$0#k0+uuuqc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eeeac : ltac2:(zQ "h00!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!iqb!od!ht6!ir2!ig2!iq1@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#c+h8Kv$1@2$5@1$0#c+h8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eeeb0 : bv 32 := 0x01013403.
Lemma F_eeeb0 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!irf!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuur0Kv$4@2$a@1$0#k0+uuur0@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eeeb0 : ltac2:(zQ "h00!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!iqb!od!ht6!ir2!ig2!irf@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#c+h0Kv$1@2$5@1$0#c+h0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eeeb4 : bv 32 := 0x00813483.
Lemma F_eeeb4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!is9!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuur4Kv$4@2$a@1$0#k0+uuur4@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eeeb4 : ltac2:(zQ "h00!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!iqb!od!ht6!ir2!ig2!is9@3$b@1$8@2$6$3$2@1$c$f@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eeeb8 : bv 32 := 0x02010113.
Lemma F_eeeb8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!it3!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuur8Kv$4@2$a@1$0#k0+uuur8@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eeeb8 : ltac2:(zQ "f1!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!hu4!huf!it3&@3$4@1$0#5+2Kv$1@2$5@1$0#5+2@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+i0Kv$1@2$5@1$0#c+i0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_eeebc : bv 32 := 0x00008067.
Lemma F_eeebc : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!itd!hlf!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+uuurcKv$4@2$a@1$0#k0+uuurc@1$1@1$0#k0@2$2@1$1@1$0#i0$7").
Proof. vm_refl. Qed.
Lemma D_eeebc : ltac2:(zQ "e0!h9!l5!hn2!hp9!l9!le!hq2!nd!o4!hq9!od!ht6!iu7!itd@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.
