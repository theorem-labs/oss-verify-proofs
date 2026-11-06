(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf01Z3h5LinuxProcessSemantics5Riscv5Instrm85instr37Corelib4Init9Datatypesp44prodp44Somep46optionp44pairk12eq3h5LinuxProcessSemantics5Riscv7DecodeCsfadecode_anym85BC_EQm86Branch69OSSVerify6Proofsaboost_jsonafuzz_parse3libaSums2_code~~~~~~hh37W_a26a4m87ALU_ADDm85OpImmhh37W_a26a8m82Ophh37W_a26acp45falsem8|41L1o1a1dm83SZ1hh37W_a26b0hh37W_a26b4hh37W_a26b8hh37W_a26bcm85Storehh37W_a26c0m85BC_NEhh37W_a26c4hh37W_a26ccm87ALU_SUBm84Op32hh37W_a26d0m86ALU_ORhh37W_a26d4m87ALU_ANDhh37W_a26d8hh37W_a26dchh37W_a26e0hh37W_a26e4hh37W_a26e8hh37W_a26echh37W_a26f0m83Jalhh37W_a26f4m84Jalrhh37W_a2710" s.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a26a4 : bv 32 := 0x06060663.
Lemma D_a26a4 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hg2!hga!hl0@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+mcKv$1@2$5@1$0#d+mc+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26a8 : bv 32 := 0x00000693.
Lemma D_a26a8 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hlb!hm5!hmd@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26ac : bv 32 := 0x00d58733.
Lemma D_a26ac : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hlb!hn8!hnd@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+eKv$1@2$5@1$0#5+e@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5+dKv$1@2$5@1$0#5+d+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26b0 : bv 32 := 0x00074703.
Lemma D_a26b0 : ltac2:(zQ "h01!h9!l5!m5!oc!l9!le!qc!r3!ho8!ra!s3!sa!v5!hp0!hpc!hq2&@3$4@1$0#5+eKv$1@2$5@1$0#5+e@3$b@1$9@2$6$3$2@1$c$f@2$7@2$6$3$2@4$a$3$2@5$d$e$8~0~0@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26b4 : bv 32 := 0x00070c63.
Lemma D_a26b4 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hg2!hga!hqd@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+eKv$1@2$5@1$0#5+e@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+h8Kv$1@2$5@1$0#d+h8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26b8 : bv 32 := 0x00d507b3.
Lemma D_a26b8 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hlb!hn8!hr8@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+fKv$1@2$5@1$0#5+f@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+dKv$1@2$5@1$0#5+d+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26bc : bv 32 := 0x00168693.
Lemma D_a26bc : ltac2:(zQ "f1!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hlb!hm5!hs3&@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+1Kv$1@2$5@1$0#c+1+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26c0 : bv 32 := 0x00e78023.
Lemma D_a26c0 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hpc!hse!ht6@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+fKv$1@2$5@1$0#5+f@3$4@1$0#5+eKv$1@2$5@1$0#5+e@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26c4 : bv 32 := 0xfed614e3.
Lemma D_a26c4 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hu1!hga!hu9@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#d+hvu8Kv$1@2$5@1$0#d+hvu8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26c8 : bv 32 := 0x00060693.

(* [comment removed for export] *)
Definition W_a26cc : bv 32 := 0x00d505b3.
Lemma D_a26cc : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hlb!hn8!hv4@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+dKv$1@2$5@1$0#5+d+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26d0 : bv 32 := 0x40d6073b.
Lemma D_a26d0 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hvf!ig9!ih0@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+eKv$1@2$5@1$0#5+e@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#5+dKv$1@2$5@1$0#5+d+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26d4 : bv 32 := 0x00b76733.
Lemma D_a26d4 : ltac2:(zQ "f1!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!ihb!hn8!ii4&@3$4@1$0#5+eKv$1@2$5@1$0#5+e@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#5+bKv$1@2$5@1$0#5+b+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26d8 : bv 32 := 0x00f77713.
Lemma D_a26d8 : ltac2:(zQ "f1!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!iif!hm5!ij9&@3$4@1$0#5+eKv$1@2$5@1$0#5+e@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+fKv$1@2$5@1$0#c+f+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26dc : bv 32 := 0x00070e63.
Lemma D_a26dc : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hg2!hga!ik4@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+eKv$1@2$5@1$0#5+e@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hcKv$1@2$5@1$0#d+hc+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26e0 : bv 32 := 0x02d60863.
Lemma D_a26e0 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hg2!hga!ikf@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#d+j0Kv$1@2$5@1$0#d+j0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26e4 : bv 32 := 0x00c50633.
Lemma D_a26e4 : ltac2:(zQ "f1!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hlb!hn8!ila&@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0@3$4@1$0#5+aKv$1@2$5@1$0#5+a~0+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26e8 : bv 32 := 0x00058023.
Lemma D_a26e8 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hpc!hse!im5@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26ec : bv 32 := 0x00158593.
Lemma D_a26ec : ltac2:(zQ "f1!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hlb!hm5!in0&@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+1Kv$1@2$5@1$0#c+1+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f0 : bv 32 := 0xfec59ce3.
Lemma D_a26f0 : ltac2:(zQ "f0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!hu1!hga!inb@3$a@1$8@2$6$3$2@1$b$e@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#d+hvv8Kv$1@2$5@1$0#d+hvv8+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f4 : bv 32 := 0x01c0006f.
Lemma D_a26f4 : ltac2:(zQ "e0!h9!m5!oc!qc!l5!l9!le!r3!ra!s3!sa!v5!io6!ioc@3$a@1$8@2$3$2$1@1$b$d@2$7@2$3$2$1@4$9$2$1@2$c@3$5@1$0#5ZKv$4@2$6@1$0#5Z@3$5@1$0#h5+hcKv$4@2$6@1$0#h5+hc+4").
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f8 : bv 32 := 0x00d60c63.

(* [comment removed for export] *)
Definition W_a26fc : bv 32 := 0x00c50633.

(* [comment removed for export] *)
Definition W_a2700 : bv 32 := 0x0005b023.

(* [comment removed for export] *)
Definition W_a2704 : bv 32 := 0x0005b423.

(* [comment removed for export] *)
Definition W_a2708 : bv 32 := 0x01058593.

(* [comment removed for export] *)
Definition W_a270c : bv 32 := 0xfec5eae3.

(* [comment removed for export] *)
Definition W_a2710 : bv 32 := 0x00008067.
Lemma D_a2710 : ltac2:(zQ "e0!h9!l5!m5!oc!l9!le!qc!r3!ra!s3!sa!v5!ip7!ipe@3$a@1$8@2$6$3$2@1$b$d@2$7@2$6$3$2@4$9$3$2@3$c@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#5+1Kv$1@2$5@1$0#5+1@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
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
