(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsImages AsPlanImages.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~06ASAN_H79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~k37x_smear37Corelib4Init5Logicob3and46Stdlib6ZArith6BinInt1Zq53addq52leq52ltq53pow37Corelib7Numbers7BinNumst34Npos35stdpp9bitvectorbdefinitionsv32bv37Corelib4Init9Datatypeshh54Somehh56optionob1Iob2eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshk8afetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~hod5ASEGSv32BVv34BvWfv37Z_to_bv" s.
Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma asan_smear_x : ltac2:(zQ "70!jb!o1!pf!rd!s3!s8!sd@2$2@2$4Z@1$1$0@2$5@2$3@1$1$0+n0@2$6+2+k0").
Proof. cbn [x_smear ASAN_H]. lia. Qed.

Lemma asan_smear_fwa : ltac2:(zQ "f3!uc!hh0!hid!hj5!hjf!hk3!hnf!jb!hsc!o1!ht5!hta!hu1!pf!rd&@3$a@1$0#i0+vlmlj3Kv$4@2$b@1$0#i0+vlmlj3&Kd~0@1$1@1$0#i0&@2$2@1$1@1$0#i0~1@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@1$9$7@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+hlllp3Kv$4@2$b@1$0#i0+hlllp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+lllllmj7Kv$4@2$b@1$0#i0+lllllmj7@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+jjjjjmr7Kv$4@2$b@1$0#i0+jjjjjmr7@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+c@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vgvhnj7Kv$4@2$b@1$0#i0+vgvhnj7@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+h0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+hghgnr7Kv$4@2$b@1$0#i0+hghgnr7@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+h4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+rlmlj3Kv$4@2$b@1$0#i0+rlmlj3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+h8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+lllmglpbKv$4@2$b@1$0#i0+lllmglpb@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+hc@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+jjjmomhbKv$4@2$b@1$0#i0+jjjmomhb@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+i0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vgvngmpbKv$4@2$b@1$0#i0+vgvngmpb@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+i4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+hghnonhbKv$4@2$b@1$0#i0+hghnonhb@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+i8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+illnp3Kv$4@2$b@1$0#i0+illnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+ic~2@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+j0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+iglpnp3Kv$4@2$b@1$0#i0+iglpnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+j4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vlolr3Kv$4@2$b@1$0#i0+vlolr3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+j8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+igmhnp3Kv$4@2$b@1$0#i0+igmhnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+jc@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vmgmj3Kv$4@2$b@1$0#i0+vmgmj3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+k0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+igmpnp3Kv$4@2$b@1$0#i0+igmpnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+k4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vmomr3Kv$4@2$b@1$0#i0+vmomr3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+k8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+ignhnp3Kv$4@2$b@1$0#i0+ignhnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+kc@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vngnj3Kv$4@2$b@1$0#i0+vngnj3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+l0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+kllnp3Kv$4@2$b@1$0#i0+kllnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+l4~2@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+l8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+ollnp3Kv$4@2$b@1$0#i0+ollnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+lc~2@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+m0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+hgllnp3Kv$4@2$b@1$0#i0+hgllnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+m4~2@2$d@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+m8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+igllnp3Kv$4@2$b@1$0#i0+igllnp3@1$1@1$0#i0@3$5@1$3@1$1@1$0#i0@2$6$8@2$c@1$0#k0@2$e@1$9$7+mc~2").
Proof. repeat split; vm_refl. Qed.
End FPX1.
