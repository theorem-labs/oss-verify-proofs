(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan BothImages BothPlanImages.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~07x_smear69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~k76BOTH_H37Corelib4Init5Logicod3and46Stdlib6ZArith6BinInt1Zq73addq72leq72ltq73pow37Corelib7Numbers7BinNumst54Npos35stdpp9bitvectorbdefinitionsv52bv37Corelib4Init9Datatypeshh74Somehh76optionod1Iod2eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshkaafetch_word69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~hof5ASEGSv52BVv54BvWfv57Z_to_bv" s.
Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma asan_smear_x : ltac2:(zQ "70!je!o4!q1!rf!s5!sa!sf@2$2@2$4Z@1$0$1@2$5@2$3@1$0$1+n0@2$6+2+k0").
Proof. cbn [x_smear ASAN_H]. lia. Qed.

Lemma asan_smear_fwa : ltac2:(zQ "f3!ue!hh2!hif!hj7!hk1!hk5!ho1!je!o4!ht0!ht9!hte!hu5!q1!rf&@3$a@1$0#i0+vlmlj3Kv$4@2$b@1$0#i0+vlmlj3&Kd~0@1$1@1$0#i0&@2$2@1$1@1$0#i0~1@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@1$7$8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+hlllp3Kv$4@2$b@1$0#i0+hlllp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+lllllmj7Kv$4@2$b@1$0#i0+lllllmj7@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+jjjjjmr7Kv$4@2$b@1$0#i0+jjjjjmr7@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+c@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vgvhnj7Kv$4@2$b@1$0#i0+vgvhnj7@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+h0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+hghgnr7Kv$4@2$b@1$0#i0+hghgnr7@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+h4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+rlmlj3Kv$4@2$b@1$0#i0+rlmlj3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+h8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+lllmglpbKv$4@2$b@1$0#i0+lllmglpb@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+hc@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+jjjmomhbKv$4@2$b@1$0#i0+jjjmomhb@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+i0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vgvngmpbKv$4@2$b@1$0#i0+vgvngmpb@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+i4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+hghnonhbKv$4@2$b@1$0#i0+hghnonhb@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+i8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+illnp3Kv$4@2$b@1$0#i0+illnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+ic~2@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+j0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+iglpnp3Kv$4@2$b@1$0#i0+iglpnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+j4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vlolr3Kv$4@2$b@1$0#i0+vlolr3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+j8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+igmhnp3Kv$4@2$b@1$0#i0+igmhnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+jc@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vmgmj3Kv$4@2$b@1$0#i0+vmgmj3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+k0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+igmpnp3Kv$4@2$b@1$0#i0+igmpnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+k4@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vmomr3Kv$4@2$b@1$0#i0+vmomr3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+k8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+ignhnp3Kv$4@2$b@1$0#i0+ignhnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+kc@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+vngnj3Kv$4@2$b@1$0#i0+vngnj3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+l0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+kllnp3Kv$4@2$b@1$0#i0+kllnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+l4~2@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+l8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+ollnp3Kv$4@2$b@1$0#i0+ollnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+lc~2@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+m0@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+hgllnp3Kv$4@2$b@1$0#i0+hgllnp3@1$1@1$0#i0@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+m4~2@2$d@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+m8@2$2@1$1@1$0#i0Kd@3$a@1$0#i0+igllnp3Kv$4@2$b@1$0#i0+igllnp3@1$1@1$0#i0@3$5@1$3@1$1@1$0#i0@2$6$9@2$c@1$0#k0@2$e@1$7$8+mc~2").
Proof. repeat split; vm_refl. Qed.
End FPX1.
