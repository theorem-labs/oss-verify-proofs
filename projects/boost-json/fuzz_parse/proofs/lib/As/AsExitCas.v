(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibAtomic.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import RefExitBase As_code_19416c_19488c.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsExitCas4FPX1~~~~~~t67W_77b9469OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~hi4floaded_segmentst67W_77b98t67W_77b9ct67W_77f04t67W_77f08t67W_77f0c01Z3h5LinuxProcessSemantics5Riscv5Instrhq15instrm54prodm54truem54pair3h5LinuxProcessSemantics5Riscv7DecodeChu3adecode_anyhq12ADhq12Lrhq15BC_NEhq16Branchhf7Z_to_bvm55falsehq12Sc69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ike4getrm54listp2h0word_to_le_bytesike4mkstike6regupd3h5LinuxProcessSemantics5Riscv7Preludeire5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~iud6wbytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~jj16mstepsike3rdn" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition W_77b94 : bv 32 := 0x160c36af.  Definition W_77b98 : bv 32 := 0x00c69663.  Definition W_77b9c : bv 32 := 0x1aec37af.
Definition W_77f04 : bv 32 := 0x160c332f.  Definition W_77f08 : bv 32 := 0x00a31663.  Definition W_77f0c : bv 32 := 0x1a5c33af.
Lemma F_77b94 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hha!hl9!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnrp4Kv$4@2$a@1$0#k0+nnrp4@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77b98 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hmc!hl9!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnrp8Kv$4@2$a@1$0#k0+nnrp8@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77b9c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hn6!hl9!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnrpcKv$4@2$a@1$0#k0+nnrpc@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77f04 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ho0!hl9!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnvg4Kv$4@2$a@1$0#k0+nnvg4@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77f08 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hoa!hl9!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnvg8Kv$4@2$a@1$0#k0+nnvg8@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77f0c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hp4!hl9!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnvgcKv$4@2$a@1$0#k0+nnvgc@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma D_77b94 : ltac2:(zQ "h00!h9!hpe!hs5!hse!ht5!l5!l9!le!nd!o4!htc!od!ig9!ih7!ihd!hha@3$b@1$9@2$3$2$1@1$c$f@2$8@2$3$2$1@4$a$2$1@5$e$d$4$4@3$6@1$0#5+dKv$5@2$7@1$0#5+d@3$6@1$0#5+h8Kv$5@2$7@1$0#5+h8+4"). Proof. vm_refl. Qed.
Lemma D_77b98 : ltac2:(zQ "h00!h9!hpe!hs5!hse!l5!l9!le!nd!o4!htc!od!ig9!ii3!iic!hmc!ij6@3$a@1$8@2$3$2$1@1$b$e@2$7@2$3$2$1@4$9$2$1@4$d$c@3$5@1$0#5+dKv$4@2$6@1$0#5+d@3$5@1$0#5+cKv$4@2$6@1$0#5+c@2$f@1$0#d+c+4"). Proof. vm_refl. Qed.
Lemma D_77b9c : ltac2:(zQ "h10!h9!l5!hpe!hs5!l9!le!hse!nd!ik0!o4!htc!ht5!od!ig9!ih7!ik8!hn6@3$c@1$9@2$6$3$2@1$d$h0@2$7@2$6$3$2@4$a$3$2@6$f$e$8$b@3$4@1$0#5+fKv$1@2$5@1$0#5+f@3$4@1$0#5+h8Kv$1@2$5@1$0#5+h8@3$4@1$0#5+eKv$1@2$5@1$0#5+e+4"). Proof. vm_refl. Qed.
Lemma D_77f04 : ltac2:(zQ "h00!h9!hpe!hs5!hse!ht5!l5!l9!le!nd!o4!htc!od!ig9!ih7!ihd!ho0@3$b@1$9@2$3$2$1@1$c$f@2$8@2$3$2$1@4$a$2$1@5$e$d$4$4@3$6@1$0#5+6Kv$5@2$7@1$0#5+6@3$6@1$0#5+h8Kv$5@2$7@1$0#5+h8+4"). Proof. vm_refl. Qed.
Lemma D_77f08 : ltac2:(zQ "h00!h9!hpe!hs5!hse!l5!l9!le!nd!o4!htc!od!ig9!ii3!iic!hoa!ij6@3$a@1$8@2$3$2$1@1$b$e@2$7@2$3$2$1@4$9$2$1@4$d$c@3$5@1$0#5+6Kv$4@2$6@1$0#5+6@3$5@1$0#5+aKv$4@2$6@1$0#5+a@2$f@1$0#d+c+4"). Proof. vm_refl. Qed.
Lemma D_77f0c : ltac2:(zQ "h10!h9!l5!hpe!hs5!l9!le!hse!nd!ik0!o4!htc!ht5!od!ig9!ih7!ik8!hp4@3$c@1$9@2$6$3$2@1$d$h0@2$7@2$6$3$2@4$a$3$2@6$f$e$8$b@3$4@1$0#5+7Kv$1@2$5@1$0#5+7@3$4@1$0#5+h8Kv$1@2$5@1$0#5+h8@3$4@1$0#5+5Kv$1@2$5@1$0#5+5+4"). Proof. vm_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cas_exit_lock : ltac2:(zQ "h31!h9!jc!l5!l9!le!ij6!od!o4!io9!ip1!ip8!iqc!ir4!hl9!nd!iu4!ji7!jma!jn4&>0@1$1@1$0#k0@1$7@1$1@1$0#8>4regs@2$f@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>1v@1$1@1$0#k0>0@3$6@1$1@1$0#k0@2$8^4@3$3@1$0#5+dKv$2@2$4@1$0#5+d@2$5@1$0#k0+nhkmk8>0@3$6@1$1@1$0#k0@2$8^5@3$3@1$0#5+bKv$2@2$4@1$0#5+b@2$5@1$0#k0Z>0@3$6@1$1@1$0#k0@2$8^6@3$3@1$0#5+cKv$2@2$4@1$0#5+c^3>0@3$6@1$7@1$9@1$1@1$0#8@4$h2$d^6@2$5@1$0#k0+nhkmk8N4@2$e@1$9@1$1@1$0#8@2$aN4@2$5@1$0#k0Z@3$h1$d@5$b?2fx^8Kd@3$3@1$0#k0+hpklhcKv$2@2$4@1$0#k0+hpklhc@1$1@1$0#k0^7^6@5$b?2fx@3$c@3$c^8@3$3@1$0#5+eKv$2@2$4@1$0#5+e@2$5@1$0#k0Z@3$3@1$0#5+fKv$2@2$4@1$0#5+f@2$5@1$0#k0ZKd@3$3@1$0#k0+hpkli8Kv$2@2$4@1$0#k0+hpkli8@1$1@1$0#k0@3$h0^7@2$5@1$0#k0+nhkmk8@2$aN4^5^6").
Proof.
  intros regs mem rom v R13 R11 R12 Mlock.
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
      [ exact F_19451c | reflexivity | exact D_19451c
      | rewrite R13; u_norm; reflexivity
      | rewrite R13; exact Mlock
      | apply bytes_le_to_Z_4; u_norm; lia ]
    | ].
  reduce_bv_eqb_ifs.
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [exact F_194520 | reflexivity | exact D_194520 | gres; rewrite R11; cond_compute ] | ].
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_sc_w_ok; [exact F_194524 | reflexivity | exact D_194524
      | gres; rewrite R13; u_norm; reflexivity | gres; reflexivity | gres; rewrite R13; sok_data ] | ].
  reduce_bv_eqb_ifs. gres. rewrite R13, R12.
  match goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
  f_equal; try reflexivity. all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cas_mu_lock : ltac2:(zQ "h31!h9!jc!l5!l9!le!ij6!o4!od!io9!ip1!ip8!iqc!ir4!hl9!nd!iu4!ji7!jma!jn4&>0@1$1@1$0#k0@1$6@1$1@1$0#8>4regs@2$f@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>1v@1$1@1$0#k0>0@3$7@1$1@1$0#k0@2$8^4@3$3@1$0#5+h8Kv$2@2$4@1$0#5+h8@2$5@1$0#k0+hrtqv0>0@3$7@1$1@1$0#k0@2$8^5@3$3@1$0#5+cKv$2@2$4@1$0#5+c^2>0@3$7@1$6@1$9@1$1@1$0#8@4$h2$d^5@2$5@1$0#k0+hrtqv0N8@2$e@1$9@1$1@1$0#8@2$aN8^3@3$h1$d@5$b?2fx^7Kd@3$3@1$0#k0+nnrp4Kv$2@2$4@1$0#k0+nnrp4@1$1@1$0#k0^6^5@5$b?2fx@3$c@3$c^7@3$3@1$0#5+dKv$2@2$4@1$0#5+d^4@3$3@1$0#5+fKv$2@2$4@1$0#5+f@2$5@1$0#k0ZKd@3$3@1$0#k0+nnrq0Kv$2@2$4@1$0#k0+nnrq0@1$1@1$0#k0@3$h0^6@2$5@1$0#k0+hrtqv0@2$aN8@2$8^7@3$3@1$0#5+eKv$2@2$4@1$0#5+e^5").
Proof.
  intros regs mem rom v R24 R12 Mmu.
  eapply mst_step; [reflexivity
    | eapply step_lr_d with (bs := word_to_le_bytes 8 v) (v := v);
      [ exact F_77b94 | reflexivity | exact D_77b94
      | rewrite R24; u_norm; reflexivity
      | rewrite R24; exact Mmu
      | apply bytes_le_to_Z_8 ]
    | ].
  reduce_bv_eqb_ifs.
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [exact F_77b98 | reflexivity | exact D_77b98 | gres; rewrite R12; apply c_eq_refl ] | ].
  eapply mst_step; [reflexivity
    | eapply step_sc_d_ok; [exact F_77b9c | reflexivity | exact D_77b9c
      | gres; rewrite R24; u_norm; reflexivity | gres; reflexivity | gres; rewrite R24; sok_data ] | ].
  reduce_bv_eqb_ifs. gres. rewrite R24.
  match goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
  f_equal; try reflexivity. all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cas_mu_unlock : ltac2:(zQ "h31!h9!jc!l5!l9!le!ij6!o4!od!io9!ip1!ip8!iqc!ir4!hl9!nd!iu4!ji7!jma!jn4&>0@1$1@1$0#k0@1$6@1$1@1$0#8>4regs@2$f@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>1v@1$1@1$0#k0>0@3$7@1$1@1$0#k0@2$8^4@3$3@1$0#5+h8Kv$2@2$4@1$0#5+h8@2$5@1$0#k0+hrtqv0>0@3$7@1$1@1$0#k0@2$8^5@3$3@1$0#5+aKv$2@2$4@1$0#5+a^2>0@3$7@1$6@1$9@1$1@1$0#8@4$h2$d^5@2$5@1$0#k0+hrtqv0N8@2$e@1$9@1$1@1$0#8@2$aN8^3@3$h1$d@5$b?2fx^7Kd@3$3@1$0#k0+nnvg4Kv$2@2$4@1$0#k0+nnvg4@1$1@1$0#k0^6^5@5$b?2fx@3$c@3$c^7@3$3@1$0#5+6Kv$2@2$4@1$0#5+6^4@3$3@1$0#5+7Kv$2@2$4@1$0#5+7@2$5@1$0#k0ZKd@3$3@1$0#k0+nnvh0Kv$2@2$4@1$0#k0+nnvh0@1$1@1$0#k0@3$h0^6@2$5@1$0#k0+hrtqv0@2$aN8@2$8^7@3$3@1$0#5+5Kv$2@2$4@1$0#5+5^5").
Proof.
  intros regs mem rom v R24 R10 Mmu.
  eapply mst_step; [reflexivity
    | eapply step_lr_d with (bs := word_to_le_bytes 8 v) (v := v);
      [ exact F_77f04 | reflexivity | exact D_77f04
      | rewrite R24; u_norm; reflexivity
      | rewrite R24; exact Mmu
      | apply bytes_le_to_Z_8 ]
    | ].
  reduce_bv_eqb_ifs.
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [exact F_77f08 | reflexivity | exact D_77f08 | gres; rewrite R10; apply c_eq_refl ] | ].
  eapply mst_step; [reflexivity
    | eapply step_sc_d_ok; [exact F_77f0c | reflexivity | exact D_77f0c
      | gres; rewrite R24; u_norm; reflexivity | gres; reflexivity | gres; rewrite R24; sok_data ] | ].
  reduce_bv_eqb_ifs. gres. rewrite R24.
  match goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
  f_equal; try reflexivity. all: try (apply bv_eq; vm_compute; reflexivity).
Qed.
End FPX1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
