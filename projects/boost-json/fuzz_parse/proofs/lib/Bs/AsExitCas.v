(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibAtomic.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import RefExitBase Bs_code_190ee4_191604.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ihf2BVhf4BvWf37Corelib4Init9Datatypesm54Somem56optionk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp2afetch_word89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsExitCas4FPX1~~~~~~t67W_77b3469OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~hi4floaded_segmentst67W_77b38t67W_77b3ct67W_77ea4t67W_77ea8t67W_77eac01Z3h5LinuxProcessSemantics5Riscv5Instrhq65instrm54prodm54truem54pair3h5LinuxProcessSemantics5Riscv7DecodeChu8adecode_anyhq62ADhq62Lrhq65BC_NEhq66Branchhf7Z_to_bvm55falsehq62Sc69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~il34getrm54listp2h0word_to_le_bytesil34mkstil36regupd3h5LinuxProcessSemantics5Riscv7Preludeis35bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~iv26wbytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~jj66mstepsil33rdn" s.
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
Definition W_77b34 : bv 32 := 0x160c36af.  Definition W_77b38 : bv 32 := 0x00c69663.  Definition W_77b3c : bv 32 := 0x1aec37af.
Definition W_77ea4 : bv 32 := 0x160c332f.  Definition W_77ea8 : bv 32 := 0x00a31663.  Definition W_77eac : bv 32 := 0x1a5c33af.
Lemma F_77b34 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hha!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnrj4Kv$4@2$a@1$0#k0+nnrj4@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77b38 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hn1!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnrj8Kv$4@2$a@1$0#k0+nnrj8@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77b3c : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hnb!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnrjcKv$4@2$a@1$0#k0+nnrjc@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77ea4 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!ho5!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnuq4Kv$4@2$a@1$0#k0+nnuq4@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77ea8 : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hof!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnuq8Kv$4@2$a@1$0#k0+nnuq8@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma F_77eac : ltac2:(zQ "b0!h9!jc!nd!o4!l5!od!s9!hp9!hle!l9!le@3$5@1$3@1$1@1$0#i0@2$6$8Kd@3$9@1$0#k0+nnuqcKv$4@2$a@1$0#k0+nnuqc@1$1@1$0#k0@2$2@1$1@1$0#i0$7"). Proof. vm_refl. Qed.
Lemma D_77b34 : ltac2:(zQ "h00!h9!hq3!hsa!ht3!hta!l5!l9!le!nd!o4!hu1!od!ige!ihc!ii2!hha@3$b@1$9@2$3$2$1@1$c$f@2$8@2$3$2$1@4$a$2$1@5$e$d$4$4@3$6@1$0#5+dKv$5@2$7@1$0#5+d@3$6@1$0#5+h8Kv$5@2$7@1$0#5+h8+4"). Proof. vm_refl. Qed.
Lemma D_77b38 : ltac2:(zQ "h00!h9!hq3!hsa!ht3!l5!l9!le!nd!o4!hu1!od!ige!ii8!ij1!hn1!ijb@3$a@1$8@2$3$2$1@1$b$e@2$7@2$3$2$1@4$9$2$1@4$d$c@3$5@1$0#5+dKv$4@2$6@1$0#5+d@3$5@1$0#5+cKv$4@2$6@1$0#5+c@2$f@1$0#d+c+4"). Proof. vm_refl. Qed.
Lemma D_77b3c : ltac2:(zQ "h10!h9!l5!hq3!hsa!l9!le!ht3!nd!ik5!o4!hu1!hta!od!ige!ihc!ikd!hnb@3$c@1$9@2$6$3$2@1$d$h0@2$7@2$6$3$2@4$a$3$2@6$f$e$8$b@3$4@1$0#5+fKv$1@2$5@1$0#5+f@3$4@1$0#5+h8Kv$1@2$5@1$0#5+h8@3$4@1$0#5+eKv$1@2$5@1$0#5+e+4"). Proof. vm_refl. Qed.
Lemma D_77ea4 : ltac2:(zQ "h00!h9!hq3!hsa!ht3!hta!l5!l9!le!nd!o4!hu1!od!ige!ihc!ii2!ho5@3$b@1$9@2$3$2$1@1$c$f@2$8@2$3$2$1@4$a$2$1@5$e$d$4$4@3$6@1$0#5+6Kv$5@2$7@1$0#5+6@3$6@1$0#5+h8Kv$5@2$7@1$0#5+h8+4"). Proof. vm_refl. Qed.
Lemma D_77ea8 : ltac2:(zQ "h00!h9!hq3!hsa!ht3!l5!l9!le!nd!o4!hu1!od!ige!ii8!ij1!hof!ijb@3$a@1$8@2$3$2$1@1$b$e@2$7@2$3$2$1@4$9$2$1@4$d$c@3$5@1$0#5+6Kv$4@2$6@1$0#5+6@3$5@1$0#5+aKv$4@2$6@1$0#5+a@2$f@1$0#d+c+4"). Proof. vm_refl. Qed.
Lemma D_77eac : ltac2:(zQ "h10!h9!l5!hq3!hsa!l9!le!ht3!nd!ik5!o4!hu1!hta!od!ige!ihc!ikd!hp9@3$c@1$9@2$6$3$2@1$d$h0@2$7@2$6$3$2@4$a$3$2@6$f$e$8$b@3$4@1$0#5+7Kv$1@2$5@1$0#5+7@3$4@1$0#5+h8Kv$1@2$5@1$0#5+h8@3$4@1$0#5+5Kv$1@2$5@1$0#5+5+4"). Proof. vm_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cas_exit_lock : ltac2:(zQ "h31!h9!jc!l5!l9!le!ijb!od!o4!ioe!ip6!ipd!ir1!ir9!hle!nd!iu9!jic!jmf!jn9&>0@1$1@1$0#k0@1$7@1$1@1$0#8>4regs@2$f@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>1v@1$1@1$0#k0>0@3$6@1$1@1$0#k0@2$8^4@3$3@1$0#5+dKv$2@2$4@1$0#5+d@2$5@1$0#k0+nhhlo8>0@3$6@1$1@1$0#k0@2$8^5@3$3@1$0#5+bKv$2@2$4@1$0#5+b@2$5@1$0#k0Z>0@3$6@1$1@1$0#k0@2$8^6@3$3@1$0#5+cKv$2@2$4@1$0#5+c^3>0@3$6@1$7@1$9@1$1@1$0#8@4$h2$d^6@2$5@1$0#k0+nhhlo8N4@2$e@1$9@1$1@1$0#8@2$aN4@2$5@1$0#k0Z@3$h1$d@5$b?2fx^8Kd@3$3@1$0#k0+hphip4Kv$2@2$4@1$0#k0+hphip4@1$1@1$0#k0^7^6@5$b?2fx@3$c@3$c^8@3$3@1$0#5+eKv$2@2$4@1$0#5+e@2$5@1$0#k0Z@3$3@1$0#5+fKv$2@2$4@1$0#5+f@2$5@1$0#k0ZKd@3$3@1$0#k0+hphiq0Kv$2@2$4@1$0#k0+hphiq0@1$1@1$0#k0@3$h0^7@2$5@1$0#k0+nhhlo8@2$aN4^5^6").
Proof.
  intros regs mem rom v R13 R11 R12 Mlock.
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
      [ exact F_191294 | reflexivity | exact D_191294
      | rewrite R13; u_norm; reflexivity
      | rewrite R13; exact Mlock
      | apply bytes_le_to_Z_4; u_norm; lia ]
    | ].
  reduce_bv_eqb_ifs.
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [exact F_191298 | reflexivity | exact D_191298 | gres; rewrite R11; cond_compute ] | ].
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_sc_w_ok; [exact F_19129c | reflexivity | exact D_19129c
      | gres; rewrite R13; u_norm; reflexivity | gres; reflexivity | gres; rewrite R13; sok_data ] | ].
  reduce_bv_eqb_ifs. gres. rewrite R13, R12.
  match goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
  f_equal; try reflexivity. all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cas_mu_lock : ltac2:(zQ "h31!h9!jc!l5!l9!le!ijb!o4!od!ioe!ip6!ipd!ir1!ir9!hle!nd!iu9!jic!jmf!jn9&>0@1$1@1$0#k0@1$6@1$1@1$0#8>4regs@2$f@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>1v@1$1@1$0#k0>0@3$7@1$1@1$0#k0@2$8^4@3$3@1$0#5+h8Kv$2@2$4@1$0#5+h8@2$5@1$0#k0+hrqqj0>0@3$7@1$1@1$0#k0@2$8^5@3$3@1$0#5+cKv$2@2$4@1$0#5+c^2>0@3$7@1$6@1$9@1$1@1$0#8@4$h2$d^5@2$5@1$0#k0+hrqqj0N8@2$e@1$9@1$1@1$0#8@2$aN8^3@3$h1$d@5$b?2fx^7Kd@3$3@1$0#k0+nnrj4Kv$2@2$4@1$0#k0+nnrj4@1$1@1$0#k0^6^5@5$b?2fx@3$c@3$c^7@3$3@1$0#5+dKv$2@2$4@1$0#5+d^4@3$3@1$0#5+fKv$2@2$4@1$0#5+f@2$5@1$0#k0ZKd@3$3@1$0#k0+nnrk0Kv$2@2$4@1$0#k0+nnrk0@1$1@1$0#k0@3$h0^6@2$5@1$0#k0+hrqqj0@2$aN8@2$8^7@3$3@1$0#5+eKv$2@2$4@1$0#5+e^5").
Proof.
  intros regs mem rom v R24 R12 Mmu.
  eapply mst_step; [reflexivity
    | eapply step_lr_d with (bs := word_to_le_bytes 8 v) (v := v);
      [ exact F_77b34 | reflexivity | exact D_77b34
      | rewrite R24; u_norm; reflexivity
      | rewrite R24; exact Mmu
      | apply bytes_le_to_Z_8 ]
    | ].
  reduce_bv_eqb_ifs.
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [exact F_77b38 | reflexivity | exact D_77b38 | gres; rewrite R12; apply c_eq_refl ] | ].
  eapply mst_step; [reflexivity
    | eapply step_sc_d_ok; [exact F_77b3c | reflexivity | exact D_77b3c
      | gres; rewrite R24; u_norm; reflexivity | gres; reflexivity | gres; rewrite R24; sok_data ] | ].
  reduce_bv_eqb_ifs. gres. rewrite R24.
  match goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
  f_equal; try reflexivity. all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cas_mu_unlock : ltac2:(zQ "h31!h9!jc!l5!l9!le!ijb!o4!od!ioe!ip6!ipd!ir1!ir9!hle!nd!iu9!jic!jmf!jn9&>0@1$1@1$0#k0@1$6@1$1@1$0#8>4regs@2$f@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>1v@1$1@1$0#k0>0@3$7@1$1@1$0#k0@2$8^4@3$3@1$0#5+h8Kv$2@2$4@1$0#5+h8@2$5@1$0#k0+hrqqj0>0@3$7@1$1@1$0#k0@2$8^5@3$3@1$0#5+aKv$2@2$4@1$0#5+a^2>0@3$7@1$6@1$9@1$1@1$0#8@4$h2$d^5@2$5@1$0#k0+hrqqj0N8@2$e@1$9@1$1@1$0#8@2$aN8^3@3$h1$d@5$b?2fx^7Kd@3$3@1$0#k0+nnuq4Kv$2@2$4@1$0#k0+nnuq4@1$1@1$0#k0^6^5@5$b?2fx@3$c@3$c^7@3$3@1$0#5+6Kv$2@2$4@1$0#5+6^4@3$3@1$0#5+7Kv$2@2$4@1$0#5+7@2$5@1$0#k0ZKd@3$3@1$0#k0+nnur0Kv$2@2$4@1$0#k0+nnur0@1$1@1$0#k0@3$h0^6@2$5@1$0#k0+hrqqj0@2$aN8@2$8^7@3$3@1$0#5+5Kv$2@2$4@1$0#5+5^5").
Proof.
  intros regs mem rom v R24 R10 Mmu.
  eapply mst_step; [reflexivity
    | eapply step_lr_d with (bs := word_to_le_bytes 8 v) (v := v);
      [ exact F_77ea4 | reflexivity | exact D_77ea4
      | rewrite R24; u_norm; reflexivity
      | rewrite R24; exact Mmu
      | apply bytes_le_to_Z_8 ]
    | ].
  reduce_bv_eqb_ifs.
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [exact F_77ea8 | reflexivity | exact D_77ea8 | gres; rewrite R10; apply c_eq_refl ] | ].
  eapply mst_step; [reflexivity
    | eapply step_sc_d_ok; [exact F_77eac | reflexivity | exact D_77eac
      | gres; rewrite R24; u_norm; reflexivity | gres; reflexivity | gres; rewrite R24; sok_data ] | ].
  reduce_bv_eqb_ifs. gres. rewrite R24.
  match goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
  f_equal; try reflexivity. all: try (apply bv_eq; vm_compute; reflexivity).
Qed.
End FPX1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
