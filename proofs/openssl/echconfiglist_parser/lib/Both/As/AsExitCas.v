(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibAtomic.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import RefExitBase As_code_524c30_5252e4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cas_exit_lock : forall regs mem rom (v : word),
  getr regs 13 = Z_to_bv 64 0xc01f00 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = v ->
  rdn RSEGS mem (Z_to_bv 64 0xc01f00) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  msteps RSEGS (mkst regs (0x55e57c : word) mem rom)
               (mkst (regupd (regupd regs 14 (Z_to_bv 64 0)) 15 (Z_to_bv 64 0)) (0x55e588 : word)
                     (wbytes mem (Z_to_bv 64 0xc01f00) (word_to_le_bytes 4 v)) rom).
Proof.
  intros regs mem rom v R13 R11 R12 Mlock.
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
      [ exact F_524f18 | reflexivity | exact D_524f18
      | rewrite R13; u_norm; reflexivity
      | rewrite R13; exact Mlock
      | apply bytes_le_to_Z_4; u_norm; lia ]
    | ].
  reduce_bv_eqb_ifs.
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_bne_ft_r; [exact F_524f1c | reflexivity | exact D_524f1c | gres; rewrite R11; cond_compute ] | ].
  (* [comment removed for export] *)
  eapply mst_step; [reflexivity
    | eapply step_sc_w_ok; [exact F_524f20 | reflexivity | exact D_524f20
      | gres; rewrite R13; u_norm; reflexivity | gres; reflexivity | gres; rewrite R13; sok_data ] | ].
  reduce_bv_eqb_ifs. gres. rewrite R13, R12.
  match goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
  f_equal; try reflexivity. all: try (apply bv_eq; vm_compute; reflexivity).
Qed.

