(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK1h.v (donor image sha256 7093581aab04), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1a YK0s.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Ltac gres :=
repeat first [ rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero.
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.
Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.
Ltac is_pos_lit p :=
lazymatch p with
| xH => idtac
| xO ?q => is_pos_lit q
| xI ?q => is_pos_lit q
end.
Ltac is_Z_lit z :=
lazymatch z with
| Z0 => idtac
| Zpos ?p => is_pos_lit p
| Zneg ?p => is_pos_lit p
end.
Ltac val_lit v :=
lazymatch v with
| Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
| @BV _ _ _ => fail
| _ => wlit_closed v
end.
Ltac vals_lit :=
repeat match goal with
| |- context [regupd _ _ ?v] => val_lit v
end.
Ltac vnorm := gres; imm_norm; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; vals_lit.
Ltac stepn F D :=
lazymatch type of D with
| decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
| _ => stepi F D; vnorm
end.
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.
Ltac stepb_tk F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
| decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
| decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
| decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
end;
[ exact F | reflexivity | exact D | gres; imm_norm; tac ]
| step_simpl; vnorm ].
Ltac stepb_ft F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
| decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
| decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
| decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
end;
[ exact F | reflexivity | exact D | gres; imm_norm; tac ]
| step_simpl; vnorm ].
Ltac cond_compute :=
idtac;
lazymatch goal with
| |- ?g => check_closed_term g; vm_compute; reflexivity
end.
Ltac stepb F D :=
first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].
Ltac stepret F D k tac :=
stepjr F D k ltac:(gres; tac);
imm_norm;
try lazymatch goal with
| Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
| Hk : v_jalr k 0 = k |- _ => rewrite Hk
end;
try (wlit (v_jalr k 0)).
Ltac stepsd F D aa vv oktac :=
chain_step;
[ reflexivity
| eapply step_sd_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D
| gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
| gres; first [ reflexivity | assumption | symmetry; assumption ]
| oktac ]
| step_simpl ].
Ltac stepld F D vv rtac :=
chain_step;
[ reflexivity
| eapply step_ld with (v := vv);
[ exact F | reflexivity | exact D
| gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
| first [ apply bytes_le_to_Z_8 | reflexivity ] ]
| step_simpl; vnorm ].
