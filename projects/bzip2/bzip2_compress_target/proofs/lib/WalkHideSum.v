(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SumWalkTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import WalkHide.
Import ListNotations.
Local Open Scope bv_scope.

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
Ltac stepST_new F D aa vv oktac :=
  wh_with ltac:(fun _ =>
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; wh_clear_side; imm_norm; SumWalkTac.addr_tac | gres; wh_clear_side; SumWalkTac.val_tac | wh_reveal; oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; wh_clear_side; imm_norm; SumWalkTac.addr_tac | gres; wh_clear_side; SumWalkTac.val_tac | wh_reveal; oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; wh_clear_side; imm_norm; SumWalkTac.addr_tac | gres; wh_clear_side; SumWalkTac.val_tac
        | reflexivity | wh_reveal; oktac ]
    end
  | step_simpl ]).
Ltac stepLD_new F D bsv vv rdtac vtac :=
  wh_with ltac:(fun _ =>
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | gres; wh_clear_side; imm_norm; SumWalkTac.getr_hyps; wh_reveal; rdtac | vtac ]
  | step_simpl ]; vnorm_old).
Ltac stepLBU_new F D bb rdtac :=
  wh_with ltac:(fun _ =>
  chain_step;
  [ reflexivity
  | eapply step_lbu with (b := bb);
    [ exact F | reflexivity | exact D | gres; wh_clear_side; imm_norm; SumWalkTac.getr_hyps; wh_reveal; rdtac ]
  | step_simpl ]; vnorm_old).

(* [comment removed for export] *)
Ltac rdn_peel1_sum_old :=
  first [ rewrite SumWalkTac.rdn_wbytes_out_Z by (SumWalkTac.zlen; SumWalkTac.lia_fast)
        | rewrite rdn_wbytes_out by (SumWalkTac.zsimp; SumWalkTac.lia_fast) ].
Ltac rdn_peel1_sum_batch := first [ wh_peel_batch | (tryif wh_top_overlaps then fail else rdn_peel1_sum_old) ].

Module OptIn.
Export WalkHide.OptIn.
#[export] Ltac SumWalkTac.rdn_peel1 ::= rdn_peel1_sum_batch.
#[export] Ltac SumWalkTac.stepST F D aa vv oktac ::= stepST_new F D aa vv oktac.
#[export] Ltac SumWalkTac.stepLD F D bsv vv rdtac vtac ::= stepLD_new F D bsv vv rdtac vtac.
#[export] Ltac SumWalkTac.stepLBU F D bb rdtac ::= stepLBU_new F D bb rdtac.
End OptIn.
