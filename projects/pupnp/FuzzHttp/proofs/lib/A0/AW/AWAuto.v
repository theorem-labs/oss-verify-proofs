(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StepFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import AWKit.
Import ListNotations.
Open Scope Z_scope.

Ltac cur_instr :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w => let d := eval vm_compute in (decode_any w) in
                 lazymatch d with Some (?i, _) => constr:(i) end
    end
  end.

Ltac all_win_ok :=
  repeat match goal with
  | HS : shw _ ?X ?n |- _ => lazymatch goal with _ : win_ok X n |- _ => fail | _ => pose proof (shw_win_ok _ _ _ HS) end
  end;
  unfold win_ok in *.

Ltac chk0_auto r APP :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    first
      [ match goal with HA : accessible mm ?X ?n |- _ => acc_chk0 r APP HA end
      | match goal with HS : shw mm ?X ?n |- _ => let HA := fresh "ACCs" in pose proof (proj1 HS) as HA; acc_chk0 r APP HA; clear HA end
      | match goal with HA : accessible ?m0 ?X ?n, WK : win_ok ?X ?n, MU : munch ?W ?m0 mm |- _ =>
          let HA' := fresh "ACCn" in
          pose proof (accessible_frame _ _ _ _ _ HA WK MU ltac:(first [app_ivs_tac | all_win_ok; app_ivs_tac])) as HA'; acc_chk0 r APP HA'; clear HA' end
      | match goal with HS : shw ?m0 ?X ?n, MU : munch ?W ?m0 mm |- _ =>
          let HA' := fresh "ACCn" in
          pose proof (accessible_frame _ _ _ _ _ (proj1 HS) (shw_win_ok _ _ _ HS) MU ltac:(first [app_ivs_tac | all_win_ok; app_ivs_tac])) as HA'; acc_chk0 r APP HA'; clear HA' end
      | fail 1 "chk0_auto: no accessibility fact covers the granule of" APP ]
  end.

Ltac closed_term c := match c with | context [?x] => is_var x; fail 1 | _ => idtac end.
Ltac lit_branch_safe :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => closed_term c; lit_branch end.

Ltac norm32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_lit e) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by lia
  end.

Ltac clear_shr := repeat match goal with H : ov_read_bytes _ _ _ 1 = Some [Z_to_bv 8 0] |- _ => clear H end.

Ltac cstep :=
  let i := cur_instr in
  lazymatch i with
  | Load _ _ _ ?rs1 _ =>
      let r := eval vm_compute in (bv_unsigned rs1) in
      let a := reg_val r in
      lazymatch a with
      | Z_to_bv 64 (Z.shiftr ?APP 3 + 2147450880) => chk0_auto r APP; step; clear_shr
      | _ => step; try norm32
      end
  | Store _ _ _ _ => step; try fix_lit_store
  | Branch _ _ _ _ => step; try lit_branch_safe
  | Op _ _ _ _ => zstep
  | OpImm _ _ _ _ => zstep
  | ShiftImm _ _ _ _ => zstep
  | OpImm32 _ _ _ => zstep; try norm32
  | Op32 _ _ _ _ => zstep; try norm32
  | _ => step
  end.

Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac is_ms := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => idtac end.
Ltac walk_to p := repeat (is_ms; tryif at_pc p then fail else cstep).

Ltac br_lia :=
  let K := fresh "K" in
  if_cases K; zify_cond K; [ first [ (exfalso; lia) |   fail 1 ] | ]; try clear K.
Ltac br_lia2 :=
  let K := fresh "K" in
  if_cases K; zify_cond K; [ | exfalso; lia ]; try clear K.
Ltac br_auto := first [ br_lia | br_lia2 ].
Ltac is_if := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.

Ltac walk_lia_to p := repeat first [ (is_ms; tryif at_pc p then fail else cstep) | (is_if; br_auto) ].
