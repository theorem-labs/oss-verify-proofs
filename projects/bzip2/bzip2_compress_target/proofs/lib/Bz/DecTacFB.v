(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export DecCutFB.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

(* [comment removed for export] *)
Ltac DecCutF.dr_closeF ::=
  unfold drest_at; cbn [r_of r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl
                        di_segs di_got di_stderrp di_crc di_rnums di_dec DI_B0]; dmodel_cbn;
  repeat match goal with |- _ /\ _ => split end; dr_pieceF.

(* [comment removed for export] *)
Ltac aframe_dj AOK :=
  DecCutB.revive_slim_ctx;
  pose proof alloc_ceiling_range;
  pose proof (alin_core _ _ AOK);
  try match goal with SM : b_small _ = _ |- _ => first [ pose proof (act_ll _ _ AOK SM) | pose proof (act_tt _ _ AOK SM) ] end;
  cbn [disjoint_from]; simpl_sizes;
  first [ slia
        | let X := fresh "SEPfb" in let Y := fresh "SEPshf" in
          pose proof (act_sep_fb _ _ AOK) as X; pose proof (act_sep_shf _ _ AOK) as Y; slia ].
Ltac aframe_revive :=
  lazymatch goal with |- aframe ?A ?m =>
    match goal with AOK : act_ok _ A, AF : aframe A ?me, MUL : munch ?W ?me m, WML : wmono _ ?me m |- _ =>
      apply (aframe_tr A W me m AF MUL WML); aframe_dj AOK
    end
  end.

(* [comment removed for export] *)
Ltac cut_sideF DP :=
  lazymatch goal with
  | |- dmem _ _ _ _ _ _ _ => close_dmemF
  | |- fuel_ok _ _ _ => fuelF
  | |- rw_cells _ ?m (a_P ?A) _ => match goal with H : rw_cells _ m (a_P A) _ |- _ => exact H end
  | |- rw_cells _ ?m (a_P ?A + ?k)%Z _ => match goal with H : rw_cells _ m (a_P A + k)%Z _ |- _ => exact H end
  | |- aframe _ ?m => first [ match goal with H : aframe _ m |- _ => exact H end | close_aframe | aframe_revive ]
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- munch _ (a_m0 _) _ => match goal with H : munch _ (a_m0 _) _ |- _ => exact H end
  | |- wmono _ (a_m0 _) _ => match goal with H : wmono _ (a_m0 _) _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  | |- dpureF _ _ _ _ _ _ => solve [ dpureF_solve DP ]
  end.

Tactic Notation "enter_cutF" uconstr(NEXT) constr(DP) :=
  eapply evt_eq; [ | eapply NEXT ]; only 1: unify_memF; try cut_sideF DP; only 1: (dvF_cbn; dmodel_cbn; st_eq).
