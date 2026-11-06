(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/tinyobjloader/fuzz_tobj_c/lib/Lib/CfgGlue.v; 259 of its 292 lines of code are new or changed and 174 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/tinyobjloader/fuzz_tobj_c/lib/U/L10/sd.v, with its module paths and module names changed; 14 of its 31 lines of code are new or changed and 275 lines of the source are left out. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_cuts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Import ListNotations.
Import R2C.
Open Scope Z_scope.

Lemma check_r2 : check_cfg segsU FUEL_r2 cutpcs_r2 NF cuts_r2 exits_r2 = true.
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_r2_strict : existsb ss_lenient cuts_r2 = false.
Proof. reflexivity. Qed.

Theorem r2_sum : r2_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_r2 cutpcs_r2 NF cuts_r2 exits_r2
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_r2U) Hok).
  - rewrite cuts_r2_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_r2.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE; apply exit_post.
    in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
