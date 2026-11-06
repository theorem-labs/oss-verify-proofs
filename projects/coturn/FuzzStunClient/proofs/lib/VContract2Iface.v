(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VCert VContract VDriver VSound VState2 VStepMem2 VCert2 VContract2 VGamma2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section Iface2.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.

  Definition contract_post2 (c : contract2) (tgt : Z) : Prop :=
    forall A spoff l nu regs mem (ra : word),
      contract_apply2 P CI c A spoff = CR2OkN l ->
      gamma2 SEGS P E mem0 A nu regs mem ->
      vs_memo A = [] ->
      get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
      (contract2_K c = 0 \/ in_ranges (vp_wstack (p1 P)) (spoff - contract2_K c) (contract2_K c) = true) ->
      ret_ok ra -> getr regs 1%bv = ra ->
      exists A1 v regs' mem' nu',
           In (A1, v) l
        /\ msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra mem' rom)
        /\ gamma2 SEGS P E mem0 (contract_frame2 c A1 spoff v) nu' regs' mem'
        /\ getr regs' 1%bv = ra
        /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next (contract_frame2 c A1 spoff v))%positive
        /\ frame_mod mem mem' (unit_regions2 P E)
        /\ flags_step P E A (contract_frame2 c A1 spoff v) nu nu' mem mem'.

  Definition contract_dead2 (c : contract2) : Prop :=
    forall A spoff nu regs mem,
      contract_apply2 P CI c A spoff = CR2Dead -> gamma2 SEGS P E mem0 A nu regs mem -> False.

  Definition ctab_sound2 (ctab : pmap contract2) : Prop :=
    forall tgt c, 0 < tgt -> pm_get (zkey tgt) ctab = Some c -> contract_post2 c tgt /\ contract_dead2 c.
End Iface2.
