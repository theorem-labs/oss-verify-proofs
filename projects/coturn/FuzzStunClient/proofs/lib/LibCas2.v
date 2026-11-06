(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac WalkTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic LibCas Ref_code_1b104_1c2fc Ref_code_1c2fc_1d2fc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem cas_lock_1b958 : forall regs mem rom (a newv : word) (old : Z),
  getr regs 13 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn RSEGS mem a 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 old)) -> (0 <= old < 2 ^ 32)%Z ->
  getr regs 11 = v_lw (Z_to_bv 64 old) ->
  getr regs 12 = newv ->
  store_ok RSEGS mem a 4%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x1bb18 : word) mem rom)
                 (mkst regs' (0x1bb28 : word) (wbytes mem a (word_to_le_bytes 4 newv)) rom)
    /\ getr regs' 14 = v_lw (Z_to_bv 64 old)
    /\ getr regs' 15 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom a newv old Ha Hal Hrd Hold Ha1 Ha2 Hok.
  eexists. split.
  - (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 old)) (v := Z_to_bv 64 old);
        [ exact F_1bb18 | reflexivity | exact D_1bb18
        | gres; rewrite Ha; exact Hal
        | gres; rewrite Ha; exact Hrd
        | apply lw_bytes; exact Hold ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1bb1c | reflexivity | exact D_1bb1c
        | gres; rewrite Ha1; apply c_eq_refl ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1bb20 | reflexivity | exact D_1bb20
        | gres; rewrite Ha; exact Hal | gres; rewrite Ha; reflexivity | gres; rewrite Ha; exact Hok ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_1bb24 D_1bb24 ltac:(cond_compute).
    rewrite Ha, Ha2.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
    intros r H14 H15. rewrite !getr_other by assumption. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
