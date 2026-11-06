(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtMuslMemcpyAL.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section AL.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation SB := (sb_ bs).
  #[local] Abbreviation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, c_ltu, bv_eqb, bv_ltu in G in change_no_check G' end); rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 1016) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    wd_eexists. split.
    - mlbu (MF_3f8 _ _ HCODE) D_f56dc k.                      (* [comment removed for export] *)
      msb (MF_3fc _ _ HCODE) D_f56e0 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      replace (k + 1)%Z with n by lia.
      aret (MF_400 _ _ HCODE) D_f56e4 ret.
      wd_refl.
    - solve_keeps.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t2_run : forall regs (ret : word) k m,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z ->
    (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
    (0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 960) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      wd_eexists. split.
      + an (MF_3c0 _ _ HCODE) D_f56a4.                          (* [comment removed for export] *)
        ab_ft (MF_3c4 _ _ HCODE) D_f56a8 ltac:(cond).           (* [comment removed for export] *)
        an (MF_3c8 _ _ HCODE) D_f56ac.                          (* [comment removed for export] *)
        ab_ft (MF_3cc _ _ HCODE) D_f56b0 ltac:(cond).           (* [comment removed for export] *)
        aret (MF_3d0 _ _ HCODE) D_f56b4 ret.
        mk_eq. wd_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 1016) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_3c0 _ _ HCODE) D_f56a4.
          ab_ft (MF_3c4 _ _ HCODE) D_f56a8 ltac:(cond).
          an (MF_3c8 _ _ HCODE) D_f56ac.
          ab_tk (MF_3cc _ _ HCODE) D_f56b0 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      wd_eexists. split.
      + an (MF_3c0 _ _ HCODE) D_f56a4.
        ab_tk (MF_3c4 _ _ HCODE) D_f56a8 ltac:(cond).           (* [comment removed for export] *)
        mlbu (MF_3d4 _ _ HCODE) D_f56b8 k.                         (* [comment removed for export] *)
        mlbu (MF_3d8 _ _ HCODE) D_f56bc (k + 1)%Z.                 (* [comment removed for export] *)
        an (MF_3dc _ _ HCODE) D_f56c0.                          (* [comment removed for export] *)
        an (MF_3e0 _ _ HCODE) D_f56c4.                          (* [comment removed for export] *)
        msb (MF_3e4 _ _ HCODE) D_f56c8 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        msb (MF_3e8 _ _ HCODE) D_f56cc (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        an (MF_3ec _ _ HCODE) D_f56d0.                          (* [comment removed for export] *)
        an (MF_3f0 _ _ HCODE) D_f56d4.                          (* [comment removed for export] *)
        ab_tk (MF_3f4 _ _ HCODE) D_f56d8 ltac:(cond).           (* [comment removed for export] *)
        aret (MF_3d0 _ _ HCODE) D_f56b4 ret.
        mk_eq. wd_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 1016) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_3c0 _ _ HCODE) D_f56a4.
          ab_tk (MF_3c4 _ _ HCODE) D_f56a8 ltac:(cond).
          mlbu (MF_3d4 _ _ HCODE) D_f56b8 k.
          mlbu (MF_3d8 _ _ HCODE) D_f56bc (k + 1)%Z.
          an (MF_3dc _ _ HCODE) D_f56c0.
          an (MF_3e0 _ _ HCODE) D_f56c4.
          msb (MF_3e4 _ _ HCODE) D_f56c8 k ltac:(apply sb_val_plain).
          msb (MF_3e8 _ _ HCODE) D_f56cc (k + 1)%Z ltac:(apply sb_val_plain).
          an (MF_3ec _ _ HCODE) D_f56d0.
          an (MF_3f0 _ _ HCODE) D_f56d4.
          ab_ft (MF_3f4 _ _ HCODE) D_f56d8 ltac:(cond).         (* [comment removed for export] *)
          mk_eq. wd_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 380) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - wd_eexists. split.
      + an (MF_17c _ _ HCODE) D_f5460.                          (* [comment removed for export] *)
        ab_tk (MF_180 _ _ HCODE) D_f5464 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. wd_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - wd_eexists. split.
      + an (MF_17c _ _ HCODE) D_f5460.
        ab_ft (MF_180 _ _ HCODE) D_f5464 ltac:(cond).           (* [comment removed for export] *)
        mlw (MF_184 _ _ HCODE) D_f5468 k.                          (* [comment removed for export] *)
        an (MF_188 _ _ HCODE) D_f546c.                          (* [comment removed for export] *)
        msw (MF_18c _ _ HCODE) D_f5470 k ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        an (MF_190 _ _ HCODE) D_f5474.                          (* [comment removed for export] *)
        an (MF_194 _ _ HCODE) D_f5478.                          (* [comment removed for export] *)
        mk_eq. wd_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 348) (MK k) rom)
                   (mkst regs' (at_ base 380) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - wd_eexists. split.
      + an (MF_15c _ _ HCODE) D_f5440.                          (* [comment removed for export] *)
        ab_tk (MF_160 _ _ HCODE) D_f5444 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. wd_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - wd_eexists. split.
      + an (MF_15c _ _ HCODE) D_f5440.
        ab_ft (MF_160 _ _ HCODE) D_f5444 ltac:(cond).
        mlw (MF_164 _ _ HCODE) D_f5448 k.                          (* [comment removed for export] *)
        mlw (MF_168 _ _ HCODE) D_f544c (k + 4)%Z.                  (* [comment removed for export] *)
        msw (MF_16c _ _ HCODE) D_f5450 k ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        msw (MF_170 _ _ HCODE) D_f5454 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        an (MF_174 _ _ HCODE) D_f5458.                          (* [comment removed for export] *)
        an (MF_178 _ _ HCODE) D_f545c.                          (* [comment removed for export] *)
        mk_eq. wd_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 300) (MK k) rom)
                   (mkst regs' (at_ base 348) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      wd_eexists. split.
      + mlw (MF_12c _ _ HCODE) D_f5410 k.                          (* [comment removed for export] *)
        mlw (MF_130 _ _ HCODE) D_f5414 (k + 4)%Z.                  (* [comment removed for export] *)
        mlw (MF_134 _ _ HCODE) D_f5418 (k + 8)%Z.                  (* [comment removed for export] *)
        mlw (MF_138 _ _ HCODE) D_f541c (k + 12)%Z.                 (* [comment removed for export] *)
        an (MF_13c _ _ HCODE) D_f5420.                          (* [comment removed for export] *)
        an (MF_140 _ _ HCODE) D_f5424.                          (* [comment removed for export] *)
        msw (MF_144 _ _ HCODE) D_f5428 k ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        msw (MF_148 _ _ HCODE) D_f542c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw (MF_14c _ _ HCODE) D_f5430 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw (MF_150 _ _ HCODE) D_f5434 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        an (MF_154 _ _ HCODE) D_f5438.                          (* [comment removed for export] *)
        ab_ft (MF_158 _ _ HCODE) D_f543c ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond).   (* [comment removed for export] *)
        mk_eq. wd_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 300) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + wd_eexists. split.
        * mlw (MF_12c _ _ HCODE) D_f5410 k.
          mlw (MF_130 _ _ HCODE) D_f5414 (k + 4)%Z.
          mlw (MF_134 _ _ HCODE) D_f5418 (k + 8)%Z.
          mlw (MF_138 _ _ HCODE) D_f541c (k + 12)%Z.
          an (MF_13c _ _ HCODE) D_f5420.
          an (MF_140 _ _ HCODE) D_f5424.
          msw (MF_144 _ _ HCODE) D_f5428 k ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
          msw (MF_148 _ _ HCODE) D_f542c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
          msw (MF_14c _ _ HCODE) D_f5430 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
          msw (MF_150 _ _ HCODE) D_f5434 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ _ HOK); lia).
          an (MF_154 _ _ HCODE) D_f5438.
          ab_tk (MF_158 _ _ HCODE) D_f543c ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond).   (* [comment removed for export] *)
          mk_eq. wd_refl.
        * cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. split.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 288) (MK k) rom)
                   (mkst regs' (at_ base 348) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      wd_eexists. split.
      + an (MF_120 _ _ HCODE) D_f5404.                          (* [comment removed for export] *)
        ab_tk (MF_124 _ _ HCODE) D_f5408 ltac:(cond).           (* [comment removed for export] *)
        replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
        wd_refl.
      + rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
        repeat split; gres; rwH; try reflexivity. solve_keeps.
    - set (q := Z.to_nat ((n - k) / 16 - 1)).
      assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
      assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 300) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_120 _ _ HCODE) D_f5404.                        (* [comment removed for export] *)
          ab_ft (MF_124 _ _ HCODE) D_f5408 ltac:(cond).         (* [comment removed for export] *)
          an (MF_128 _ _ HCODE) D_f540c.                        (* [comment removed for export] *)
          wd_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.


End AL.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End AsRtMuslMemcpyAL.
Module AsRtMuslMemcpyMIS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase AsRtMuslMemcpyAL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section MIS.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation SB := (sb_ bs).
  #[local] Abbreviation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, c_ltu, bv_eqb, bv_ltu in G in change_no_check G' end); rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b4_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 916) (MK k) rom) (mkst regs' (at_ base 960) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. wd_eexists. split.
    - mlbu (MF_394 _ _ HCODE) D_f5678 k. mlbu (MF_398 _ _ HCODE) D_f567c (k+1)%Z. mlbu (MF_39c _ _ HCODE) D_f5680 (k+2)%Z. mlbu (MF_3a0 _ _ HCODE) D_f5684 (k+3)%Z.
      an (MF_3a4 _ _ HCODE) D_f5688.                            (* [comment removed for export] *)
      an (MF_3a8 _ _ HCODE) D_f568c.                            (* [comment removed for export] *)
      msb (MF_3ac _ _ HCODE) D_f5690 k ltac:(sbp). msb (MF_3b0 _ _ HCODE) D_f5694 (k+1)%Z ltac:(sbp).
      msb (MF_3b4 _ _ HCODE) D_f5698 (k+2)%Z ltac:(sbp). msb (MF_3b8 _ _ HCODE) D_f569c (k+3)%Z ltac:(sbp).
      an (MF_3bc _ _ HCODE) D_f56a0.                            (* [comment removed for export] *)
      mk_eq. wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 832) (MK k) rom) (mkst regs' (at_ base 908) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. wd_eexists. split.
    - mlbu (MF_340 _ _ HCODE) D_f5624 k. mlbu (MF_344 _ _ HCODE) D_f5628 (k+1)%Z. mlbu (MF_348 _ _ HCODE) D_f562c (k+2)%Z. mlbu (MF_34c _ _ HCODE) D_f5630 (k+3)%Z.
      mlbu (MF_350 _ _ HCODE) D_f5634 (k+4)%Z. mlbu (MF_354 _ _ HCODE) D_f5638 (k+5)%Z. mlbu (MF_358 _ _ HCODE) D_f563c (k+6)%Z. mlbu (MF_35c _ _ HCODE) D_f5640 (k+7)%Z.
      an (MF_360 _ _ HCODE) D_f5644.                            (* [comment removed for export] *)
      msb (MF_364 _ _ HCODE) D_f5648 k ltac:(sbp). msb (MF_368 _ _ HCODE) D_f564c (k+1)%Z ltac:(sbp).
      msb (MF_36c _ _ HCODE) D_f5650 (k+2)%Z ltac:(sbp). msb (MF_370 _ _ HCODE) D_f5654 (k+3)%Z ltac:(sbp).
      an (MF_374 _ _ HCODE) D_f5658.                            (* [comment removed for export] *)
      msb (MF_378 _ _ HCODE) D_f565c (k+4)%Z ltac:(sbp). msb (MF_37c _ _ HCODE) D_f5660 (k+5)%Z ltac:(sbp).
      msb (MF_380 _ _ HCODE) D_f5664 (k+6)%Z ltac:(sbp). msb (MF_384 _ _ HCODE) D_f5668 (k+7)%Z ltac:(sbp).
      an (MF_388 _ _ HCODE) D_f566c.                            (* [comment removed for export] *)
      mk_eq. wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 684) (MK k) rom) (mkst regs' (at_ base 824) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. wd_eexists. split.
    - mlbu (MF_2ac _ _ HCODE) D_f5590 k. mlbu (MF_2b0 _ _ HCODE) D_f5594 (k+1)%Z. mlbu (MF_2b4 _ _ HCODE) D_f5598 (k+2)%Z. mlbu (MF_2b8 _ _ HCODE) D_f559c (k+3)%Z.
      mlbu (MF_2bc _ _ HCODE) D_f55a0 (k+4)%Z. mlbu (MF_2c0 _ _ HCODE) D_f55a4 (k+5)%Z. mlbu (MF_2c4 _ _ HCODE) D_f55a8 (k+6)%Z. mlbu (MF_2c8 _ _ HCODE) D_f55ac (k+7)%Z.
      msb (MF_2cc _ _ HCODE) D_f55b0 k ltac:(sbp). msb (MF_2d0 _ _ HCODE) D_f55b4 (k+1)%Z ltac:(sbp).
      msb (MF_2d4 _ _ HCODE) D_f55b8 (k+2)%Z ltac:(sbp). msb (MF_2d8 _ _ HCODE) D_f55bc (k+3)%Z ltac:(sbp).
      mlbu (MF_2dc _ _ HCODE) D_f55c0 (k+8)%Z. mlbu (MF_2e0 _ _ HCODE) D_f55c4 (k+9)%Z. mlbu (MF_2e4 _ _ HCODE) D_f55c8 (k+10)%Z. mlbu (MF_2e8 _ _ HCODE) D_f55cc (k+11)%Z.
      msb (MF_2ec _ _ HCODE) D_f55d0 (k+4)%Z ltac:(sbp). msb (MF_2f0 _ _ HCODE) D_f55d4 (k+5)%Z ltac:(sbp).
      msb (MF_2f4 _ _ HCODE) D_f55d8 (k+6)%Z ltac:(sbp). msb (MF_2f8 _ _ HCODE) D_f55dc (k+7)%Z ltac:(sbp).
      mlbu (MF_2fc _ _ HCODE) D_f55e0 (k+12)%Z. mlbu (MF_300 _ _ HCODE) D_f55e4 (k+13)%Z. mlbu (MF_304 _ _ HCODE) D_f55e8 (k+14)%Z. mlbu (MF_308 _ _ HCODE) D_f55ec (k+15)%Z.
      an (MF_30c _ _ HCODE) D_f55f0.                            (* [comment removed for export] *)
      msb (MF_310 _ _ HCODE) D_f55f4 (k+8)%Z ltac:(sbp). msb (MF_314 _ _ HCODE) D_f55f8 (k+9)%Z ltac:(sbp).
      msb (MF_318 _ _ HCODE) D_f55fc (k+10)%Z ltac:(sbp). msb (MF_31c _ _ HCODE) D_f5600 (k+11)%Z ltac:(sbp).
      an (MF_320 _ _ HCODE) D_f5604.                            (* [comment removed for export] *)
      msb (MF_324 _ _ HCODE) D_f5608 (k+12)%Z ltac:(sbp). msb (MF_328 _ _ HCODE) D_f560c (k+13)%Z ltac:(sbp).
      msb (MF_32c _ _ HCODE) D_f5610 (k+14)%Z ltac:(sbp). msb (MF_330 _ _ HCODE) D_f5614 (k+15)%Z ltac:(sbp).
      an (MF_334 _ _ HCODE) D_f5618.                            (* [comment removed for export] *)
      mk_eq. wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 104) (MK k) rom) (mkst regs' (at_ base 960) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - wd_eexists. split.
      + an (MF_068 _ _ HCODE) D_f534c.                          (* [comment removed for export] *)
        ab_ft (MF_06c _ _ HCODE) D_f5350 ltac:(cond).           (* [comment removed for export] *)
        an (MF_070 _ _ HCODE) D_f5354.                          (* [comment removed for export] *)
        mk_eq. wd_refl.
      + post.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 916) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_068 _ _ HCODE) D_f534c.
          ab_tk (MF_06c _ _ HCODE) D_f5350 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 908) (MK k) rom) (mkst regs' (at_ base 960) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - wd_eexists. split.
      + an (MF_38c _ _ HCODE) D_f5670.                          (* [comment removed for export] *)
        ab_tk (MF_390 _ _ HCODE) D_f5674 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. wd_refl.
      + post.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 916) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_38c _ _ HCODE) D_f5670.
          ab_ft (MF_390 _ _ HCODE) D_f5674 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 96) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 104) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_060 _ _ HCODE) D_f5344.                        (* [comment removed for export] *)
          ab_ft (MF_064 _ _ HCODE) D_f5348 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 832) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_060 _ _ HCODE) D_f5344.
          ab_tk (MF_064 _ _ HCODE) D_f5348 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 908) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 824) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 104) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_338 _ _ HCODE) D_f561c.                        (* [comment removed for export] *)
          ab_tk (MF_33c _ _ HCODE) D_f5620 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 832) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_338 _ _ HCODE) D_f561c.
          ab_ft (MF_33c _ _ HCODE) D_f5620 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 908) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 88) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 96) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_058 _ _ HCODE) D_f533c.                        (* [comment removed for export] *)
          ab_ft (MF_05c _ _ HCODE) D_f5340 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 684) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_058 _ _ HCODE) D_f533c.
          ab_tk (MF_05c _ _ HCODE) D_f5340 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 824) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End AsRtMuslMemcpyMIS.
Module AsRtMuslMemcpyC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase AsRtMuslMemcpyAL AsRtMuslMemcpyMIS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section C1.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation SB := (sb_ bs).
  #[local] Abbreviation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, c_ltu, bv_eqb, bv_ltu in G in change_no_check G' end); rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m24 := eapply (merge_s24 _ _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c1_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 116) (MK k) rom) (mkst regs' (at_ base 576) (MK (k + 3)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. wd_eexists. split.
    - mlw (MF_074 _ _ HCODE) D_f5358 k.                            (* [comment removed for export] *)
      an (MF_078 _ _ HCODE) D_f535c.                            (* [comment removed for export] *)
      ab_ft (MF_07c _ _ HCODE) D_f5360 ltac:(cond).             (* [comment removed for export] *)
      an (MF_080 _ _ HCODE) D_f5364.                            (* [comment removed for export] *)
      ab_tk (MF_084 _ _ HCODE) D_f5368 ltac:(cond).             (* [comment removed for export] *)
      an (MF_21c _ _ HCODE) D_f5500.                            (* [comment removed for export] *)
      an (MF_220 _ _ HCODE) D_f5504.                            (* [comment removed for export] *)
      an (MF_224 _ _ HCODE) D_f5508.                            (* [comment removed for export] *)
      msb (MF_228 _ _ HCODE) D_f550c k ltac:(eapply (sb_val_word0' _ _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
      msb (MF_22c _ _ HCODE) D_f5510 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
      msb (MF_230 _ _ HCODE) D_f5514 (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      an (MF_234 _ _ HCODE) D_f5518.                            (* [comment removed for export] *)
      an (MF_238 _ _ HCODE) D_f551c.                            (* [comment removed for export] *)
      an (MF_23c _ _ HCODE) D_f5520.                            (* [comment removed for export] *)
      mk_eq. wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
    (ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 576) (MK kk) rom)
                   (mkst regs' (at_ base 672) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - wd_eexists. split.
      + an (MF_240 _ _ HCODE) D_f5524.                          (* [comment removed for export] *)
        mlw (MF_244 _ _ HCODE) D_f5528 (kk + 1)%Z.                 (* [comment removed for export] *)
        mlw (MF_248 _ _ HCODE) D_f552c (kk + 5)%Z.                 (* [comment removed for export] *)
        mlw (MF_24c _ _ HCODE) D_f5530 (kk + 9)%Z.                 (* [comment removed for export] *)
        mlw (MF_250 _ _ HCODE) D_f5534 (kk + 13)%Z.                (* [comment removed for export] *)
        an (MF_254 _ _ HCODE) D_f5538. an (MF_258 _ _ HCODE) D_f553c. an (MF_25c _ _ HCODE) D_f5540.
        an (MF_260 _ _ HCODE) D_f5544. an (MF_264 _ _ HCODE) D_f5548. an (MF_268 _ _ HCODE) D_f554c.
        an (MF_26c _ _ HCODE) D_f5550. an (MF_270 _ _ HCODE) D_f5554. an (MF_274 _ _ HCODE) D_f5558.
        an (MF_278 _ _ HCODE) D_f555c. an (MF_27c _ _ HCODE) D_f5560.
        an (MF_280 _ _ HCODE) D_f5564.                          (* [comment removed for export] *)
        msw (MF_284 _ _ HCODE) D_f5568 kk ltac:(m24).
        msw (MF_288 _ _ HCODE) D_f556c (kk + 4)%Z ltac:(m24).
        msw (MF_28c _ _ HCODE) D_f5570 (kk + 8)%Z ltac:(m24).
        msw (MF_290 _ _ HCODE) D_f5574 (kk + 12)%Z ltac:(m24).
        an (MF_294 _ _ HCODE) D_f5578.                          (* [comment removed for export] *)
        an (MF_298 _ _ HCODE) D_f557c.                          (* [comment removed for export] *)
        ab_ft (MF_29c _ _ HCODE) D_f5580 ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond).   (* [comment removed for export] *)
        mk_eq. wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 576) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
                         /\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_240 _ _ HCODE) D_f5524.
          mlw (MF_244 _ _ HCODE) D_f5528 (kk + 1)%Z.
          mlw (MF_248 _ _ HCODE) D_f552c (kk + 5)%Z.
          mlw (MF_24c _ _ HCODE) D_f5530 (kk + 9)%Z.
          mlw (MF_250 _ _ HCODE) D_f5534 (kk + 13)%Z.
          an (MF_254 _ _ HCODE) D_f5538. an (MF_258 _ _ HCODE) D_f553c. an (MF_25c _ _ HCODE) D_f5540.
          an (MF_260 _ _ HCODE) D_f5544. an (MF_264 _ _ HCODE) D_f5548. an (MF_268 _ _ HCODE) D_f554c.
          an (MF_26c _ _ HCODE) D_f5550. an (MF_270 _ _ HCODE) D_f5554. an (MF_274 _ _ HCODE) D_f5558.
          an (MF_278 _ _ HCODE) D_f555c. an (MF_27c _ _ HCODE) D_f5560.
          an (MF_280 _ _ HCODE) D_f5564.
          msw (MF_284 _ _ HCODE) D_f5568 kk ltac:(m24).
          msw (MF_288 _ _ HCODE) D_f556c (kk + 4)%Z ltac:(m24).
          msw (MF_28c _ _ HCODE) D_f5570 (kk + 8)%Z ltac:(m24).
          msw (MF_290 _ _ HCODE) D_f5574 (kk + 12)%Z ltac:(m24).
          an (MF_294 _ _ HCODE) D_f5578.
          an (MF_298 _ _ HCODE) D_f557c.
          ab_tk (MF_29c _ _ HCODE) D_f5580 ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond).   (* [comment removed for export] *)
          mk_eq. wd_refl.
        * cbv beta. post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps segs (mkst regs (at_ base 672) (MK kk) rom)
                   (mkst regs' (at_ base 960) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 96) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_2a0 _ _ HCODE) D_f5584.                        (* [comment removed for export] *)
          an (MF_2a4 _ _ HCODE) D_f5588.                        (* [comment removed for export] *)
          ab_tk (MF_2a8 _ _ HCODE) D_f558c ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ HCODE _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 684) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_2a0 _ _ HCODE) D_f5584.
          an (MF_2a4 _ _ HCODE) D_f5588.
          ab_ft (MF_2a8 _ _ HCODE) D_f558c ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 824) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ HCODE _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ HCODE _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c1_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps segs (mkst regs (at_ base 116) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C1.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End AsRtMuslMemcpyC1.
Module AsRtMuslMemcpyC2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase AsRtMuslMemcpyAL AsRtMuslMemcpyMIS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section C2.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation SB := (sb_ bs).
  #[local] Abbreviation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, c_ltu, bv_eqb, bv_ltu in G in change_no_check G' end); rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m16 := eapply (merge_s16 _ _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma c2_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 116) (MK k) rom) (mkst regs' (at_ base 164) (MK (k + 2)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. wd_eexists. split.
    - mlw (MF_074 _ _ HCODE) D_f5358 k.                            (* [comment removed for export] *)
      an (MF_078 _ _ HCODE) D_f535c.                            (* [comment removed for export] *)
      ab_ft (MF_07c _ _ HCODE) D_f5360 ltac:(cond).             (* [comment removed for export] *)
      an (MF_080 _ _ HCODE) D_f5364.                            (* [comment removed for export] *)
      ab_ft (MF_084 _ _ HCODE) D_f5368 ltac:(cond).             (* [comment removed for export] *)
      an (MF_088 _ _ HCODE) D_f536c.                            (* [comment removed for export] *)
      an (MF_08c _ _ HCODE) D_f5370.                            (* [comment removed for export] *)
      msb (MF_090 _ _ HCODE) D_f5374 k ltac:(eapply (sb_val_word0' _ _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      msb (MF_094 _ _ HCODE) D_f5378 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      an (MF_098 _ _ HCODE) D_f537c.                            (* [comment removed for export] *)
      an (MF_09c _ _ HCODE) D_f5380.                            (* [comment removed for export] *)
      an (MF_0a0 _ _ HCODE) D_f5384.                            (* [comment removed for export] *)
      mk_eq. wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
    (ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 164) (MK kk) rom)
                   (mkst regs' (at_ base 260) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - wd_eexists. split.
      + an (MF_0a4 _ _ HCODE) D_f5388.                          (* [comment removed for export] *)
        mlw (MF_0a8 _ _ HCODE) D_f538c (kk + 2)%Z.                 (* [comment removed for export] *)
        mlw (MF_0ac _ _ HCODE) D_f5390 (kk + 6)%Z.                 (* [comment removed for export] *)
        mlw (MF_0b0 _ _ HCODE) D_f5394 (kk + 10)%Z.                (* [comment removed for export] *)
        mlw (MF_0b4 _ _ HCODE) D_f5398 (kk + 14)%Z.                (* [comment removed for export] *)
        an (MF_0b8 _ _ HCODE) D_f539c. an (MF_0bc _ _ HCODE) D_f53a0. an (MF_0c0 _ _ HCODE) D_f53a4.   (* [comment removed for export] *)
        an (MF_0c4 _ _ HCODE) D_f53a8. an (MF_0c8 _ _ HCODE) D_f53ac. an (MF_0cc _ _ HCODE) D_f53b0.   (* [comment removed for export] *)
        an (MF_0d0 _ _ HCODE) D_f53b4. an (MF_0d4 _ _ HCODE) D_f53b8. an (MF_0d8 _ _ HCODE) D_f53bc.   (* [comment removed for export] *)
        an (MF_0dc _ _ HCODE) D_f53c0. an (MF_0e0 _ _ HCODE) D_f53c4.                          (* [comment removed for export] *)
        an (MF_0e4 _ _ HCODE) D_f53c8.                          (* [comment removed for export] *)
        msw (MF_0e8 _ _ HCODE) D_f53cc kk ltac:(m16).              (* [comment removed for export] *)
        msw (MF_0ec _ _ HCODE) D_f53d0 (kk + 4)%Z ltac:(m16).      (* [comment removed for export] *)
        msw (MF_0f0 _ _ HCODE) D_f53d4 (kk + 8)%Z ltac:(m16).      (* [comment removed for export] *)
        msw (MF_0f4 _ _ HCODE) D_f53d8 (kk + 12)%Z ltac:(m16).     (* [comment removed for export] *)
        an (MF_0f8 _ _ HCODE) D_f53dc.                          (* [comment removed for export] *)
        an (MF_0fc _ _ HCODE) D_f53e0.                          (* [comment removed for export] *)
        ab_ft (MF_100 _ _ HCODE) D_f53e4 ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond).   (* [comment removed for export] *)
        mk_eq. wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 164) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
                         /\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_0a4 _ _ HCODE) D_f5388.
          mlw (MF_0a8 _ _ HCODE) D_f538c (kk + 2)%Z.
          mlw (MF_0ac _ _ HCODE) D_f5390 (kk + 6)%Z.
          mlw (MF_0b0 _ _ HCODE) D_f5394 (kk + 10)%Z.
          mlw (MF_0b4 _ _ HCODE) D_f5398 (kk + 14)%Z.
          an (MF_0b8 _ _ HCODE) D_f539c. an (MF_0bc _ _ HCODE) D_f53a0. an (MF_0c0 _ _ HCODE) D_f53a4.
          an (MF_0c4 _ _ HCODE) D_f53a8. an (MF_0c8 _ _ HCODE) D_f53ac. an (MF_0cc _ _ HCODE) D_f53b0.
          an (MF_0d0 _ _ HCODE) D_f53b4. an (MF_0d4 _ _ HCODE) D_f53b8. an (MF_0d8 _ _ HCODE) D_f53bc.
          an (MF_0dc _ _ HCODE) D_f53c0. an (MF_0e0 _ _ HCODE) D_f53c4.
          an (MF_0e4 _ _ HCODE) D_f53c8.
          msw (MF_0e8 _ _ HCODE) D_f53cc kk ltac:(m16).
          msw (MF_0ec _ _ HCODE) D_f53d0 (kk + 4)%Z ltac:(m16).
          msw (MF_0f0 _ _ HCODE) D_f53d4 (kk + 8)%Z ltac:(m16).
          msw (MF_0f4 _ _ HCODE) D_f53d8 (kk + 12)%Z ltac:(m16).
          an (MF_0f8 _ _ HCODE) D_f53dc.
          an (MF_0fc _ _ HCODE) D_f53e0.
          ab_tk (MF_100 _ _ HCODE) D_f53e4 ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond).   (* [comment removed for export] *)
          mk_eq. wd_refl.
        * cbv beta. post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps segs (mkst regs (at_ base 260) (MK kk) rom)
                   (mkst regs' (at_ base 960) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 96) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_104 _ _ HCODE) D_f53e8.                        (* [comment removed for export] *)
          an (MF_108 _ _ HCODE) D_f53ec.                        (* [comment removed for export] *)
          ab_tk (MF_10c _ _ HCODE) D_f53f0 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ HCODE _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 684) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_104 _ _ HCODE) D_f53e8.
          an (MF_108 _ _ HCODE) D_f53ec.
          ab_ft (MF_10c _ _ HCODE) D_f53f0 ltac:(cond).         (* [comment removed for export] *)
          an (MF_110 _ _ HCODE) D_f53f4.                        (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 824) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ HCODE _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ HCODE _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c2_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps segs (mkst regs (at_ base 116) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C2.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End AsRtMuslMemcpyC2.
Module AsRtMuslMemcpyC3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase AsRtMuslMemcpyAL AsRtMuslMemcpyMIS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section C3.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation SB := (sb_ bs).
  #[local] Abbreviation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, c_ltu, bv_eqb, bv_ltu in G in change_no_check G' end); rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m8 := eapply (merge_s8 _ _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c3_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 116) (MK k) rom) (mkst regs' (at_ base 428) (MK (k + 1)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. wd_eexists. split.
    - mlw (MF_074 _ _ HCODE) D_f5358 k.                            (* [comment removed for export] *)
      an (MF_078 _ _ HCODE) D_f535c.                            (* [comment removed for export] *)
      ab_tk (MF_07c _ _ HCODE) D_f5360 ltac:(cond).             (* [comment removed for export] *)
      msb (MF_198 _ _ HCODE) D_f547c k ltac:(eapply (sb_val_word0' _ _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      an (MF_19c _ _ HCODE) D_f5480.                            (* [comment removed for export] *)
      an (MF_1a0 _ _ HCODE) D_f5484.                            (* [comment removed for export] *)
      an (MF_1a4 _ _ HCODE) D_f5488.                            (* [comment removed for export] *)
      an (MF_1a8 _ _ HCODE) D_f548c.                            (* [comment removed for export] *)
      mk_eq. wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
    (ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 428) (MK kk) rom)
                   (mkst regs' (at_ base 524) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - wd_eexists. split.
      + an (MF_1ac _ _ HCODE) D_f5490.                          (* [comment removed for export] *)
        mlw (MF_1b0 _ _ HCODE) D_f5494 (kk + 3)%Z.                 (* [comment removed for export] *)
        mlw (MF_1b4 _ _ HCODE) D_f5498 (kk + 7)%Z.                 (* [comment removed for export] *)
        mlw (MF_1b8 _ _ HCODE) D_f549c (kk + 11)%Z.                (* [comment removed for export] *)
        mlw (MF_1bc _ _ HCODE) D_f54a0 (kk + 15)%Z.                (* [comment removed for export] *)
        an (MF_1c0 _ _ HCODE) D_f54a4. an (MF_1c4 _ _ HCODE) D_f54a8. an (MF_1c8 _ _ HCODE) D_f54ac.
        an (MF_1cc _ _ HCODE) D_f54b0. an (MF_1d0 _ _ HCODE) D_f54b4. an (MF_1d4 _ _ HCODE) D_f54b8.
        an (MF_1d8 _ _ HCODE) D_f54bc. an (MF_1dc _ _ HCODE) D_f54c0. an (MF_1e0 _ _ HCODE) D_f54c4.
        an (MF_1e4 _ _ HCODE) D_f54c8. an (MF_1e8 _ _ HCODE) D_f54cc.
        an (MF_1ec _ _ HCODE) D_f54d0.                          (* [comment removed for export] *)
        msw (MF_1f0 _ _ HCODE) D_f54d4 kk ltac:(m8).
        msw (MF_1f4 _ _ HCODE) D_f54d8 (kk + 4)%Z ltac:(m8).
        msw (MF_1f8 _ _ HCODE) D_f54dc (kk + 8)%Z ltac:(m8).
        msw (MF_1fc _ _ HCODE) D_f54e0 (kk + 12)%Z ltac:(m8).
        an (MF_200 _ _ HCODE) D_f54e4.                          (* [comment removed for export] *)
        an (MF_204 _ _ HCODE) D_f54e8.                          (* [comment removed for export] *)
        ab_ft (MF_208 _ _ HCODE) D_f54ec ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond).   (* [comment removed for export] *)
        mk_eq. wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 428) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
                         /\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_1ac _ _ HCODE) D_f5490.
          mlw (MF_1b0 _ _ HCODE) D_f5494 (kk + 3)%Z.
          mlw (MF_1b4 _ _ HCODE) D_f5498 (kk + 7)%Z.
          mlw (MF_1b8 _ _ HCODE) D_f549c (kk + 11)%Z.
          mlw (MF_1bc _ _ HCODE) D_f54a0 (kk + 15)%Z.
          an (MF_1c0 _ _ HCODE) D_f54a4. an (MF_1c4 _ _ HCODE) D_f54a8. an (MF_1c8 _ _ HCODE) D_f54ac.
          an (MF_1cc _ _ HCODE) D_f54b0. an (MF_1d0 _ _ HCODE) D_f54b4. an (MF_1d4 _ _ HCODE) D_f54b8.
          an (MF_1d8 _ _ HCODE) D_f54bc. an (MF_1dc _ _ HCODE) D_f54c0. an (MF_1e0 _ _ HCODE) D_f54c4.
          an (MF_1e4 _ _ HCODE) D_f54c8. an (MF_1e8 _ _ HCODE) D_f54cc.
          an (MF_1ec _ _ HCODE) D_f54d0.
          msw (MF_1f0 _ _ HCODE) D_f54d4 kk ltac:(m8).
          msw (MF_1f4 _ _ HCODE) D_f54d8 (kk + 4)%Z ltac:(m8).
          msw (MF_1f8 _ _ HCODE) D_f54dc (kk + 8)%Z ltac:(m8).
          msw (MF_1fc _ _ HCODE) D_f54e0 (kk + 12)%Z ltac:(m8).
          an (MF_200 _ _ HCODE) D_f54e4.
          an (MF_204 _ _ HCODE) D_f54e8.
          ab_tk (MF_208 _ _ HCODE) D_f54ec ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond).   (* [comment removed for export] *)
          mk_eq. wd_refl.
        * cbv beta. post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps segs (mkst regs (at_ base 524) (MK kk) rom)
                   (mkst regs' (at_ base 960) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 96) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_20c _ _ HCODE) D_f54f0.                        (* [comment removed for export] *)
          an (MF_210 _ _ HCODE) D_f54f4.                        (* [comment removed for export] *)
          ab_tk (MF_214 _ _ HCODE) D_f54f8 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ HCODE _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 684) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_20c _ _ HCODE) D_f54f0.
          an (MF_210 _ _ HCODE) D_f54f4.
          ab_ft (MF_214 _ _ HCODE) D_f54f8 ltac:(cond).
          an (MF_218 _ _ HCODE) D_f54fc.                        (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 824) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ HCODE _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ HCODE _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c3_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps segs (mkst regs (at_ base 116) (MK k) rom)
                   (mkst regs' (at_ base 960) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C3.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End AsRtMuslMemcpyC3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase AsRtMuslMemcpyAL AsRtMuslMemcpyMIS AsRtMuslMemcpyC1 AsRtMuslMemcpyC2 AsRtMuslMemcpyC3.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section ALL.
  Variable segs : list Segment.
  Variable base : word.
  Hypothesis HCODE : code_at segs base 0 mmemcpy_words.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation SB := (sb_ bs).
  #[local] Abbreviation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, c_ltu, bv_eqb, bv_ltu in G in change_no_check G' end); rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  (* [comment removed for export] *)
  Ltac conda := rwH; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); cond.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_finish : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 288) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    set (m := ((n - k) mod 16)%Z).
    pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 348) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run _ _ HCODE _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P). exists r.
      subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
    cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 380) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run _ _ HCODE _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 960) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run _ _ HCODE _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
    destruct (t2_run _ _ HCODE _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P).
    exists r. split; [exact R | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mis_run : forall regs (ret : word) k q,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 80) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hn0 HOK HCODE.
    intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
    destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
      assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_050 _ _ HCODE) D_f5334.                        (* [comment removed for export] *)
          ab_ft (MF_054 _ _ HCODE) D_f5338 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        set (m := (n - k)%Z) in *.
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 960) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
                           /\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (t16_run _ _ HCODE _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (t2_run _ _ HCODE _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3).
          exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 116) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_050 _ _ HCODE) D_f5334.                        (* [comment removed for export] *)
          ab_tk (MF_054 _ _ HCODE) D_f5338 ltac:(cond).         (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
        assert (CASE : exists regs' m,
          msteps segs (mkst r1 (at_ base 116) (MK k) rom)
                       (mkst regs' (at_ base 960) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
          /\ (0 <= m < 32)%Z
          /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
        { destruct Hq as [-> | [-> | ->]].
          - apply (c1_run _ _ HCODE _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c2_run _ _ HCODE _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c3_run _ _ HCODE _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
        destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2).
        destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
        assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
        destruct (t2_run _ _ HCODE _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3).
        exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
        eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma j_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 72) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hnwd Hn0 HOK HCODE.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    pose proof (u64_range dst).
    set (q := ((bv_unsigned dst + k) mod 4)%Z).
    pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
    destruct (Z.eq_dec q 0) as [Hq0|Hq0].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 288) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_048 _ _ HCODE) D_f532c.                        (* [comment removed for export] *)
          ab_tk (MF_04c _ _ HCODE) D_f5330 ltac:(conda).        (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 80) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + wd_eexists. split.
        * an (MF_048 _ _ HCODE) D_f532c.
          ab_ft (MF_04c _ _ HCODE) D_f5330 ltac:(conda).        (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post. (lazymatch goal with |- ?G => let G' := eval unfold v_andi, at_ in G in change_no_check G' end). subst q. rewrite <- land_3 by lia. unorm.
          change (bv_wrap 64 3) with 3%Z. reflexivity.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
        destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hl_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
    (Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 24) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hnwd Hnws Hn0 HOK HCODE.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 72) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * wd_eexists. split.
          -- mlbu (MF_018 _ _ HCODE) D_f52fc k.                    (* [comment removed for export] *)
             an (MF_01c _ _ HCODE) D_f5300.                    (* [comment removed for export] *)
             an (MF_020 _ _ HCODE) D_f5304.                    (* [comment removed for export] *)
             an (MF_024 _ _ HCODE) D_f5308.                    (* [comment removed for export] *)
             msb (MF_028 _ _ HCODE) D_f530c k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
             an (MF_02c _ _ HCODE) D_f5310.                    (* [comment removed for export] *)
             an (MF_030 _ _ HCODE) D_f5314.                    (* [comment removed for export] *)
             ab_tk (MF_034 _ _ HCODE) D_f5318 ltac:(conda).    (* [comment removed for export] *)
             wd_refl.
          -- cbv beta. post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 72) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * wd_eexists. split.
          -- mlbu (MF_018 _ _ HCODE) D_f52fc k.
             an (MF_01c _ _ HCODE) D_f5300.
             an (MF_020 _ _ HCODE) D_f5304.
             an (MF_024 _ _ HCODE) D_f5308.
             msb (MF_028 _ _ HCODE) D_f530c k ltac:(apply sb_val_plain).
             an (MF_02c _ _ HCODE) D_f5310.
             an (MF_030 _ _ HCODE) D_f5314.
             ab_ft (MF_034 _ _ HCODE) D_f5318 ltac:(conda).    (* [comment removed for export] *)
             an (MF_038 _ _ HCODE) D_f531c.                    (* [comment removed for export] *)
             ab_ft (MF_03c _ _ HCODE) D_f5320 ltac:(cond).     (* [comment removed for export] *)
             an (MF_040 _ _ HCODE) D_f5324.                    (* [comment removed for export] *)
             wd_refl.
          -- cbv beta. post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
      + wd_eexists. split.
        * mlbu (MF_018 _ _ HCODE) D_f52fc k.
          an (MF_01c _ _ HCODE) D_f5300.
          an (MF_020 _ _ HCODE) D_f5304.
          an (MF_024 _ _ HCODE) D_f5308.
          msb (MF_028 _ _ HCODE) D_f530c k ltac:(apply sb_val_plain).
          an (MF_02c _ _ HCODE) D_f5310.
          an (MF_030 _ _ HCODE) D_f5314.
          ab_ft (MF_034 _ _ HCODE) D_f5318 ltac:(conda).       (* [comment removed for export] *)
          an (MF_038 _ _ HCODE) D_f531c.                       (* [comment removed for export] *)
          ab_tk (MF_03c _ _ HCODE) D_f5320 ltac:(cond).        (* [comment removed for export] *)
          wd_refl.
        * cbv beta. post. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem mmemcpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof using Hnwd Hnws Hn0 HOK HCODE.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite <- (memk_n _ _ _ _ _ _ HOK). change mem0 with (MK 0).
    assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
    assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
    destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 288) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * wd_eexists. split.
          -- an (MF_000 _ _ HCODE) D_f52e4.                     (* [comment removed for export] *)
             ab_tk (MF_004 _ _ HCODE) D_f52e8 ltac:(conda).     (* [comment removed for export] *)
             an (MF_114 _ _ HCODE) D_f53f8.                     (* [comment removed for export] *)
             an (MF_118 _ _ HCODE) D_f53fc.                     (* [comment removed for export] *)
             ab_ft (MF_11c _ _ HCODE) D_f5400 ltac:(cond).      (* [comment removed for export] *)
             wd_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 80) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
        * wd_eexists. split.
          -- an (MF_000 _ _ HCODE) D_f52e4.
             ab_tk (MF_004 _ _ HCODE) D_f52e8 ltac:(conda).
             an (MF_114 _ _ HCODE) D_f53f8.
             an (MF_118 _ _ HCODE) D_f53fc.
             ab_tk (MF_11c _ _ HCODE) D_f5400 ltac:(cond).      (* [comment removed for export] *)
             wd_refl.
          -- cbv beta. post; try (rewrite at_0; reflexivity).
             (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
          pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
          destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 72) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * wd_eexists. split.
          -- an (MF_000 _ _ HCODE) D_f52e4.                     (* [comment removed for export] *)
             ab_ft (MF_004 _ _ HCODE) D_f52e8 ltac:(conda).     (* [comment removed for export] *)
             ab_tk (MF_008 _ _ HCODE) D_f52ec ltac:(cond).      (* [comment removed for export] *)
             an (MF_044 _ _ HCODE) D_f5328.                     (* [comment removed for export] *)
             wd_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
        pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
        * wd_eexists. split.
          -- an (MF_000 _ _ HCODE) D_f52e4.                     (* [comment removed for export] *)
             ab_ft (MF_004 _ _ HCODE) D_f52e8 ltac:(conda).     (* [comment removed for export] *)
             ab_ft (MF_008 _ _ HCODE) D_f52ec ltac:(cond).      (* [comment removed for export] *)
             an (MF_00c _ _ HCODE) D_f52f0.                     (* [comment removed for export] *)
             an (MF_010 _ _ HCODE) D_f52f4.                     (* [comment removed for export] *)
             an (MF_014 _ _ HCODE) D_f52f8.                     (* [comment removed for export] *)
             wd_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
          destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2).
          { subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

End ALL.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPGen1.


From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Section FPGen2.
Context {fx : FPState}.


Definition asan_memcpy_entry : word := 0xf52e0.

Lemma asan_memcpy_code :
  code_at Asan.M.loaded_segments asan_memcpy_entry 0 mmemcpy_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mmemcpy_words in G in change_no_check G' end). code_at_vm. Qed.

Theorem asan_memcpy : forall (mem0 : word -> option byte) (dst src : word) n bs (rom : word -> option byte) regs (ret : word),
  mcH Asan.M.loaded_segments mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps Asan.M.loaded_segments
           (mkst regs asan_memcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ keeps regs regs'.
Proof using.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 asan_memcpy_entry).
  apply (mmemcpy_run _ _ asan_memcpy_code mem0 dst src n bs rom HOK).
Qed.

End FPGen2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

