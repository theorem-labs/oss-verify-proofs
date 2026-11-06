(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDUM BzDU7 DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts6 S0F_decCuts7.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDUM BzDU7 DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts6 S0F_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit DecFast DecFastT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzImg0TacFR BzImg0Tac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA RelLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0F_dec_U7A.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts7.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFast OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0TacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  (* [comment removed for export] *)
  Variable t : Z.
  Hypothesis HL7C : forall mn mx, S0F_cut_L7C A F t mn mx.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Definition L7I (i mn mx : Z) : Prop :=
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x9 x12 x14 x16 x17 x23 x26 x27 x28 x29 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f32 f40 f56 f64 f72 f80 f88 f136 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 (Z_to_bv 64 (sv_nSelectors L)) f32 f40 (Z_to_bv 64 (sv_alphaSize L + 43888)) f56 f64 f72 f80 f88 (Z_to_bv 64 (sv_nGroups L))
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 51628)) (Z_to_bv 64 (S + 45436)) f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (dinv_L7I L d t i mn mx /\ i < sv_alphaSize L)%Z ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7I F L d s t i mn mx))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 (S + 43888 + 258 * t + sv_alphaSize L)) (Z_to_bv 64 (S + 43888 + 258 * t + i)) x12 (Z_to_bv 64 (258 * t)) x14 (Z_to_bv 64 mx) x16 x17
              (Z_to_bv 64 mn) (Z_to_bv 64 S) (Z_to_bv 64 (S + 43888)) (Z_to_bv 64 (S + 64012))
              (Z_to_bv 64 (S + 2047)) x23 (Z_to_bv 64 t) (Z_to_bv 64 (S + 43888 + 258 * t)) x26 x27 x28 x29
              (Z_to_bv 64 (sv_alphaSize L)) x31)
          (a_F A) (Z_to_bv 64 0x1dd34) (a_fc A) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Lemma S0F_U7_I : forall i mn mx, (forall mn' mx', L7I (i + 1) mn' mx') -> L7I i mn mx.
  Proof.
    intros i mn mx NXI. unfold L7I. intros until pb. intros DM FR ST MU WM MI DP [DI Hia] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht & Hi & Hmn & Hmx & SCAN & SC0 & TU).
    pose proof COM as COM'. destruct COM' as [SEL LALL]. pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_at [S + 43888]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    pose proof (LALL t i ltac:(lia) ltac:(lia)) as Bb.
    lazymatch goal with H : u8arr _ ?mm (S + 43888)%Z (zb8 ?a ?n) |- _ =>
      pose proof (zb8_read1 s0segs mm (S + 43888) a n (258 * t + i)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. rewrite zxb_lit8 by lia.
    set (b := zget (d_len d) (258 * t + i)) in *.
    rewrite (K_L7I_step F L d s t i mn mx) in KQ by lia. fold b in KQ.
    Ltac fin_scan t NXI MUL WML DP b mn mx :=
      (* [comment removed for export] *)
      let K := fresh "K" in
      wstepl;
      wstepl; if_cases K; zify_cond_z K;
      [ revive_all MUL WML AOK; enter_sameF (NXI (Z.min mn b) (Z.max mx b)) DP
      | (* [comment removed for export] *) wstepl;
        match goal with KQ : kq _ _ |- _ => rewrite K_L7I_exit in KQ by (unset_Z; lia) end;
        revive_all MUL WML AOK; enter_sameF (HL7C (Z.min mn b) (Z.max mx b)) DP ].
    replace (if (b <? mn)%Z then b else mn) with (Z.min mn b) in KQ by (destruct (Z.ltb_spec b mn); lia).
    replace (if (mx <? b)%Z then b else mx) with (Z.max mx b) in KQ by (destruct (Z.ltb_spec mx b); lia).
    assert (SCAN' : forall j, (0 <= j < i + 1)%Z -> (Z.min mn b <= zget (d_len d) (258 * t + j) <= Z.max mx b)%Z).
    { intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [unset_Z; lia|]. specialize (SCAN j ltac:(lia)). lia. }
    (* [comment removed for export] *)
    wstepl; if_cases K1; zify_cond_z K1.
    - wstepl; if_cases K2; zify_cond_z K2.
      + replace (Z_to_bv 64 mx) with (Z_to_bv 64 (Z.max mx b)) by (f_equal; lia).
        replace (Z_to_bv 64 mn) with (Z_to_bv 64 (Z.min mn b)) by (f_equal; lia).
        fin_scan t NXI MUL WML DP b mn mx.
        all: unfold dinv_L7I, dinv_L7C; repeat match goal with |- _ /\ _ => split end; try assumption; try (unset_Z; lia).
        all: try (intros j Hj; apply SCAN'; unset_Z; lia).
      + wstepl.
        replace (Z_to_bv 64 mx) with (Z_to_bv 64 (Z.max mx b)) by (f_equal; lia).
        replace (Z_to_bv 64 b) with (Z_to_bv 64 (Z.min mn b)) by (f_equal; lia).
        fin_scan t NXI MUL WML DP b mn mx.
        all: unfold dinv_L7I, dinv_L7C; repeat match goal with |- _ /\ _ => split end; try assumption; try (unset_Z; lia).
        all: try (intros j Hj; apply SCAN'; unset_Z; lia).
    - wstepl.
      wstepl; if_cases K2; zify_cond_z K2.
      + replace (Z_to_bv 64 b) with (Z_to_bv 64 (Z.max mx b)) by (f_equal; lia).
        replace (Z_to_bv 64 mn) with (Z_to_bv 64 (Z.min mn b)) by (f_equal; lia).
        fin_scan t NXI MUL WML DP b mn mx.
        all: unfold dinv_L7I, dinv_L7C; repeat match goal with |- _ /\ _ => split end; try assumption; try (unset_Z; lia).
        all: try (intros j Hj; apply SCAN'; unset_Z; lia).
      + wstepl.
        replace (Z_to_bv 64 b) with (Z_to_bv 64 (Z.max mx b)) by (f_equal; lia).
        fin_scan t NXI MUL WML DP b mn mx.
        all: unfold dinv_L7I, dinv_L7C; repeat match goal with |- _ /\ _ => split end; try assumption; try (unset_Z; lia).
        all: try (intros j Hj; apply SCAN'; unset_Z; lia).
  Qed.

  Lemma S0F_U7_I_all : forall k : nat, forall i mn mx, (258 - Z.of_nat k <= i)%Z -> L7I i mn mx.
  Proof.
    induction k as [|k IH]; intros i mn mx Hi.
    - (* [comment removed for export] *)
      unfold L7I. intros until pb. intros DM FR ST MU WM MI DP [DI Hia] FU. exfalso.
      destruct DI as (((AL & _) & _) & _). unfold alpha_ok in AL. cbn in Hi. lia.
    - apply S0F_U7_I. intros mn' mx'. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U7_T : S0F_cut_L7T A F t.
  Proof.
    unfold S0F_cut_L7T. intros until pb. intros DM FR ST MU WM MI DP [DI LT] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht & TU).
    pose proof COM as COM'. destruct COM' as [SEL LALL]. pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro.
    rewrite K_L7T_scan in KQ by exact LT.
    hide_all_but_at [usp + -320]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    wstepl. wstepl. wstepl. wstepl. wstepl. if_false_z. wstepl. wstepl. wstepl. wstepl. wstepl.
    revive_all MUL WML AOK.
    enter_sameF (S0F_U7_I_all 258%nat 0 32 0 ltac:(cbn; lia)) DP.
    split; [| lia]. unfold dinv_L7I. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.
End R.
End ACeilS1.
End S0F_dec_U7A.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_dec_U7B.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_dec_U7C.S0F_dec_U7A OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_dec_U7B.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require SasFastF.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HH7M : S0F_cut_H7M A F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Lemma S0F_U7_D : forall t, S0F_cut_L7T A F (t + 1) -> S0F_cut_L7D A F t.
  Proof.
    intros t NXT. unfold S0F_cut_L7D. intros until pb. intros DM FR ST MU WM MI DP [DI Ht] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht1 & TU).
    pose proof COM as COM'. destruct COM' as [SEL LALL]. pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro.
    hide_all_but_at [usp + -320]%Z.
    pose proof (munch_refl [(usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl.
    wstepl; if_cases KC; zify_cond_z KC.
    - revive_all MUL WML AOK. enter_sameF NXT DP. split; [exact DI| lia].
    - (* [comment removed for export] *)
      do 7 wstepl.
      rewrite (K_L7T_exit F L d s (t + 1)) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HH7M DP.
      unfold dinv_H7M. split; [exact COM|]. replace (sv_nGroups L) with (t + 1)%Z by lia. exact TU.
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U7_pro : S0F_cut_L7T A F 0 -> S0F_cut_HHB A F.
  Proof.
    intros NX. unfold S0F_cut_HHB. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (SEL & HtG & LALL). pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro. rewrite K_HHB_L7T in KQ.
    hide_all_but_at [usp + -320]%Z.
    pose proof (munch_refl [(usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    do 6 wstepl. wstepl. if_false_z. do 2 wstepl.
    do 24 wstepl.
    (* [comment removed for export] *)
    rewrite (Z.div_mul (sv_alphaSize L) 4294967296) in * by lia.
    revive_all MUL WML AOK. enter_sameF NX DP.
    split; [| lia]. unfold dinv_L7T, u7com. split; [split; [exact SEL| exact LALL]|]. split; [lia| apply tabs_upto_0].
  Qed.
End R.

(* [comment removed for export] *)
Lemma S0F_U7_tab : forall A, act_ok 320 A -> forall F, S0F_cut_H7M A F -> S0F_cut_HHB A F.
Proof.
  intros A AOK F HH7M.
  assert (STEP : forall t, S0F_cut_L7T A F (t + 1) -> S0F_cut_L7T A F t).
  { intros t NXT. apply (S0F_U7_T A AOK F t). intros mn mx. apply (S0F_U7_C A AOK F t mn mx). apply (S0F_U7_D A AOK F HH7M t NXT). }
  assert (TOP : forall t, (7 <= t)%Z -> S0F_cut_L7T A F t).
  { intros t Ht. unfold S0F_cut_L7T. intros until pb. intros DM FR ST MU WM MI DP [DI LT] FU. exfalso.
    destruct DI as (((_ & NG & _) & _) & _). lia. }
  assert (ALL : forall k : nat, forall t, (7 - Z.of_nat k <= t)%Z -> S0F_cut_L7T A F t).
  { induction k as [|k IH]; intros t Ht.
    - apply TOP. lia.
    - apply STEP. apply IH. lia. }
  apply (S0F_U7_pro A AOK F). apply (ALL 7%nat). cbn; lia.
Qed.

End ACeilS1.
