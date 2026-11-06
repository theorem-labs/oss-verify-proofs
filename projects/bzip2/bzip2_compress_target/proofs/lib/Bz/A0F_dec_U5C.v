(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decCuts5 A0F_decPos.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decPos.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.
  Hypothesis HCOD : A0F_cut_HCOD A Q F.
  (* [comment removed for export] *)
  Variables (L : dsv) (s : dstrm) (J : jk).
  Notation ng := (sv_nGroups L).
  Notation ns := (sv_nSelectors L).
  Notation nsc := (Z.min (sv_nSelectors L) 18002).
  Hypothesis NG : (2 <= sv_nGroups L <= 6)%Z.
  Hypothesis NS : (1 <= sv_nSelectors L < 32768)%Z.
  Hypothesis NBL : (0 <= sv_nblock L <= 900000)%Z.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Notation COMMONA mm dd pb K :=
    (dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) mm (dvF cx J dd s) ->
     aframe_pos A mm ->
     u8arr a0segs mm (a_fb A + 32) pb ->
     rw_cells a0segs mm (a_shf A) (FSH (Z_to_bv 8 6)) ->
     stk a0segs mm (a_lo A) (a_P A) ->
     munch (W14 A) (a_m0 A) mm -> wmono a0segs (a_m0 A) mm -> mem_inv a0segs mm ->
     dpureF cx (a_b0 A) (a_payload A) J dd s ->
     fuel_ok F dd s ->
     alpha_ok L dd -> belown (d_selMtf dd) nsc ng -> K) (only parsing).

  (* [comment removed for export] *)
  Definition LP1cutA (v : Z) (pos : zarr) : Prop :=
    forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x28 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w80 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w592 w608 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word) (pb : list byte),
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 ns) w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 ng) w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    COMMONA m d pb (
    (0 <= v <= ng)%Z ->
    pos_agA pb pos v ->
    (forall k, 0 <= k < v -> zget pos k = k)%Z ->
    evt a0segs (Q (K_LP1 F L d s nsc v pos))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 nsc) x28 (Z_to_bv 64 (a_fb A + 32)) x30 x31)
          (a_F A) (Z_to_bv 64 0xa4c34) (a_fc A) None m (seg_rom a0segs))).

  (* [comment removed for export] *)
  Definition X8cutA (pos : zarr) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x28 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w80 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w592 w608 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word) (pb : list byte),
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 ns) w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 ng) w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    COMMONA m d pb (
    pos_agA pb pos ng ->
    pos_okz pos ng ->
    belown (d_sel d) 0 ng ->
    evt a0segs (Q (K_LP2 F L d s nsc 0 pos))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 nsc) x28 (Z_to_bv 64 (a_fb A + 32)) x30 x31)
          (a_F A) (Z_to_bv 64 0xa4c70) (a_fc A) None m (seg_rom a0segs))).

  (* [comment removed for export] *)
  Definition LP2cutA (i : Z) (pos : zarr) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x17 x18 x22 x23 x24 x25 x26 x28 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w80 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w592 w608 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word) (pb : list byte),
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 ns) w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 ng) w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    COMMONA m d pb (
    pos_agA pb pos ng ->
    pos_okz pos ng ->
    (0 <= i <= nsc)%Z ->
    belown (d_sel d) i ng ->
    evt a0segs (Q (K_LP2 F L d s nsc i pos))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 (Z_to_bv 64 i) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884)) x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 nsc) x28 (Z_to_bv 64 (a_fb A + 32)) x30 x31)
          (a_F A) (Z_to_bv 64 0xa4c9c) (a_fc A) None m (seg_rom a0segs))).

  (* [comment removed for export] *)
  Definition LP3cutA (i : Z) (pos : zarr) (tmp w : Z) : Prop :=
    forall (x1 x7 x12 x18 x22 x23 x24 x25 x26 x28 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w80 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w592 w608 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word) (pb : list byte),
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 ns) w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 ng) w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    COMMONA m d pb (
    pos_agA pb pos ng ->
    pos_okz pos ng ->
    (0 <= i < nsc)%Z ->
    belown (d_sel d) i ng ->
    (0 <= tmp < ng)%Z ->
    (1 <= w < ng)%Z ->
    evt a0segs (Q (K_LP3 F L d s nsc i pos tmp w))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 w) (Z_to_bv 64 (w + 4294967295)) x7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (a_fb A + 32 + w)) (Z_to_bv 64 (a_fb A + 32 + w)) x12 (Z_to_bv 64 i) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 tmp) x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 nsc) x28 (Z_to_bv 64 (a_fb A + 32)) x30 x31)
          (a_F A) (Z_to_bv 64 0xa4cd8) (a_fc A) None m (seg_rom a0segs))).

  (* [comment removed for export] *)
  Definition X78cutA (i : Z) (pos : zarr) (tmp : Z) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x18 x22 x23 x24 x25 x26 x28 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w80 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w592 w608 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word) (pb : list byte),
    A0FL A m w0 w8 w16 w24 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 ns) w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 ng) w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    COMMONA m d pb (
    pos_agA pb pos ng ->
    pos_okz pos ng ->
    (0 <= i < nsc)%Z ->
    belown (d_sel d) i ng ->
    (0 <= tmp < ng)%Z ->
    evt a0segs (Q (K_X78 F L d s nsc i pos tmp))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 (Z_to_bv 64 i) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 tmp) x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 nsc) x28 (Z_to_bv 64 (a_fb A + 32)) x30 x31)
          (a_F A) (Z_to_bv 64 0xa4d3c) (a_fc A) None m (seg_rom a0segs))).

  (* [comment removed for export] *)
  Ltac pos_seps AOK :=
    pose proof (proj1 (act_sep_fb _ _ AOK) : id _) as SEPfs;
    pose proof (proj2 (proj2 (proj2 (act_sep_fb _ _ AOK))) : id _) as SEPff;
    pose proof (proj1 (act_sep_shf _ _ AOK) : id _) as SEPss.
  (* [comment removed for export] *)
  Ltac pos_lb v ANF := rewrite (pos_sh_addr _ _ v ANF) by lia; astep; rewrite sxb_6.
  (* [comment removed for export] *)
  Ltac pos_br v ANF :=
    astep; astep; rewrite (pos_land7 _ _ v ANF) by lia;
    let K := fresh "Kpos" in astep; if_cases K; zify_cond_z K; try (exfalso; lia); clear K.
  (* [comment removed for export] *)
  Ltac pos_brj v ANF := pos_br v ANF; astep.
  Ltac aframe_pos_revive :=
    lazymatch goal with |- aframe_pos ?A ?m =>
      match goal with AOK : act_ok _ A, AF : aframe_pos A ?me, MUL : munch ?W ?me m, WML : wmono _ ?me m |- _ =>
        apply (aframe_pos_tr A W me m AF MUL WML); aframe_dj AOK
      end
    end.
  (* [comment removed for export] *)
  Ltac enter_cutP NXT DP :=
    eapply evt_eq; [ | eapply NXT ]; only 1: unify_memF; try cut_sideF DP; only 1: (dvF_cbn; dmodel_cbn; st_eq);
    try match goal with H : u8arr _ ?mm ?a _ |- u8arr _ ?mm ?a _ => exact H end;
    try match goal with H : rw_cells _ ?mm ?a _ |- rw_cells _ ?mm ?a _ => exact H end;
    try aframe_pos_revive;
    try assumption; try (dmodel_cbn; assumption); try (cbn; lia).
  Ltac prepA DP MU :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    pose proof (act_anchor_fb _ _ AOK) as ANF; pos_seps AOK.

  (* [comment removed for export] *)
  Lemma A0F_U5_entry : LP1cutA 0 znew ->
    forall (d : dst) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w80 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w592 w608 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    A0FL A m w0 w8 w16 (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (S + 8)) w80 (Z_to_bv 64 (S + 7820)) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 (Z_to_bv 64 (sv_nSelectors L)) w592 (Z_to_bv 64 (sv_alphaSize L)) w608 (Z_to_bv 64 (sv_nGroups L)) w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    dinv_HUND L d ->
    fuel_ok F d s ->
    evt a0segs (Q (K_HUND F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xa4c00) (a_fc A) None m (seg_rom a0segs)).
  Proof.
    intros NXT. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prepA DP MU.
    destruct DI as [AL [_ [_ SOK]]].
    view_aframe_mid AF.
    destruct (aframe_pos_open _ _ AF) as (pb & LPB & AFP & POS & FS). unfold FSH in FS. clear AF.
    open_dmemF DM. a0img.
    hide_all_but_atF [a_fb A + 32; a_shf A; a_P A; a_P A + 96; a_P A + 496]%Z.
    pose proof (munch_refl [(a_shf A, a_shf A + 8)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    rewrite K_HUND_LP1, nsel_clamp_eq.
    (* [comment removed for export] *)
    Ltac entry_fin NXT DP LPB MUL WML AOK :=
      arun;
      let KZ := fresh "KZ" in if_cases KZ; zify_cond_z KZ; [exfalso; lia|];
      arun_to 0xa4c34%Z;
      revive_all_fb MUL WML AOK;
      unfold LP1cutA in NXT; enter_cutP NXT DP;
      try (apply pos_agA_nil; exact LPB); try (intros k Hk; exfalso; lia).
    arun. if_cases K; zify_cond_z K.
    - (* [comment removed for export] *) entry_fin NXT DP LPB MUL WML AOK.
    - entry_fin NXT DP LPB MUL WML AOK.
  Qed.

  (* [comment removed for export] *)
  Ltac u8st ARR A i :=
    lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of ARR with u8arr _ _ _ ?bs =>
      pose proof (u8arr_store_ok sg mm A bs i _ ARR ltac:(lia) eq_refl) as SO;
      step; u8_store_doneA ARR i; try clear SO; zsimp; bz32l
    end end.

  Lemma A0F_U5_LP1 : forall v pos, (0 <= v < ng)%Z ->
    ((v + 1 < ng)%Z -> LP1cutA (v + 1) (zset pos v v)) -> X8cutA (zset pos v v) -> LP1cutA v pos.
  Proof.
    intros v pos Hv NXT X8. unfold LP1cutA. intros until pb. intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK Hv' PAG PK.
    prepA DP MU. open_dmemF DM. a0img. unfold FSH in FS.
    hide_all_but_atF [a_fb A + 32; a_shf A; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(a_fb A + 32, a_fb A + 38)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    astep. rewrite (land255_small v) by lia. arun.
    pos_lb v ANF. pos_br v ANF.
    u8st POS (a_fb A + 32)%Z v.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small v 256) in POS by lia.
    assert (PAG' : pos_agA (upd pb (Z.to_nat v) (Z_to_bv 8 v)) (zset pos v v) (v + 1))
      by (apply (pos_agA_set pb pos v); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]).
    assert (PK' : forall k, (0 <= k < v + 1 -> zget (zset pos v v) k = k)%Z)
      by (intros k Hk; rewrite zget_zset; destruct (Z.eqb_spec k v); [lia| apply PK; lia]).
    rewrite K_LP1_step by lia.
    (* [comment removed for export] *)
    arun. rewrite (land255_small (v + 1)) by lia.
    if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP1cutA in NX. revive_all_fb MUL WML AOK.
      enter_cutP NX DP.
    - (* [comment removed for export] *)
      astep. unfold X8cutA in X8. revive_all_fb MUL WML AOK.
      rewrite K_LP1_exit by lia.
      enter_cutP X8 DP.
      + replace ng with (v + 1)%Z by lia. exact PAG'.
      + apply pos_okz_init. replace ng with (v + 1)%Z by lia. exact PK'.
      + apply belown_0.
  Qed.

  Lemma A0F_U5_X8 : forall pos, LP2cutA 0 pos -> X8cutA pos.
  Proof.
    intros pos NXT. unfold X8cutA. intros until pb. intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK PAG POK SEL.
    prepA DP MU.
    (* [comment removed for export] *)
    arun. if_cases K; zify_cond_z K; [exfalso; lia|].
    arun_to 0xa4c9c%Z.
    unfold LP2cutA in NXT. enter_cutP NXT DP.
  Qed.

  Lemma A0F_U5_X78 : forall i pos tmp, (0 <= i < nsc)%Z ->
    ((i + 1 < nsc)%Z -> LP2cutA (i + 1) (zset pos 0 tmp)) -> X78cutA i pos tmp.
  Proof using ACEIL__ A AOK ASH Q F HCOD L s J NG NS NBL.
    intros i pos tmp Hi NXT. unfold X78cutA. intros until pb. intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK PAG POK Hi' SEL TMP.
    prepA DP MU. open_dmemF DM. a0img. unfold FSH in FS.
    destruct (aframe_pos_mid _ _ AFP) as [zt FRM]; unfold FM_CELLS in FRM.
    unfold r_of in DR. dr_open. hide_all_but_atF [a_fb A + 32; a_shf A; S + 7884; a_P A; a_P A + 96; a_P A + 496]%Z.
    pose proof (munch_refl [(a_fb A + 32, a_fb A + 38); (S + 7884, S + 25886); (a_shf A, a_shf A + 8); (a_P A + 496, a_P A + 728)]%Z m) as MUL.
    pose proof (wmono_refl a0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    u8st POS (a_fb A + 32)%Z 0%Z.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small tmp 256) in POS by lia.
    assert (PAG' : pos_agA (upd pb (Z.to_nat 0) (Z_to_bv 8 tmp)) (zset pos 0 tmp) ng)
      by (apply (pos_agA_set pb pos ng); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]).
    assert (POK' : pos_okz (zset pos 0 tmp) ng) by (apply pos_okz_set; [exact POK| lia]).
    (* [comment removed for export] *)
    arun_to 0xa4d58%Z.
    lazymatch goal with H : u8arr _ _ (S + 7884)%Z _ |- _ =>
      zb8_sb H i; try rewrite (Z.mod_small tmp 256) in H by lia end.
    unfold K_X78.
    (* [comment removed for export] *)
    arun; if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP2cutA in NX. revive_all_fb MUL WML AOK.
      enter_cutP NX DP.
      dmodel_cbn. apply belown_set; [exact SEL| lia].
    - (* [comment removed for export] *)
      arun_to 0xa4e2c%Z.
      revive_all_fb MUL WML AOK.
      rewrite K_LP2_exit_HCOD by lia.
      unfold A0F_cut_HCOD in HCOD. enter_cutF (HCOD _ _ _ JK_) DP.
      + eapply aframe_pos_close; [ aframe_pos_revive | exact POS | rewrite upd_length; exact LPB | exact FS ].
      + pose proof AL as AL'. unfold alpha_ok in AL'.
        unfold dinv_HCOD, L_cod, alpha_ok. dmodel_cbn.
        repeat match goal with |- _ /\ _ => split end; try lia.
        replace (Z.min ns 18002) with (i + 1)%Z by lia. apply belown_set; [exact SEL| lia].
  Qed.

  Lemma A0F_U5_LP3 : forall i pos tmp w, (0 <= i < nsc)%Z -> (1 <= w < ng)%Z ->
    ((1 <= w - 1)%Z -> LP3cutA i (zset pos w (zget pos (w - 1))) tmp (w - 1)) ->
    X78cutA i (zset pos w (zget pos (w - 1))) tmp -> LP3cutA i pos tmp w.
  Proof.
    intros i pos tmp w Hi Hw NXT X78. unfold LP3cutA. intros until pb.
    intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK PAG POK Hi' SEL TMP Hw'.
    prepA DP MU. open_dmemF DM. a0img. unfold FSH in FS.
    hide_all_but_atF [a_fb A + 32; a_shf A; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(a_fb A + 32, a_fb A + 38)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    astep. rewrite (land_w32 w) by lia. arun.
    pos_lb (w - 1)%Z ANF. pos_brj (w - 1)%Z ANF.
    (* [comment removed for export] *)
    arun.
    pos_lb w ANF.
    (* [comment removed for export] *)
    pose proof (POK (w - 1)%Z ltac:(lia)) as Bb.
    pose proof (u8arr_read a0segs _ (a_fb A + 32) pb (w - 1)%Z (Z_to_bv 8 (zget pos (w - 1))) _ POS (PAG (w - 1)%Z ltac:(lia)) ltac:(lia) eq_refl) as RD.
    astep. clear RD. rewrite zxb_lit8 by lia.
    pos_brj w ANF.
    (* [comment removed for export] *)
    u8st POS (a_fb A + 32)%Z w.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small (zget pos (w - 1)) 256) in POS by lia.
    assert (PAG' : pos_agA (upd pb (Z.to_nat w) (Z_to_bv 8 (zget pos (w - 1)))) (zset pos w (zget pos (w - 1))) ng)
      by (apply (pos_agA_set pb pos ng); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]).
    assert (POK' : pos_okz (zset pos w (zget pos (w - 1))) ng) by (apply pos_okz_set; [exact POK| lia]).
    rewrite K_LP3_step by lia.
    (* [comment removed for export] *)
    arun. rewrite (land255_small (w + -1)) by lia.
    if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP3cutA in NX. revive_all_fb MUL WML AOK.
      rewrite if_trueP by blia.
      enter_cutP NX DP.
    - astep. unfold X78cutA in X78. revive_all_fb MUL WML AOK.
      rewrite if_falseP by blia.
      enter_cutP X78 DP.
  Qed.

  Lemma A0F_U5_LP2 : forall i pos, (0 <= i < nsc)%Z ->
    (forall tmp w, (0 <= tmp < ng)%Z -> (1 <= w < ng)%Z -> LP3cutA i pos tmp w) ->
    (forall tmp, (0 <= tmp < ng)%Z -> X78cutA i pos tmp) -> LP2cutA i pos.
  Proof.
    intros i pos Hi LP3 X78. unfold LP2cutA. intros until pb. intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK PAG POK Hi' SEL.
    prepA DP MU. open_dmemF DM. a0img. unfold FSH in FS.
    unfold r_of in DR. dr_open. hide_all_but_atF [a_fb A + 32; a_shf A; S + 25886; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    pose proof PAG as PAG0. destruct PAG as [LPB PAG].
    pose proof (SOK i ltac:(lia)) as Bv. set (v := zget (d_selMtf d) i) in Bv.
    (* [comment removed for export] *)
    arun_to 0xa4cb0%Z.
    lazymatch goal with H : u8arr _ ?mm (S + 25886)%Z (zb8 ?a ?n) |- _ =>
      pose proof (zb8_read1 a0segs mm (S + 25886) a n i _ H ltac:(lia) eq_refl) as RD end.
    astep. clear RD. fold v. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    arun.
    pos_lb v ANF. pos_brj v ANF.
    pose proof (POK v ltac:(lia)) as Bt.
    pose proof (u8arr_read a0segs _ (a_fb A + 32) pb v (Z_to_bv 8 (zget pos v)) _ POS (PAG v ltac:(lia)) ltac:(lia) eq_refl) as RD.
    astep. clear RD. rewrite zxb_lit8 by lia.
    rewrite (K_LP2_step F L d s nsc i pos) by lia. fold v.
    (* [comment removed for export] *)
    arun; if_cases Kv0; zify_cond Kv0.
    - (* [comment removed for export] *)
      rewrite if_falseP by blia.
      pose proof (X78 (zget pos v) Bt) as NX. unfold X78cutA in NX. revive_all_fb MUL WML AOK.
      enter_cutP NX DP.
    - (* [comment removed for export] *)
      rewrite if_trueP by blia.
      arun_to 0xa4cd8%Z.
      pose proof (LP3 (zget pos v) v Bt ltac:(lia)) as NX. unfold LP3cutA in NX. revive_all_fb MUL WML AOK.
      enter_cutP NX DP.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U5_all : LP1cutA 0 znew.
  Proof.
    assert (STEP : forall i, (0 <= i < nsc)%Z -> ((i + 1 < nsc)%Z -> forall pos, LP2cutA (i + 1) pos) -> forall pos, LP2cutA i pos).
    { intros i Hi NX pos.
      assert (X78s : forall pos' tmp, (0 <= tmp < ng)%Z -> X78cutA i pos' tmp)
        by (intros pos' tmp Bt; apply A0F_U5_X78; [lia | intros Hlt; apply NX; exact Hlt]).
      apply A0F_U5_LP2; [lia | | intros tmp Bt; apply X78s; exact Bt].
      intros tmp w Bt Hw.
      assert (G : forall k : nat, (1 <= Z.of_nat k < ng)%Z -> forall pos', LP3cutA i pos' tmp (Z.of_nat k)).
      { induction k as [|k IH]; intros Hk pos'; [exfalso; lia|].
        apply A0F_U5_LP3; [lia | lia | | apply X78s; exact Bt].
        intros Hk1. replace (Z.of_nat (Datatypes.S k) - 1)%Z with (Z.of_nat k) by lia. apply IH. lia. }
      replace w with (Z.of_nat (Z.to_nat w)) by lia. apply G. lia. }
    assert (ALL : forall k : nat, (Z.of_nat k < nsc)%Z -> forall pos, LP2cutA (nsc - 1 - Z.of_nat k)%Z pos).
    { induction k as [|k IH]; intros Hk.
      - apply STEP; [lia | intros; exfalso; lia].
      - apply STEP; [lia | intros _].
        replace (nsc - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (nsc - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    assert (L2 : forall pos, LP2cutA 0 pos).
    { pose proof (ALL (Z.to_nat (nsc - 1)) ltac:(lia)) as X.
      replace (nsc - 1 - Z.of_nat (Z.to_nat (nsc - 1)))%Z with 0%Z in X by lia. exact X. }
    assert (X8 : forall pos, X8cutA pos) by (intros pos; apply A0F_U5_X8; apply L2).
    assert (L1 : forall k : nat, (Z.of_nat k < ng)%Z -> forall pos, LP1cutA (ng - 1 - Z.of_nat k)%Z pos).
    { induction k as [|k IH]; intros Hk pos.
      - apply A0F_U5_LP1; [lia | intros; exfalso; lia | apply X8].
      - apply A0F_U5_LP1; [lia | intros _ | apply X8].
        replace (ng - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (ng - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (L1 (Z.to_nat (ng - 1)) ltac:(lia) znew) as X.
    replace (ng - 1 - Z.of_nat (Z.to_nat (ng - 1)))%Z with 0%Z in X by lia. exact X.
  Qed.
End R.

(* [comment removed for export] *)
Lemma A0F_dec_U5C : forall A, act_ok AIHI0 A -> act_sh DI_A0 A -> forall Q F, A0F_cut_HCOD A Q F -> A0F_cut_HUND A Q F.
Proof.
  intros A AOK ASH Q F HC. unfold A0F_cut_HUND. intros L d s J. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
  pose proof DI as DI'. destruct DI' as [[_ NBL] [NG [NS _]]].
  eapply (A0F_U5_entry A AOK ASH Q F L s J); first [ exact DM | exact FRL | exact FRH | eassumption | eapply (A0F_U5_all A AOK ASH Q F HC); eassumption ].
Qed.
End ACeilS1.
