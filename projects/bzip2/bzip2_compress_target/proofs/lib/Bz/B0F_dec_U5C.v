(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCuts5 B0F_decPos.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decPos.
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
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.
  Hypothesis HCOD : B0F_cut_HCOD A Q F.
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
    (dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) mm (dvF cx J dd s) ->
     aframe_pos A mm ->
     u8arr b0segs mm (a_fb A + 32) pb ->
     rw_cells b0segs mm (a_shf A) (FSH (Z_to_bv 8 6)) ->
     stk b0segs mm (a_lo A) (a_P A) ->
     munch (W14 A) (a_m0 A) mm -> wmono b0segs (a_m0 A) mm -> mem_inv b0segs mm ->
     dpureF cx (a_b0 A) (a_payload A) J dd s ->
     fuel_ok F dd s ->
     alpha_ok L dd -> belown (d_selMtf dd) nsc ng -> K) (only parsing).

  (* [comment removed for export] *)
  Definition LP1cutB (v : Z) (pos : zarr) : Prop :=
    forall (x1 x5 x6 x7 x10 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
           (w344 w352 w360 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word) (pb : list byte),
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 nsc) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 ng) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    COMMONA m d pb (
    (0 <= v <= ng)%Z ->
    pos_agA pb pos v ->
    (forall k, 0 <= k < v -> zget pos k = k)%Z ->
    evt b0segs (Q (K_LP1 F L d s nsc v pos))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 ns) (Z_to_bv 64 6) (Z_to_bv 64 v) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0d58) (a_fc A) None m (seg_rom b0segs))).

  (* [comment removed for export] *)
  Definition X8cutB (pos : zarr) : Prop :=
    forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
           (w344 w352 w360 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word) (pb : list byte),
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 nsc) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 ng) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    COMMONA m d pb (
    pos_agA pb pos ng ->
    pos_okz pos ng ->
    belown (d_sel d) 0 ng ->
    evt b0segs (Q (K_LP2 F L d s nsc 0 pos))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 ns) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0d94) (a_fc A) None m (seg_rom b0segs))).

  (* [comment removed for export] *)
  Definition LP2cutB (i : Z) (pos : zarr) : Prop :=
    forall (x1 x5 x6 x7 x10 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
           (w344 w352 w360 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word) (pb : list byte),
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 nsc) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 ng) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    COMMONA m d pb (
    pos_agA pb pos ng ->
    pos_okz pos ng ->
    (0 <= i <= nsc)%Z ->
    belown (d_sel d) i ng ->
    evt b0segs (Q (K_LP2 F L d s nsc i pos))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 i) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (18446744073709551615 - (S + 25886))) (Z_to_bv 64 (18446744073709551615 - (S + 7884))) (Z_to_bv 64 5) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0dc8) (a_fc A) None m (seg_rom b0segs))).

  (* [comment removed for export] *)
  Definition LP3cutB (i : Z) (pos : zarr) (tmp w : Z) : Prop :=
    forall (x1 x7 x10 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
           (w344 w352 w360 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word) (pb : list byte),
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 nsc) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 ng) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    COMMONA m d pb (
    pos_agA pb pos ng ->
    pos_okz pos ng ->
    (0 <= i < nsc)%Z ->
    belown (d_sel d) i ng ->
    (0 <= tmp < ng)%Z ->
    (1 <= w < ng)%Z ->
    evt b0segs (Q (K_LP3 F L d s nsc i pos tmp w))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 tmp) (Z_to_bv 64 w) x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 i) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (18446744073709551615 - (S + 25886))) (Z_to_bv 64 (18446744073709551615 - (S + 7884))) (Z_to_bv 64 5) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0dfc) (a_fc A) None m (seg_rom b0segs))).

  (* [comment removed for export] *)
  Definition X78cutB (i : Z) (pos : zarr) (tmp : Z) : Prop :=
    forall (x1 x6 x7 x10 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
           (w344 w352 w360 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word) (pb : list byte),
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 (Z_to_bv 64 nsc) w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 ng) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    COMMONA m d pb (
    pos_agA pb pos ng ->
    pos_okz pos ng ->
    (0 <= i < nsc)%Z ->
    belown (d_sel d) i ng ->
    (0 <= tmp < ng)%Z ->
    evt b0segs (Q (K_X78 F L d s nsc i pos tmp))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 tmp) x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 i) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (18446744073709551615 - (S + 25886))) (Z_to_bv 64 (18446744073709551615 - (S + 7884))) (Z_to_bv 64 5) x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0e4c) (a_fc A) None m (seg_rom b0segs))).

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
  (* [comment removed for export] *)
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
  Lemma B0F_U5_entry : LP1cutB 0 znew ->
    forall (d : dst) (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w88 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w440 w448 w456 w472 w480 w496 w504 w528 w720 w728 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) w88 (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 (Z_to_bv 64 (sv_alphaSize L)) w440 w448 w456 (Z_to_bv 64 (sv_nGroups L)) w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch (W14 A) (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    dinv_HUND L d ->
    fuel_ok F d s ->
    evt b0segs (Q (K_HUND F L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 (Z_to_bv 64 (sv_nSelectors L)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb0d2c) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros NXT. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prepA DP MU.
    destruct DI as [AL [_ [_ SOK]]].
    destruct (aframe_pos_open _ _ AF) as (pb & LPB & AFP & POS & FS). unfold FSH in FS. clear AF.
    open_dmemF DM. b0img.
    hide_all_but_atF [a_fb A + 32; a_shf A; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_shf A, a_shf A + 8); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    rewrite K_HUND_LP1, nsel_clamp_eq.
    (* [comment removed for export] *)
    Ltac entry_fin NXT DP LPB MUL WML AOK :=
      brun;
      let KZ := fresh "KZ" in if_cases KZ; zify_cond_z KZ; [exfalso; lia|];
      brun_to 0xb0d58%Z;
      revive_all_fb MUL WML AOK;
      unfold LP1cutB in NXT; enter_cutP NXT DP;
      try (apply pos_agA_nil; exact LPB); try (intros k Hk; exfalso; lia).
    brun. if_cases K; zify_cond_z K.
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

  Lemma B0F_U5_LP1 : forall v pos, (0 <= v < ng)%Z ->
    ((v + 1 < ng)%Z -> LP1cutB (v + 1) (zset pos v v)) -> X8cutB (zset pos v v) -> LP1cutB v pos.
  Proof.
    intros v pos Hv NXT X8. unfold LP1cutB. intros until pb. intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK Hv' PAG PK.
    prepA DP MU. open_dmemF DM. b0img. unfold FSH in FS.
    hide_all_but_atF [a_fb A + 32; a_shf A; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_fb A + 32, a_fb A + 38)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    brun.
    pos_lb v ANF. pos_br v ANF.
    u8st POS (a_fb A + 32)%Z v.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small v 256) in POS by lia.
    assert (PAG' : pos_agA (upd pb (Z.to_nat v) (Z_to_bv 8 v)) (zset pos v v) (v + 1))
      by (apply (pos_agA_set pb pos v); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]).
    assert (PK' : forall k, (0 <= k < v + 1 -> zget (zset pos v v) k = k)%Z)
      by (intros k Hk; rewrite zget_zset; destruct (Z.eqb_spec k v); [lia| apply PK; lia]).
    rewrite K_LP1_step by lia.
    (* [comment removed for export] *)
    brun.
    if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP1cutB in NX. revive_all_fb MUL WML AOK.
      enter_cutP NX DP.
    - (* [comment removed for export] *)
      astep. unfold X8cutB in X8. revive_all_fb MUL WML AOK.
      rewrite K_LP1_exit by lia.
      enter_cutP X8 DP.
      + replace ng with (v + 1)%Z by lia. exact PAG'.
      + apply pos_okz_init. replace ng with (v + 1)%Z by lia. exact PK'.
      + apply belown_0.
  Qed.

  Lemma B0F_U5_X8 : forall pos, LP2cutB 0 pos -> X8cutB pos.
  Proof.
    intros pos NXT. unfold X8cutB. intros until pb. intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK PAG POK SEL.
    prepA DP MU.
    (* [comment removed for export] *)
    brun. if_cases K; zify_cond_z K; [exfalso; lia|].
    brun_to 0xb0dc8%Z.
    unfold LP2cutB in NXT. enter_cutP NXT DP.
  Qed.

  Lemma B0F_U5_X78 : forall i pos tmp, (0 <= i < nsc)%Z ->
    ((i + 1 < nsc)%Z -> LP2cutB (i + 1) (zset pos 0 tmp)) -> X78cutB i pos tmp.
  Proof using ACEIL__ A AOK ASH Q F HCOD L s J NG NS NBL.
    intros i pos tmp Hi NXT. unfold X78cutB. intros until pb. intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK PAG POK Hi' SEL TMP.
    prepA DP MU. open_dmemF DM. b0img. unfold FSH in FS.
    unfold r_of in DR. dr_open. hide_all_but_atF [a_fb A + 32; a_shf A; S + 7884; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_fb A + 32, a_fb A + 38); (S + 7884, S + 25886); (a_shf A, a_shf A + 8); (a_P A + 344, a_P A + 760)]%Z m) as MUL.
    pose proof (wmono_refl b0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    astep.
    u8st POS (a_fb A + 32)%Z 0%Z.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small tmp 256) in POS by lia.
    assert (PAG' : pos_agA (upd pb (Z.to_nat 0) (Z_to_bv 8 tmp)) (zset pos 0 tmp) ng)
      by (apply (pos_agA_set pb pos ng); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]).
    assert (POK' : pos_okz (zset pos 0 tmp) ng) by (apply pos_okz_set; [exact POK| lia]).
    (* [comment removed for export] *)
    brun_to 0xb0e74%Z.
    lazymatch goal with H : u8arr _ _ (S + 7884)%Z _ |- _ =>
      zb8_sb H i; try rewrite (Z.mod_small tmp 256) in H by lia end.
    unfold K_X78.
    (* [comment removed for export] *)
    brun; if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP2cutB in NX. revive_all_fb MUL WML AOK.
      enter_cutP NX DP.
      dmodel_cbn. apply belown_set; [exact SEL| lia].
    - (* [comment removed for export] *)
      brun_to 0xb0f3c%Z.
      revive_all_fb MUL WML AOK.
      rewrite K_LP2_exit_HCOD by lia.
      unfold B0F_cut_HCOD in HCOD. enter_cutF (HCOD _ _ _ JK_) DP.
      + eapply aframe_pos_close; [ aframe_pos_revive | exact POS | rewrite upd_length; exact LPB | exact FS ].
      + pose proof AL as AL'. unfold alpha_ok in AL'.
        unfold dinv_HCOD, L_cod, alpha_ok. dmodel_cbn.
        repeat match goal with |- _ /\ _ => split end; try lia.
        replace (Z.min ns 18002) with (i + 1)%Z by lia. apply belown_set; [exact SEL| lia].
  Qed.

  Lemma B0F_U5_LP3 : forall i pos tmp w, (0 <= i < nsc)%Z -> (1 <= w < ng)%Z ->
    ((1 <= w - 1)%Z -> LP3cutB i (zset pos w (zget pos (w - 1))) tmp (w - 1)) ->
    X78cutB i (zset pos w (zget pos (w - 1))) tmp -> LP3cutB i pos tmp w.
  Proof.
    intros i pos tmp w Hi Hw NXT X78. unfold LP3cutB. intros until pb.
    intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK PAG POK Hi' SEL TMP Hw'.
    prepA DP MU. open_dmemF DM. b0img. unfold FSH in FS.
    hide_all_but_atF [a_fb A + 32; a_shf A; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_fb A + 32, a_fb A + 38)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    astep. rewrite (land255_small w) by lia. astep. astep. rewrite (land_w32 w) by lia. brun.
    pos_lb w ANF.
    (* [comment removed for export] *)
    pose proof (POK (w - 1)%Z ltac:(lia)) as Bb.
    pose proof (u8arr_read b0segs _ (a_fb A + 32) pb (w - 1)%Z (Z_to_bv 8 (zget pos (w - 1))) _ POS (PAG (w - 1)%Z ltac:(lia)) ltac:(lia) eq_refl) as RD.
    astep. clear RD. rewrite zxb_lit8 by lia.
    pos_br w ANF.
    (* [comment removed for export] *)
    astep. astep. rewrite (land255_small (w + -1)) by lia.
    u8st POS (a_fb A + 32)%Z w.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small (zget pos (w - 1)) 256) in POS by lia.
    assert (PAG' : pos_agA (upd pb (Z.to_nat w) (Z_to_bv 8 (zget pos (w - 1)))) (zset pos w (zget pos (w - 1))) ng)
      by (apply (pos_agA_set pb pos ng); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]).
    assert (POK' : pos_okz (zset pos w (zget pos (w - 1))) ng) by (apply pos_okz_set; [exact POK| lia]).
    rewrite K_LP3_step by lia.
    (* [comment removed for export] *)
    astep. if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP3cutB in NX. revive_all_fb MUL WML AOK.
      rewrite if_trueP by blia.
      enter_cutP NX DP.
    - astep. unfold X78cutB in X78. revive_all_fb MUL WML AOK.
      rewrite if_falseP by blia.
      enter_cutP X78 DP.
  Qed.

  Lemma B0F_U5_LP2 : forall i pos, (0 <= i < nsc)%Z ->
    (forall tmp w, (0 <= tmp < ng)%Z -> (1 <= w < ng)%Z -> LP3cutB i pos tmp w) ->
    (forall tmp, (0 <= tmp < ng)%Z -> X78cutB i pos tmp) -> LP2cutB i pos.
  Proof.
    intros i pos Hi LP3 X78. unfold LP2cutB. intros until pb. intros FRL FRH DM AFP POS FS ST MU WM MI DP FU AL SOK PAG POK Hi' SEL.
    prepA DP MU. open_dmemF DM. b0img. unfold FSH in FS.
    unfold r_of in DR. dr_open. hide_all_but_atF [a_fb A + 32; a_shf A; S + 25886; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    pose proof PAG as PAG0. destruct PAG as [LPB PAG].
    pose proof (SOK i ltac:(lia)) as Bv. set (v := zget (d_selMtf d) i) in Bv.
    (* [comment removed for export] *)
    brun_to 0xb0de4%Z.
    lazymatch goal with H : u8arr _ ?mm (S + 25886)%Z (zb8 ?a ?n) |- _ =>
      pose proof (zb8_read1 b0segs mm (S + 25886) a n i _ H ltac:(lia) eq_refl) as RD end.
    astep. clear RD. fold v. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    brun_to 0xb0df4%Z.
    pose proof (POK v ltac:(lia)) as Bt.
    pose proof (u8arr_read b0segs _ (a_fb A + 32) pb v (Z_to_bv 8 (zget pos v)) _ POS (PAG v ltac:(lia)) ltac:(lia) eq_refl) as RD.
    astep. clear RD. rewrite zxb_lit8 by lia.
    rewrite (K_LP2_step F L d s nsc i pos) by lia. fold v.
    (* [comment removed for export] *)
    astep. if_cases Kv0; zify_cond Kv0.
    - (* [comment removed for export] *)
      rewrite if_falseP by blia.
      pose proof (X78 (zget pos v) Bt) as NX. unfold X78cutB in NX. revive_all_fb MUL WML AOK.
      enter_cutP NX DP.
    - (* [comment removed for export] *)
      rewrite if_trueP by blia.
      pose proof (LP3 (zget pos v) v Bt ltac:(lia)) as NX. unfold LP3cutB in NX. revive_all_fb MUL WML AOK.
      enter_cutP NX DP.
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U5_all : LP1cutB 0 znew.
  Proof.
    assert (STEP : forall i, (0 <= i < nsc)%Z -> ((i + 1 < nsc)%Z -> forall pos, LP2cutB (i + 1) pos) -> forall pos, LP2cutB i pos).
    { intros i Hi NX pos.
      assert (X78s : forall pos' tmp, (0 <= tmp < ng)%Z -> X78cutB i pos' tmp)
        by (intros pos' tmp Bt; apply B0F_U5_X78; [lia | intros Hlt; apply NX; exact Hlt]).
      apply B0F_U5_LP2; [lia | | intros tmp Bt; apply X78s; exact Bt].
      intros tmp w Bt Hw.
      assert (G : forall k : nat, (1 <= Z.of_nat k < ng)%Z -> forall pos', LP3cutB i pos' tmp (Z.of_nat k)).
      { induction k as [|k IH]; intros Hk pos'; [exfalso; lia|].
        apply B0F_U5_LP3; [lia | lia | | apply X78s; exact Bt].
        intros Hk1. replace (Z.of_nat (Datatypes.S k) - 1)%Z with (Z.of_nat k) by lia. apply IH. lia. }
      replace w with (Z.of_nat (Z.to_nat w)) by lia. apply G. lia. }
    assert (ALL : forall k : nat, (Z.of_nat k < nsc)%Z -> forall pos, LP2cutB (nsc - 1 - Z.of_nat k)%Z pos).
    { induction k as [|k IH]; intros Hk.
      - apply STEP; [lia | intros; exfalso; lia].
      - apply STEP; [lia | intros _].
        replace (nsc - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (nsc - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    assert (L2 : forall pos, LP2cutB 0 pos).
    { pose proof (ALL (Z.to_nat (nsc - 1)) ltac:(lia)) as X.
      replace (nsc - 1 - Z.of_nat (Z.to_nat (nsc - 1)))%Z with 0%Z in X by lia. exact X. }
    assert (X8 : forall pos, X8cutB pos) by (intros pos; apply B0F_U5_X8; apply L2).
    assert (L1 : forall k : nat, (Z.of_nat k < ng)%Z -> forall pos, LP1cutB (ng - 1 - Z.of_nat k)%Z pos).
    { induction k as [|k IH]; intros Hk pos.
      - apply B0F_U5_LP1; [lia | intros; exfalso; lia | apply X8].
      - apply B0F_U5_LP1; [lia | intros _ | apply X8].
        replace (ng - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (ng - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (L1 (Z.to_nat (ng - 1)) ltac:(lia) znew) as X.
    replace (ng - 1 - Z.of_nat (Z.to_nat (ng - 1)))%Z with 0%Z in X by lia. exact X.
  Qed.
End R.

(* [comment removed for export] *)
Lemma B0F_dec_U5C : forall A, act_ok BIHI0 A -> act_sh DI_B0 A -> forall Q F, B0F_cut_HCOD A Q F -> B0F_cut_HUND A Q F.
Proof.
  intros A AOK ASH Q F HC. unfold B0F_cut_HUND. intros L d s J. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
  pose proof DI as DI'. destruct DI' as [[_ NBL] [NG [NS _]]].
  eapply (B0F_U5_entry A AOK ASH Q F L s J); first [ exact DM | exact FRL | exact FRH | eassumption | eapply (B0F_U5_all A AOK ASH Q F HC); eassumption ].
Qed.
End ACeilS1.

