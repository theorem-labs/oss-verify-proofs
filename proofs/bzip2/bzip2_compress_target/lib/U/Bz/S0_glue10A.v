(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv DecCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0_glue10K.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Musl Require Import S0_memset.
From Stdlib Require Lia. 
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit.
Module S0_glue10C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glue10K.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
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
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Notation FR10 mm usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
              e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era :=
  (rw_cells s0segs mm (usp + -336)
     [CB 8 j0; C8 f8; C8 f16; C8 f24; C8 f32; C8 f40; C8 f48; C8 f56; C8 f64; C8 f72; C8 f80; C8 f88; C8 f96;
      C8 f104; C8 f112; C8 f120; C8 f128; C8 f136; C8 f144; C8 f152; C8 f160; C8 f168; C8 f176; C8 f184; C8 f192; C8 f200;
      C8 f208; C8 f216;
      CB 8 pb; C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 era]) (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil}.


Section C.
  Variables (usp S strm lo : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis GEO : (0 < S /\ S + 64144 <= lo /\ alloc_ceiling <= lo /\ lo <= usp - 1024 /\ usp + 112 <= strm /\ strm + 80 < 2 ^ 64)%Z.

  (* [comment removed for export] *)
  Definition MSm (ra : Z) (m : word -> option byte) (n : Z)
      (x5 x6 x7 x8 x9 y11 y12 y13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 n) y11 y12 y13 x14 x15 x16 x17
            (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x29504) fc None m (seg_rom s0segs).

  (* [comment removed for export] *)
  Lemma g10_C1 : forall (x1 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (uc small : Z) (m : word -> option byte) (h : dsh) (b : bzs)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte)
      (e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era : word) (Q : machine_state -> Prop),
    FR10 m usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
         e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
    rw_cells s0segs m S (HEAD_CELLS h) -> bv_unsigned (sh_small h) = small -> (small = 0 \/ small = 1)%Z ->
    (0 <= sh_n h < 2 ^ 32)%Z -> length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    (0 <= sh_strm h < 2 ^ 64)%Z ->
    rw_cells s0segs m strm (STRM_CELLS b) -> bs_bzalloc b = Z_to_bv 64 0x13e24 ->
    (0 <= bs_ai b <= bs_len b /\ 0 <= bs_av b <= bs_dlen b /\ 0 < bs_src b /\ bs_src b + bs_len b < 2 ^ 64 /\
     0 <= bs_dst b /\ bs_dst b + bs_dlen b < 2 ^ 64 /\ 0 <= bs_S b < 2 ^ 64)%Z ->
    (49 <= uc <= 57)%Z ->
    mem_inv s0segs m ->
    (forall (m' : word -> option byte) (y11 y12 y13 : word),
        let h' := DSH (sh_strm h) (sh_state h) (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h)
                      (sh_bsBuff h) (sh_bsLive h) (uc - 48) (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
        small = 0%Z ->
        FR10 m' usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 x24 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
             e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
        rw_cells s0segs m' S (HEAD_CELLS h') -> rw_cells s0segs m' strm (STRM_CELLS b) ->
        munch [(usp + -336, usp); (S, S + 68)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MSm 0x24c10 m' ((uc - 48) * 400000) x5 x6 x7 x30 x9 y11 y12 y13 x14 x15 x16 x17 x31 x1 x22 x8 x23 x19 x26 x27 x28 x29 x30 x31)) ->
    (forall (m' : word -> option byte) (y11 y12 y13 : word),
        let h' := DSH (sh_strm h) (sh_state h) (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h)
                      (sh_bsBuff h) (sh_bsLive h) (uc - 48) (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
        small = 1%Z ->
        FR10 m' usp j0 f8 f16 f24 f32 f40 f48 f56 f64 x19 x1 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
             e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
        rw_cells s0segs m' S (HEAD_CELLS h') -> rw_cells s0segs m' strm (STRM_CELLS b) ->
        munch [(usp + -336, usp); (S, S + 68)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MSm 0x24b64 m' ((uc - 48) * 200000) x5 x6 x7 x8 x9 y11 y12 y13 x14 x15 x16 x17 x31 x30 x22 x23 x24 (Z_to_bv 64 strm) x26 x27 x28 x29 x30 x31)) ->
    evt s0segs Q (MSd usp S strm gp tp F fc 0x24b14 m x1 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 (Z_to_bv 64 uc) x13 x14 x15 x16 x17 x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until Q. intros FR HD Hsm SM01 HN L1 L2 L3 HSTRM STRM BZA BWF UC MI HKF HKS.
    cps_pose GEO as (G1 & G2 & G3 & G4 & G5 & G6).
    unfold MSd, MSm in *. rewrite BZA in STRM.
    pose proof (bv_unsigned_in_range 8 (sh_small h)) as Rsm; unfold bv_modulus in Rsm; cbn in Rsm.
    pose proof (munch_refl [(usp + -336, usp); (S, S + 68)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    do 3 wstepl.
    (* [comment removed for export] *)
    do 3 wstepl.
    (* [comment removed for export] *)
    wstepl; if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      wstepl. replace (0 <? strm)%Z with true by (symmetry; apply Z.ltb_lt; lia). UKit.u_lit_branch.
      UKit.urun_to 0x29504%Z.
      enter_with HKF; [ st_eq | lia | by_rw (usp + -336)%Z | by_head S Hsm | rewrite BZA; by_rw strm | exact MU | exact WM | by_mi ].
    - (* [comment removed for export] *)
      wstepl. replace (0 <? strm)%Z with true by (symmetry; apply Z.ltb_lt; lia). UKit.u_lit_branch.
      UKit.urun_to 0x29504%Z.
      enter_with HKS; [ st_eq | lia | by_rw (usp + -336)%Z | by_head S Hsm | rewrite BZA; by_rw strm | exact MU | exact WM | by_mi ].
  Qed.

  (* [comment removed for export] *)
  Lemma g10_C2f : forall (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (r : Z) (m : word -> option byte) (d : dsm)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte)
      (e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era : word) (Q : machine_state -> Prop),
    FR10 m usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
         e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
    rw_cells s0segs m (S + 3152) (MID_CELLS d) -> (0 <= sm_ll16 d < 2 ^ 64)%Z -> (0 <= sm_ll4 d < 2 ^ 64)%Z -> (0 <= sm_nInUse d < 2 ^ 32)%Z ->
    (0 <= r < 2 ^ 64)%Z ->
    mem_inv s0segs m ->
    (forall (m' : word -> option byte),
        r = 0%Z ->
        rw_cells s0segs m' (S + 3152) (MID_CELLS (DSM r (sm_ll16 d) (sm_ll4 d) (sm_sbcrc d) (sm_sccrc d) (sm_cbcrc d) (sm_cccrc d) (sm_nInUse d))) ->
        munch [(S + 3152, S + 3196)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MS (mkR x21 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x23 x9 (Z_to_bv 64 (-3))
                            (Z_to_bv 64 (S + 2047)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S) x25 (Z_to_bv 64 (S + 64036)) x21 x22 x24 f80 x25 x26 x27 x28 x29 x8 x19)
                         F (Z_to_bv 64 0x2613c) fc None m' (seg_rom s0segs))) ->
    (forall (m' : word -> option byte),
        r <> 0%Z ->
        rw_cells s0segs m' (S + 3152) (MID_CELLS (DSM r (sm_ll16 d) (sm_ll4 d) (sm_sbcrc d) (sm_sccrc d) (sm_cbcrc d) (sm_cccrc d) (sm_nInUse d))) ->
        munch [(S + 3152, S + 3196)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MS (mkR x21 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x23 x9 (Z_to_bv 64 r)
                            (Z_to_bv 64 (S + 2047)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S) x25 (Z_to_bv 64 (S + 64036)) x21 x22 x24 f80 x25 x26 x27 x28 x29 x8 x19)
                         F (Z_to_bv 64 0x24c3c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 0x24c10) (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r)
                        x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x24c10) fc None m (seg_rom s0segs)).
  Proof.
    intros until Q. intros FR MID L16 L4 NIU R MI HX3 HH.
    cps_pose GEO as (G1 & G2 & G3 & G4 & G5 & G6).
    pose proof (munch_refl [(S + 3152, S + 3196)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    do 9 wstepl.
    (* [comment removed for export] *)
    wstepl; if_cases K; zify_cond K.
    - enter_with HH; [ st_eq | mlia | cbn [sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse]; by_rw (S + 3152)%Z | exact MU | exact WM | by_mi ].
    - (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      enter_with HX3; [ st_eq | mlia | cbn [sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse]; by_rw (S + 3152)%Z | exact MU | exact WM | by_mi ].
  Qed.
End C.

End ACeilS1.
End S0_glue10C.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0_glue10D.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glue10K.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
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
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Notation FR10 mm usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
              e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era :=
  (rw_cells s0segs mm (usp + -336)
     [CB 8 j0; C8 f8; C8 f16; C8 f24; C8 f32; C8 f40; C8 f48; C8 f56; C8 f64; C8 f72; C8 f80; C8 f88; C8 f96;
      C8 f104; C8 f112; C8 f120; C8 f128; C8 f136; C8 f144; C8 f152; C8 f160; C8 f168; C8 f176; C8 f184; C8 f192; C8 f200;
      C8 f208; C8 f216;
      CB 8 pb; C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 era]) (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil}.


Section D.
  Variables (usp S strm lo : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis GEO : (0 < S /\ S + 64144 <= lo /\ alloc_ceiling <= lo /\ lo <= usp - 1024 /\ usp + 112 <= strm /\ strm + 80 < 2 ^ 64)%Z.

  (* [comment removed for export] *)
  Lemma g10_C2s : forall (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (r1 n : Z) (m : word -> option byte) (h : dsh) (b : bzs) (d : dsm)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte)
      (e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era : word) (Q : machine_state -> Prop),
    FR10 m usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
         e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
    rw_cells s0segs m S (HEAD_CELLS h) -> sh_n h = n -> (1 <= n <= 9)%Z ->
    length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat -> (0 <= sh_strm h < 2 ^ 64)%Z ->
    rw_cells s0segs m strm (STRM_CELLS b) -> bs_bzalloc b = Z_to_bv 64 0x13e24 ->
    (0 <= bs_ai b <= bs_len b /\ 0 <= bs_av b <= bs_dlen b /\ 0 < bs_src b /\ bs_src b + bs_len b < 2 ^ 64 /\
     0 <= bs_dst b /\ bs_dst b + bs_dlen b < 2 ^ 64 /\ 0 <= bs_S b < 2 ^ 64)%Z ->
    rw_cells s0segs m (S + 3152) (MID_CELLS d) -> (0 <= sm_tt d < 2 ^ 64)%Z -> (0 <= sm_ll4 d < 2 ^ 64)%Z -> (0 <= sm_nInUse d < 2 ^ 32)%Z ->
    (0 <= r1 < 2 ^ 64)%Z ->
    mem_inv s0segs m ->
    (forall (m' : word -> option byte) (y11 y12 y13 : word),
        rw_cells s0segs m' (S + 3152) (MID_CELLS (DSM (sm_tt d) r1 (sm_ll4 d) (sm_sbcrc d) (sm_sccrc d) (sm_cbcrc d) (sm_cccrc d) (sm_nInUse d))) ->
        munch [(S + 3152, S + 3196)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MS (mkR (Z_to_bv 64 0x24b9c) (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (n * 50000))
                            y11 y12 y13 x14 x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 (Z_to_bv 64 strm) x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x29504) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 0x24b64) (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r1)
                        x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 (Z_to_bv 64 strm) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x24b64) fc None m (seg_rom s0segs)).
  Proof.
    intros until Q. intros FR HD Hn N19 L1 L2 L3 HSTRM STRM BZA BWF MID Ltt L4 NIU R1 MI HK.
    cps_pose GEO as (G1 & G2 & G3 & G4 & G5 & G6). rewrite BZA in STRM. rewrite Hn in HD.
    pose proof (munch_refl [(S + 3152, S + 3196)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    UKit.urun_to 0x29504%Z.
    enter_with HK; [ st_eq; mlia | cbn [sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse]; by_rw (S + 3152)%Z | exact MU | exact WM | by_mi ].
  Qed.

  (* [comment removed for export] *)
  Lemma g10_C3s : forall (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (r1 r2 : Z) (m : word -> option byte) (d : dsm)
      (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte)
      (e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era : word) (Q : machine_state -> Prop),
    FR10 m usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
         e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
    rw_cells s0segs m (S + 3152) (MID_CELLS d) -> sm_ll16 d = r1 -> (0 <= r1 < 2 ^ 64)%Z -> (0 <= sm_tt d < 2 ^ 64)%Z -> (0 <= sm_nInUse d < 2 ^ 32)%Z ->
    (0 <= r2 < 2 ^ 64)%Z ->
    mem_inv s0segs m ->
    let d' := DSM (sm_tt d) r1 r2 (sm_sbcrc d) (sm_sccrc d) (sm_cbcrc d) (sm_cccrc d) (sm_nInUse d) in
    (forall (m' : word -> option byte),
        r1 = 0%Z ->
        rw_cells s0segs m' (S + 3152) (MID_CELLS d') ->
        munch [(S + 3152, S + 3196)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MS (mkR f80 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (-3))
                            f168 f104 x13 f136 x15 x16 x17 (Z_to_bv 64 S) f72 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 f112 x28 x29 x30 x19)
                         F (Z_to_bv 64 0x2614c) fc None m' (seg_rom s0segs))) ->
    (forall (m' : word -> option byte),
        r1 <> 0%Z -> r2 = 0%Z ->
        rw_cells s0segs m' (S + 3152) (MID_CELLS d') ->
        munch [(S + 3152, S + 3196)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MS (mkR f80 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (-3))
                            (Z_to_bv 64 r2) (Z_to_bv 64 r1) x13 x14 x15 x16 x17 (Z_to_bv 64 S) f72 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x21 x19)
                         F (Z_to_bv 64 0x2613c) fc None m' (seg_rom s0segs))) ->
    (forall (m' : word -> option byte),
        r1 <> 0%Z -> r2 <> 0%Z ->
        rw_cells s0segs m' (S + 3152) (MID_CELLS d') ->
        munch [(S + 3152, S + 3196)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        evt s0segs Q (MS (mkR f80 (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (-3))
                            (Z_to_bv 64 r2) (Z_to_bv 64 r1) x13 x14 x15 x16 x17 (Z_to_bv 64 S) f72 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x21 x19)
                         F (Z_to_bv 64 0x24c3c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 0x24b9c) (Z_to_bv 64 (usp + -336)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r2)
                        x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x24b9c) fc None m (seg_rom s0segs)).
  Proof.
    intros until Q. intros FR MID Hl16 R1 Ltt NIU R2 MI. cbv zeta. intros HXc HX0 HH.
    cps_pose GEO as (G1 & G2 & G3 & G4 & G5 & G6). rewrite Hl16 in MID.
    pose proof (munch_refl [(S + 3152, S + 3196)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    do 6 wstepl.
    (* [comment removed for export] *)
    wstepl; if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 3 wstepl.
      wstepl; if_cases K2; zify_cond K2.
      + enter_with HH; [ st_eq | mlia | mlia | cbn [sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse]; by_rw (S + 3152)%Z | exact MU | exact WM | by_mi ].
      + wstepl.
        enter_with HX0; [ st_eq | mlia | mlia | cbn [sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse]; by_rw (S + 3152)%Z | exact MU | exact WM | by_mi ].
    - (* [comment removed for export] *)
      do 8 wstepl.
      enter_with HXc; [ st_eq | mlia | cbn [sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse]; by_rw (S + 3152)%Z | exact MU | exact WM | by_mi ].
  Qed.
End D.

End ACeilS1.
End S0_glue10D.

Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Notation FR10 mm usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb
              e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era :=
  (rw_cells s0segs mm (usp + -336)
     [CB 8 j0; C8 f8; C8 f16; C8 f24; C8 f32; C8 f40; C8 f48; C8 f56; C8 f64; C8 f72; C8 f80; C8 f88; C8 f96;
      C8 f104; C8 f112; C8 f120; C8 f128; C8 f136; C8 f144; C8 f152; C8 f160; C8 f168; C8 f176; C8 f184; C8 f192; C8 f200;
      C8 f208; C8 f216;
      CB 8 pb; C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 era]) (only parsing).

Notation Z0 := (Z_to_bv 64 0) (only parsing).
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require JunkFast.
Local Ltac BzTac.bz32 ::= JunkFast.bz32_j.
Local Ltac BzTac2.bz32l ::= JunkFast.bz32l_j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


Lemma g10_A : forall (era e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo S : Z) (h : dsh) (js : list byte)
    (Q : machine_state -> Prop),
  rw_cells s0segs m S (HEAD_CELLS h) -> sh_state h = 10%Z -> (0 <= sh_strm h < 2 ^ 64)%Z -> sh_bsLive h = 0%Z ->
  length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
  rw_cells s0segs m (S + 64036) [CB 108 js] ->
  stk s0segs m lo usp -> (lo <= usp - 1024)%Z -> (0x66000 <= lo)%Z -> (usp < 2 ^ 64)%Z ->
  (0 < S)%Z -> (S + 64144 <= 2 ^ 64)%Z -> (S + 64144 <= 65536 \/ 0x66000 <= S)%Z ->
  (S + 64144 <= lo)%Z -> (S mod 8 = 0)%Z ->
  mem_inv s0segs m ->
  (forall (m' : word -> option byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 : word) (j0 : list byte)
          (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 : word) (pb : list byte),
      FR10 m' usp j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80
           (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 0) (Z_to_bv 64 0) pb
           e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 era ->
      rw_cells s0segs m' S (HEAD_CELLS h) ->
      rw_cells s0segs m' (S + 64036) [CB 108 (repeat (Z_to_bv 8 0) 108)] ->
      stk s0segs m' lo (usp + -336) ->
      munch [(usp + -336, usp); (S + 64036, S + 64144)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
      evt s0segs Q
        (MSd usp S (sh_strm h) gp tp F fc 0x247c4 m' (Z_to_bv 64 0) x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 0) (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 (S + 3176)) x28 x29 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 0))) ->
  evt s0segs Q
    (MS (mkR era (Z_to_bv 64 usp) gp tp t0 t1 t2 e0 e1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2462c) fc None m (seg_rom s0segs)).
Proof.
  intros until Q. intros HD ST10 STRM HBL L1 L2 L3 SAV ST LO LOLO USP S0 S1 IMG SLO SAL MI HK. unfold MSd in HK.
  pose proof (munch_refl [(usp + -336, usp); (S + 64036, S + 64144)]%Z m) as MU.
  pose proof (wmono_refl s0segs m) as WM.
  rewrite ST10, HBL in HD.
  carve_frame 336%nat ST.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ ?mm _ [CB _ ?jb] =>
    apply (rw_cells_split_CB s0segs mm (usp + -336)%Z [] 336%nat jb [] [232; 104]%nat) in FR; [| reflexivity];
    cbn [mk_CB_cells app] in FR;
    apply (rw_cells_CB_c8 s0segs mm (usp + -336)%Z [CB 232%nat (firstn 232 jb)] 13%nat) in FR;
    apply (rw_cells_split_CB s0segs mm (usp + -336)%Z [] 232%nat (firstn 232 jb) _ [8; 216; 8]%nat) in FR; [| reflexivity];
    cbn [mk_CB_cells app] in FR;
    apply (rw_cells_CB_c8 s0segs mm (usp + -336)%Z [CB 8%nat (firstn 8 (firstn 232 jb))] 27%nat) in FR;
    cbn [c8cells app] in FR
  end.
  repeat match type of FR with context [C8 (le_bytes_to_word ?x)] =>
    let w := fresh "fj" in let E := fresh "Efj" in remember (le_bytes_to_word x) as w eqn:E in FR; clear E end.
  do 14 wstepl.
  (* [comment removed for export] *)
  UKit.urun_to 0x2467c%Z. wstepl.
  try change (sx32 (Z_to_bv 64 10)) with (Z_to_bv 64 10).
  (* [comment removed for export] *)
  lazymatch type of HD with rw_cells _ ?m0 _ _ =>
    pose proof (munch_refl [(usp + -336, usp); (S + 64036, S + 64144)]%Z m0) as MUH; pose proof (wmono_refl s0segs m0) as WMH end.
  hide HD.
  (* [comment removed for export] *)
  wstepl. wstepl. wstepl. wstepl.
  wstepl. if_false_z.
  (* [comment removed for export] *)
  do 14 lstep.
  lazymatch goal with H : rw_cells s0segs ?m1 (S + 64036)%Z ?cs |- _ =>
    pose proof (rw_cells_merge s0segs m1 (S + 64036)%Z [] cs [] ltac:(rewrite app_nil_r; exact H)) as SAVM;
    clear H; cbn [app] in SAVM;
    replace (CB (cells_size cs) (cells_bytes cs)) with (CB 108 (repeat (Z_to_bv 8 0) 108)) in SAVM by (vm_compute; reflexivity) end.
  match goal with H : mem_inv s0segs _ |- _ => rename H into MI' end.
  (* [comment removed for export] *)
  match goal with H : rw_cells s0segs ?m1 (S + 64036)%Z _ |- _ =>
    rename H into SAVZ; pose proof SAVZ as SAV1; hide SAVZ;
    pose proof (munch_refl [(usp + -336, usp)]%Z m1) as MUL; pose proof (wmono_refl s0segs m1) as WML end.
  (* [comment removed for export] *)
  do 39 wstepl.
  (* [comment removed for export] *)
  wstepl. wstepl. wstepl. if_false_z.
  do 9 wstepl.
  (* [comment removed for export] *)
  wstepl.
  do 2 wstepl.
  (* [comment removed for export] *)
  wstepl.
  unfold hidden in HD, SAVZ. clear SAV1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUH with munch _ ?m0 _ =>
      eapply (rw_cells_transport s0segs _ m0 mm) in HD; [ | exact MUH | exact WMH | cbn [disjoint_from]; simpl_sizes; lia ] end;
    lazymatch type of MUL with munch _ ?m1 _ =>
      eapply (rw_cells_transport s0segs _ m1 mm) in SAVZ; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; lia ] end end.
  clear MUH WMH MUL WML.
  do 6 wstepl.
  wstepl. try change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  rewrite <- ST10, <- HBL in HD.
  enter_with HK; [ st_eq | | exact HD | | | | | ];
  [ match goal with H : rw_cells s0segs _ (usp + -336)%Z _ |- _ => exact H end
  | match goal with H : rw_cells s0segs _ (S + 64036)%Z _ |- _ => exact H end
  | match goal with H : stk s0segs _ _ _ |- _ => exact H end
  | match goal with H : munch _ m _ |- _ => exact H end
  | match goal with H : wmono s0segs m _ |- _ => exact H end
  | match goal with H : mem_inv s0segs _ |- _ => exact H end ].
Qed.

End ACeilS1.
