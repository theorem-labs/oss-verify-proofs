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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV DecTacSB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSB.
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

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0_glue10K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_g10A.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_g10M.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Definition W10c1 (A : act14) : list ivl := [(b_s (a_cx A), b_s (a_cx A) + 68)%Z; (a_P A, a_P A + 128)%Z].
Definition W10c (A : act14) : list ivl := [(b_s (a_cx A) + 3152, b_s (a_cx A) + 3176)%Z].
Definition B0F_MALLOC : Z := 0x537a4.   (* [comment removed for export] *)
Definition B0F_DBZA : Z := 0x81e4c.     (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sh_norm_in H :=
  repeat match type of H with
  | context [((?X + ?o) / 8 + 2147450880)%Z] =>
      is_Zlit o; lazymatch goal with AN : sanchor X ?SHX |- _ =>
        let q := eval vm_compute in (o / 8)%Z in rewrite (sanchor_addr_lit X SHX o q AN eq_refl) in H end
  | context [(?X / 8 + 2147450880)%Z] => lazymatch goal with AN : sanchor X ?SHX |- _ => rewrite (sanchor_addr0 X SHX AN) in H end
  end.
Ltac g_mid MID := cbn [sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse]; exact MID.
Ltac g_hd := hd_proj; lazymatch goal with H : rw_cells b0segs ?mm ?S0 _ |- rw_cells b0segs ?mm ?S0 _ => rw_by H end.

Section C.
  Variable A : act14.
  Variable Q : machine_state -> Prop.
  Variable m0 : word -> option byte.
  Notation S := (b_s (a_cx A)).
  Notation strm := (b_strm (a_cx A)).
  Notation P := (a_P A).
  Hypothesis GL : g10_lin A.
  Hypothesis ANS : sanchor S (a_shs A).
  Hypothesis ANT : sanchor strm (a_sht A).
  Hypothesis SEPst : (S + 64144 <= strm \/ strm + 80 <= S)%Z.
  Section C1.
  Hypothesis SHS : shzW b0segs (W10 A) m0 S (S + 64144).
  Hypothesis SHT : shzW b0segs (W10 A) m0 strm (strm + 80).
  Lemma B0F_g10_C1 : forall (x1 gp tp x5 x6 x7 x8 x12 x13 x14 x15 x16 x18 x21 x23 x25 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32)
      (m : word -> option byte) (h : dsh) (b : bzs) (uc : Z)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word),
    munch (W10 A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m S (HEAD_CELLS h) -> length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    rw_cells b0segs m strm (STRM_CELLS b) -> bs_bzalloc b = Z_to_bv 64 B0F_DBZA ->
    (49 <= uc <= 57)%Z ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    (forall (m' : word -> option byte) (y11 y12 y13 y14 : word),
        (bv_unsigned (sh_small h) = 0)%Z ->
        rw_cells b0segs m' S (HEAD_CELLS (DSH (sh_strm h) (sh_state h) (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h) (sh_bsBuff h) (sh_bsLive h) (uc - 48) (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h))) ->
        rw_cells b0segs m' strm (STRM_CELLS b) ->
        B0FL A m' w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
        stk b0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono b0segs m0 m' -> munch (W10c1 A) m m' -> wmono b0segs m m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 0xaa7a8) (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 ((uc - 48) * 400000)) y11 y12 y13 y14 x15 x16 (Z_to_bv 64 0) x18 (Z_to_bv 64 (a_shs A + 5)) (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 (S + 40)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 B0F_MALLOC) fc None m' (seg_rom b0segs))) ->
    (forall (m' : word -> option byte) (y11 y12 y13 y14 : word),
        (bv_unsigned (sh_small h) <> 0)%Z ->
        rw_cells b0segs m' S (HEAD_CELLS (DSH (sh_strm h) (sh_state h) (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h) (sh_bsBuff h) (sh_bsLive h) (uc - 48) (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h))) ->
        rw_cells b0segs m' strm (STRM_CELLS b) ->
        B0FL A m' w0 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (a_sht A + 7)) w64 w72 w80 w88 w96 w104 w112 w120 ->
        stk b0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono b0segs m0 m' -> munch (W10c1 A) m m' -> wmono b0segs m m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 0xaa4f4) (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 ((uc - 48) * 200000)) y11 y12 y13 y14 x15 x16 (Z_to_bv 64 0) (Z_to_bv 64 (strm + 72)) (Z_to_bv 64 (a_shs A + 5)) (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) (Z_to_bv 64 (strm + 56)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 (a_sht A + 9)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 B0F_MALLOC) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) (Z_to_bv 64 uc) x12 x13 x14 x15 x16 (Z_to_bv 64 0) x18 (Z_to_bv 64 (a_shs A + 5)) (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 (Z_to_bv 64 (S + 40)) x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xaa45c) fc None m (seg_rom b0segs)).
  Proof.
    intros until w120. intros MU WM HD L1 L2 L3 STRM BZA UC FRL ST MI HKF HKS.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANT) as STRM8. pose proof (proj2 ANT : saddr strm (a_sht A)) as ANT0.
    unfold W10 in MU, SHS, SHT. unfold B0F_MALLOC in HKF, HKS. unfold B0F_DBZA in BZA.
    pose proof (SEPst : id _) as BXst.
    pose proof (munch_refl (W10c1 A) m) as MUL. pose proof (wmono_refl b0segs m) as WML. unfold W10c1 in MUL.
    pose proof (bv_unsigned_in_range 8 (sh_small h)) as Rsm; unfold bv_modulus in Rsm; cbn in Rsm.
    rewrite BZA in STRM.
    brun.
    if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0x537a4%Z. sh_norm.
      eapply evt_eq; [ | eapply (HKF _) ];
        [ st_eq | clear - K Rsm; lia | g_hd | rewrite BZA; exact STRM | exact FRL | exact ST | unfold W10; exact MU | exact WM | unfold W10c1; exact MUL | exact WML | g_mi ]. }
    (* [comment removed for export] *)
    brun_to 0x537a4%Z. sh_norm.
    lazymatch goal with H : rw_cells _ _ P _ |- _ => sh_norm_in H end.
    eapply evt_eq; [ | eapply (HKS _) ];
      [ st_eq | clear - K Rsm; lia | g_hd | rewrite BZA; exact STRM | exact FRL | exact ST | unfold W10; exact MU | exact WM | unfold W10c1; exact MUL | exact WML | g_mi ].
  Qed.
  End C1.
  Section CR.
  Hypothesis SHS : shzW b0segs (W10c A) m0 S (S + 64144).
  Hypothesis SHT : shzW b0segs (W10c A) m0 strm (strm + 80).
  Lemma B0F_g10_C2s : forall (x1 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32)
      (m : word -> option byte) (h : dsh) (b : bzs) (d : dsm) (r : Z)
      (w0 w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w104 w112 w120 : word),
    munch (W10c A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m S (HEAD_CELLS h) -> (1 <= sh_n h <= 9)%Z -> length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    rw_cells b0segs m strm (STRM_CELLS b) -> bs_bzalloc b = Z_to_bv 64 B0F_DBZA ->
    rw_cells b0segs m (S + 3152) (MID_CELLS d) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (a_sht A + 7)) w64 w72 w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 w120 ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    (forall (m' : word -> option byte) (y11 y12 y13 : word),
        rw_cells b0segs m' S (HEAD_CELLS h) -> rw_cells b0segs m' strm (STRM_CELLS b) ->
        rw_cells b0segs m' (S + 3152) (MID_CELLS (DSM (sm_tt d) r (sm_ll4 d) (sm_sbcrc d) (sm_sccrc d) (sm_cbcrc d) (sm_cccrc d) (sm_nInUse d))) ->
        B0FL A m' w0 w8 w16 w24 w32 w40 w48 (Z_to_bv 64 (a_sht A + 7)) w64 w72 w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 w120 ->
        stk b0segs m' (a_lo A) P -> munch (W10c A) m0 m' -> wmono b0segs m0 m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 0xaa570) (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 (50000 * sh_n h)) y11 y12 y13 x14 x15 x16 x17 (Z_to_bv 64 (strm + 72)) (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (strm + 56)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 (a_sht A + 9)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 B0F_MALLOC) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (strm + 72)) (Z_to_bv 64 (a_shs A + 5)) (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) (Z_to_bv 64 (strm + 56)) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 (a_sht A + 9)) (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xaa4f4) fc None m (seg_rom b0segs)).
  Proof.
    intros until w120. intros MU WM HD HN L1 L2 L3 STRM BZA MID FRL ST MI HK.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANT) as STRM8. pose proof (proj2 ANT : saddr strm (a_sht A)) as ANT0.
    unfold W10c in MU, SHS, SHT. unfold B0F_MALLOC in HK. unfold B0F_DBZA in BZA.
    pose proof (SEPst : id _) as BXst.
    rewrite BZA in STRM.
    brun_to 0x537a4%Z.
    sh_norm.
    replace (sh_n h * 100000 / 2 * 1 + 0)%Z with (50000 * sh_n h)%Z by (clear; Z.div_mod_to_equations; lia).
    eapply evt_eq; [ | eapply (HK _) ];
      [ st_eq | exact HD | rewrite BZA; exact STRM | g_mid MID | exact FRL | exact ST | unfold W10c; exact MU | exact WM | g_mi ].
  Qed.
  Lemma B0F_g10_C3s : forall (x1 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32)
      (m : word -> option byte) (d : dsm) (r2 : Z)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 w112 w120 : word),
    munch (W10c A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m (S + 3152) (MID_CELLS d) -> (0 < sm_ll16 d < 2 ^ 64)%Z -> (0 < r2 < 2 ^ 64)%Z ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 w120 ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    (forall (m' : word -> option byte) (y10 y11 y12 y13 : word),
        rw_cells b0segs m' (S + 3152) (MID_CELLS (DSM (sm_tt d) (sm_ll16 d) r2 (sm_sbcrc d) (sm_sccrc d) (sm_cbcrc d) (sm_cccrc d) (sm_nInUse d))) ->
        B0FL A m' w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 w120 ->
        stk b0segs m' (a_lo A) P -> munch (W10c A) m0 m' -> wmono b0segs m0 m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) y10 y11 y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xaa7cc) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 r2) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (a_shs A + 395)) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xaa570) fc None m (seg_rom b0segs)).
  Proof.
    intros until w120. intros MU WM MID R1 R2 FRL ST MI HK.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold W10c in MU, SHS, SHT.
    brun.
    if_cases K1; zify_cond_z K1; try (exfalso; clear - K1 R1; lia).
    brun. if_cases K2; zify_cond_z K2; try (exfalso; clear - K2 R2; lia).
    brun_to 0xaa7cc%Z.
    eapply evt_eq; [ | eapply (HK _) ];
      [ st_eq | g_mid MID | exact FRL | exact ST | unfold W10c; exact MU | exact WM | g_mi ].
  Qed.
  Lemma B0F_g10_C2f : forall (x1 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32)
      (m : word -> option byte) (d : dsm) (r : Z)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 w112 w120 : word),
    munch (W10c A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m (S + 3152) (MID_CELLS d) -> (0 < r < 2 ^ 64)%Z ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 w120 ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    (forall (m' : word -> option byte) (y11 y12 : word),
        rw_cells b0segs m' (S + 3152) (MID_CELLS (DSM r (sm_ll16 d) (sm_ll4 d) (sm_sbcrc d) (sm_sccrc d) (sm_cbcrc d) (sm_cccrc d) (sm_nInUse d))) ->
        B0FL A m' w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 (S + 3152)) w104 w112 w120 ->
        stk b0segs m' (a_lo A) P -> munch (W10c A) m0 m' -> wmono b0segs m0 m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 r) y11 y12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xaa7cc) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xaa7a8) fc None m (seg_rom b0segs)).
  Proof.
    intros until w120. intros MU WM MID R0 FRL ST MI HK.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold W10c in MU, SHS, SHT.
    brun.
    if_cases K1; zify_cond_z K1; try (exfalso; clear - K1 R0; lia).
    brun_to 0xaa7cc%Z.
    eapply evt_eq; [ | eapply (HK _) ];
      [ st_eq | g_mid MID | exact FRL | exact ST | unfold W10c; exact MU | exact WM | g_mi ].
  Qed.
  End CR.
End C.
End ACeilS1.
