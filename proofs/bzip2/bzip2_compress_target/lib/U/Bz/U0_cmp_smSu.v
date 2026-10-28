(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpFsKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpHmKit CmpSmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section U0SMSU.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (ra gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SF : smA_facts e.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx).
  Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nInUse := (e_nInUse e).
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation MASK := (Z_to_bv 64 18446744071562067969).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac st := ustep; lit_store.
  Ltac cellK :=
    lazymatch goal with
    | |- rw_cells _ ?mm ?a [C8 ?v] =>
        lazymatch goal with
        | R : rw_cells _ mm a [C8 ?w] |- _ => first [ exact R | replace v with w; [exact R| CmpStEq.st_eq_leaf] ]
        end
    end.

  Notation RIu t0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 :=
    (mkR ra cSP gp tp t0 (Z_to_bv 64 258) (Z_to_bv 64 1) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 6) s3 s4 s5 s6 (Z_to_bv 64 (A - 1)) (Z_to_bv 64 257) (NOT (E + 37708)) (Z_to_bv 64 (E + 672)) (NOT (E + 672))
         MASK (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 15)).
  Notation RIT t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 (Z_to_bv 64 (4 * A)) s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).

  Notation Wsu := [(SP + 24, SP + 48); (SP + 528, SP + 584); (SP + 800, SP + 832); (SP + 888, SP + 896); (SP + 944, SP + 960); (SP + 992, SP + 1024)]%Z.
  Lemma U0_smA_setup : forall (me m : word -> option byte)
      (t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 : word)
      (w24 w32 w40 w528 w536 w544 w552 w560 w568 w576 w800 w808 w816 w824 w888 w944 w952 w992 w1008 w1016 : word),
    rw_cells s0segs m (SP + 24) [C8 w24] -> rw_cells s0segs m (SP + 32) [C8 w32] -> rw_cells s0segs m (SP + 40) [C8 w40] ->
    rw_cells s0segs m (SP + 528) [C8 w528] -> rw_cells s0segs m (SP + 536) [C8 w536] -> rw_cells s0segs m (SP + 544) [C8 w544] ->
    rw_cells s0segs m (SP + 552) [C8 w552] -> rw_cells s0segs m (SP + 560) [C8 w560] -> rw_cells s0segs m (SP + 568) [C8 w568] ->
    rw_cells s0segs m (SP + 576) [C8 w576] ->
    rw_cells s0segs m (SP + 800) [C8 w800] -> rw_cells s0segs m (SP + 808) [C8 w808] -> rw_cells s0segs m (SP + 816) [C8 w816] ->
    rw_cells s0segs m (SP + 824) [C8 w824] -> rw_cells s0segs m (SP + 888) [C8 w888] ->
    rw_cells s0segs m (SP + 944) [C8 w944] -> rw_cells s0segs m (SP + 952) [C8 w952] -> rw_cells s0segs m (SP + 992) [C8 w992] ->
    rw_cells s0segs m (SP + 1000) [C8 (Z_to_bv 64 (A * 4294967296))] ->
    rw_cells s0segs m (SP + 1008) [C8 w1008] -> rw_cells s0segs m (SP + 1016) [C8 w1016] ->
    mem_inv s0segs m -> munch Wsu me m -> wmono s0segs me m ->
    frdW s0segs Wsu me (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] -> frdW s0segs Wsu me (SP + 928) [C8 (Z_to_bv 64 nG)] ->
    frdW s0segs Wsu me (SP + 968) [C8 (Z_to_bv 64 A)] -> frdW s0segs Wsu me (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
      rw_cells s0segs m' (SP + 24) [C8 (Z_to_bv 64 (flag6 nG))] -> rw_cells s0segs m' (SP + 32) [C8 (Z_to_bv 64 0)] ->
      rw_cells s0segs m' (SP + 40) [C8 (Z_to_bv 64 (4 * A))] ->
      rw_cells s0segs m' (SP + 528) [C8 (NOT (E + 38740))] -> rw_cells s0segs m' (SP + 536) [C8 (NOT (E + 38998))] ->
      rw_cells s0segs m' (SP + 544) [C8 (NOT (E + 38224))] -> rw_cells s0segs m' (SP + 552) [C8 (NOT (E + 38482))] ->
      rw_cells s0segs m' (SP + 560) [C8 (Z_to_bv 64 (E + 38998))] -> rw_cells s0segs m' (SP + 568) [C8 (NOT (E + 51640))] ->
      rw_cells s0segs m' (SP + 576) [C8 (NOT (E + 37966))] ->
      rw_cells s0segs m' (SP + 800) [C8 (Z_to_bv 64 18002)] -> rw_cells s0segs m' (SP + 808) [C8 (NOT (SP + 1060))] ->
      rw_cells s0segs m' (SP + 816) [C8 (Z_to_bv 64 (E + 1704))] -> rw_cells s0segs m' (SP + 824) [C8 (NOT (E + 1704))] ->
      rw_cells s0segs m' (SP + 888) [C8 (Z_to_bv 64 (1032 * nG))] ->
      rw_cells s0segs m' (SP + 944) [C8 (NOT (E + 45448))] -> rw_cells s0segs m' (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
      rw_cells s0segs m' (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] -> rw_cells s0segs m' (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] ->
      rw_cells s0segs m' (SP + 1008) [C8 (Z_to_bv 64 1)] -> rw_cells s0segs m' (SP + 1016) [C8 (Z_to_bv 64 1)] ->
      mem_inv s0segs m' -> munch Wsu me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RIT t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 1084)) s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1745c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIu t0 (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))) a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6)
                     F (Z_to_bv 64 0x17338) fc None m (seg_rom s0segs)).
  Proof.
    intros me m t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6
           w24 w32 w40 w528 w536 w544 w552 w560 w568 w576 w800 w808 w816 w824 w888 w944 w952 w992 w1008 w1016
           C24 C32 C40 C528 C536 C544 C552 C560 C568 C576 C800 C808 C816 C824 C888 C944 C952 C992 C1000 C1008 C1016
           MI MU WM V904 V928 V968 V1032 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA2 MF Mb Mf LJb. openSF. unfold CEIL in CEP.
    assert (HA : A = (nInUse + 2)%Z) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    assert (F6 : (flag6 nG = 0 \/ flag6 nG = 1)%Z) by (unfold flag6; destruct (Z.eqb nG 6); [right| left]; reflexivity).
    st.
    poseV V968 RO. st. clear RO.
    do 5 st.
    poseV V1032 RO. st. clear RO.
    do 5 st.
    st.
    do 11 st.
    poseV V904 RO. st. clear RO.
    do 32 st.
    poseV V928 RO. st. clear RO.
    do 14 st.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| first [ cellK | assumption ] ..].
  Qed.
End U0SMSU.
End ACeilS1.
