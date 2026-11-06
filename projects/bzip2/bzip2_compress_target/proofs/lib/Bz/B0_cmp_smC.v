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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpSmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV B0_cmp_sdV B0_cmp_smV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section B0SMC.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SF : smA_facts e.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis FBL : (0 < FB)%Z. Hypothesis FBH : (FB + 160 <= CEIL)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac sdw_to p := brun_to p; wstep; lit_store.

  (* [comment removed for export] *)
  Notation HIT v32 v48 v56 v88 v20 v28 :=
    (sd_hi cx nG (SDW (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_smA_setup : forall (m : word -> option byte) (w24 w64 w72 w104 w128 : word)
      (w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376 : word)
      (w1384 w1392 w1408 w1424 w1432 w1448 w1456 w1528 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (P + 24) [C8 w24] ->
    rw_cells b0segs m (P + 32) [C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 E); C8 w64; C8 w72; C8 (Z_to_bv 64 (FB + 128)); C8 (Z_to_bv 64 (SHE + 83)); C8 (Z_to_bv 64 (E + 668)); C8 w104; C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 w128] ->
    rw_cells b0segs m (P + 1264) [C8 w1264; C8 w1272; C8 w1280; C8 w1288; C8 w1296; C8 w1304; C8 w1312; C8 w1320; C8 w1328; C8 w1336; C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376] ->
    rw_cells b0segs m (P + 1384) [C8 w1384; C8 w1392; C8 (Z_to_bv 64 (FB + 64)); C8 w1408; C8 (Z_to_bv 64 A); C8 w1424; C8 w1432; C8 (Z_to_bv 64 (flag6 nG)); C8 w1448; C8 w1456; C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 nG); C8 (Z_to_bv 64 37450); C8 (Z_to_bv 64 (A * 4294967296)); C8 (Z_to_bv 64 (E + 672)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + -1)); C8 w1528; C8 (Z_to_bv 64 18446744071562067969); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 A1); C8 (NOT (E + 37708)); C8 (Z_to_bv 64 FB)] ->
    mem_inv b0segs m ->
    (forall m' (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word),
      rw_cells b0segs m' (P + 24) [C8 (Z_to_bv 64 (E + 37450))] ->
      rw_cells b0segs m' (P + 32) (sd_loA cx FB SHF SHE (Z_to_bv 64 (FB + 88)) (Z_to_bv 64 (flag6 nG)) (Z_to_bv 64 0)) ->
      rw_cells b0segs m' (P + 1264) (sm_set cx (FB + 64)) ->
      rw_cells b0segs m' (P + 1384) (HIT w1432 w1448 w1456 (Z_to_bv 64 37450) (Z_to_bv 64 (A + -1)) (Z_to_bv 64 (E + 37708))) ->
      rw_cells b0segs m' (P + 1568) [C8 (Z_to_bv 64 FB)] ->
      mem_inv b0segs m' -> munch [(P + 24, P + 136); (P + 1264, P + 1576)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (mkR ra' cP gp tp t0' t1' t2' s0 cP a0' a1' a2' a3' a4' a5' a6' a7' cSB (Z_to_bv 64 (258 * nG)) (Z_to_bv 64 (FB + 88)) (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A))
                            (Z_to_bv 64 257) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 258) (Z_to_bv 64 (FB + 44)) t3' t4' (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9)))
                       F (Z_to_bv 64 0x8c480) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (FB + 32)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8c318) fc None m (seg_rom b0segs)).
  Proof.
    intros m w24 w64 w72 w104 w128 w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1408 w1424 w1432 w1448 w1456 w1528
           ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 SL24 LOW SET HI MI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA2 MF Mb Mf LJb. openSF. unfold CEIL in CEP. assert (HA : A = (nInUse + 2)%Z) by reflexivity.
    pose proof FBH as FBH'. unfold CEIL in FBH'.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (munch_refl [(P + 24, P + 136); (P + 1264, P + 1576)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    assert (F6 : (flag6 nG = 0 \/ flag6 nG = 1)%Z) by (unfold flag6; destruct (Z.eqb nG 6); [right| left]; reflexivity).
    wstep; lit_store.
    sdw_to 0x8c344%Z. sdw_to 0x8c3a0%Z. sdw_to 0x8c3b0%Z. sdw_to 0x8c3d0%Z. sdw_to 0x8c3d8%Z.
    sdw_to 0x8c3e8%Z. sdw_to 0x8c3f4%Z. sdw_to 0x8c3f8%Z. sdw_to 0x8c400%Z. sdw_to 0x8c410%Z. sdw_to 0x8c414%Z. sdw_to 0x8c41c%Z. sdw_to 0x8c420%Z. sdw_to 0x8c428%Z.
    sdw_to 0x8c42c%Z. sdw_to 0x8c434%Z. sdw_to 0x8c438%Z. sdw_to 0x8c440%Z. sdw_to 0x8c444%Z. sdw_to 0x8c44c%Z. sdw_to 0x8c450%Z. sdw_to 0x8c458%Z. sdw_to 0x8c45c%Z.
    sdw_to 0x8c464%Z. sdw_to 0x8c468%Z. sdw_to 0x8c470%Z. sdw_to 0x8c478%Z. sdw_to 0x8c47c%Z.
    replace (flag6 nG mod 2)%Z with (flag6 nG) in LOW by (destruct F6 as [-> | ->]; reflexivity).
    replace (37450 + E)%Z with (E + 37450)%Z in SL24 by lia.
    replace (37450 + E + 258)%Z with (E + 37708)%Z in HI by lia. replace (nG * 1032)%Z with (1032 * nG)%Z in HI by lia.
    destruct (rw_cells_cutS b0segs _ (P + 1384) _ 23%nat HI) as [HIc S1568]. cbn [firstn skipn cells_size csize Nat.add] in HIc, S1568.
    change (Z.of_nat 184) with 184%Z in S1568. replace (P + 1384 + 184)%Z with (P + 1568)%Z in S1568 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq; try (Z.div_mod_to_equations; lia)| exact SL24| exact LOW| exact SET| exact HIc| exact S1568| assumption| eassumption| eassumption] end.
  Qed.
End B0SMC.
End ACeilS1.
