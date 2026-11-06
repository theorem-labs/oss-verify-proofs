(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSmB CmpCutSmB0 BzCFactsSmA BzCFactsSmB CmpFsKit0 CmpHmKit CmpSmKit.
From Stdlib Require Lia. 
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.
Module S0_cmp_smBf1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc1 : forall (m mf : word -> option byte) (xa0 xa2 xa3 xa4 xa5 xa6 xra xs6 xt5 xt6 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x584 : word),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 (Z_to_bv 64 (p 4 2 + p 5 2)); C8 x424; C8 (Z_to_bv 64 (p 9 0)); C8 x440; C8 x448; C8 (Z_to_bv 64 (p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 2 1 + p 3 1)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0)); C8 (Z_to_bv 64 (q 14)); C8 (Z_to_bv 64 (q 10)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (E + q 13 * 16 + 51640)) sp gp tp (Z_to_bv 64 (E + q 11 * 16 + 51640)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 7 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (p 8 2)) (Z_to_bv 64 (p 7 0 + p 8 0)) (Z_to_bv 64 (p 8 1)) (Z_to_bv 64 (p 9 0)) (Z_to_bv 64 (p 4 2 + p 5 2)) (Z_to_bv 64 (p 4 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 7 0)) (Z_to_bv 64 (p 0 2 + p 1 2)) (Z_to_bv 64 (p 2 0 + p 3 0)) (Z_to_bv 64 (p 2 1 + p 3 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 4 1 + p 5 1)) (Z_to_bv 64 (E + q 12 * 16 + 51640)) (Z_to_bv 64 (p 4 0 + p 5 0)) (Z_to_bv 64 (E + q 9 * 16 + 51640)) (Z_to_bv 64 (E + q 6 * 16 + 51640)) (Z_to_bv 64 (p 7 2)) (Z_to_bv 64 (E + q 7 * 16 + 51640)))
           F (Z_to_bv 64 0x16378) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra sp gp tp (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + 37708)) xa0 (Z_to_bv 64 (flag6 nG)) xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (totc)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (usp + 616)) xs6 (Z_to_bv 64 (usp + nG * 4 + 616)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (A)) (Z_to_bv 64 ((-1))) (Z_to_bv 64 (1032)) (Z_to_bv 64 (49)) (Z_to_bv 64 (1)) xt5 xt6)
         F (Z_to_bv 64 0x161e8) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf xa0 xa2 xa3 xa4 xa5 xa6 xra xs6 xt5 xt6 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x584 AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDQ AR1 0%Z.
    (* [comment removed for export] *) RDQ AR1 1%Z.
    (* [comment removed for export] *) RDQ AR1 2%Z.
    (* [comment removed for export] *) RDQ AR1 3%Z.
    (* [comment removed for export] *) RDQ AR1 4%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 5%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 6%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 7%Z.
    (* [comment removed for export] *) RDQ AR1 8%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 9%Z.
    (* [comment removed for export] *) RDQ AR1 10%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 11%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 12%Z.
    (* [comment removed for export] *) RDQ AR1 13%Z.
    (* [comment removed for export] *) RDQ AR1 14%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 15%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 0%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 0%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 0%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 1%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 1%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 1%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 2%Z 0%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 2%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 2%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 3%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 3%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 3%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 4%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 4%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 4%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 5%Z 0%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 5%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 5%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 6%Z 0%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 6%Z 1%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 7%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 7%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 7%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 8%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 8%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 8%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 9%Z 0%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
End S0_cmp_smBf1.

Unset Lia Cache.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (lp cb : zarr) (gs iter nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDQ AR1 k :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD end;
    change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
    pose proof (QB k ltac:(lia)) as ?QBk;
    lstep; clear RD; rewrite (zx16_lit (q k)) by lia.
  (* [comment removed for export] *)
  Ltac RDP LPK k j :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPK ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD end;
    change (zget lp (4 * q k + j)) with (p k j) in RD;
    pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
    lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia).
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fc2 : forall (m mf : word -> option byte) (x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x424 x440 x448 : word),
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (usp + 184) [C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 (Z_to_bv 64 (p 4 2 + p 5 2)); C8 x424; C8 (Z_to_bv 64 (p 9 0)); C8 x440; C8 x448; C8 (Z_to_bv 64 (p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 2 1 + p 3 1)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0)); C8 (Z_to_bv 64 (q 14)); C8 (Z_to_bv 64 (q 10)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) ->
    mem_inv s0segs m ->
    munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m ->
    wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (usp + 184) [C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 29 1 + p 30 1)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (p 22 2 + p 23 2)); C8 (Z_to_bv 64 (p 16 2 + p 17 2)); C8 (Z_to_bv 64 (p 16 1 + p 17 1)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 22 1 + p 23 1)); C8 (Z_to_bv 64 (p 22 0 + p 23 0)); C8 (Z_to_bv 64 (p 16 0 + p 17 0)); C8 (Z_to_bv 64 (p 11 2 + p 12 2)); C8 (Z_to_bv 64 (p 11 1 + p 12 1)); C8 (Z_to_bv 64 (q 19)); C8 (Z_to_bv 64 (p 11 0 + p 12 0)); C8 (Z_to_bv 64 (p 7 0 + p 8 0)); C8 (Z_to_bv 64 (p 4 2 + p 5 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 7 2 + p 8 2)); C8 (Z_to_bv 64 (p 7 1 + p 8 1)); C8 (Z_to_bv 64 (p 2 2 + p 3 2)); C8 (Z_to_bv 64 (p 2 1 + p 3 1)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 0 1 + p 1 1)); C8 (Z_to_bv 64 (p 0 0 + p 1 0)); C8 (Z_to_bv 64 (q 14)); C8 (Z_to_bv 64 (q 10)); C8 (Z_to_bv 64 (q 15)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs)); C8 (Z_to_bv 64 (gs + 50)); C8 (Z_to_bv 64 (totc))] ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u8arr s0segs m' (usp + 888) (zb8 cb 12) ->
      mem_inv s0segs m' ->
      munch [(usp + 184, usp + 592); (usp + 888, usp + 900)]%Z mf m' ->
      wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 (E + q 13 * 16 + 51640)) sp gp tp (Z_to_bv 64 (p 29 1)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 23 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (E + q 38 * 16 + 51640)) (Z_to_bv 64 (E + q 31 * 16 + 51640)) (Z_to_bv 64 (E + q 37 * 16 + 51640)) (Z_to_bv 64 (p 30 2)) (Z_to_bv 64 (p 37 0)) (Z_to_bv 64 (p 38 0)) (Z_to_bv 64 (p 31 0)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 29 1 + p 30 1)) (Z_to_bv 64 (p 0 2 + p 1 2)) (Z_to_bv 64 (p 2 0 + p 3 0)) (Z_to_bv 64 (E + q 30 * 16 + 51640)) (Z_to_bv 64 (E + q 13 * 16 + 51640)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 29 2)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 4 1 + p 5 1)) (Z_to_bv 64 (E + q 18 * 16 + 51640)) (Z_to_bv 64 (p 4 0 + p 5 0)) (Z_to_bv 64 (E + q 9 * 16 + 51640)) (Z_to_bv 64 (E + q 6 * 16 + 51640)) (Z_to_bv 64 (q 39)) (Z_to_bv 64 (E + q 7 * 16 + 51640)))
           F (Z_to_bv 64 0x164f4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 (E + q 13 * 16 + 51640)) sp gp tp (Z_to_bv 64 (E + q 11 * 16 + 51640)) (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (p 7 1)) (Z_to_bv 64 (E)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (p 8 2)) (Z_to_bv 64 (p 7 0 + p 8 0)) (Z_to_bv 64 (p 8 1)) (Z_to_bv 64 (p 9 0)) (Z_to_bv 64 (p 4 2 + p 5 2)) (Z_to_bv 64 (p 4 2)) (Z_to_bv 64 (A1 + gs * 2)) (Z_to_bv 64 (p 7 0)) (Z_to_bv 64 (p 0 2 + p 1 2)) (Z_to_bv 64 (p 2 0 + p 3 0)) (Z_to_bv 64 (p 2 1 + p 3 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (usp + nG * 2 + 888)) (Z_to_bv 64 (p 4 1 + p 5 1)) (Z_to_bv 64 (E + q 12 * 16 + 51640)) (Z_to_bv 64 (p 4 0 + p 5 0)) (Z_to_bv 64 (E + q 9 * 16 + 51640)) (Z_to_bv 64 (E + q 6 * 16 + 51640)) (Z_to_bv 64 (p 7 2)) (Z_to_bv 64 (E + q 7 * 16 + 51640)))
         F (Z_to_bv 64 0x16378) fc None m (seg_rom s0segs)).
  Proof.
    intros m mf x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x424 x440 x448 AR1 LPK S8 SPL C576 COST MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length lp (jseg J 51640 4128) 1032 ltac:(lia)) as LLP.
    pose proof (zb8_length_nat cb 12) as LC.
    unfold sm_slots3 in S8. cbv zeta in S8.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (QB 10 ltac:(lia)) as QB10.
    pose proof (QB 11 ltac:(lia)) as QB11.
    pose proof (QB 12 ltac:(lia)) as QB12.
    pose proof (QB 13 ltac:(lia)) as QB13.
    pose proof (QB 14 ltac:(lia)) as QB14.
    pose proof (QB 15 ltac:(lia)) as QB15.
    pose proof (QB 6 ltac:(lia)) as QB6.
    pose proof (QB 7 ltac:(lia)) as QB7.
    pose proof (QB 9 ltac:(lia)) as QB9.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 11%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 11%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 11%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 12%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 12%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 12%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 13%Z 0%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 16%Z.
    (* [comment removed for export] *) RDQ AR1 17%Z.
    (* [comment removed for export] *) RDQ AR1 18%Z.
    (* [comment removed for export] *) RDQ AR1 19%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 17%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 16%Z 0%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 16%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 16%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 17%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 17%Z 2%Z.
    (* [comment removed for export] *) RDQ AR1 22%Z.
    (* [comment removed for export] *) RDQ AR1 23%Z.
    (* [comment removed for export] *) RDP LPK 18%Z 0%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 18%Z 1%Z.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 22%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 22%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 23%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 23%Z 1%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 23%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 29%Z.
    (* [comment removed for export] *) RDQ AR1 30%Z.
    (* [comment removed for export] *) RDP LPK 22%Z 2%Z.
    (* [comment removed for export] *) RDQ AR1 31%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 29%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 30%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 30%Z 1%Z.
    (* [comment removed for export] *) RDP LPK 29%Z 1%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDP LPK 29%Z 2%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) SST.
    (* [comment removed for export] *) RDQ AR1 37%Z.
    (* [comment removed for export] *) RDQ AR1 38%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDQ AR1 39%Z.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) lstep.
    (* [comment removed for export] *) RDP LPK 30%Z 2%Z.
    (* [comment removed for export] *) RDP LPK 37%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 38%Z 0%Z.
    (* [comment removed for export] *) RDP LPK 31%Z 0%Z.
    (* [comment removed for export] *) SST.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | exact AR1 | exact LPK | exact S8
      | lazymatch type of SPL with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | lazymatch type of C576 with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact C576| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with | rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end | u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.

End ACeilS1.
