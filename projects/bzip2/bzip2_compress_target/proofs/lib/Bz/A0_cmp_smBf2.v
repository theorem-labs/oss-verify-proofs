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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA CmpCutSmB BzCFactsSmA BzCFactsSmB CmpSmKit CmpFsKit CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO FV : Z).
  Variables (lp cb : zarr) (gs nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Hypothesis COL : (0 < CO)%Z. Hypothesis COH : (CO + 12 <= CEIL)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis NG6 : nG = 6%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis HnS : (0 <= nSel < 18002)%Z. Hypothesis Htc : (0 <= totc <= 4294967296)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
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
  Ltac fstep := AsanKit.a_zstep_nofb; bzl; AsanKit.a_try_lit_branch.
  Ltac frun_to p := first [ AsanKit.a_at_pc p | AsanKit.a_pc_is_lit; fstep; frun_to p | fail 1 "frun_to: stuck before" p ].
  Notation Wsp := [(P + 232, P + 1344)]%Z.
  (* [comment removed for export] *)
  Ltac RDQ VAR1 k :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let AR1v := fresh "AR1v" in let RD := fresh "RD" in
      pose proof (VAR1 mm MU') as AR1v;
      pose proof (zb8_read2 a0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1v ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD;
      clear AR1v;
      change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
      pose proof (QB k ltac:(lia)) as ?QBk;
      lstep; clear RD; rewrite (zx16_lit (q k)) by lia end.
  (* [comment removed for export] *)
  Ltac RDP VLPK k j :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let LPKv := fresh "LPKv" in let RD := fresh "RD" in
      pose proof (VLPK mm MU') as LPKv;
      pose proof (ovw_read a0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPKv ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD;
      clear LPKv;
      change (zget lp (4 * q k + j)) with (p k j) in RD;
      pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
      lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia) end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fc3 : forall (m me : word -> option byte) (xa4 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x1312 x1320 x1328 x1336 : word),
    rw_cells a0segs m (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 2)); C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
    mem_inv a0segs m -> munch [(P + 232, P + 1344)]%Z me m -> wmono a0segs me m ->
    (forall m', munch [(P + 232, P + 1344)]%Z me m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW a0segs [(P + 232, P + 1344)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 232, P + 1344)]%Z me m' -> u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW a0segs [(P + 232, P + 1344)]%Z me E (E + ESTATE_SIZE) ->
    (forall m' (ya4 : word),
      rw_cells a0segs m' (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 2)); C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
      mem_inv a0segs m' -> munch [(P + 232, P + 1344)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 (p 3 2)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (p 4 1)) (Z_to_bv 64 (p 0 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) (Z_to_bv 64 (E + 16 * q 32 + 51640)) (Z_to_bv 64 (E + 16 * q 32 + 51644)) (Z_to_bv 64 (E + 51640)) ya4 (Z_to_bv 64 (p 32 0)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (49)) (Z_to_bv 64 (p 1 2)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (p 2 0)) (Z_to_bv 64 (p 2 2)) (Z_to_bv 64 (p 2 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (gs + 49)))
           F (Z_to_bv 64 0x8bc90) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 (p 3 2)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (p 4 1)) (Z_to_bv 64 (p 0 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) (Z_to_bv 64 (p 21 1)) (Z_to_bv 64 (E + 16 * q 21 + 51648)) (Z_to_bv 64 (E + 51640)) xa4 (Z_to_bv 64 (p 21 0)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (49)) (Z_to_bv 64 (p 1 2)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (p 2 0)) (Z_to_bv 64 (p 2 2)) (Z_to_bv 64 (p 2 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (gs + 49)))
         F (Z_to_bv 64 0x8b730) fc None m (seg_rom a0segs)).
  Proof.
    intros m me xa4 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x1312 x1320 x1328 x1336 SPL MI MU WM VAR1 SHa VLPK SHe K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (QB 21 ltac:(lia)) as QB21.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 15 0 ltac:(lia) ltac:(lia)) as PB15_0.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 20 0 ltac:(lia) ltac:(lia)) as PB20_0.
    pose proof (PB 21 0 ltac:(lia) ltac:(lia)) as PB21_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 15 1 ltac:(lia) ltac:(lia)) as PB15_1.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 20 1 ltac:(lia) ltac:(lia)) as PB20_1.
    pose proof (PB 21 1 ltac:(lia) ltac:(lia)) as PB21_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (PB 10 2 ltac:(lia) ltac:(lia)) as PB10_2.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 2 ltac:(lia) ltac:(lia)) as PB14_2.
    pose proof (PB 15 2 ltac:(lia) ltac:(lia)) as PB15_2.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 20 2 ltac:(lia) ltac:(lia)) as PB20_2.
    frun_to 0x8b740%Z. RDP VLPK 21%Z 2%Z.
    frun_to 0x8b744%Z. SST.
    frun_to 0x8b750%Z. RDQ VAR1 22%Z.
    frun_to 0x8b780%Z. RDP VLPK 22%Z 0%Z.
    frun_to 0x8b784%Z. SST.
    frun_to 0x8b7a0%Z. RDP VLPK 22%Z 1%Z.
    frun_to 0x8b7a4%Z. SST.
    frun_to 0x8b7c0%Z. RDP VLPK 22%Z 2%Z.
    frun_to 0x8b7c4%Z. SST.
    frun_to 0x8b7d0%Z. RDQ VAR1 23%Z.
    frun_to 0x8b800%Z. RDP VLPK 23%Z 0%Z.
    frun_to 0x8b804%Z. SST.
    frun_to 0x8b820%Z. RDP VLPK 23%Z 1%Z.
    frun_to 0x8b824%Z. SST.
    frun_to 0x8b840%Z. RDP VLPK 23%Z 2%Z.
    frun_to 0x8b844%Z. SST.
    frun_to 0x8b850%Z. RDQ VAR1 24%Z.
    frun_to 0x8b880%Z. RDP VLPK 24%Z 0%Z.
    frun_to 0x8b884%Z. SST.
    frun_to 0x8b8a0%Z. RDP VLPK 24%Z 1%Z.
    frun_to 0x8b8a4%Z. SST.
    frun_to 0x8b8c0%Z. RDP VLPK 24%Z 2%Z.
    frun_to 0x8b8c4%Z. SST.
    frun_to 0x8b8d0%Z. RDQ VAR1 25%Z.
    frun_to 0x8b900%Z. RDP VLPK 25%Z 0%Z.
    frun_to 0x8b904%Z. SST.
    frun_to 0x8b920%Z. RDP VLPK 25%Z 1%Z.
    frun_to 0x8b924%Z. SST.
    frun_to 0x8b940%Z. RDP VLPK 25%Z 2%Z.
    frun_to 0x8b944%Z. SST.
    frun_to 0x8b950%Z. RDQ VAR1 26%Z.
    frun_to 0x8b980%Z. RDP VLPK 26%Z 0%Z.
    frun_to 0x8b984%Z. SST.
    frun_to 0x8b9a0%Z. RDP VLPK 26%Z 1%Z.
    frun_to 0x8b9a4%Z. SST.
    frun_to 0x8b9c0%Z. RDP VLPK 26%Z 2%Z.
    frun_to 0x8b9c4%Z. SST.
    frun_to 0x8b9d0%Z. RDQ VAR1 27%Z.
    frun_to 0x8ba00%Z. RDP VLPK 27%Z 0%Z.
    frun_to 0x8ba04%Z. SST.
    frun_to 0x8ba20%Z. RDP VLPK 27%Z 1%Z.
    frun_to 0x8ba24%Z. SST.
    frun_to 0x8ba40%Z. RDP VLPK 27%Z 2%Z.
    frun_to 0x8ba44%Z. SST.
    frun_to 0x8ba50%Z. RDQ VAR1 28%Z.
    frun_to 0x8ba80%Z. RDP VLPK 28%Z 0%Z.
    frun_to 0x8ba84%Z. SST.
    frun_to 0x8baa0%Z. RDP VLPK 28%Z 1%Z.
    frun_to 0x8baa4%Z. SST.
    frun_to 0x8bac0%Z. RDP VLPK 28%Z 2%Z.
    frun_to 0x8bac4%Z. SST.
    frun_to 0x8bad0%Z. RDQ VAR1 29%Z.
    frun_to 0x8bb00%Z. RDP VLPK 29%Z 0%Z.
    frun_to 0x8bb04%Z. SST.
    frun_to 0x8bb20%Z. RDP VLPK 29%Z 1%Z.
    frun_to 0x8bb24%Z. SST.
    frun_to 0x8bb40%Z. RDP VLPK 29%Z 2%Z.
    frun_to 0x8bb44%Z. SST.
    frun_to 0x8bb50%Z. RDQ VAR1 30%Z.
    frun_to 0x8bb80%Z. RDP VLPK 30%Z 0%Z.
    frun_to 0x8bb84%Z. SST.
    frun_to 0x8bba0%Z. RDP VLPK 30%Z 1%Z.
    frun_to 0x8bba4%Z. SST.
    frun_to 0x8bbc0%Z. RDP VLPK 30%Z 2%Z.
    frun_to 0x8bbc4%Z. SST.
    frun_to 0x8bbd0%Z. RDQ VAR1 31%Z.
    frun_to 0x8bc00%Z. RDP VLPK 31%Z 0%Z.
    frun_to 0x8bc04%Z. SST.
    frun_to 0x8bc20%Z. RDP VLPK 31%Z 1%Z.
    frun_to 0x8bc24%Z. SST.
    frun_to 0x8bc40%Z. RDP VLPK 31%Z 2%Z.
    frun_to 0x8bc44%Z. SST.
    frun_to 0x8bc50%Z. RDQ VAR1 32%Z.
    frun_to 0x8bc80%Z. RDP VLPK 32%Z 0%Z.
    frun_to 0x8bc84%Z. SST.
    frun_to 0x8bc90%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fc4 : forall (m me : word -> option byte) (xa4 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x1312 x1320 x1328 x1336 : word),
    rw_cells a0segs m (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 2)); C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
    mem_inv a0segs m -> munch [(P + 232, P + 1344)]%Z me m -> wmono a0segs me m ->
    (forall m', munch [(P + 232, P + 1344)]%Z me m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW a0segs [(P + 232, P + 1344)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 232, P + 1344)]%Z me m' -> u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW a0segs [(P + 232, P + 1344)]%Z me E (E + ESTATE_SIZE) ->
    (forall m' (ya2 ya4 : word),
      rw_cells a0segs m' (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 (Z_to_bv 64 (p 42 2)); C8 x392; C8 (Z_to_bv 64 (p 42 1)); C8 (Z_to_bv 64 (p 42 0)); C8 (Z_to_bv 64 (p 41 2)); C8 (Z_to_bv 64 (p 41 1)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 40 2)); C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 2)); C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
      mem_inv a0segs m' -> munch [(P + 232, P + 1344)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 (p 3 2)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (p 4 1)) (Z_to_bv 64 (p 0 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) (Z_to_bv 64 (E + 16 * q 43 + 51640)) ya2 (Z_to_bv 64 (E + 51640)) ya4 (Z_to_bv 64 (p 42 0)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (49)) (Z_to_bv 64 (p 1 2)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (p 2 0)) (Z_to_bv 64 (p 2 2)) (Z_to_bv 64 (p 2 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (gs + 49)))
           F (Z_to_bv 64 0x8c1f0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 (p 3 2)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (p 4 1)) (Z_to_bv 64 (p 0 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) (Z_to_bv 64 (E + 16 * q 32 + 51640)) (Z_to_bv 64 (E + 16 * q 32 + 51644)) (Z_to_bv 64 (E + 51640)) xa4 (Z_to_bv 64 (p 32 0)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (49)) (Z_to_bv 64 (p 1 2)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (p 2 0)) (Z_to_bv 64 (p 2 2)) (Z_to_bv 64 (p 2 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (gs + 49)))
         F (Z_to_bv 64 0x8bc90) fc None m (seg_rom a0segs)).
  Proof.
    intros m me xa4 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x1312 x1320 x1328 x1336 SPL MI MU WM VAR1 SHa VLPK SHe K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (QB 32 ltac:(lia)) as QB32.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 7 0 ltac:(lia) ltac:(lia)) as PB7_0.
    pose proof (PB 8 0 ltac:(lia) ltac:(lia)) as PB8_0.
    pose proof (PB 9 0 ltac:(lia) ltac:(lia)) as PB9_0.
    pose proof (PB 10 0 ltac:(lia) ltac:(lia)) as PB10_0.
    pose proof (PB 11 0 ltac:(lia) ltac:(lia)) as PB11_0.
    pose proof (PB 12 0 ltac:(lia) ltac:(lia)) as PB12_0.
    pose proof (PB 13 0 ltac:(lia) ltac:(lia)) as PB13_0.
    pose proof (PB 14 0 ltac:(lia) ltac:(lia)) as PB14_0.
    pose proof (PB 15 0 ltac:(lia) ltac:(lia)) as PB15_0.
    pose proof (PB 16 0 ltac:(lia) ltac:(lia)) as PB16_0.
    pose proof (PB 17 0 ltac:(lia) ltac:(lia)) as PB17_0.
    pose proof (PB 18 0 ltac:(lia) ltac:(lia)) as PB18_0.
    pose proof (PB 19 0 ltac:(lia) ltac:(lia)) as PB19_0.
    pose proof (PB 20 0 ltac:(lia) ltac:(lia)) as PB20_0.
    pose proof (PB 21 0 ltac:(lia) ltac:(lia)) as PB21_0.
    pose proof (PB 22 0 ltac:(lia) ltac:(lia)) as PB22_0.
    pose proof (PB 23 0 ltac:(lia) ltac:(lia)) as PB23_0.
    pose proof (PB 24 0 ltac:(lia) ltac:(lia)) as PB24_0.
    pose proof (PB 25 0 ltac:(lia) ltac:(lia)) as PB25_0.
    pose proof (PB 26 0 ltac:(lia) ltac:(lia)) as PB26_0.
    pose proof (PB 27 0 ltac:(lia) ltac:(lia)) as PB27_0.
    pose proof (PB 28 0 ltac:(lia) ltac:(lia)) as PB28_0.
    pose proof (PB 29 0 ltac:(lia) ltac:(lia)) as PB29_0.
    pose proof (PB 30 0 ltac:(lia) ltac:(lia)) as PB30_0.
    pose proof (PB 31 0 ltac:(lia) ltac:(lia)) as PB31_0.
    pose proof (PB 32 0 ltac:(lia) ltac:(lia)) as PB32_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 7 1 ltac:(lia) ltac:(lia)) as PB7_1.
    pose proof (PB 8 1 ltac:(lia) ltac:(lia)) as PB8_1.
    pose proof (PB 9 1 ltac:(lia) ltac:(lia)) as PB9_1.
    pose proof (PB 10 1 ltac:(lia) ltac:(lia)) as PB10_1.
    pose proof (PB 11 1 ltac:(lia) ltac:(lia)) as PB11_1.
    pose proof (PB 12 1 ltac:(lia) ltac:(lia)) as PB12_1.
    pose proof (PB 13 1 ltac:(lia) ltac:(lia)) as PB13_1.
    pose proof (PB 14 1 ltac:(lia) ltac:(lia)) as PB14_1.
    pose proof (PB 15 1 ltac:(lia) ltac:(lia)) as PB15_1.
    pose proof (PB 16 1 ltac:(lia) ltac:(lia)) as PB16_1.
    pose proof (PB 17 1 ltac:(lia) ltac:(lia)) as PB17_1.
    pose proof (PB 18 1 ltac:(lia) ltac:(lia)) as PB18_1.
    pose proof (PB 19 1 ltac:(lia) ltac:(lia)) as PB19_1.
    pose proof (PB 20 1 ltac:(lia) ltac:(lia)) as PB20_1.
    pose proof (PB 21 1 ltac:(lia) ltac:(lia)) as PB21_1.
    pose proof (PB 22 1 ltac:(lia) ltac:(lia)) as PB22_1.
    pose proof (PB 23 1 ltac:(lia) ltac:(lia)) as PB23_1.
    pose proof (PB 24 1 ltac:(lia) ltac:(lia)) as PB24_1.
    pose proof (PB 25 1 ltac:(lia) ltac:(lia)) as PB25_1.
    pose proof (PB 26 1 ltac:(lia) ltac:(lia)) as PB26_1.
    pose proof (PB 27 1 ltac:(lia) ltac:(lia)) as PB27_1.
    pose proof (PB 28 1 ltac:(lia) ltac:(lia)) as PB28_1.
    pose proof (PB 29 1 ltac:(lia) ltac:(lia)) as PB29_1.
    pose proof (PB 30 1 ltac:(lia) ltac:(lia)) as PB30_1.
    pose proof (PB 31 1 ltac:(lia) ltac:(lia)) as PB31_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    pose proof (PB 6 2 ltac:(lia) ltac:(lia)) as PB6_2.
    pose proof (PB 7 2 ltac:(lia) ltac:(lia)) as PB7_2.
    pose proof (PB 8 2 ltac:(lia) ltac:(lia)) as PB8_2.
    pose proof (PB 9 2 ltac:(lia) ltac:(lia)) as PB9_2.
    pose proof (PB 10 2 ltac:(lia) ltac:(lia)) as PB10_2.
    pose proof (PB 11 2 ltac:(lia) ltac:(lia)) as PB11_2.
    pose proof (PB 12 2 ltac:(lia) ltac:(lia)) as PB12_2.
    pose proof (PB 13 2 ltac:(lia) ltac:(lia)) as PB13_2.
    pose proof (PB 14 2 ltac:(lia) ltac:(lia)) as PB14_2.
    pose proof (PB 15 2 ltac:(lia) ltac:(lia)) as PB15_2.
    pose proof (PB 16 2 ltac:(lia) ltac:(lia)) as PB16_2.
    pose proof (PB 17 2 ltac:(lia) ltac:(lia)) as PB17_2.
    pose proof (PB 18 2 ltac:(lia) ltac:(lia)) as PB18_2.
    pose proof (PB 19 2 ltac:(lia) ltac:(lia)) as PB19_2.
    pose proof (PB 20 2 ltac:(lia) ltac:(lia)) as PB20_2.
    pose proof (PB 21 2 ltac:(lia) ltac:(lia)) as PB21_2.
    pose proof (PB 22 2 ltac:(lia) ltac:(lia)) as PB22_2.
    pose proof (PB 23 2 ltac:(lia) ltac:(lia)) as PB23_2.
    pose proof (PB 24 2 ltac:(lia) ltac:(lia)) as PB24_2.
    pose proof (PB 25 2 ltac:(lia) ltac:(lia)) as PB25_2.
    pose proof (PB 26 2 ltac:(lia) ltac:(lia)) as PB26_2.
    pose proof (PB 27 2 ltac:(lia) ltac:(lia)) as PB27_2.
    pose proof (PB 28 2 ltac:(lia) ltac:(lia)) as PB28_2.
    pose proof (PB 29 2 ltac:(lia) ltac:(lia)) as PB29_2.
    pose proof (PB 30 2 ltac:(lia) ltac:(lia)) as PB30_2.
    pose proof (PB 31 2 ltac:(lia) ltac:(lia)) as PB31_2.
    frun_to 0x8bca0%Z. RDP VLPK 32%Z 1%Z.
    frun_to 0x8bca4%Z. SST.
    frun_to 0x8bcc0%Z. RDP VLPK 32%Z 2%Z.
    frun_to 0x8bcc4%Z. SST.
    frun_to 0x8bcd0%Z. RDQ VAR1 33%Z.
    frun_to 0x8bd00%Z. RDP VLPK 33%Z 0%Z.
    frun_to 0x8bd04%Z. SST.
    frun_to 0x8bd20%Z. RDP VLPK 33%Z 1%Z.
    frun_to 0x8bd24%Z. SST.
    frun_to 0x8bd40%Z. RDP VLPK 33%Z 2%Z.
    frun_to 0x8bd44%Z. SST.
    frun_to 0x8bd50%Z. RDQ VAR1 34%Z.
    frun_to 0x8bd80%Z. RDP VLPK 34%Z 0%Z.
    frun_to 0x8bd84%Z. SST.
    frun_to 0x8bda0%Z. RDP VLPK 34%Z 1%Z.
    frun_to 0x8bda4%Z. SST.
    frun_to 0x8bdc0%Z. RDP VLPK 34%Z 2%Z.
    frun_to 0x8bdc4%Z. SST.
    frun_to 0x8bdd0%Z. RDQ VAR1 35%Z.
    frun_to 0x8be00%Z. RDP VLPK 35%Z 0%Z.
    frun_to 0x8be04%Z. SST.
    frun_to 0x8be20%Z. RDP VLPK 35%Z 1%Z.
    frun_to 0x8be24%Z. SST.
    frun_to 0x8be40%Z. RDP VLPK 35%Z 2%Z.
    frun_to 0x8be44%Z. SST.
    frun_to 0x8be50%Z. RDQ VAR1 36%Z.
    frun_to 0x8be80%Z. RDP VLPK 36%Z 0%Z.
    frun_to 0x8be84%Z. SST.
    frun_to 0x8bea0%Z. RDP VLPK 36%Z 1%Z.
    frun_to 0x8bea4%Z. SST.
    frun_to 0x8bec0%Z. RDP VLPK 36%Z 2%Z.
    frun_to 0x8bec4%Z. SST.
    frun_to 0x8bed0%Z. RDQ VAR1 37%Z.
    frun_to 0x8bf00%Z. RDP VLPK 37%Z 0%Z.
    frun_to 0x8bf04%Z. SST.
    frun_to 0x8bf20%Z. RDP VLPK 37%Z 1%Z.
    frun_to 0x8bf24%Z. SST.
    frun_to 0x8bf40%Z. RDP VLPK 37%Z 2%Z.
    frun_to 0x8bf44%Z. SST.
    frun_to 0x8bf50%Z. RDQ VAR1 38%Z.
    frun_to 0x8bf80%Z. RDP VLPK 38%Z 0%Z.
    frun_to 0x8bf84%Z. SST.
    frun_to 0x8bfa0%Z. RDP VLPK 38%Z 1%Z.
    frun_to 0x8bfa4%Z. SST.
    frun_to 0x8bfc0%Z. RDP VLPK 38%Z 2%Z.
    frun_to 0x8bfc4%Z. SST.
    frun_to 0x8bfd0%Z. RDQ VAR1 39%Z.
    frun_to 0x8c000%Z. RDP VLPK 39%Z 0%Z.
    frun_to 0x8c004%Z. SST.
    frun_to 0x8c020%Z. RDP VLPK 39%Z 1%Z.
    frun_to 0x8c024%Z. SST.
    frun_to 0x8c040%Z. RDP VLPK 39%Z 2%Z.
    frun_to 0x8c044%Z. SST.
    frun_to 0x8c050%Z. RDQ VAR1 40%Z.
    frun_to 0x8c080%Z. RDP VLPK 40%Z 0%Z.
    frun_to 0x8c084%Z. SST.
    frun_to 0x8c0a0%Z. RDP VLPK 40%Z 1%Z.
    frun_to 0x8c0a4%Z. SST.
    frun_to 0x8c0c0%Z. RDP VLPK 40%Z 2%Z.
    frun_to 0x8c0c4%Z. SST.
    frun_to 0x8c0d0%Z. RDQ VAR1 41%Z.
    frun_to 0x8c100%Z. RDP VLPK 41%Z 0%Z.
    frun_to 0x8c104%Z. SST.
    frun_to 0x8c120%Z. RDP VLPK 41%Z 1%Z.
    frun_to 0x8c124%Z. SST.
    frun_to 0x8c140%Z. RDP VLPK 41%Z 2%Z.
    frun_to 0x8c144%Z. SST.
    frun_to 0x8c150%Z. RDQ VAR1 42%Z.
    frun_to 0x8c180%Z. RDP VLPK 42%Z 0%Z.
    frun_to 0x8c184%Z. SST.
    frun_to 0x8c1a0%Z. RDP VLPK 42%Z 1%Z.
    frun_to 0x8c1a4%Z. SST.
    frun_to 0x8c1c0%Z. RDP VLPK 42%Z 2%Z.
    frun_to 0x8c1c4%Z. SST.
    frun_to 0x8c1d0%Z. RDQ VAR1 43%Z.
    frun_to 0x8c1f0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
End FC.
End ACeilS1.
