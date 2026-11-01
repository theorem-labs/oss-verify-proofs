(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA CmpCutSmB BzCFactsSmA BzCFactsSmB CmpSmKit CmpFsKit CmpHmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
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
  Ltac RDV V :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let RO := fresh "RO" in pose proof (V mm MU') as RO; lstep; clear RO end.
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  Ltac CST COST i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_storeN_ok a0segs mm CO _ i 2 _ COST ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
    lstep; store_addr (CO + i)%Z; zb8_store2 COST i; rewrite unsigned_lit in COST by lia end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fc5 : forall (m me : word -> option byte) (xa2 xa4 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x392 x1312 x1320 x1328 x1336 x1360 : word),
    rw_cells a0segs m (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 (Z_to_bv 64 (p 42 2)); C8 x392; C8 (Z_to_bv 64 (p 42 1)); C8 (Z_to_bv 64 (p 42 0)); C8 (Z_to_bv 64 (p 41 2)); C8 (Z_to_bv 64 (p 41 1)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 40 2)); C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 2)); C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
    rw_cells a0segs m (P + 1344) [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (999999999)); C8 x1360; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (CO)); C8 (Z_to_bv 64 (FV)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 (A)); C8 (Z_to_bv 64 (totc)); C8 (Z_to_bv 64 (gs))] ->
    mem_inv a0segs m -> munch [(P + 232, P + 1344); (P + 1360, P + 1368)]%Z me m -> wmono a0segs me m ->
    (forall m', munch [(P + 232, P + 1344); (P + 1360, P + 1368)]%Z me m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW a0segs [(P + 232, P + 1344); (P + 1360, P + 1368)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 232, P + 1344); (P + 1360, P + 1368)]%Z me m' -> u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW a0segs [(P + 232, P + 1344); (P + 1360, P + 1368)]%Z me E (E + ESTATE_SIZE) ->
    (forall m',
      rw_cells a0segs m' (P + 232) [C8 (Z_to_bv 64 (p 49 1)); C8 (Z_to_bv 64 (p 49 0)); C8 (Z_to_bv 64 (p 48 2)); C8 (Z_to_bv 64 (p 48 1)); C8 (Z_to_bv 64 (p 48 0)); C8 (Z_to_bv 64 (p 47 2)); C8 (Z_to_bv 64 (p 47 1)); C8 (Z_to_bv 64 (p 47 0)); C8 (Z_to_bv 64 (p 46 2)); C8 (Z_to_bv 64 (p 46 1)); C8 (Z_to_bv 64 (p 46 0)); C8 (Z_to_bv 64 (p 45 2)); C8 (Z_to_bv 64 (p 45 1)); C8 (Z_to_bv 64 (p 45 0)); C8 (Z_to_bv 64 (p 44 0)); C8 (Z_to_bv 64 (p 43 2)); C8 (Z_to_bv 64 (p 43 1)); C8 (Z_to_bv 64 (p 44 2)); C8 (Z_to_bv 64 (p 43 0)); C8 (Z_to_bv 64 (p 42 2)); C8 (Z_to_bv 64 (p 44 1)); C8 (Z_to_bv 64 (p 42 1)); C8 (Z_to_bv 64 (p 42 0)); C8 (Z_to_bv 64 (p 41 2)); C8 (Z_to_bv 64 (p 41 1)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 40 2)); C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (E + 16 * q 49 + 51648)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs + 50))] ->
      rw_cells a0segs m' (P + 1344) [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (999999999)); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (CO)); C8 (Z_to_bv 64 (FV)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 (A)); C8 (Z_to_bv 64 (totc)); C8 (Z_to_bv 64 (gs))] ->
      mem_inv a0segs m' -> munch [(P + 232, P + 1344); (P + 1360, P + 1368)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 4 0 + p 5 0 + p 6 0)) (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1)) (Z_to_bv 64 (p 31 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (p 37 2 + p 38 2)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)) (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)) (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2)) (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2)) (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1)) (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1)) (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2)) (Z_to_bv 64 (p 29 2 + p 30 2)) (Z_to_bv 64 (p 2 1 + p 3 1)) (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2)) (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)) (Z_to_bv 64 (p 2 0 + p 3 0)) (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)) (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2)))
           F (Z_to_bv 64 0x8c708) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 (p 3 2)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (p 4 1)) (Z_to_bv 64 (p 0 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) (Z_to_bv 64 (E + 16 * q 43 + 51640)) xa2 (Z_to_bv 64 (E + 51640)) xa4 (Z_to_bv 64 (p 42 0)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (49)) (Z_to_bv 64 (p 1 2)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (p 2 0)) (Z_to_bv 64 (p 2 2)) (Z_to_bv 64 (p 2 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (gs + 49)))
         F (Z_to_bv 64 0x8c1f0) fc None m (seg_rom a0segs)).
  Proof using CX HA Hgs HgsM HM ZB QB PB PD.
    intros m me xa2 xa4 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x392 x1312 x1320 x1328 x1336 x1360 Fr Fh Inv Mu Mono Arr1At ShA1 LpAt ShE Kont.
    clear CEP PHI COL COH NG6 HnS Htc.
    openCX. bz_ceil. unfold ESTATE_SIZE in ShE.
    pose proof (QB 43 ltac:(lia)) as Q43.
    do 4 lstep; RDP LpAt 43 0; SST; fstep.
    do 4 lstep; RDP LpAt 43 1; SST; fstep.
    do 4 lstep; RDP LpAt 43 2; SST; fstep.
    lstep; RDQ Arr1At 44; do 5 lstep; fstep.
    do 4 lstep; RDP LpAt 44 0; SST; fstep.
    do 4 lstep; RDP LpAt 44 1; SST; fstep.
    do 4 lstep; RDP LpAt 44 2; SST; fstep.
    RDQ Arr1At 45; do 5 lstep; fstep.
    do 4 lstep; RDP LpAt 45 0; SST; fstep.
    do 4 lstep; RDP LpAt 45 1; SST; fstep.
    do 4 lstep; RDP LpAt 45 2; SST; fstep.
    RDQ Arr1At 46; do 5 lstep; fstep.
    do 4 lstep; RDP LpAt 46 0; SST; fstep.
    do 4 lstep; RDP LpAt 46 1; SST; fstep.
    do 4 lstep; RDP LpAt 46 2; SST; fstep.
    RDQ Arr1At 47; do 5 lstep; fstep.
    do 4 lstep; RDP LpAt 47 0; SST; fstep.
    do 4 lstep; RDP LpAt 47 1; SST; fstep.
    do 4 lstep; RDP LpAt 47 2; SST; fstep.
    RDQ Arr1At 48; do 5 lstep; fstep.
    do 4 lstep; RDP LpAt 48 0; SST; fstep.
    do 4 lstep; RDP LpAt 48 1; SST; fstep.
    do 4 lstep; RDP LpAt 48 2; SST; fstep.
    lstep; RDQ Arr1At 49; do 5 lstep; fstep.
    do 4 lstep; RDP LpAt 49 0; SST; fstep.
    do 5 SST; do 4 lstep; RDP LpAt 49 1; SST; fstep.
    frun_to 574840; SST.
    frun_to 575008; SST.
    frun_to 575048; SST.
    frun_to 575064; SST.
    frun_to 575080; SST.
    frun_to 575240.
    replace (p 1 0 + p 0 0 + (p 2 0 + p 3 0)) with (p 0 0 + p 1 0 + p 2 0 + p 3 0) by lia.
    replace (p 1 1 + p 0 1 + (p 2 1 + p 3 1)) with (p 0 1 + p 1 1 + p 2 1 + p 3 1) by lia.
    replace (p 1 2 + p 0 2 + (p 2 2 + p 3 2)) with (p 0 2 + p 1 2 + p 2 2 + p 3 2) by lia.
    replace (E + 51640 + q 49 * 16 + 8) with (E + 16 * q 49 + 51648) in Fr by lia.
    apply Kont; assumption.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fc6 : forall (m me : word -> option byte),
    rw_cells a0segs m (P + 232) [C8 (Z_to_bv 64 (p 49 1)); C8 (Z_to_bv 64 (p 49 0)); C8 (Z_to_bv 64 (p 48 2)); C8 (Z_to_bv 64 (p 48 1)); C8 (Z_to_bv 64 (p 48 0)); C8 (Z_to_bv 64 (p 47 2)); C8 (Z_to_bv 64 (p 47 1)); C8 (Z_to_bv 64 (p 47 0)); C8 (Z_to_bv 64 (p 46 2)); C8 (Z_to_bv 64 (p 46 1)); C8 (Z_to_bv 64 (p 46 0)); C8 (Z_to_bv 64 (p 45 2)); C8 (Z_to_bv 64 (p 45 1)); C8 (Z_to_bv 64 (p 45 0)); C8 (Z_to_bv 64 (p 44 0)); C8 (Z_to_bv 64 (p 43 2)); C8 (Z_to_bv 64 (p 43 1)); C8 (Z_to_bv 64 (p 44 2)); C8 (Z_to_bv 64 (p 43 0)); C8 (Z_to_bv 64 (p 42 2)); C8 (Z_to_bv 64 (p 44 1)); C8 (Z_to_bv 64 (p 42 1)); C8 (Z_to_bv 64 (p 42 0)); C8 (Z_to_bv 64 (p 41 2)); C8 (Z_to_bv 64 (p 41 1)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 40 2)); C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (E + 16 * q 49 + 51648)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs + 50))] ->
    rw_cells a0segs m (P + 1344) [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (999999999)); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (CO)); C8 (Z_to_bv 64 (FV)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 (A)); C8 (Z_to_bv 64 (totc)); C8 (Z_to_bv 64 (gs))] ->
    u8arr a0segs m CO (zb8 cb 12) ->
    mem_inv a0segs m -> munch [(P + 232, P + 1344); (CO, CO + 12)]%Z me m -> wmono a0segs me m ->
    (forall m', munch [(P + 232, P + 1344); (CO, CO + 12)]%Z me m' -> u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW a0segs [(P + 232, P + 1344); (CO, CO + 12)]%Z me E (E + ESTATE_SIZE) ->
    frdW a0segs [(P + 232, P + 1344); (CO, CO + 12)]%Z me (P + 176) [C8 (Z_to_bv 64 (E + 668))] ->
    frdW a0segs [(P + 232, P + 1344); (CO, CO + 12)]%Z me (P + 184) [C8 (Z_to_bv 64 (SHE + 83))] ->
    frdW a0segs [(P + 232, P + 1344); (CO, CO + 12)]%Z me (P + 192) [C8 (Z_to_bv 64 (A))] ->
    frdW a0segs [(P + 232, P + 1344); (CO, CO + 12)]%Z me (P + 200) [C8 (Z_to_bv 64 (nG))] ->
    frdW a0segs [(P + 232, P + 1344); (CO, CO + 12)]%Z me (P + 208) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW a0segs [(P + 232, P + 1344); (CO, CO + 12)]%Z me (P + 216) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (S0 S1 S2 : Z) (yra yt0 yt1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 : word),
      S0 = psum arr1 lp gs 0 0 50 -> S1 = psum arr1 lp gs 1 0 50 -> S2 = psum arr1 lp gs 2 0 50 ->
      rw_cells a0segs m' (P + 232) [C8 (Z_to_bv 64 (p 49 1)); C8 (Z_to_bv 64 (p 49 0)); C8 (Z_to_bv 64 (p 48 2)); C8 (Z_to_bv 64 (p 48 1)); C8 (Z_to_bv 64 (p 48 0)); C8 (Z_to_bv 64 (p 47 2)); C8 (Z_to_bv 64 (p 47 1)); C8 (Z_to_bv 64 (p 47 0)); C8 (Z_to_bv 64 (p 46 2)); C8 (Z_to_bv 64 (p 46 1)); C8 (Z_to_bv 64 (p 46 0)); C8 (Z_to_bv 64 (p 45 2)); C8 (Z_to_bv 64 (p 45 1)); C8 (Z_to_bv 64 (p 45 0)); C8 (Z_to_bv 64 (p 44 0)); C8 (Z_to_bv 64 (p 43 2)); C8 (Z_to_bv 64 (p 43 1)); C8 (Z_to_bv 64 (p 44 2)); C8 (Z_to_bv 64 (p 43 0)); C8 (Z_to_bv 64 (p 42 2)); C8 (Z_to_bv 64 (p 44 1)); C8 (Z_to_bv 64 (p 42 1)); C8 (Z_to_bv 64 (p 42 0)); C8 (Z_to_bv 64 (p 41 2)); C8 (Z_to_bv 64 (p 41 1)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 40 2)); C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 37 2 + p 38 2)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 37 1 + p 38 1)); C8 (Z_to_bv 64 (p 37 0 + p 38 0)); C8 (Z_to_bv 64 (E + 16 * q 49 + 51648)); C8 (Z_to_bv 64 (p 29 0 + p 30 0)); C8 (Z_to_bv 64 (1)); C8 (Z_to_bv 64 (49)); C8 (Z_to_bv 64 (gs + 49)); C8 (Z_to_bv 64 (gs + 50))] ->
      rw_cells a0segs m' (P + 1344) [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (999999999)); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (CO)); C8 (Z_to_bv 64 (FV)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 (A)); C8 (Z_to_bv 64 (totc)); C8 (Z_to_bv 64 (gs))] ->
      u8arr a0segs m' CO (zb8 (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 cb 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536)) 12) ->
      mem_inv a0segs m' -> munch [(P + 232, P + 1344); (CO, CO + 12)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR yra (Z_to_bv 64 (P)) gp tp yt0 yt1 (Z_to_bv 64 (CO)) s0 (Z_to_bv 64 (P)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (49)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (A)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 (nG)) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)))
           F (Z_to_bv 64 0x8ca4c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 (p 22 0 + p 23 0 + p 24 0)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 4 0 + p 5 0 + p 6 0)) (Z_to_bv 64 (p 0 1 + p 1 1 + p 2 1 + p 3 1)) (Z_to_bv 64 (p 31 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (p 37 2 + p 38 2)) (Z_to_bv 64 (p 29 0 + p 30 0 + p 31 0)) (Z_to_bv 64 (p 22 1 + p 23 1 + p 24 1)) (Z_to_bv 64 (p 11 0 + p 12 0 + p 13 0)) (Z_to_bv 64 (p 0 0 + p 1 0 + p 2 0 + p 3 0)) (Z_to_bv 64 (p 4 2 + p 5 2 + p 6 2)) (Z_to_bv 64 (p 22 2 + p 23 2 + p 24 2)) (Z_to_bv 64 (p 0 2 + p 1 2 + p 2 2 + p 3 2)) (Z_to_bv 64 (p 16 0 + p 17 0 + p 18 0)) (Z_to_bv 64 (p 7 1 + p 8 1 + p 9 1)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (p 11 1 + p 12 1 + p 13 1)) (Z_to_bv 64 (p 29 1 + p 30 1 + p 31 1)) (Z_to_bv 64 (p 11 2 + p 12 2 + p 13 2)) (Z_to_bv 64 (p 29 2 + p 30 2)) (Z_to_bv 64 (p 2 1 + p 3 1)) (Z_to_bv 64 (p 7 2 + p 8 2 + p 9 2)) (Z_to_bv 64 (p 4 1 + p 5 1 + p 6 1)) (Z_to_bv 64 (p 2 0 + p 3 0)) (Z_to_bv 64 (p 7 0 + p 8 0 + p 9 0)) (Z_to_bv 64 (p 16 1 + p 17 1 + p 18 1)) (Z_to_bv 64 (p 16 2 + p 17 2 + p 18 2)))
         F (Z_to_bv 64 0x8c708) fc None m (seg_rom a0segs)).
  Proof using CX CEP PHI COL COH HA QB PB PD.
    intros m me Fr Fh Cost Inv Mu Mono LpAt ShE SlotE668 SlotSHE SlotA SlotNG SlotE37708 SlotA1 Kont.
    clear Hgs HgsM HM ZB NG6 HnS Htc.
    assert (SumB : forall j, 0 <= j < 3 -> forall n k0 : nat, (k0 + n <= 50)%nat ->
              0 <= psum arr1 lp gs j k0 n <= Z.of_nat n * 2097151).
    { intros j Rj n; induction n as [|n IHn]; intros k0 Rk; cbn [psum]; [lia|].
      pose proof (PB (Z.of_nat k0) j ltac:(lia) Rj) as Bk0.
      specialize (IHn (S k0) ltac:(lia)); lia. }
    frun_to 575844.
    RDP LpAt 49 2.
    frun_to 575968.
    pose proof (SumB 0 ltac:(lia) 50%nat 0%nat ltac:(lia)) as Sum0B.
    pose proof (SumB 1 ltac:(lia) 50%nat 0%nat ltac:(lia)) as Sum1B.
    pose proof (SumB 2 ltac:(lia) 50%nat 0%nat ltac:(lia)) as Sum2B.
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?c0) (Z_to_bv 64 ?c1) (Z_to_bv 64 ?c2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        replace c0 with (psum arr1 lp gs 0 0 50) by (rewrite psum50_eq; ring);
        replace c1 with (psum arr1 lp gs 1 0 50) by (rewrite psum50_eq; ring);
        replace c2 with (psum arr1 lp gs 2 0 50) by (rewrite psum50_eq; ring)
    end.
    frun_to 575984.
    CST Cost 0. CST Cost 2. CST Cost 4. CST Cost 6. CST Cost 8. CST Cost 10.
    RDV SlotE668. RDV SlotA1. RDV SlotSHE. RDV SlotNG.
    fstep. RDV SlotA. RDV SlotE37708.
    frun_to 576076.
    eapply Kont; [reflexivity | reflexivity | reflexivity | assumption ..].
  Qed.
End FC.
End ACeilS1.
