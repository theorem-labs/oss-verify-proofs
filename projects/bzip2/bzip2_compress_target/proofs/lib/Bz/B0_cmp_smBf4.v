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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA CmpCutSmB BzCFactsSmA BzCFactsSmB CmpSmKit CmpFsKit CmpHmKit.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section FC.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 a4 s3 s6 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P CO : Z).
  Variables (lp cb : zarr) (gs nSel totc : Z).
  Hypothesis CX : cctx_ok cx.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
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
    | |- context [Z.lxor ?e 18446744073709551615] => rewrite (zb_lxor_ones e) by lia
    | |- context [Z.lxor ?e 9223372036854775808] => rewrite (lxor_sign_small e) by lia      (* [comment removed for export] *)
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac fstep := let R := AsanKitB0.b_regs in AsanKit.a_zstep_nofb; bzl; AsanKitB0.b_flags R; AsanKit.a_try_lit_branch; AsanKitB0.b_try_guard.
  Ltac frun_to p := first [ AsanKit.a_at_pc p | AsanKit.a_pc_is_lit; fstep; frun_to p | fail 1 "frun_to: stuck before" p ].
  (* [comment removed for export] *)
  Ltac RDQ VAR1 k :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let AR1v := fresh "AR1v" in let RD := fresh "RD" in
      pose proof (VAR1 mm MU') as AR1v;
      pose proof (zb8_read2 b0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1v ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD;
      clear AR1v;
      change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
      pose proof (QB k ltac:(lia)) as ?QBk;
      lstep; clear RD; rewrite (zx16_lit (q k)) by lia end.
  (* [comment removed for export] *)
  Ltac RDP VLPK k j :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let LPKv := fresh "LPKv" in let RD := fresh "RD" in
      pose proof (VLPK mm MU') as LPKv;
      pose proof (ovw_read b0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPKv ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD;
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
    pose proof (u8arr_storeN_ok b0segs mm CO _ i 2 _ COST ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
    lstep; store_addr (CO + i)%Z; zb8_store2 COST i; rewrite unsigned_lit in COST by lia end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_fc7 : forall (m me : word -> option byte) (xt0 xt1 xt2 xa5 xs4 xs5 xs10 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 : word),
    rw_cells b0segs m (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
    mem_inv b0segs m -> munch [(P + 136, P + 1264)]%Z me m -> wmono b0segs me m ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me E (E + ESTATE_SIZE) ->
    frdW b0segs [(P + 136, P + 1264)]%Z me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (yt0 yt1 yt2 ya0 ya2 ya3 ya5 ys4 ys10 : word),
      rw_cells b0segs m' (P + 136) [C8 x136; C8 x144; C8 x152; C8 (Z_to_bv 64 (p 47 1)); C8 (Z_to_bv 64 (p 46 2)); C8 (Z_to_bv 64 (p 46 1)); C8 (Z_to_bv 64 (p 45 2)); C8 (Z_to_bv 64 (p 46 0)); C8 (Z_to_bv 64 (p 45 1)); C8 (Z_to_bv 64 (p 44 2)); C8 (Z_to_bv 64 (p 45 0)); C8 (Z_to_bv 64 (p 44 1)); C8 (Z_to_bv 64 (p 43 2)); C8 (Z_to_bv 64 (p 44 0)); C8 (Z_to_bv 64 (p 43 1)); C8 (Z_to_bv 64 (p 42 2)); C8 (Z_to_bv 64 (p 43 0)); C8 (Z_to_bv 64 (p 42 1)); C8 (Z_to_bv 64 (p 41 2)); C8 (Z_to_bv 64 (p 42 0)); C8 (Z_to_bv 64 (p 41 1)); C8 (Z_to_bv 64 (p 40 2)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
      mem_inv b0segs m' -> munch [(P + 136, P + 1264)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp yt0 yt1 yt2 s0 (Z_to_bv 64 (P)) ya0 (Z_to_bv 64 (E + 16 * q 47 + 51648)) ya2 ya3 a4 ya5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 ys4 (Z_to_bv 64 (p 47 0)) s6 s7 s8 (Z_to_bv 64 (CO)) ys10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
           F (Z_to_bv 64 0x8f14c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp xt0 xt1 xt2 s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (2 * gs + 82)) (Z_to_bv 64 (E + 16 * q 40 + 51648)) (Z_to_bv 64 (gs + 41)) (Z_to_bv 64 (A1)) a4 xa5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 xs4 xs5 s6 s7 s8 (Z_to_bv 64 (CO)) xs10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
         F (Z_to_bv 64 0x8eb60) fc None m (seg_rom b0segs)).
  Proof.
    intros m me xt0 xt1 xt2 xa5 xs4 xs5 xs10 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 SPL MI MU WM VAR1 SHa VLPK SHe V1552 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (QB 40 ltac:(lia)) as QB40.
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
    pose proof (PB 33 0 ltac:(lia) ltac:(lia)) as PB33_0.
    pose proof (PB 34 0 ltac:(lia) ltac:(lia)) as PB34_0.
    pose proof (PB 35 0 ltac:(lia) ltac:(lia)) as PB35_0.
    pose proof (PB 36 0 ltac:(lia) ltac:(lia)) as PB36_0.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 40 0 ltac:(lia) ltac:(lia)) as PB40_0.
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
    pose proof (PB 32 1 ltac:(lia) ltac:(lia)) as PB32_1.
    pose proof (PB 33 1 ltac:(lia) ltac:(lia)) as PB33_1.
    pose proof (PB 34 1 ltac:(lia) ltac:(lia)) as PB34_1.
    pose proof (PB 35 1 ltac:(lia) ltac:(lia)) as PB35_1.
    pose proof (PB 36 1 ltac:(lia) ltac:(lia)) as PB36_1.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 40 1 ltac:(lia) ltac:(lia)) as PB40_1.
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
    pose proof (PB 32 2 ltac:(lia) ltac:(lia)) as PB32_2.
    pose proof (PB 33 2 ltac:(lia) ltac:(lia)) as PB33_2.
    pose proof (PB 34 2 ltac:(lia) ltac:(lia)) as PB34_2.
    pose proof (PB 35 2 ltac:(lia) ltac:(lia)) as PB35_2.
    pose proof (PB 36 2 ltac:(lia) ltac:(lia)) as PB36_2.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    frun_to 0x8eb6c%Z. RDV V1552.
    frun_to 0x8eba0%Z. RDP VLPK 40%Z 2%Z.
    frun_to 0x8eba4%Z. SST.
    frun_to 0x8ebb0%Z. RDQ VAR1 41%Z.
    frun_to 0x8ebf0%Z. RDP VLPK 41%Z 0%Z.
    frun_to 0x8ebf4%Z. SST.
    frun_to 0x8ec18%Z. RDP VLPK 41%Z 1%Z.
    frun_to 0x8ec1c%Z. SST.
    frun_to 0x8ec38%Z. RDV V1552.
    frun_to 0x8ec48%Z. RDV V1552.
    frun_to 0x8ec7c%Z. RDP VLPK 41%Z 2%Z.
    frun_to 0x8ec80%Z. SST.
    frun_to 0x8ec8c%Z. RDQ VAR1 42%Z.
    frun_to 0x8eccc%Z. RDP VLPK 42%Z 0%Z.
    frun_to 0x8ecd0%Z. SST.
    frun_to 0x8ecf4%Z. RDP VLPK 42%Z 1%Z.
    frun_to 0x8ecf8%Z. SST.
    frun_to 0x8ed14%Z. RDV V1552.
    frun_to 0x8ed24%Z. RDV V1552.
    frun_to 0x8ed58%Z. RDP VLPK 42%Z 2%Z.
    frun_to 0x8ed5c%Z. SST.
    frun_to 0x8ed68%Z. RDQ VAR1 43%Z.
    frun_to 0x8eda8%Z. RDP VLPK 43%Z 0%Z.
    frun_to 0x8edac%Z. SST.
    frun_to 0x8edd0%Z. RDP VLPK 43%Z 1%Z.
    frun_to 0x8edd4%Z. SST.
    frun_to 0x8edf0%Z. RDV V1552.
    frun_to 0x8ee00%Z. RDV V1552.
    frun_to 0x8ee34%Z. RDP VLPK 43%Z 2%Z.
    frun_to 0x8ee38%Z. SST.
    frun_to 0x8ee44%Z. RDQ VAR1 44%Z.
    frun_to 0x8ee84%Z. RDP VLPK 44%Z 0%Z.
    frun_to 0x8ee88%Z. SST.
    frun_to 0x8eeac%Z. RDP VLPK 44%Z 1%Z.
    frun_to 0x8eeb0%Z. SST.
    frun_to 0x8eecc%Z. RDV V1552.
    frun_to 0x8eedc%Z. RDV V1552.
    frun_to 0x8ef10%Z. RDP VLPK 44%Z 2%Z.
    frun_to 0x8ef14%Z. SST.
    frun_to 0x8ef20%Z. RDQ VAR1 45%Z.
    frun_to 0x8ef60%Z. RDP VLPK 45%Z 0%Z.
    frun_to 0x8ef64%Z. SST.
    frun_to 0x8ef88%Z. RDP VLPK 45%Z 1%Z.
    frun_to 0x8ef8c%Z. SST.
    frun_to 0x8efa8%Z. RDV V1552.
    frun_to 0x8efb8%Z. RDV V1552.
    frun_to 0x8efec%Z. RDP VLPK 45%Z 2%Z.
    frun_to 0x8eff0%Z. SST.
    frun_to 0x8effc%Z. RDQ VAR1 46%Z.
    frun_to 0x8f03c%Z. RDP VLPK 46%Z 0%Z.
    frun_to 0x8f040%Z. SST.
    frun_to 0x8f064%Z. RDP VLPK 46%Z 1%Z.
    frun_to 0x8f068%Z. SST.
    frun_to 0x8f084%Z. RDV V1552.
    frun_to 0x8f094%Z. RDV V1552.
    frun_to 0x8f0c8%Z. RDP VLPK 46%Z 2%Z.
    frun_to 0x8f0cc%Z. SST.
    frun_to 0x8f0d8%Z. RDQ VAR1 47%Z.
    frun_to 0x8f118%Z. RDP VLPK 47%Z 0%Z.
    frun_to 0x8f13c%Z. RDP VLPK 47%Z 1%Z.
    frun_to 0x8f140%Z. SST.
    frun_to 0x8f14c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_fc8 : forall (m me : word -> option byte) (xt0 xt1 xt2 xa0 xa2 xa3 xa5 xs4 xs10 x136 x144 x152 : word),
    rw_cells b0segs m (P + 136) [C8 x136; C8 x144; C8 x152; C8 (Z_to_bv 64 (p 47 1)); C8 (Z_to_bv 64 (p 46 2)); C8 (Z_to_bv 64 (p 46 1)); C8 (Z_to_bv 64 (p 45 2)); C8 (Z_to_bv 64 (p 46 0)); C8 (Z_to_bv 64 (p 45 1)); C8 (Z_to_bv 64 (p 44 2)); C8 (Z_to_bv 64 (p 45 0)); C8 (Z_to_bv 64 (p 44 1)); C8 (Z_to_bv 64 (p 43 2)); C8 (Z_to_bv 64 (p 44 0)); C8 (Z_to_bv 64 (p 43 1)); C8 (Z_to_bv 64 (p 42 2)); C8 (Z_to_bv 64 (p 43 0)); C8 (Z_to_bv 64 (p 42 1)); C8 (Z_to_bv 64 (p 41 2)); C8 (Z_to_bv 64 (p 42 0)); C8 (Z_to_bv 64 (p 41 1)); C8 (Z_to_bv 64 (p 40 2)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
    u8arr b0segs m CO (zb8 cb 12) ->
    mem_inv b0segs m -> munch [(P + 136, P + 1264); (CO, CO + 12)]%Z me m -> wmono b0segs me m ->
    (forall m', munch [(P + 136, P + 1264); (CO, CO + 12)]%Z me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs [(P + 136, P + 1264); (CO, CO + 12)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 136, P + 1264); (CO, CO + 12)]%Z me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW b0segs [(P + 136, P + 1264); (CO, CO + 12)]%Z me E (E + ESTATE_SIZE) ->
    frdW b0segs [(P + 136, P + 1264); (CO, CO + 12)]%Z me (P + 128) [C8 (Z_to_bv 64 (E + 51640))] ->
    frdW b0segs [(P + 136, P + 1264); (CO, CO + 12)]%Z me (P + 1424) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW b0segs [(P + 136, P + 1264); (CO, CO + 12)]%Z me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (S0 S1 S2 : Z) (yt0 yt1 yt2 ya0 ya2 ya3 ya5 ya7 ys10 yt3 yt4 : word),
      S0 = psum arr1 lp gs 0 0 50 -> S1 = psum arr1 lp gs 1 0 50 -> S2 = psum arr1 lp gs 2 0 50 ->
      rw_cells b0segs m' (P + 136) [C8 (Z_to_bv 64 (p 48 2)); C8 (Z_to_bv 64 (p 48 1)); C8 (Z_to_bv 64 (p 47 2)); C8 (Z_to_bv 64 (p 47 1)); C8 (Z_to_bv 64 (p 46 2)); C8 (Z_to_bv 64 (p 46 1)); C8 (Z_to_bv 64 (p 45 2)); C8 (Z_to_bv 64 (p 46 0)); C8 (Z_to_bv 64 (p 45 1)); C8 (Z_to_bv 64 (p 44 2)); C8 (Z_to_bv 64 (p 45 0)); C8 (Z_to_bv 64 (p 44 1)); C8 (Z_to_bv 64 (p 43 2)); C8 (Z_to_bv 64 (p 44 0)); C8 (Z_to_bv 64 (p 43 1)); C8 (Z_to_bv 64 (p 42 2)); C8 (Z_to_bv 64 (p 43 0)); C8 (Z_to_bv 64 (p 42 1)); C8 (Z_to_bv 64 (p 41 2)); C8 (Z_to_bv 64 (p 42 0)); C8 (Z_to_bv 64 (p 41 1)); C8 (Z_to_bv 64 (p 40 2)); C8 (Z_to_bv 64 (p 41 0)); C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
      u8arr b0segs m' CO (zb8 (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 cb 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536)) 12) ->
      mem_inv b0segs m' -> munch [(P + 136, P + 1264); (CO, CO + 12)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp yt0 yt1 yt2 s0 (Z_to_bv 64 (P)) ya0 (Z_to_bv 64 ((-11))) ya2 ya3 a4 ya5 (Z_to_bv 64 (gs)) ya7 (Z_to_bv 64 (2147450880)) s3 (Z_to_bv 64 (258)) (Z_to_bv 64 (1032)) s6 s7 s8 (Z_to_bv 64 (CO)) ys10 s11 yt3 yt4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 ((-9))))
           F (Z_to_bv 64 0x8f920) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp xt0 xt1 xt2 s0 (Z_to_bv 64 (P)) xa0 (Z_to_bv 64 (E + 16 * q 47 + 51648)) xa2 xa3 a4 xa5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 xs4 (Z_to_bv 64 (p 47 0)) s6 s7 s8 (Z_to_bv 64 (CO)) xs10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
         F (Z_to_bv 64 0x8f14c) fc None m (seg_rom b0segs)).
  Proof.
    intros m me xt0 xt1 xt2 xa0 xa2 xa3 xa5 xs4 xs10 x136 x144 x152 SPL COST MI MU WM VAR1 SHa VLPK SHe V128 V1424 V1552 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat cb 12) as LC.
    pose proof (QB 47 ltac:(lia)) as QB47.
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
    pose proof (PB 33 0 ltac:(lia) ltac:(lia)) as PB33_0.
    pose proof (PB 34 0 ltac:(lia) ltac:(lia)) as PB34_0.
    pose proof (PB 35 0 ltac:(lia) ltac:(lia)) as PB35_0.
    pose proof (PB 36 0 ltac:(lia) ltac:(lia)) as PB36_0.
    pose proof (PB 37 0 ltac:(lia) ltac:(lia)) as PB37_0.
    pose proof (PB 38 0 ltac:(lia) ltac:(lia)) as PB38_0.
    pose proof (PB 39 0 ltac:(lia) ltac:(lia)) as PB39_0.
    pose proof (PB 40 0 ltac:(lia) ltac:(lia)) as PB40_0.
    pose proof (PB 41 0 ltac:(lia) ltac:(lia)) as PB41_0.
    pose proof (PB 42 0 ltac:(lia) ltac:(lia)) as PB42_0.
    pose proof (PB 43 0 ltac:(lia) ltac:(lia)) as PB43_0.
    pose proof (PB 44 0 ltac:(lia) ltac:(lia)) as PB44_0.
    pose proof (PB 45 0 ltac:(lia) ltac:(lia)) as PB45_0.
    pose proof (PB 46 0 ltac:(lia) ltac:(lia)) as PB46_0.
    pose proof (PB 47 0 ltac:(lia) ltac:(lia)) as PB47_0.
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
    pose proof (PB 32 1 ltac:(lia) ltac:(lia)) as PB32_1.
    pose proof (PB 33 1 ltac:(lia) ltac:(lia)) as PB33_1.
    pose proof (PB 34 1 ltac:(lia) ltac:(lia)) as PB34_1.
    pose proof (PB 35 1 ltac:(lia) ltac:(lia)) as PB35_1.
    pose proof (PB 36 1 ltac:(lia) ltac:(lia)) as PB36_1.
    pose proof (PB 37 1 ltac:(lia) ltac:(lia)) as PB37_1.
    pose proof (PB 38 1 ltac:(lia) ltac:(lia)) as PB38_1.
    pose proof (PB 39 1 ltac:(lia) ltac:(lia)) as PB39_1.
    pose proof (PB 40 1 ltac:(lia) ltac:(lia)) as PB40_1.
    pose proof (PB 41 1 ltac:(lia) ltac:(lia)) as PB41_1.
    pose proof (PB 42 1 ltac:(lia) ltac:(lia)) as PB42_1.
    pose proof (PB 43 1 ltac:(lia) ltac:(lia)) as PB43_1.
    pose proof (PB 44 1 ltac:(lia) ltac:(lia)) as PB44_1.
    pose proof (PB 45 1 ltac:(lia) ltac:(lia)) as PB45_1.
    pose proof (PB 46 1 ltac:(lia) ltac:(lia)) as PB46_1.
    pose proof (PB 47 1 ltac:(lia) ltac:(lia)) as PB47_1.
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
    pose proof (PB 32 2 ltac:(lia) ltac:(lia)) as PB32_2.
    pose proof (PB 33 2 ltac:(lia) ltac:(lia)) as PB33_2.
    pose proof (PB 34 2 ltac:(lia) ltac:(lia)) as PB34_2.
    pose proof (PB 35 2 ltac:(lia) ltac:(lia)) as PB35_2.
    pose proof (PB 36 2 ltac:(lia) ltac:(lia)) as PB36_2.
    pose proof (PB 37 2 ltac:(lia) ltac:(lia)) as PB37_2.
    pose proof (PB 38 2 ltac:(lia) ltac:(lia)) as PB38_2.
    pose proof (PB 39 2 ltac:(lia) ltac:(lia)) as PB39_2.
    pose proof (PB 40 2 ltac:(lia) ltac:(lia)) as PB40_2.
    pose proof (PB 41 2 ltac:(lia) ltac:(lia)) as PB41_2.
    pose proof (PB 42 2 ltac:(lia) ltac:(lia)) as PB42_2.
    pose proof (PB 43 2 ltac:(lia) ltac:(lia)) as PB43_2.
    pose proof (PB 44 2 ltac:(lia) ltac:(lia)) as PB44_2.
    pose proof (PB 45 2 ltac:(lia) ltac:(lia)) as PB45_2.
    pose proof (PB 46 2 ltac:(lia) ltac:(lia)) as PB46_2.
    frun_to 0x8f15c%Z. RDV V1552.
    frun_to 0x8f16c%Z. RDV V1552.
    frun_to 0x8f1a0%Z. RDP VLPK 47%Z 2%Z.
    frun_to 0x8f1a4%Z. SST.
    frun_to 0x8f1b0%Z. RDQ VAR1 48%Z.
    frun_to 0x8f1f0%Z. RDP VLPK 48%Z 0%Z.
    frun_to 0x8f214%Z. RDP VLPK 48%Z 1%Z.
    frun_to 0x8f218%Z. SST.
    frun_to 0x8f234%Z. RDV V1552.
    frun_to 0x8f244%Z. RDV V1552.
    frun_to 0x8f278%Z. RDP VLPK 48%Z 2%Z.
    frun_to 0x8f27c%Z. SST.
    frun_to 0x8f288%Z. RDQ VAR1 49%Z.
    frun_to 0x8f2c8%Z. RDP VLPK 49%Z 0%Z.
    frun_to 0x8f2f4%Z. RDP VLPK 49%Z 1%Z.
    frun_to 0x8f304%Z. lstep.
    frun_to 0x8f308%Z. lstep.
    frun_to 0x8f310%Z. lstep.
    frun_to 0x8f314%Z. lstep.
    frun_to 0x8f31c%Z. lstep.
    frun_to 0x8f320%Z. lstep.
    frun_to 0x8f328%Z. lstep.
    frun_to 0x8f32c%Z. lstep.
    frun_to 0x8f334%Z. lstep.
    frun_to 0x8f338%Z. lstep.
    frun_to 0x8f340%Z. lstep.
    frun_to 0x8f344%Z. lstep.
    frun_to 0x8f34c%Z. lstep.
    frun_to 0x8f350%Z. lstep.
    frun_to 0x8f358%Z. lstep.
    frun_to 0x8f35c%Z. lstep.
    frun_to 0x8f368%Z. lstep.
    frun_to 0x8f370%Z. lstep.
    frun_to 0x8f378%Z. lstep.
    frun_to 0x8f380%Z. lstep.
    frun_to 0x8f388%Z. lstep.
    frun_to 0x8f390%Z. lstep.
    frun_to 0x8f398%Z. lstep.
    frun_to 0x8f3a4%Z. lstep.
    frun_to 0x8f3ac%Z. lstep.
    frun_to 0x8f3b4%Z. lstep.
    frun_to 0x8f3bc%Z. lstep.
    frun_to 0x8f3c4%Z. lstep.
    frun_to 0x8f3cc%Z. lstep.
    frun_to 0x8f3d8%Z. lstep.
    frun_to 0x8f3e0%Z. RDP VLPK 49%Z 2%Z.
    frun_to 0x8f3e8%Z. lstep.
    frun_to 0x8f3f0%Z. lstep.
    frun_to 0x8f3f8%Z. lstep.
    frun_to 0x8f400%Z. lstep.
    frun_to 0x8f408%Z. lstep.
    frun_to 0x8f414%Z. lstep.
    frun_to 0x8f41c%Z. lstep.
    frun_to 0x8f424%Z. lstep.
    frun_to 0x8f42c%Z. lstep.
    frun_to 0x8f438%Z. lstep.
    frun_to 0x8f440%Z. lstep.
    frun_to 0x8f448%Z. lstep.
    frun_to 0x8f454%Z. lstep.
    frun_to 0x8f45c%Z. lstep.
    frun_to 0x8f468%Z. lstep.
    frun_to 0x8f47c%Z. CST COST 0%Z.
    frun_to 0x8f484%Z. RDV V128.
    frun_to 0x8f49c%Z. CST COST 2%Z.
    frun_to 0x8f4b0%Z. lstep.
    frun_to 0x8f4b4%Z. lstep.
    frun_to 0x8f4bc%Z. lstep.
    frun_to 0x8f4c0%Z. lstep.
    frun_to 0x8f4c8%Z. lstep.
    frun_to 0x8f4cc%Z. lstep.
    frun_to 0x8f4d4%Z. lstep.
    frun_to 0x8f4d8%Z. lstep.
    frun_to 0x8f4e0%Z. lstep.
    frun_to 0x8f4e4%Z. lstep.
    frun_to 0x8f4ec%Z. lstep.
    frun_to 0x8f4f0%Z. lstep.
    frun_to 0x8f4f8%Z. lstep.
    frun_to 0x8f4fc%Z. lstep.
    frun_to 0x8f504%Z. lstep.
    frun_to 0x8f508%Z. lstep.
    frun_to 0x8f514%Z. lstep.
    frun_to 0x8f51c%Z. lstep.
    frun_to 0x8f524%Z. lstep.
    frun_to 0x8f52c%Z. lstep.
    frun_to 0x8f534%Z. lstep.
    frun_to 0x8f53c%Z. lstep.
    frun_to 0x8f544%Z. lstep.
    frun_to 0x8f550%Z. lstep.
    frun_to 0x8f558%Z. lstep.
    frun_to 0x8f560%Z. lstep.
    frun_to 0x8f568%Z. lstep.
    frun_to 0x8f570%Z. lstep.
    frun_to 0x8f578%Z. lstep.
    frun_to 0x8f580%Z. lstep.
    frun_to 0x8f584%Z. lstep.
    frun_to 0x8f58c%Z. lstep.
    frun_to 0x8f598%Z. lstep.
    frun_to 0x8f5a0%Z. lstep.
    frun_to 0x8f5a8%Z. lstep.
    frun_to 0x8f5b0%Z. lstep.
    frun_to 0x8f5b8%Z. lstep.
    frun_to 0x8f5c4%Z. lstep.
    frun_to 0x8f5cc%Z. lstep.
    frun_to 0x8f5d4%Z. lstep.
    frun_to 0x8f5dc%Z. lstep.
    frun_to 0x8f5e8%Z. lstep.
    frun_to 0x8f5f0%Z. lstep.
    frun_to 0x8f5f8%Z. lstep.
    frun_to 0x8f604%Z. lstep.
    frun_to 0x8f60c%Z. lstep.
    frun_to 0x8f618%Z. RDV V1424.
    frun_to 0x8f61c%Z. lstep.
    frun_to 0x8f634%Z. CST COST 4%Z.
    frun_to 0x8f648%Z. CST COST 6%Z.
    frun_to 0x8f654%Z. lstep.
    frun_to 0x8f658%Z. lstep.
    frun_to 0x8f660%Z. lstep.
    frun_to 0x8f664%Z. lstep.
    frun_to 0x8f66c%Z. lstep.
    frun_to 0x8f670%Z. lstep.
    frun_to 0x8f678%Z. lstep.
    frun_to 0x8f67c%Z. lstep.
    frun_to 0x8f684%Z. lstep.
    frun_to 0x8f688%Z. lstep.
    frun_to 0x8f690%Z. lstep.
    frun_to 0x8f694%Z. lstep.
    frun_to 0x8f69c%Z. lstep.
    frun_to 0x8f6a0%Z. lstep.
    frun_to 0x8f6a8%Z. lstep.
    frun_to 0x8f6ac%Z. lstep.
    frun_to 0x8f6b4%Z. lstep.
    frun_to 0x8f6b8%Z. lstep.
    frun_to 0x8f6c4%Z. lstep.
    frun_to 0x8f6cc%Z. lstep.
    frun_to 0x8f6d4%Z. lstep.
    frun_to 0x8f6dc%Z. lstep.
    frun_to 0x8f6e4%Z. lstep.
    frun_to 0x8f6ec%Z. lstep.
    frun_to 0x8f6f4%Z. lstep.
    frun_to 0x8f700%Z. lstep.
    frun_to 0x8f708%Z. lstep.
    frun_to 0x8f710%Z. lstep.
    frun_to 0x8f718%Z. lstep.
    frun_to 0x8f720%Z. lstep.
    frun_to 0x8f728%Z. lstep.
    frun_to 0x8f730%Z. lstep.
    frun_to 0x8f734%Z. lstep.
    frun_to 0x8f73c%Z. lstep.
    frun_to 0x8f748%Z. lstep.
    frun_to 0x8f750%Z. lstep.
    frun_to 0x8f758%Z. lstep.
    frun_to 0x8f760%Z. lstep.
    frun_to 0x8f768%Z. lstep.
    frun_to 0x8f774%Z. lstep.
    frun_to 0x8f77c%Z. lstep.
    frun_to 0x8f784%Z. lstep.
    frun_to 0x8f78c%Z. lstep.
    frun_to 0x8f798%Z. lstep.
    frun_to 0x8f7a0%Z. lstep.
    frun_to 0x8f7a8%Z. lstep.
    frun_to 0x8f7b4%Z. lstep.
    frun_to 0x8f7bc%Z. lstep.
    frun_to 0x8f7c8%Z. lstep.
    frun_to 0x8f7dc%Z. CST COST 8%Z.
    frun_to 0x8f7f0%Z. CST COST 10%Z.
    frun_to 0x8f920%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0 + p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0 + p 21 0 + p 22 0 + p 23 0 + p 24 0 + p 25 0 + p 26 0 + p 27 0 + p 28 0 + p 29 0 + p 30 0 + p 31 0 + p 32 0 + p 33 0 + p 34 0 + p 35 0 + p 36 0 + p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0 + p 42 0 + p 43 0 + p 44 0 + p 45 0 + p 46 0 + p 47 0 + p 48 0 + p 49 0)%Z (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1 + p 11 1 + p 12 1 + p 13 1 + p 14 1 + p 15 1 + p 16 1 + p 17 1 + p 18 1 + p 19 1 + p 20 1 + p 21 1 + p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1 + p 27 1 + p 28 1 + p 29 1 + p 30 1 + p 31 1 + p 32 1 + p 33 1 + p 34 1 + p 35 1 + p 36 1 + p 37 1 + p 38 1 + p 39 1 + p 40 1 + p 41 1 + p 42 1 + p 43 1 + p 44 1 + p 45 1 + p 46 1 + p 47 1 + p 48 1 + p 49 1)%Z (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2 + p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2 + p 21 2 + p 22 2 + p 23 2 + p 24 2 + p 25 2 + p 26 2 + p 27 2 + p 28 2 + p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2 + p 34 2 + p 35 2 + p 36 2 + p 37 2 + p 38 2 + p 39 2 + p 40 2 + p 41 2 + p 42 2 + p 43 2 + p 44 2 + p 45 2 + p 46 2 + p 47 2 + p 48 2 + p 49 2)%Z _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq
      | rewrite psum50_eq; lia | rewrite psum50_eq; lia | rewrite psum50_eq; lia
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | first [exact COST | lazymatch type of COST with u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | exact MU | exact WM ].
  Qed.
End FC.
End ACeilS1.
