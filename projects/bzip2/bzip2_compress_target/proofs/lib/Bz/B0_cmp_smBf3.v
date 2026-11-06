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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_fc5 : forall (m me : word -> option byte) (xt0 xt1 xt2 xa1 xa2 xa3 xa5 xs4 xs5 xs10 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x648 : word),
    rw_cells b0segs m (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 (Z_to_bv 64 (p 26 2)); C8 x648; C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
    mem_inv b0segs m -> munch [(P + 136, P + 1264)]%Z me m -> wmono b0segs me m ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me E (E + ESTATE_SIZE) ->
    frdW b0segs [(P + 136, P + 1264)]%Z me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (yt0 yt1 yt2 ya2 ya3 ya5 ys4 ys5 ys10 : word),
      rw_cells b0segs m' (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
      mem_inv b0segs m' -> munch [(P + 136, P + 1264)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp yt0 yt1 yt2 s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs + 68)) (Z_to_bv 64 (E + 16 * q 33 + 51648)) ya2 ya3 a4 ya5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 ys4 ys5 s6 s7 s8 (Z_to_bv 64 (CO)) ys10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
           F (Z_to_bv 64 0x8e584) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp xt0 xt1 xt2 s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs + 54)) xa1 xa2 xa3 a4 xa5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 xs4 xs5 s6 s7 s8 (Z_to_bv 64 (CO)) xs10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
         F (Z_to_bv 64 0x8dfa8) fc None m (seg_rom b0segs)).
  Proof.
    intros m me xt0 xt1 xt2 xa1 xa2 xa3 xa5 xs4 xs5 xs10 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x648 SPL MI MU WM VAR1 SHa VLPK SHe V1552 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
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
    frun_to 0x8dfa8%Z. RDQ VAR1 27%Z.
    frun_to 0x8dfe8%Z. RDP VLPK 27%Z 0%Z.
    frun_to 0x8dfec%Z. SST.
    frun_to 0x8e010%Z. RDP VLPK 27%Z 1%Z.
    frun_to 0x8e014%Z. SST.
    frun_to 0x8e030%Z. RDV V1552.
    frun_to 0x8e040%Z. RDV V1552.
    frun_to 0x8e074%Z. RDP VLPK 27%Z 2%Z.
    frun_to 0x8e078%Z. SST.
    frun_to 0x8e084%Z. RDQ VAR1 28%Z.
    frun_to 0x8e0c4%Z. RDP VLPK 28%Z 0%Z.
    frun_to 0x8e0c8%Z. SST.
    frun_to 0x8e0ec%Z. RDP VLPK 28%Z 1%Z.
    frun_to 0x8e0f0%Z. SST.
    frun_to 0x8e10c%Z. RDV V1552.
    frun_to 0x8e11c%Z. RDV V1552.
    frun_to 0x8e150%Z. RDP VLPK 28%Z 2%Z.
    frun_to 0x8e154%Z. SST.
    frun_to 0x8e160%Z. RDQ VAR1 29%Z.
    frun_to 0x8e1a0%Z. RDP VLPK 29%Z 0%Z.
    frun_to 0x8e1a4%Z. SST.
    frun_to 0x8e1c8%Z. RDP VLPK 29%Z 1%Z.
    frun_to 0x8e1cc%Z. SST.
    frun_to 0x8e1e8%Z. RDV V1552.
    frun_to 0x8e1f8%Z. RDV V1552.
    frun_to 0x8e22c%Z. RDP VLPK 29%Z 2%Z.
    frun_to 0x8e230%Z. SST.
    frun_to 0x8e23c%Z. RDQ VAR1 30%Z.
    frun_to 0x8e27c%Z. RDP VLPK 30%Z 0%Z.
    frun_to 0x8e280%Z. SST.
    frun_to 0x8e2a4%Z. RDP VLPK 30%Z 1%Z.
    frun_to 0x8e2a8%Z. SST.
    frun_to 0x8e2c4%Z. RDV V1552.
    frun_to 0x8e2d4%Z. RDV V1552.
    frun_to 0x8e308%Z. RDP VLPK 30%Z 2%Z.
    frun_to 0x8e30c%Z. SST.
    frun_to 0x8e318%Z. RDQ VAR1 31%Z.
    frun_to 0x8e358%Z. RDP VLPK 31%Z 0%Z.
    frun_to 0x8e35c%Z. SST.
    frun_to 0x8e380%Z. RDP VLPK 31%Z 1%Z.
    frun_to 0x8e384%Z. SST.
    frun_to 0x8e3a0%Z. RDV V1552.
    frun_to 0x8e3b0%Z. RDV V1552.
    frun_to 0x8e3e4%Z. RDP VLPK 31%Z 2%Z.
    frun_to 0x8e3e8%Z. SST.
    frun_to 0x8e3f4%Z. RDQ VAR1 32%Z.
    frun_to 0x8e434%Z. RDP VLPK 32%Z 0%Z.
    frun_to 0x8e438%Z. SST.
    frun_to 0x8e45c%Z. RDP VLPK 32%Z 1%Z.
    frun_to 0x8e460%Z. SST.
    frun_to 0x8e47c%Z. RDV V1552.
    frun_to 0x8e48c%Z. RDV V1552.
    frun_to 0x8e4c0%Z. RDP VLPK 32%Z 2%Z.
    frun_to 0x8e4c4%Z. SST.
    frun_to 0x8e4d0%Z. RDQ VAR1 33%Z.
    frun_to 0x8e510%Z. RDP VLPK 33%Z 0%Z.
    frun_to 0x8e514%Z. SST.
    frun_to 0x8e538%Z. RDP VLPK 33%Z 1%Z.
    frun_to 0x8e53c%Z. SST.
    frun_to 0x8e558%Z. RDV V1552.
    frun_to 0x8e568%Z. RDV V1552.
    frun_to 0x8e584%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_fc6 : forall (m me : word -> option byte) (xt0 xt1 xt2 xa2 xa3 xa5 xs4 xs5 xs10 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 : word),
    rw_cells b0segs m (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
    mem_inv b0segs m -> munch [(P + 136, P + 1264)]%Z me m -> wmono b0segs me m ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me E (E + ESTATE_SIZE) ->
    frdW b0segs [(P + 136, P + 1264)]%Z me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (yt0 yt1 yt2 ya5 ys4 ys5 ys10 : word),
      rw_cells b0segs m' (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 (Z_to_bv 64 (p 40 1)); C8 (Z_to_bv 64 (p 39 2)); C8 (Z_to_bv 64 (p 40 0)); C8 (Z_to_bv 64 (p 39 1)); C8 (Z_to_bv 64 (p 38 2)); C8 (Z_to_bv 64 (p 39 0)); C8 (Z_to_bv 64 (p 38 1)); C8 (Z_to_bv 64 (p 37 2)); C8 (Z_to_bv 64 (p 38 0)); C8 (Z_to_bv 64 (p 37 1)); C8 (Z_to_bv 64 (p 36 2)); C8 (Z_to_bv 64 (p 37 0)); C8 (Z_to_bv 64 (p 36 1)); C8 (Z_to_bv 64 (p 35 2)); C8 (Z_to_bv 64 (p 36 0)); C8 (Z_to_bv 64 (p 35 1)); C8 (Z_to_bv 64 (p 34 2)); C8 (Z_to_bv 64 (p 35 0)); C8 (Z_to_bv 64 (p 34 1)); C8 (Z_to_bv 64 (p 33 2)); C8 (Z_to_bv 64 (p 34 0)); C8 (Z_to_bv 64 (p 33 1)); C8 (Z_to_bv 64 (p 32 2)); C8 (Z_to_bv 64 (p 33 0)); C8 (Z_to_bv 64 (p 32 1)); C8 (Z_to_bv 64 (p 31 2)); C8 (Z_to_bv 64 (p 32 0)); C8 (Z_to_bv 64 (p 31 1)); C8 (Z_to_bv 64 (p 30 2)); C8 (Z_to_bv 64 (p 31 0)); C8 (Z_to_bv 64 (p 30 1)); C8 (Z_to_bv 64 (p 29 2)); C8 (Z_to_bv 64 (p 30 0)); C8 (Z_to_bv 64 (p 29 1)); C8 (Z_to_bv 64 (p 28 2)); C8 (Z_to_bv 64 (p 29 0)); C8 (Z_to_bv 64 (p 28 1)); C8 (Z_to_bv 64 (p 27 2)); C8 (Z_to_bv 64 (p 28 0)); C8 (Z_to_bv 64 (p 27 1)); C8 (Z_to_bv 64 (p 26 2)); C8 (Z_to_bv 64 (p 27 0)); C8 (Z_to_bv 64 (p 26 1)); C8 (Z_to_bv 64 (p 25 2)); C8 (Z_to_bv 64 (p 26 0)); C8 (Z_to_bv 64 (p 25 1)); C8 (Z_to_bv 64 (p 24 2)); C8 (Z_to_bv 64 (p 25 0)); C8 (Z_to_bv 64 (p 24 1)); C8 (Z_to_bv 64 (p 23 2)); C8 (Z_to_bv 64 (p 24 0)); C8 (Z_to_bv 64 (p 23 1)); C8 (Z_to_bv 64 (p 22 2)); C8 (Z_to_bv 64 (p 23 0)); C8 (Z_to_bv 64 (p 22 1)); C8 (Z_to_bv 64 (p 21 2)); C8 (Z_to_bv 64 (p 22 0)); C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
      mem_inv b0segs m' -> munch [(P + 136, P + 1264)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp yt0 yt1 yt2 s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (2 * gs + 82)) (Z_to_bv 64 (E + 16 * q 40 + 51648)) (Z_to_bv 64 (gs + 41)) (Z_to_bv 64 (A1)) a4 ya5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 ys4 ys5 s6 s7 s8 (Z_to_bv 64 (CO)) ys10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
           F (Z_to_bv 64 0x8eb60) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp xt0 xt1 xt2 s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs + 68)) (Z_to_bv 64 (E + 16 * q 33 + 51648)) xa2 xa3 a4 xa5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 xs4 xs5 s6 s7 s8 (Z_to_bv 64 (CO)) xs10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
         F (Z_to_bv 64 0x8e584) fc None m (seg_rom b0segs)).
  Proof.
    intros m me xt0 xt1 xt2 xa2 xa3 xa5 xs4 xs5 xs10 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 SPL MI MU WM VAR1 SHa VLPK SHe V1552 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (QB 33 ltac:(lia)) as QB33.
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
    frun_to 0x8e59c%Z. RDP VLPK 33%Z 2%Z.
    frun_to 0x8e5a0%Z. SST.
    frun_to 0x8e5ac%Z. RDQ VAR1 34%Z.
    frun_to 0x8e5ec%Z. RDP VLPK 34%Z 0%Z.
    frun_to 0x8e5f0%Z. SST.
    frun_to 0x8e614%Z. RDP VLPK 34%Z 1%Z.
    frun_to 0x8e618%Z. SST.
    frun_to 0x8e634%Z. RDV V1552.
    frun_to 0x8e644%Z. RDV V1552.
    frun_to 0x8e678%Z. RDP VLPK 34%Z 2%Z.
    frun_to 0x8e67c%Z. SST.
    frun_to 0x8e688%Z. RDQ VAR1 35%Z.
    frun_to 0x8e6c8%Z. RDP VLPK 35%Z 0%Z.
    frun_to 0x8e6cc%Z. SST.
    frun_to 0x8e6f0%Z. RDP VLPK 35%Z 1%Z.
    frun_to 0x8e6f4%Z. SST.
    frun_to 0x8e710%Z. RDV V1552.
    frun_to 0x8e720%Z. RDV V1552.
    frun_to 0x8e754%Z. RDP VLPK 35%Z 2%Z.
    frun_to 0x8e758%Z. SST.
    frun_to 0x8e764%Z. RDQ VAR1 36%Z.
    frun_to 0x8e7a4%Z. RDP VLPK 36%Z 0%Z.
    frun_to 0x8e7a8%Z. SST.
    frun_to 0x8e7cc%Z. RDP VLPK 36%Z 1%Z.
    frun_to 0x8e7d0%Z. SST.
    frun_to 0x8e7ec%Z. RDV V1552.
    frun_to 0x8e7fc%Z. RDV V1552.
    frun_to 0x8e830%Z. RDP VLPK 36%Z 2%Z.
    frun_to 0x8e834%Z. SST.
    frun_to 0x8e840%Z. RDQ VAR1 37%Z.
    frun_to 0x8e880%Z. RDP VLPK 37%Z 0%Z.
    frun_to 0x8e884%Z. SST.
    frun_to 0x8e8a8%Z. RDP VLPK 37%Z 1%Z.
    frun_to 0x8e8ac%Z. SST.
    frun_to 0x8e8c8%Z. RDV V1552.
    frun_to 0x8e8d8%Z. RDV V1552.
    frun_to 0x8e90c%Z. RDP VLPK 37%Z 2%Z.
    frun_to 0x8e910%Z. SST.
    frun_to 0x8e91c%Z. RDQ VAR1 38%Z.
    frun_to 0x8e95c%Z. RDP VLPK 38%Z 0%Z.
    frun_to 0x8e960%Z. SST.
    frun_to 0x8e984%Z. RDP VLPK 38%Z 1%Z.
    frun_to 0x8e988%Z. SST.
    frun_to 0x8e9a4%Z. RDV V1552.
    frun_to 0x8e9b4%Z. RDV V1552.
    frun_to 0x8e9e8%Z. RDP VLPK 38%Z 2%Z.
    frun_to 0x8e9ec%Z. SST.
    frun_to 0x8e9f8%Z. RDQ VAR1 39%Z.
    frun_to 0x8ea38%Z. RDP VLPK 39%Z 0%Z.
    frun_to 0x8ea3c%Z. SST.
    frun_to 0x8ea60%Z. RDP VLPK 39%Z 1%Z.
    frun_to 0x8ea64%Z. SST.
    frun_to 0x8ea80%Z. RDV V1552.
    frun_to 0x8ea90%Z. RDV V1552.
    frun_to 0x8eac4%Z. RDP VLPK 39%Z 2%Z.
    frun_to 0x8eac8%Z. SST.
    frun_to 0x8ead4%Z. RDQ VAR1 40%Z.
    frun_to 0x8eb14%Z. RDP VLPK 40%Z 0%Z.
    frun_to 0x8eb18%Z. SST.
    frun_to 0x8eb3c%Z. RDP VLPK 40%Z 1%Z.
    frun_to 0x8eb40%Z. SST.
    frun_to 0x8eb5c%Z. RDV V1552.
    frun_to 0x8eb60%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
End FC.
End ACeilS1.
