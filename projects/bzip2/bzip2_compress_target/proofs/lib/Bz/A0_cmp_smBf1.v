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
  Ltac RDV V :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let RO := fresh "RO" in pose proof (V mm MU') as RO; lstep; clear RO end.
  Ltac SST := lstep; lit_store.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fc1 : forall (m me : word -> option byte) (xra xt0 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x904 x912 x920 x928 x936 x944 x952 x960 x968 x976 x984 x992 x1000 x1008 x1016 x1024 x1032 x1040 x1048 x1056 x1064 x1072 x1080 x1088 x1096 x1104 x1112 x1120 x1128 x1136 x1144 x1152 x1160 x1168 x1176 x1184 x1192 x1200 x1208 x1216 x1224 x1232 x1240 x1248 x1256 x1264 x1272 x1280 x1288 x1296 x1304 x1312 x1320 x1328 x1336 : word),
    rw_cells a0segs m (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 x904; C8 x912; C8 x920; C8 x928; C8 x936; C8 x944; C8 x952; C8 x960; C8 x968; C8 x976; C8 x984; C8 x992; C8 x1000; C8 x1008; C8 x1016; C8 x1024; C8 x1032; C8 x1040; C8 x1048; C8 x1056; C8 x1064; C8 x1072; C8 x1080; C8 x1088; C8 x1096; C8 x1104; C8 x1112; C8 x1120; C8 x1128; C8 x1136; C8 x1144; C8 x1152; C8 x1160; C8 x1168; C8 x1176; C8 x1184; C8 x1192; C8 x1200; C8 x1208; C8 x1216; C8 x1224; C8 x1232; C8 x1240; C8 x1248; C8 x1256; C8 x1264; C8 x1272; C8 x1280; C8 x1288; C8 x1296; C8 x1304; C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
    mem_inv a0segs m -> munch [(P + 232, P + 1344)]%Z me m -> wmono a0segs me m ->
    (forall m', munch [(P + 232, P + 1344)]%Z me m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW a0segs [(P + 232, P + 1344)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 232, P + 1344)]%Z me m' -> u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW a0segs [(P + 232, P + 1344)]%Z me E (E + ESTATE_SIZE) ->
    frdW a0segs [(P + 232, P + 1344)]%Z me (P + 168) [C8 (Z_to_bv 64 (E + 51640))] ->
    (forall m' (ya4 : word),
      rw_cells a0segs m' (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 x904; C8 x912; C8 x920; C8 x928; C8 x936; C8 x944; C8 x952; C8 x960; C8 x968; C8 x976; C8 x984; C8 x992; C8 x1000; C8 x1008; C8 x1016; C8 x1024; C8 x1032; C8 x1040; C8 x1048; C8 x1056; C8 x1064; C8 x1072; C8 x1080; C8 x1088; C8 x1096; C8 x1104; C8 x1112; C8 x1120; C8 x1128; C8 x1136; C8 x1144; C8 x1152; C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 2)); C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
      mem_inv a0segs m' -> munch [(P + 232, P + 1344)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 (p 3 2)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (p 4 1)) (Z_to_bv 64 (p 0 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) (Z_to_bv 64 (A1 + 2 * gs + 22)) (Z_to_bv 64 (p 10 2)) (Z_to_bv 64 (E + 51640)) ya4 (Z_to_bv 64 (p 10 0)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (49)) (Z_to_bv 64 (p 1 2)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (p 2 0)) (Z_to_bv 64 (p 2 2)) (Z_to_bv 64 (p 2 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (gs + 49)))
           F (Z_to_bv 64 0x8b1d0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR xra (Z_to_bv 64 (P)) gp tp xt0 (Z_to_bv 64 (E + 37708)) xt2 s0 (Z_to_bv 64 (P)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (49)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (A)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 (nG)) (Z_to_bv 64 (E + 668)) xt3 (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)))
         F (Z_to_bv 64 0x8ac68) fc None m (seg_rom a0segs)).
  Proof.
    intros m me xra xt0 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x904 x912 x920 x928 x936 x944 x952 x960 x968 x976 x984 x992 x1000 x1008 x1016 x1024 x1032 x1040 x1048 x1056 x1064 x1072 x1080 x1088 x1096 x1104 x1112 x1120 x1128 x1136 x1144 x1152 x1160 x1168 x1176 x1184 x1192 x1200 x1208 x1216 x1224 x1232 x1240 x1248 x1256 x1264 x1272 x1280 x1288 x1296 x1304 x1312 x1320 x1328 x1336 SPL MI MU WM VAR1 SHa VLPK SHe V168 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    frun_to 0x8ac7c%Z. RDV V168.
    frun_to 0x8ac88%Z. RDQ VAR1 0%Z.
    frun_to 0x8acb8%Z. RDP VLPK 0%Z 0%Z.
    frun_to 0x8acd4%Z. RDP VLPK 0%Z 1%Z.
    frun_to 0x8acf0%Z. RDP VLPK 0%Z 2%Z.
    frun_to 0x8acfc%Z. RDQ VAR1 1%Z.
    frun_to 0x8ad2c%Z. RDP VLPK 1%Z 0%Z.
    frun_to 0x8ad48%Z. RDP VLPK 1%Z 1%Z.
    frun_to 0x8ad64%Z. RDP VLPK 1%Z 2%Z.
    frun_to 0x8ad70%Z. RDQ VAR1 2%Z.
    frun_to 0x8ada0%Z. RDP VLPK 2%Z 0%Z.
    frun_to 0x8adbc%Z. RDP VLPK 2%Z 1%Z.
    frun_to 0x8add8%Z. RDP VLPK 2%Z 2%Z.
    frun_to 0x8ade4%Z. RDQ VAR1 3%Z.
    frun_to 0x8ae14%Z. RDP VLPK 3%Z 0%Z.
    frun_to 0x8ae30%Z. RDP VLPK 3%Z 1%Z.
    frun_to 0x8ae4c%Z. RDP VLPK 3%Z 2%Z.
    frun_to 0x8ae58%Z. RDQ VAR1 4%Z.
    frun_to 0x8ae88%Z. RDP VLPK 4%Z 0%Z.
    frun_to 0x8aea4%Z. RDP VLPK 4%Z 1%Z.
    frun_to 0x8aec0%Z. RDP VLPK 4%Z 2%Z.
    frun_to 0x8aec4%Z. SST.
    frun_to 0x8aed0%Z. RDQ VAR1 5%Z.
    frun_to 0x8af00%Z. RDP VLPK 5%Z 0%Z.
    frun_to 0x8af04%Z. SST.
    frun_to 0x8af20%Z. RDP VLPK 5%Z 1%Z.
    frun_to 0x8af24%Z. SST.
    frun_to 0x8af40%Z. RDP VLPK 5%Z 2%Z.
    frun_to 0x8af44%Z. SST.
    frun_to 0x8af50%Z. RDQ VAR1 6%Z.
    frun_to 0x8af80%Z. RDP VLPK 6%Z 0%Z.
    frun_to 0x8af84%Z. SST.
    frun_to 0x8afa0%Z. RDP VLPK 6%Z 1%Z.
    frun_to 0x8afa4%Z. SST.
    frun_to 0x8afc0%Z. RDP VLPK 6%Z 2%Z.
    frun_to 0x8afc4%Z. SST.
    frun_to 0x8afd0%Z. RDQ VAR1 7%Z.
    frun_to 0x8b000%Z. RDP VLPK 7%Z 0%Z.
    frun_to 0x8b004%Z. SST.
    frun_to 0x8b020%Z. RDP VLPK 7%Z 1%Z.
    frun_to 0x8b024%Z. SST.
    frun_to 0x8b040%Z. RDP VLPK 7%Z 2%Z.
    frun_to 0x8b044%Z. SST.
    frun_to 0x8b050%Z. RDQ VAR1 8%Z.
    frun_to 0x8b080%Z. RDP VLPK 8%Z 0%Z.
    frun_to 0x8b084%Z. SST.
    frun_to 0x8b0a0%Z. RDP VLPK 8%Z 1%Z.
    frun_to 0x8b0a4%Z. SST.
    frun_to 0x8b0c0%Z. RDP VLPK 8%Z 2%Z.
    frun_to 0x8b0c4%Z. SST.
    frun_to 0x8b0d0%Z. RDQ VAR1 9%Z.
    frun_to 0x8b100%Z. RDP VLPK 9%Z 0%Z.
    frun_to 0x8b104%Z. SST.
    frun_to 0x8b120%Z. RDP VLPK 9%Z 1%Z.
    frun_to 0x8b124%Z. SST.
    frun_to 0x8b140%Z. RDP VLPK 9%Z 2%Z.
    frun_to 0x8b144%Z. SST.
    frun_to 0x8b150%Z. RDQ VAR1 10%Z.
    frun_to 0x8b180%Z. RDP VLPK 10%Z 0%Z.
    frun_to 0x8b184%Z. SST.
    frun_to 0x8b1a0%Z. RDP VLPK 10%Z 1%Z.
    frun_to 0x8b1a4%Z. SST.
    frun_to 0x8b1c0%Z. RDP VLPK 10%Z 2%Z.
    frun_to 0x8b1c4%Z. SST.
    frun_to 0x8b1d0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fc2 : forall (m me : word -> option byte) (xa4 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x904 x912 x920 x928 x936 x944 x952 x960 x968 x976 x984 x992 x1000 x1008 x1016 x1024 x1032 x1040 x1048 x1056 x1064 x1072 x1080 x1088 x1096 x1104 x1112 x1120 x1128 x1136 x1144 x1152 x1312 x1320 x1328 x1336 : word),
    rw_cells a0segs m (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 x904; C8 x912; C8 x920; C8 x928; C8 x936; C8 x944; C8 x952; C8 x960; C8 x968; C8 x976; C8 x984; C8 x992; C8 x1000; C8 x1008; C8 x1016; C8 x1024; C8 x1032; C8 x1040; C8 x1048; C8 x1056; C8 x1064; C8 x1072; C8 x1080; C8 x1088; C8 x1096; C8 x1104; C8 x1112; C8 x1120; C8 x1128; C8 x1136; C8 x1144; C8 x1152; C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 2)); C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
    mem_inv a0segs m -> munch [(P + 232, P + 1344)]%Z me m -> wmono a0segs me m ->
    (forall m', munch [(P + 232, P + 1344)]%Z me m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW a0segs [(P + 232, P + 1344)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 232, P + 1344)]%Z me m' -> u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW a0segs [(P + 232, P + 1344)]%Z me E (E + ESTATE_SIZE) ->
    (forall m' (ya4 : word),
      rw_cells a0segs m' (P + 232) [C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 (Z_to_bv 64 (p 21 1)); C8 (Z_to_bv 64 (p 21 0)); C8 (Z_to_bv 64 (p 20 2)); C8 (Z_to_bv 64 (p 20 1)); C8 (Z_to_bv 64 (p 20 0)); C8 (Z_to_bv 64 (p 19 2)); C8 (Z_to_bv 64 (p 19 1)); C8 (Z_to_bv 64 (p 19 0)); C8 (Z_to_bv 64 (p 18 2)); C8 (Z_to_bv 64 (p 18 1)); C8 (Z_to_bv 64 (p 18 0)); C8 (Z_to_bv 64 (p 17 2)); C8 (Z_to_bv 64 (p 17 1)); C8 (Z_to_bv 64 (p 17 0)); C8 (Z_to_bv 64 (p 16 2)); C8 (Z_to_bv 64 (p 16 1)); C8 (Z_to_bv 64 (p 16 0)); C8 (Z_to_bv 64 (p 15 2)); C8 (Z_to_bv 64 (p 15 1)); C8 (Z_to_bv 64 (p 15 0)); C8 (Z_to_bv 64 (p 14 2)); C8 (Z_to_bv 64 (p 14 1)); C8 (Z_to_bv 64 (p 14 0)); C8 (Z_to_bv 64 (p 13 2)); C8 (Z_to_bv 64 (p 13 1)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 2)); C8 x1312; C8 x1320; C8 x1328; C8 x1336] ->
      mem_inv a0segs m' -> munch [(P + 232, P + 1344)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 (p 3 2)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (p 4 1)) (Z_to_bv 64 (p 0 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) (Z_to_bv 64 (p 21 1)) (Z_to_bv 64 (E + 16 * q 21 + 51648)) (Z_to_bv 64 (E + 51640)) ya4 (Z_to_bv 64 (p 21 0)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (49)) (Z_to_bv 64 (p 1 2)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (p 2 0)) (Z_to_bv 64 (p 2 2)) (Z_to_bv 64 (p 2 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (gs + 49)))
           F (Z_to_bv 64 0x8b730) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 (p 3 2)) (Z_to_bv 64 (P)) gp tp (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (p 4 1)) (Z_to_bv 64 (p 0 2)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) (Z_to_bv 64 (A1 + 2 * gs + 22)) (Z_to_bv 64 (p 10 2)) (Z_to_bv 64 (E + 51640)) xa4 (Z_to_bv 64 (p 10 0)) (Z_to_bv 64 (p 4 0)) (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (49)) (Z_to_bv 64 (p 1 2)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (p 2 0)) (Z_to_bv 64 (p 2 2)) (Z_to_bv 64 (p 2 1)) (Z_to_bv 64 (p 3 0)) (Z_to_bv 64 (p 3 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (gs + 49)))
         F (Z_to_bv 64 0x8b1d0) fc None m (seg_rom a0segs)).
  Proof.
    intros m me xa4 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x904 x912 x920 x928 x936 x944 x952 x960 x968 x976 x984 x992 x1000 x1008 x1016 x1024 x1032 x1040 x1048 x1056 x1064 x1072 x1080 x1088 x1096 x1104 x1112 x1120 x1128 x1136 x1144 x1152 x1312 x1320 x1328 x1336 SPL MI MU WM VAR1 SHa VLPK SHe K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
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
    frun_to 0x8b1d0%Z. RDQ VAR1 11%Z.
    frun_to 0x8b200%Z. RDP VLPK 11%Z 0%Z.
    frun_to 0x8b204%Z. SST.
    frun_to 0x8b220%Z. RDP VLPK 11%Z 1%Z.
    frun_to 0x8b224%Z. SST.
    frun_to 0x8b240%Z. RDP VLPK 11%Z 2%Z.
    frun_to 0x8b244%Z. SST.
    frun_to 0x8b250%Z. RDQ VAR1 12%Z.
    frun_to 0x8b280%Z. RDP VLPK 12%Z 0%Z.
    frun_to 0x8b284%Z. SST.
    frun_to 0x8b2a0%Z. RDP VLPK 12%Z 1%Z.
    frun_to 0x8b2a4%Z. SST.
    frun_to 0x8b2c0%Z. RDP VLPK 12%Z 2%Z.
    frun_to 0x8b2c4%Z. SST.
    frun_to 0x8b2d0%Z. RDQ VAR1 13%Z.
    frun_to 0x8b300%Z. RDP VLPK 13%Z 0%Z.
    frun_to 0x8b304%Z. SST.
    frun_to 0x8b320%Z. RDP VLPK 13%Z 1%Z.
    frun_to 0x8b324%Z. SST.
    frun_to 0x8b340%Z. RDP VLPK 13%Z 2%Z.
    frun_to 0x8b344%Z. SST.
    frun_to 0x8b350%Z. RDQ VAR1 14%Z.
    frun_to 0x8b380%Z. RDP VLPK 14%Z 0%Z.
    frun_to 0x8b384%Z. SST.
    frun_to 0x8b3a0%Z. RDP VLPK 14%Z 1%Z.
    frun_to 0x8b3a4%Z. SST.
    frun_to 0x8b3c0%Z. RDP VLPK 14%Z 2%Z.
    frun_to 0x8b3c4%Z. SST.
    frun_to 0x8b3d0%Z. RDQ VAR1 15%Z.
    frun_to 0x8b400%Z. RDP VLPK 15%Z 0%Z.
    frun_to 0x8b404%Z. SST.
    frun_to 0x8b420%Z. RDP VLPK 15%Z 1%Z.
    frun_to 0x8b424%Z. SST.
    frun_to 0x8b440%Z. RDP VLPK 15%Z 2%Z.
    frun_to 0x8b444%Z. SST.
    frun_to 0x8b450%Z. RDQ VAR1 16%Z.
    frun_to 0x8b480%Z. RDP VLPK 16%Z 0%Z.
    frun_to 0x8b484%Z. SST.
    frun_to 0x8b4a0%Z. RDP VLPK 16%Z 1%Z.
    frun_to 0x8b4a4%Z. SST.
    frun_to 0x8b4c0%Z. RDP VLPK 16%Z 2%Z.
    frun_to 0x8b4c4%Z. SST.
    frun_to 0x8b4d0%Z. RDQ VAR1 17%Z.
    frun_to 0x8b500%Z. RDP VLPK 17%Z 0%Z.
    frun_to 0x8b504%Z. SST.
    frun_to 0x8b520%Z. RDP VLPK 17%Z 1%Z.
    frun_to 0x8b524%Z. SST.
    frun_to 0x8b540%Z. RDP VLPK 17%Z 2%Z.
    frun_to 0x8b544%Z. SST.
    frun_to 0x8b550%Z. RDQ VAR1 18%Z.
    frun_to 0x8b580%Z. RDP VLPK 18%Z 0%Z.
    frun_to 0x8b584%Z. SST.
    frun_to 0x8b5a0%Z. RDP VLPK 18%Z 1%Z.
    frun_to 0x8b5a4%Z. SST.
    frun_to 0x8b5c0%Z. RDP VLPK 18%Z 2%Z.
    frun_to 0x8b5c4%Z. SST.
    frun_to 0x8b5d0%Z. RDQ VAR1 19%Z.
    frun_to 0x8b600%Z. RDP VLPK 19%Z 0%Z.
    frun_to 0x8b604%Z. SST.
    frun_to 0x8b620%Z. RDP VLPK 19%Z 1%Z.
    frun_to 0x8b624%Z. SST.
    frun_to 0x8b640%Z. RDP VLPK 19%Z 2%Z.
    frun_to 0x8b644%Z. SST.
    frun_to 0x8b650%Z. RDQ VAR1 20%Z.
    frun_to 0x8b680%Z. RDP VLPK 20%Z 0%Z.
    frun_to 0x8b684%Z. SST.
    frun_to 0x8b6a0%Z. RDP VLPK 20%Z 1%Z.
    frun_to 0x8b6a4%Z. SST.
    frun_to 0x8b6c0%Z. RDP VLPK 20%Z 2%Z.
    frun_to 0x8b6c4%Z. SST.
    frun_to 0x8b6d0%Z. RDQ VAR1 21%Z.
    frun_to 0x8b700%Z. RDP VLPK 21%Z 0%Z.
    frun_to 0x8b704%Z. SST.
    frun_to 0x8b720%Z. RDP VLPK 21%Z 1%Z.
    frun_to 0x8b724%Z. SST.
    frun_to 0x8b730%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
End FC.
End ACeilS1.
