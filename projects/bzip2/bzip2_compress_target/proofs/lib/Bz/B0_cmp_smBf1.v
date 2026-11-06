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
  Lemma B0_fc1 : forall (m me : word -> option byte) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa7 xs4 xs5 xs10 xt3 xt4 xt5 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x904 x912 x920 x928 x936 x944 x952 x960 x968 x976 x984 x992 x1000 x1008 x1016 x1024 x1032 x1040 x1048 x1056 x1064 x1072 x1080 x1088 x1096 x1104 x1112 x1120 x1128 x1136 x1144 x1152 x1160 x1168 x1176 x1184 x1192 x1200 x1208 x1216 x1224 x1232 x1240 x1248 x1256 : word),
    rw_cells b0segs m (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 x904; C8 x912; C8 x920; C8 x928; C8 x936; C8 x944; C8 x952; C8 x960; C8 x968; C8 x976; C8 x984; C8 x992; C8 x1000; C8 x1008; C8 x1016; C8 x1024; C8 x1032; C8 x1040; C8 x1048; C8 x1056; C8 x1064; C8 x1072; C8 x1080; C8 x1088; C8 x1096; C8 x1104; C8 x1112; C8 x1120; C8 x1128; C8 x1136; C8 x1144; C8 x1152; C8 x1160; C8 x1168; C8 x1176; C8 x1184; C8 x1192; C8 x1200; C8 x1208; C8 x1216; C8 x1224; C8 x1232; C8 x1240; C8 x1248; C8 x1256] ->
    mem_inv b0segs m -> munch [(P + 136, P + 1264)]%Z me m -> wmono b0segs me m ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me E (E + ESTATE_SIZE) ->
    frdW b0segs [(P + 136, P + 1264)]%Z me (P + 1544) [C8 (Z_to_bv 64 (1))] ->
    frdW b0segs [(P + 136, P + 1264)]%Z me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (yt0 yt1 yt2 ya0 ya2 ya3 ya5 ys4 ys5 ys10 : word),
      rw_cells b0segs m' (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 x904; C8 x912; C8 x920; C8 x928; C8 x936; C8 x944; C8 x952; C8 x960; C8 x968; C8 x976; C8 x984; C8 x992; C8 x1000; C8 x1008; C8 x1016; C8 x1024; C8 x1032; C8 x1040; C8 x1048; C8 x1056; C8 x1064; C8 x1072; C8 x1080; C8 x1088; C8 x1096; C8 x1104; C8 x1112; C8 x1120; C8 x1128; C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
      mem_inv b0segs m' -> munch [(P + 136, P + 1264)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp yt0 yt1 yt2 s0 (Z_to_bv 64 (P)) ya0 (Z_to_bv 64 (E + 16 * q 6 + 51648)) ya2 ya3 a4 ya5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 ys4 ys5 s6 s7 s8 (Z_to_bv 64 (CO)) ys10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
           F (Z_to_bv 64 0x8ce14) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp xt0 xt1 xt2 s0 (Z_to_bv 64 (P)) xa0 xa1 xa2 xa3 a4 xa5 (Z_to_bv 64 (gs)) xa7 (Z_to_bv 64 (2147450880)) s3 xs4 xs5 s6 s7 s8 (Z_to_bv 64 (CO)) xs10 s11 xt3 xt4 xt5 (Z_to_bv 64 ((-9))))
         F (Z_to_bv 64 0x8c820) fc None m (seg_rom b0segs)).
  Proof.
    intros m me xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa7 xs4 xs5 xs10 xt3 xt4 xt5 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x904 x912 x920 x928 x936 x944 x952 x960 x968 x976 x984 x992 x1000 x1008 x1016 x1024 x1032 x1040 x1048 x1056 x1064 x1072 x1080 x1088 x1096 x1104 x1112 x1120 x1128 x1136 x1144 x1152 x1160 x1168 x1176 x1184 x1192 x1200 x1208 x1216 x1224 x1232 x1240 x1248 x1256 SPL MI MU WM VAR1 SHa VLPK SHe V1544 V1552 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    frun_to 0x8c824%Z. RDV V1552.
    frun_to 0x8c830%Z. RDV V1544.
    frun_to 0x8c83c%Z. RDV V1552.
    frun_to 0x8c858%Z. RDV V1552.
    frun_to 0x8c884%Z. RDQ VAR1 0%Z.
    frun_to 0x8c8c4%Z. RDP VLPK 0%Z 0%Z.
    frun_to 0x8c8e8%Z. RDP VLPK 0%Z 1%Z.
    frun_to 0x8c904%Z. RDV V1552.
    frun_to 0x8c914%Z. RDV V1552.
    frun_to 0x8c948%Z. RDP VLPK 0%Z 2%Z.
    frun_to 0x8c94c%Z. SST.
    frun_to 0x8c958%Z. RDQ VAR1 1%Z.
    frun_to 0x8c998%Z. RDP VLPK 1%Z 0%Z.
    frun_to 0x8c9bc%Z. RDP VLPK 1%Z 1%Z.
    frun_to 0x8c9d8%Z. RDV V1552.
    frun_to 0x8c9e8%Z. RDV V1552.
    frun_to 0x8ca1c%Z. RDP VLPK 1%Z 2%Z.
    frun_to 0x8ca20%Z. SST.
    frun_to 0x8ca2c%Z. RDQ VAR1 2%Z.
    frun_to 0x8ca6c%Z. RDP VLPK 2%Z 0%Z.
    frun_to 0x8ca70%Z. SST.
    frun_to 0x8ca94%Z. RDP VLPK 2%Z 1%Z.
    frun_to 0x8ca98%Z. SST.
    frun_to 0x8cab4%Z. RDV V1552.
    frun_to 0x8cac4%Z. RDV V1552.
    frun_to 0x8caf8%Z. RDP VLPK 2%Z 2%Z.
    frun_to 0x8cafc%Z. SST.
    frun_to 0x8cb08%Z. RDQ VAR1 3%Z.
    frun_to 0x8cb48%Z. RDP VLPK 3%Z 0%Z.
    frun_to 0x8cb4c%Z. SST.
    frun_to 0x8cb70%Z. RDP VLPK 3%Z 1%Z.
    frun_to 0x8cb74%Z. SST.
    frun_to 0x8cb90%Z. RDV V1552.
    frun_to 0x8cba0%Z. RDV V1552.
    frun_to 0x8cbd4%Z. RDP VLPK 3%Z 2%Z.
    frun_to 0x8cbd8%Z. SST.
    frun_to 0x8cbe4%Z. RDQ VAR1 4%Z.
    frun_to 0x8cc24%Z. RDP VLPK 4%Z 0%Z.
    frun_to 0x8cc28%Z. SST.
    frun_to 0x8cc4c%Z. RDP VLPK 4%Z 1%Z.
    frun_to 0x8cc50%Z. SST.
    frun_to 0x8cc6c%Z. RDV V1552.
    frun_to 0x8cc7c%Z. RDV V1552.
    frun_to 0x8ccb0%Z. RDP VLPK 4%Z 2%Z.
    frun_to 0x8ccb4%Z. SST.
    frun_to 0x8ccc0%Z. RDQ VAR1 5%Z.
    frun_to 0x8cd00%Z. RDP VLPK 5%Z 0%Z.
    frun_to 0x8cd04%Z. SST.
    frun_to 0x8cd28%Z. RDP VLPK 5%Z 1%Z.
    frun_to 0x8cd2c%Z. SST.
    frun_to 0x8cd48%Z. RDV V1552.
    frun_to 0x8cd58%Z. RDV V1552.
    frun_to 0x8cd8c%Z. RDP VLPK 5%Z 2%Z.
    frun_to 0x8cd90%Z. SST.
    frun_to 0x8cd9c%Z. RDQ VAR1 6%Z.
    frun_to 0x8cddc%Z. RDP VLPK 6%Z 0%Z.
    frun_to 0x8cde0%Z. SST.
    frun_to 0x8ce04%Z. RDP VLPK 6%Z 1%Z.
    frun_to 0x8ce08%Z. SST.
    frun_to 0x8ce14%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_fc2 : forall (m me : word -> option byte) (xt0 xt1 xt2 xa0 xa2 xa3 xa5 xs4 xs5 xs10 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x904 x912 x920 x928 x936 x944 x952 x960 x968 x976 x984 x992 x1000 x1008 x1016 x1024 x1032 x1040 x1048 x1056 x1064 x1072 x1080 x1088 x1096 x1104 x1112 x1120 x1128 : word),
    rw_cells b0segs m (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 x904; C8 x912; C8 x920; C8 x928; C8 x936; C8 x944; C8 x952; C8 x960; C8 x968; C8 x976; C8 x984; C8 x992; C8 x1000; C8 x1008; C8 x1016; C8 x1024; C8 x1032; C8 x1040; C8 x1048; C8 x1056; C8 x1064; C8 x1072; C8 x1080; C8 x1088; C8 x1096; C8 x1104; C8 x1112; C8 x1120; C8 x1128; C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
    mem_inv b0segs m -> munch [(P + 136, P + 1264)]%Z me m -> wmono b0segs me m ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch [(P + 136, P + 1264)]%Z me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW b0segs [(P + 136, P + 1264)]%Z me E (E + ESTATE_SIZE) ->
    frdW b0segs [(P + 136, P + 1264)]%Z me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (yt0 yt1 yt2 ya1 ya2 ya3 ya5 ys4 ys5 ys10 : word),
      rw_cells b0segs m' (P + 136) [C8 x136; C8 x144; C8 x152; C8 x160; C8 x168; C8 x176; C8 x184; C8 x192; C8 x200; C8 x208; C8 x216; C8 x224; C8 x232; C8 x240; C8 x248; C8 x256; C8 x264; C8 x272; C8 x280; C8 x288; C8 x296; C8 x304; C8 x312; C8 x320; C8 x328; C8 x336; C8 x344; C8 x352; C8 x360; C8 x368; C8 x376; C8 x384; C8 x392; C8 x400; C8 x408; C8 x416; C8 x424; C8 x432; C8 x440; C8 x448; C8 x456; C8 x464; C8 x472; C8 x480; C8 x488; C8 x496; C8 x504; C8 x512; C8 x520; C8 x528; C8 x536; C8 x544; C8 x552; C8 x560; C8 x568; C8 x576; C8 x584; C8 x592; C8 x600; C8 x608; C8 x616; C8 x624; C8 x632; C8 x640; C8 x648; C8 x656; C8 x664; C8 x672; C8 x680; C8 x688; C8 x696; C8 x704; C8 x712; C8 x720; C8 x728; C8 x736; C8 x744; C8 x752; C8 x760; C8 x768; C8 x776; C8 x784; C8 x792; C8 x800; C8 x808; C8 x816; C8 x824; C8 x832; C8 x840; C8 x848; C8 x856; C8 x864; C8 x872; C8 x880; C8 x888; C8 x896; C8 x904; C8 x912; C8 x920; C8 x928; C8 x936; C8 x944; C8 x952; C8 x960; C8 x968; C8 (Z_to_bv 64 (p 12 2)); C8 (Z_to_bv 64 (p 13 0)); C8 (Z_to_bv 64 (p 12 1)); C8 (Z_to_bv 64 (p 11 2)); C8 (Z_to_bv 64 (p 12 0)); C8 (Z_to_bv 64 (p 11 1)); C8 (Z_to_bv 64 (p 10 2)); C8 (Z_to_bv 64 (p 11 0)); C8 (Z_to_bv 64 (p 10 1)); C8 (Z_to_bv 64 (p 9 2)); C8 (Z_to_bv 64 (p 10 0)); C8 (Z_to_bv 64 (p 9 1)); C8 (Z_to_bv 64 (p 8 2)); C8 (Z_to_bv 64 (p 9 0)); C8 (Z_to_bv 64 (p 8 1)); C8 (Z_to_bv 64 (p 7 2)); C8 (Z_to_bv 64 (p 8 0)); C8 (Z_to_bv 64 (p 7 1)); C8 (Z_to_bv 64 (p 6 2)); C8 (Z_to_bv 64 (p 7 0)); C8 (Z_to_bv 64 (p 6 1)); C8 (Z_to_bv 64 (p 5 2)); C8 (Z_to_bv 64 (p 6 0)); C8 (Z_to_bv 64 (p 5 1)); C8 (Z_to_bv 64 (p 4 2)); C8 (Z_to_bv 64 (p 5 0)); C8 (Z_to_bv 64 (p 4 1)); C8 (Z_to_bv 64 (p 3 2)); C8 (Z_to_bv 64 (p 4 0)); C8 (Z_to_bv 64 (p 3 1)); C8 (Z_to_bv 64 (p 2 2)); C8 (Z_to_bv 64 (p 3 0)); C8 (Z_to_bv 64 (p 2 1)); C8 (Z_to_bv 64 (p 1 2)); C8 (Z_to_bv 64 (p 2 0)); C8 (Z_to_bv 64 (p 0 2))] ->
      mem_inv b0segs m' -> munch [(P + 136, P + 1264)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp yt0 yt1 yt2 s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (E + 16 * q 13 + 51640)) ya1 ya2 ya3 a4 ya5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 ys4 ys5 s6 s7 s8 (Z_to_bv 64 (CO)) ys10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
           F (Z_to_bv 64 0x8d3f0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp xt0 xt1 xt2 s0 (Z_to_bv 64 (P)) xa0 (Z_to_bv 64 (E + 16 * q 6 + 51648)) xa2 xa3 a4 xa5 (Z_to_bv 64 (gs)) (Z_to_bv 64 (p 0 1)) (Z_to_bv 64 (2147450880)) s3 xs4 xs5 s6 s7 s8 (Z_to_bv 64 (CO)) xs10 s11 (Z_to_bv 64 (p 0 0)) (Z_to_bv 64 (p 1 1)) (Z_to_bv 64 (p 1 0)) (Z_to_bv 64 ((-9))))
         F (Z_to_bv 64 0x8ce14) fc None m (seg_rom b0segs)).
  Proof.
    intros m me xt0 xt1 xt2 xa0 xa2 xa3 xa5 xs4 xs5 xs10 x136 x144 x152 x160 x168 x176 x184 x192 x200 x208 x216 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 x344 x352 x360 x368 x376 x384 x392 x400 x408 x416 x424 x432 x440 x448 x456 x464 x472 x480 x488 x496 x504 x512 x520 x528 x536 x544 x552 x560 x568 x576 x584 x592 x600 x608 x616 x624 x632 x640 x648 x656 x664 x672 x680 x688 x696 x704 x712 x720 x728 x736 x744 x752 x760 x768 x776 x784 x792 x800 x808 x816 x824 x832 x840 x848 x856 x864 x872 x880 x888 x896 x904 x912 x920 x928 x936 x944 x952 x960 x968 x976 x984 x992 x1000 x1008 x1016 x1024 x1032 x1040 x1048 x1056 x1064 x1072 x1080 x1088 x1096 x1104 x1112 x1120 x1128 SPL MI MU WM VAR1 SHa VLPK SHe V1552 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (QB 6 ltac:(lia)) as QB6.
    pose proof (PB 0 0 ltac:(lia) ltac:(lia)) as PB0_0.
    pose proof (PB 1 0 ltac:(lia) ltac:(lia)) as PB1_0.
    pose proof (PB 2 0 ltac:(lia) ltac:(lia)) as PB2_0.
    pose proof (PB 3 0 ltac:(lia) ltac:(lia)) as PB3_0.
    pose proof (PB 4 0 ltac:(lia) ltac:(lia)) as PB4_0.
    pose proof (PB 5 0 ltac:(lia) ltac:(lia)) as PB5_0.
    pose proof (PB 6 0 ltac:(lia) ltac:(lia)) as PB6_0.
    pose proof (PB 0 1 ltac:(lia) ltac:(lia)) as PB0_1.
    pose proof (PB 1 1 ltac:(lia) ltac:(lia)) as PB1_1.
    pose proof (PB 2 1 ltac:(lia) ltac:(lia)) as PB2_1.
    pose proof (PB 3 1 ltac:(lia) ltac:(lia)) as PB3_1.
    pose proof (PB 4 1 ltac:(lia) ltac:(lia)) as PB4_1.
    pose proof (PB 5 1 ltac:(lia) ltac:(lia)) as PB5_1.
    pose proof (PB 6 1 ltac:(lia) ltac:(lia)) as PB6_1.
    pose proof (PB 0 2 ltac:(lia) ltac:(lia)) as PB0_2.
    pose proof (PB 1 2 ltac:(lia) ltac:(lia)) as PB1_2.
    pose proof (PB 2 2 ltac:(lia) ltac:(lia)) as PB2_2.
    pose proof (PB 3 2 ltac:(lia) ltac:(lia)) as PB3_2.
    pose proof (PB 4 2 ltac:(lia) ltac:(lia)) as PB4_2.
    pose proof (PB 5 2 ltac:(lia) ltac:(lia)) as PB5_2.
    frun_to 0x8ce24%Z. RDV V1552.
    frun_to 0x8ce34%Z. RDV V1552.
    frun_to 0x8ce68%Z. RDP VLPK 6%Z 2%Z.
    frun_to 0x8ce6c%Z. SST.
    frun_to 0x8ce78%Z. RDQ VAR1 7%Z.
    frun_to 0x8ceb8%Z. RDP VLPK 7%Z 0%Z.
    frun_to 0x8cebc%Z. SST.
    frun_to 0x8cee0%Z. RDP VLPK 7%Z 1%Z.
    frun_to 0x8cee4%Z. SST.
    frun_to 0x8cf00%Z. RDV V1552.
    frun_to 0x8cf10%Z. RDV V1552.
    frun_to 0x8cf44%Z. RDP VLPK 7%Z 2%Z.
    frun_to 0x8cf48%Z. SST.
    frun_to 0x8cf54%Z. RDQ VAR1 8%Z.
    frun_to 0x8cf94%Z. RDP VLPK 8%Z 0%Z.
    frun_to 0x8cf98%Z. SST.
    frun_to 0x8cfbc%Z. RDP VLPK 8%Z 1%Z.
    frun_to 0x8cfc0%Z. SST.
    frun_to 0x8cfdc%Z. RDV V1552.
    frun_to 0x8cfec%Z. RDV V1552.
    frun_to 0x8d020%Z. RDP VLPK 8%Z 2%Z.
    frun_to 0x8d024%Z. SST.
    frun_to 0x8d030%Z. RDQ VAR1 9%Z.
    frun_to 0x8d070%Z. RDP VLPK 9%Z 0%Z.
    frun_to 0x8d074%Z. SST.
    frun_to 0x8d098%Z. RDP VLPK 9%Z 1%Z.
    frun_to 0x8d09c%Z. SST.
    frun_to 0x8d0b8%Z. RDV V1552.
    frun_to 0x8d0c8%Z. RDV V1552.
    frun_to 0x8d0fc%Z. RDP VLPK 9%Z 2%Z.
    frun_to 0x8d100%Z. SST.
    frun_to 0x8d10c%Z. RDQ VAR1 10%Z.
    frun_to 0x8d14c%Z. RDP VLPK 10%Z 0%Z.
    frun_to 0x8d150%Z. SST.
    frun_to 0x8d174%Z. RDP VLPK 10%Z 1%Z.
    frun_to 0x8d178%Z. SST.
    frun_to 0x8d194%Z. RDV V1552.
    frun_to 0x8d1a4%Z. RDV V1552.
    frun_to 0x8d1d8%Z. RDP VLPK 10%Z 2%Z.
    frun_to 0x8d1dc%Z. SST.
    frun_to 0x8d1e8%Z. RDQ VAR1 11%Z.
    frun_to 0x8d228%Z. RDP VLPK 11%Z 0%Z.
    frun_to 0x8d22c%Z. SST.
    frun_to 0x8d250%Z. RDP VLPK 11%Z 1%Z.
    frun_to 0x8d254%Z. SST.
    frun_to 0x8d270%Z. RDV V1552.
    frun_to 0x8d280%Z. RDV V1552.
    frun_to 0x8d2b4%Z. RDP VLPK 11%Z 2%Z.
    frun_to 0x8d2b8%Z. SST.
    frun_to 0x8d2c4%Z. RDQ VAR1 12%Z.
    frun_to 0x8d304%Z. RDP VLPK 12%Z 0%Z.
    frun_to 0x8d308%Z. SST.
    frun_to 0x8d32c%Z. RDP VLPK 12%Z 1%Z.
    frun_to 0x8d330%Z. SST.
    frun_to 0x8d34c%Z. RDV V1552.
    frun_to 0x8d35c%Z. RDV V1552.
    frun_to 0x8d390%Z. RDP VLPK 12%Z 2%Z.
    frun_to 0x8d394%Z. SST.
    frun_to 0x8d3a0%Z. RDQ VAR1 13%Z.
    frun_to 0x8d3e0%Z. RDP VLPK 13%Z 0%Z.
    frun_to 0x8d3e4%Z. SST.
    frun_to 0x8d3f0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq
      | lazymatch type of SPL with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SPL| CmpFast.rlf] end end
      | assumption | exact MU | exact WM ].
  Qed.
End FC.
End ACeilS1.
