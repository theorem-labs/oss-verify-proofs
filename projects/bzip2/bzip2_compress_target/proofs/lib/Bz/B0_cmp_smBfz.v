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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_smBf1 B0_cmp_smBf2 B0_cmp_smBf3 B0_cmp_smBf4.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wfc := [(P + 136, P + 1264); (CO, CO + 12)]%Z.
  Ltac vsub V MU := let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply V; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); a_sub_fp.
  Ltac ssub SH MU := eapply (shzW_sub b0segs Wfc); [exact SH| exact MU| a_sub_fp| lia| lia].
  Ltac fsub V MU := eapply (frdW_sub b0segs Wfc); [exact V| exact MU| a_sub_fp].
  Ltac fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552 :=
    first [ eassumption |
    lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- forall _, munch _ _ _ -> u8arr _ _ _ _ => vsub VAR1 MU
    | |- forall _, munch _ _ _ -> u32arr _ _ _ _ => vsub VLPK MU
    | |- shzW _ _ _ A1 _ => ssub SHa MU
    | |- shzW _ _ _ E _ => ssub SHe MU
    | |- frdW _ _ _ (P + 128)%Z _ => fsub V128 MU
    | |- frdW _ _ _ (P + 1424)%Z _ => fsub V1424 MU
    | |- frdW _ _ _ (P + 1544)%Z _ => fsub V1544 MU
    | |- frdW _ _ _ (P + 1552)%Z _ => fsub V1552 MU
    | |- _ => idtac
    end ].
  Lemma B0_fc : forall (m me : word -> option byte) (Jsp : list byte) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa7 xs4 xs5 xs10 xt3 xt4 xt5 : word),
    u8arr b0segs m (P + 136) Jsp -> length Jsp = 1128%nat ->
    u8arr b0segs m CO (zb8 cb 12) ->
    mem_inv b0segs m -> munch Wfc me m -> wmono b0segs me m ->
    (forall m', munch Wfc me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs Wfc me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch Wfc me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW b0segs Wfc me E (E + ESTATE_SIZE) ->
    frdW b0segs Wfc me (P + 128) [C8 (Z_to_bv 64 (E + 51640))] ->
    frdW b0segs Wfc me (P + 1424) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW b0segs Wfc me (P + 1544) [C8 (Z_to_bv 64 (1))] ->
    frdW b0segs Wfc me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (S0 S1 S2 : Z) (Jsp' : list byte) (yt0 yt1 yt2 ya0 ya2 ya3 ya5 ya7 ys10 yt3 yt4 : word),
      S0 = psum arr1 lp gs 0 0 50 -> S1 = psum arr1 lp gs 1 0 50 -> S2 = psum arr1 lp gs 2 0 50 ->
      u8arr b0segs m' (P + 136) Jsp' -> length Jsp' = 1128%nat ->
      u8arr b0segs m' CO (zb8 (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 cb 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536)) 12) ->
      mem_inv b0segs m' -> munch Wfc me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp yt0 yt1 yt2 s0 (Z_to_bv 64 (P)) ya0 (Z_to_bv 64 ((-11))) ya2 ya3 a4 ya5 (Z_to_bv 64 (gs)) ya7 (Z_to_bv 64 (2147450880)) s3 (Z_to_bv 64 (258)) (Z_to_bv 64 (1032)) s6 s7 s8 (Z_to_bv 64 (CO)) ys10 s11 yt3 yt4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 ((-9))))
           F (Z_to_bv 64 0x8f920) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (P)) gp tp xt0 xt1 xt2 s0 (Z_to_bv 64 (P)) xa0 xa1 xa2 xa3 a4 xa5 (Z_to_bv 64 (gs)) xa7 (Z_to_bv 64 (2147450880)) s3 xs4 xs5 s6 s7 s8 (Z_to_bv 64 (CO)) xs10 s11 xt3 xt4 xt5 (Z_to_bv 64 ((-9))))
         F (Z_to_bv 64 0x8c820) fc None m (seg_rom b0segs)).
  Proof.
    intros m me Jsp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa7 xs4 xs5 xs10 xt3 xt4 xt5 SPLu LJ COST MI MU WM VAR1 SHa VLPK SHe V128 V1424 V1544 V1552 K.
    destruct (u8arr_C8s 141 b0segs _ _ _ SPLu ltac:(rewrite LJ; reflexivity)) as (x136 & x144 & x152 & x160 & x168 & x176 & x184 & x192 & x200 & x208 & x216 & x224 & x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & x344 & x352 & x360 & x368 & x376 & x384 & x392 & x400 & x408 & x416 & x424 & x432 & x440 & x448 & x456 & x464 & x472 & x480 & x488 & x496 & x504 & x512 & x520 & x528 & x536 & x544 & x552 & x560 & x568 & x576 & x584 & x592 & x600 & x608 & x616 & x624 & x632 & x640 & x648 & x656 & x664 & x672 & x680 & x688 & x696 & x704 & x712 & x720 & x728 & x736 & x744 & x752 & x760 & x768 & x776 & x784 & x792 & x800 & x808 & x816 & x824 & x832 & x840 & x848 & x856 & x864 & x872 & x880 & x888 & x896 & x904 & x912 & x920 & x928 & x936 & x944 & x952 & x960 & x968 & x976 & x984 & x992 & x1000 & x1008 & x1016 & x1024 & x1032 & x1040 & x1048 & x1056 & x1064 & x1072 & x1080 & x1088 & x1096 & x1104 & x1112 & x1120 & x1128 & x1136 & x1144 & x1152 & x1160 & x1168 & x1176 & x1184 & x1192 & x1200 & x1208 & x1216 & x1224 & x1232 & x1240 & x1248 & x1256 & SPL). clear SPLu. cbn [map] in SPL.
    (* [comment removed for export] *)
    eapply B0_fc1 with (me := m). all: fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552.
    clear SPL MI. intros m1 yt0_1 yt1_1 yt2_1 ya0_1 ya2_1 ya3_1 ya5_1 ys4_1 ys5_1 ys10_1 SPL MI MUc WMc. transport_after_call b0segs m m1 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply B0_fc2 with (me := m1). all: fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552.
    clear SPL MI. intros m2 yt0_2 yt1_2 yt2_2 ya1_2 ya2_2 ya3_2 ya5_2 ys4_2 ys5_2 ys10_2 SPL MI MUc WMc. transport_after_call b0segs m1 m2 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply B0_fc3 with (me := m2). all: fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552.
    clear SPL MI. intros m3 yt0_3 yt1_3 yt2_3 ya1_3 ya2_3 ya3_3 ya5_3 ys4_3 ys5_3 ys10_3 SPL MI MUc WMc. transport_after_call b0segs m2 m3 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply B0_fc4 with (me := m3). all: fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552.
    clear SPL MI. intros m4 yt0_4 yt1_4 yt2_4 ya1_4 ya2_4 ya3_4 ya5_4 ys4_4 ys5_4 ys10_4 SPL MI MUc WMc. transport_after_call b0segs m3 m4 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply B0_fc5 with (me := m4). all: fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552.
    clear SPL MI. intros m5 yt0_5 yt1_5 yt2_5 ya2_5 ya3_5 ya5_5 ys4_5 ys5_5 ys10_5 SPL MI MUc WMc. transport_after_call b0segs m4 m5 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply B0_fc6 with (me := m5). all: fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552.
    clear SPL MI. intros m6 yt0_6 yt1_6 yt2_6 ya5_6 ys4_6 ys5_6 ys10_6 SPL MI MUc WMc. transport_after_call b0segs m5 m6 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply B0_fc7 with (me := m6). all: fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552.
    clear SPL MI. intros m7 yt0_7 yt1_7 yt2_7 ya0_7 ya2_7 ya3_7 ya5_7 ys4_7 ys10_7 SPL MI MUc WMc. transport_after_call b0segs m6 m7 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply B0_fc8 with (me := m7). all: fc_side MU VAR1 SHa VLPK SHe V128 V1424 V1544 V1552.
    clear SPL COST MI. intros m8 S0 S1 S2 yt0_8 yt1_8 yt2_8 ya0_8 ya2_8 ya3_8 ya5_8 ya7_8 ys10_8 yt3_8 yt4_8 ES0 ES1 ES2 SPL COST MI MUc WMc. transport_after_call b0segs m7 m8 MUc WMc. clear MUc WMc.
    destruct (u8arr_of_cells b0segs _ _ _ SPL) as [SPLu LJ']. cbn [cells_size csize Nat.add] in LJ'.
    eapply (K m8 S0 S1 S2 _ yt0_8 yt1_8 yt2_8 ya0_8 ya2_8 ya3_8 ya5_8 ya7_8 ys10_8 yt3_8 yt4_8 ES0 ES1 ES2 SPLu LJ' COST MI MU WM).
  Qed.
End FC.
End ACeilS1.
