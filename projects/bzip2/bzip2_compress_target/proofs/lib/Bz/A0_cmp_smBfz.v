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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smBf1 A0_cmp_smBf2 A0_cmp_smBf3.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wsp := [(P + 232, P + 1344)]%Z.
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
  Notation Wfc := [(P + 232, P + 1344); (P + 1360, P + 1368); (CO, CO + 12)]%Z.
  Ltac vsub V MU := let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply V; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); a_sub_fp.
  Ltac ssub SH MU := eapply (shzW_sub a0segs Wfc); [exact SH| exact MU| a_sub_fp| lia| lia].
  Ltac fsub V MU := eapply (frdW_sub a0segs Wfc); [exact V| exact MU| a_sub_fp].
  Ltac fc_side MU VAR1 SHa VLPK SHe V168 V176 V184 V192 V200 V208 V216 :=
    first [ eassumption |
    lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- forall _, munch _ _ _ -> u8arr _ _ _ _ => vsub VAR1 MU
    | |- forall _, munch _ _ _ -> u32arr _ _ _ _ => vsub VLPK MU
    | |- shzW _ _ _ A1 _ => ssub SHa MU
    | |- shzW _ _ _ E _ => ssub SHe MU
    | |- frdW _ _ _ (P + 168)%Z _ => fsub V168 MU
    | |- frdW _ _ _ (P + 176)%Z _ => fsub V176 MU
    | |- frdW _ _ _ (P + 184)%Z _ => fsub V184 MU
    | |- frdW _ _ _ (P + 192)%Z _ => fsub V192 MU
    | |- frdW _ _ _ (P + 200)%Z _ => fsub V200 MU
    | |- frdW _ _ _ (P + 208)%Z _ => fsub V208 MU
    | |- frdW _ _ _ (P + 216)%Z _ => fsub V216 MU
    | |- _ => idtac
    end ].
  Lemma A0_fc : forall (m me : word -> option byte) (Jsp : list byte) (x1360 xra xt0 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 : word),
    u8arr a0segs m (P + 232) Jsp -> length Jsp = 1112%nat ->
    rw_cells a0segs m (P + 1344) [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (999999999)); C8 x1360; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (CO)); C8 (Z_to_bv 64 (FV)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 (A)); C8 (Z_to_bv 64 (totc)); C8 (Z_to_bv 64 (gs))] ->
    u8arr a0segs m CO (zb8 cb 12) ->
    mem_inv a0segs m -> munch Wfc me m -> wmono a0segs me m ->
    (forall m', munch Wfc me m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW a0segs Wfc me A1 (A1 + ARR1_SIZE) ->
    (forall m', munch Wfc me m' -> u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    shzW a0segs Wfc me E (E + ESTATE_SIZE) ->
    frdW a0segs Wfc me (P + 168) [C8 (Z_to_bv 64 (E + 51640))] ->
    frdW a0segs Wfc me (P + 176) [C8 (Z_to_bv 64 (E + 668))] ->
    frdW a0segs Wfc me (P + 184) [C8 (Z_to_bv 64 (SHE + 83))] ->
    frdW a0segs Wfc me (P + 192) [C8 (Z_to_bv 64 (A))] ->
    frdW a0segs Wfc me (P + 200) [C8 (Z_to_bv 64 (nG))] ->
    frdW a0segs Wfc me (P + 208) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW a0segs Wfc me (P + 216) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (S0 S1 S2 : Z) (Jsp' : list byte) (yra yt0 yt1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 : word),
      S0 = psum arr1 lp gs 0 0 50 -> S1 = psum arr1 lp gs 1 0 50 -> S2 = psum arr1 lp gs 2 0 50 ->
      u8arr a0segs m' (P + 232) Jsp' -> length Jsp' = 1112%nat ->
      rw_cells a0segs m' (P + 1344) [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (999999999)); C8 (Z_to_bv 64 (nSel)); C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (CO)); C8 (Z_to_bv 64 (FV)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 (A)); C8 (Z_to_bv 64 (totc)); C8 (Z_to_bv 64 (gs))] ->
      u8arr a0segs m' CO (zb8 (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 cb 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536)) 12) ->
      mem_inv a0segs m' -> munch Wfc me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR yra (Z_to_bv 64 (P)) gp tp yt0 yt1 (Z_to_bv 64 (CO)) s0 (Z_to_bv 64 (P)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (49)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (A)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 (nG)) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)))
           F (Z_to_bv 64 0x8ca4c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR xra (Z_to_bv 64 (P)) gp tp xt0 (Z_to_bv 64 (E + 37708)) xt2 s0 (Z_to_bv 64 (P)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (49)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (A)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 (nG)) (Z_to_bv 64 (E + 668)) xt3 (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)))
         F (Z_to_bv 64 0x8ac68) fc None m (seg_rom a0segs)).
  Proof.
    intros m me Jsp x1360 xra xt0 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 SPLu LJ HI COST MI MU WM VAR1 SHa VLPK SHe V168 V176 V184 V192 V200 V208 V216 K.
    destruct (u8arr_C8s 139 a0segs _ _ _ SPLu ltac:(rewrite LJ; reflexivity)) as (x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & x344 & x352 & x360 & x368 & x376 & x384 & x392 & x400 & x408 & x416 & x424 & x432 & x440 & x448 & x456 & x464 & x472 & x480 & x488 & x496 & x504 & x512 & x520 & x528 & x536 & x544 & x552 & x560 & x568 & x576 & x584 & x592 & x600 & x608 & x616 & x624 & x632 & x640 & x648 & x656 & x664 & x672 & x680 & x688 & x696 & x704 & x712 & x720 & x728 & x736 & x744 & x752 & x760 & x768 & x776 & x784 & x792 & x800 & x808 & x816 & x824 & x832 & x840 & x848 & x856 & x864 & x872 & x880 & x888 & x896 & x904 & x912 & x920 & x928 & x936 & x944 & x952 & x960 & x968 & x976 & x984 & x992 & x1000 & x1008 & x1016 & x1024 & x1032 & x1040 & x1048 & x1056 & x1064 & x1072 & x1080 & x1088 & x1096 & x1104 & x1112 & x1120 & x1128 & x1136 & x1144 & x1152 & x1160 & x1168 & x1176 & x1184 & x1192 & x1200 & x1208 & x1216 & x1224 & x1232 & x1240 & x1248 & x1256 & x1264 & x1272 & x1280 & x1288 & x1296 & x1304 & x1312 & x1320 & x1328 & x1336 & SPL). clear SPLu. cbn [map] in SPL.
    (* [comment removed for export] *)
    eapply A0_fc1 with (me := m). all: fc_side MU VAR1 SHa VLPK SHe V168 V176 V184 V192 V200 V208 V216.
    clear SPL MI. intros m1 ya4_1 SPL MI MUc WMc. transport_after_call a0segs m m1 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply A0_fc2 with (me := m1). all: fc_side MU VAR1 SHa VLPK SHe V168 V176 V184 V192 V200 V208 V216.
    clear SPL MI. intros m2 ya4_2 SPL MI MUc WMc. transport_after_call a0segs m1 m2 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply A0_fc3 with (me := m2). all: fc_side MU VAR1 SHa VLPK SHe V168 V176 V184 V192 V200 V208 V216.
    clear SPL MI. intros m3 ya4_3 SPL MI MUc WMc. transport_after_call a0segs m2 m3 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply A0_fc4 with (me := m3). all: fc_side MU VAR1 SHa VLPK SHe V168 V176 V184 V192 V200 V208 V216.
    clear SPL MI. intros m4 ya2_4 ya4_4 SPL MI MUc WMc. transport_after_call a0segs m3 m4 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply A0_fc5 with (me := m4). all: fc_side MU VAR1 SHa VLPK SHe V168 V176 V184 V192 V200 V208 V216.
    clear SPL HI MI. intros m5  SPL HI MI MUc WMc. transport_after_call a0segs m4 m5 MUc WMc. clear MUc WMc.
    (* [comment removed for export] *)
    eapply A0_fc6 with (me := m5). all: fc_side MU VAR1 SHa VLPK SHe V168 V176 V184 V192 V200 V208 V216.
    clear SPL HI COST MI. intros m6 S0 S1 S2 yra_6 yt0_6 yt1_6 ya0_6 ya1_6 ya2_6 ya3_6 ya4_6 ya5_6 ya6_6 ya7_6 ES0 ES1 ES2 SPL HI COST MI MUc WMc. transport_after_call a0segs m5 m6 MUc WMc. clear MUc WMc.
    destruct (u8arr_of_cells a0segs _ _ _ SPL) as [SPLu LJ']. cbn [cells_size csize Nat.add] in LJ'.
    eapply (K m6 S0 S1 S2 _ yra_6 yt0_6 yt1_6 ya0_6 ya1_6 ya2_6 ya3_6 ya4_6 ya5_6 ya6_6 ya7_6 ES0 ES1 ES2 SPLu LJ' HI COST MI MU WM).
  Qed.
End FC.
End ACeilS1.
