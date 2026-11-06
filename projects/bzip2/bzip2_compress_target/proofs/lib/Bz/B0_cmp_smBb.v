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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV B0_cmp_sdV B0_cmp_smV B0_cmp_smBa B0_cmp_smBfz B0_cmp_smBrz.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GGB.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32) (lp len : zarr).
  Variables (P SHE CO FV : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis COL : (0 < CO)%Z. Hypothesis COH : (CO + 12 <= CEIL)%Z. Hypothesis FVL : (0 < FV)%Z. Hypothesis FVH : (FV + 24 <= CEIL)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  (* [comment removed for export] *)
  Hypothesis SEFV : id ((c_E cx + 55768 <= FV)%Z \/ (FV + 24 <= c_E cx)%Z).
  Hypothesis SECO : id ((c_E cx + 55768 <= CO)%Z \/ (CO + 12 <= c_E cx)%Z).
  Hypothesis SCOFV : id ((CO + 12 <= FV)%Z \/ (FV + 24 <= CO)%Z).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis MV : forall i, (0 <= i < nMTF)%Z -> (0 <= mtfv_at arr1 i < A)%Z.
  Hypothesis LF : forall t v, (0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z.
  Hypothesis LPF : nG = 6%Z -> forall v j, (0 <= v < A)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * v + j) = true /\ (0 <= zget lp (4 * v + j) < 2097152)%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)

  Notation GRB t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 :=
    (mkR (Z_to_bv 64 (E + 51640)) cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (258 * nG)) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 257)
         (Z_to_bv 64 CO) s10 (Z_to_bv 64 (CO + 12)) t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9))).
  (* [comment removed for export] *)
  Notation HIG v32 totc v88 nSel :=
    (sd_hi cx nG (SDW (Z_to_bv 64 FV) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 (Z_to_bv 64 totc) (Z_to_bv 64 nMTF) (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448))
                      (Z_to_bv 64 A) (Z_to_bv 64 nSel) (Z_to_bv 64 (E + 37708)))).

  (* [comment removed for export] *)
  Definition Wg : list (Z * Z) :=
    [(E + 1704, E + 19706); (E + 45448, E + 51640); (P + 136, P + 1264); (P + 1384, P + 1568); (FV, FV + 24); (CO, CO + 12)]%Z.
  (* [comment removed for export] *)
  Ltac hidisj := cbn [disjoint_from]; unfold sd_hi; cbv zeta; simpl_sizes; Lib.Step.slia.
  Ltac gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc :=
    first [ eassumption |
    lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- forall _, munch _ _ _ -> u8arr _ _ A1 _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VAR1; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); unfold Wg; a_sub_fp
    | |- forall _, munch _ _ _ -> u8arr _ _ (E + 37708)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VLEN; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); unfold Wg; a_sub_fp
    | |- forall _, munch _ _ _ -> u32arr _ _ (E + 51640)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VLPK; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); unfold Wg; a_sub_fp
    | |- shzW _ _ _ A1 _ => eapply (shzW_sub b0segs Wg); [exact SHa| exact MU| unfold Wg; a_sub_fp| lia| lia]
    | |- shzW _ _ _ E _ => eapply (shzW_sub b0segs Wg); [exact SHe| exact MU| unfold Wg; a_sub_fp| lia| lia]
    | |- shzW _ _ _ FV _ => eapply (shzW_sub b0segs Wg); [exact SHf| exact MU| unfold Wg; a_sub_fp| lia| lia]
    | |- shpW _ _ _ CO _ => eapply (shpW_sub b0segs Wg); [exact SHc| exact MU| unfold Wg; a_sub_fp| lia| lia]
    | |- frdW _ _ _ (P + 128)%Z _ => eapply (frdW_sub b0segs Wg); [exact V128| exact MU| unfold Wg; a_sub_fp]
    | |- frdW _ _ _ (P + 1264)%Z _ => eapply (frdW_sub b0segs Wg); [exact VSET| exact MU| unfold Wg; a_sub_fp]
    | |- frdW _ _ _ (P + 1384)%Z _ => apply frdW_intro; [exact HI| hidisj]
    | |- frdW _ _ _ (P + ?o)%Z _ =>
        let k := eval vm_compute in (Z.to_nat (o - 1384)) in
        eapply (frdW_cell_at b0segs _ _ (P + 1384)%Z _ k); [apply frdW_intro; [exact HI| hidisj]| reflexivity| lia]
    | |- (_ <= _)%Z => first [lia | idtac]
    | |- (_ < _)%Z => first [lia | idtac]
    | |- (_ /\ _) => first [lia | idtac]
    | |- (_ \/ _) => first [lia | idtac]
    | |- (@eq Z _ _) => first [lia | idtac]
    | |- _ => idtac
    end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_grp : forall (rf sel cost fave : zarr) (gs nSel totc : Z) (Jsp jc : list byte) (v32 v88 : word) (m me : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s10 t3 t4 : word),
    (0 <= gs < nMTF)%Z -> (0 <= nSel < 18001)%Z -> (0 <= totc <= 65535 * nSel)%Z ->
    (forall t, (0 <= t < nG)%Z -> RFrow rf t A gs) -> (forall t, (0 <= t < 6)%Z -> (0 <= zget fave t <= nSel)%Z) ->
    length Jsp = 1128%nat -> length jc = 12%nat ->
    u32arr b0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    u8arr b0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    u8arr b0segs m (P + 136) Jsp ->
    rw_cells b0segs m (P + 1384) (HIG v32 totc v88 nSel) ->
    u32arr b0segs m FV (zw32 fave 6) ->
    u8arr b0segs m CO jc ->
    mem_inv b0segs m -> munch Wg me m -> wmono b0segs me m ->
    (forall m', munch Wg me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wg me m' -> u8arr b0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    (forall m', munch Wg me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    frdW b0segs Wg me (P + 128) [C8 (Z_to_bv 64 (E + 51640))] -> frdW b0segs Wg me (P + 1264) (sm_set cx FV) ->
    shzW b0segs Wg me A1 (A1 + ARR1_SIZE) -> shzW b0segs Wg me E (E + ESTATE_SIZE) -> shzW b0segs Wg me FV (FV + 24) -> shpW b0segs Wg me CO (CO + 12) ->
    (forall m' (Jsp' jc' : list byte) (t0' t1' t2' a0' a1' a2' a3' a5' a6' a7' s10' t3' t4' : word),
      let ge := GE nMTF gs in let cst := COSTC arr1 len lp nG gs ge cost in let r := sm_best (Z.to_nat nG) cst 0 999999999 (-1) in
      length Jsp' = 1128%nat -> length jc' = 12%nat -> (0 <= snd r < nG)%Z -> (0 <= fst r <= 65535)%Z ->
      u32arr b0segs m' (E + 45448) (ovw (sm_rfreq_inc (Z.to_nat (ge - gs + 1)) rf arr1 (snd r) gs) (jseg J 45448 6192) 1548) ->
      u8arr b0segs m' (E + 1704) (ovb (zset sel nSel (snd r mod 256)) (jseg J 1704 18002) 18002) ->
      u8arr b0segs m' (P + 136) Jsp' ->
      rw_cells b0segs m' (P + 1384) (HIG (Z_to_bv 64 ge) (totc + fst r) (Z_to_bv 64 (gs + 50)) (nSel + 1)) ->
      u32arr b0segs m' FV (zw32 (zincr fave (snd r)) 6) ->
      u8arr b0segs m' CO jc' ->
      mem_inv b0segs m' -> munch Wg me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (GRB t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 (ge + 1)) a5' a6' a7' s10' t3' t4')
                       F (Z_to_bv 64 (if (ge + 1 <? nMTF)%Z then 0x8c7a4 else 0x9394c)) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8c7a4) fc None m (seg_rom b0segs)).
  Proof.
    intros rf sel cost fave gs nSel totc Jsp jc v32 v88 m me t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s10 t3 t4
           Hgs HnS Htc RFR FVB LJsp Ljc RFQ SEL SPL HI FAVE COST MI MU WM VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold Wg in *.
    pose proof CEP as CEP'. pose proof COH as COH'. pose proof FVH as FVH'. unfold CEIL in CEP', COH', FVH'.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    cbv zeta in K. set (ge := GE nMTF gs) in *.
    (* [comment removed for export] *)
    assert (KT : forall (bc bt : Z) (cst : zarr) (m4 : word -> option byte) (Jsp4 jc4 : list byte) (y0 y1 y2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys10 y3 y4 : word),
      cst = COSTC arr1 len lp nG gs ge cost -> sm_best (Z.to_nat nG) cst 0 999999999 (-1) = (bc, bt) -> (0 <= bt < nG)%Z -> (0 <= bc <= 65535)%Z ->
      length Jsp4 = 1128%nat -> length jc4 = 12%nat ->
      u32arr b0segs m4 (E + 45448) (ovw (sm_rfreq_inc (Z.to_nat (ge - gs + 1)) rf arr1 bt gs) (jseg J 45448 6192) 1548) ->
      u8arr b0segs m4 (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      u8arr b0segs m4 (P + 136) Jsp4 ->
      rw_cells b0segs m4 (P + 1384) (HIG (Z_to_bv 64 ge) (totc + bc) (Z_to_bv 64 (gs + 50)) nSel) ->
      u32arr b0segs m4 FV (zw32 (zincr fave bt) 6) ->
      u8arr b0segs m4 CO jc4 ->
      mem_inv b0segs m4 -> munch [(E + 1704, E + 19706); (E + 45448, E + 51640); (P + 136, P + 1264); (P + 1384, P + 1568); (FV, FV + 24); (CO, CO + 12)]%Z me m4 -> wmono b0segs me m4 ->
      evt b0segs Q (MS (GRB y0 y1 y2 ya0 ya1 ya2 ya3 (Z_to_bv 64 (ge + 1)) ya5 ya6 ya7 ys10 y3 y4) F (Z_to_bv 64 0x91d9c) fc None m4 (seg_rom b0segs))).
    { intros bc bt cst m4 Jsp4 jc4 y0 y1 y2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys10 y3 y4 Ecst EB Hbt Hbc LJ4 Lj4 RFQ4 SEL4 SPL4 HI4 FAVE4 COST4 MI4 MU4 WM4.
      eapply evt_eq; [| eapply B0_sm_tail with (gs := gs) (nSel := nSel) (mf := m4) (P := P) (CO := CO) (FV := FV)].
      all: gside MU4 HI4 VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      - (* [comment removed for export] *)
        intros m5 xa0 xa1 Hlt HI5 MI5 MU5 WM5. clear HI4 MI4. transport_after_call b0segs m4 m5 MU5 WM5. clear MU5 WM5.
        pose proof (K m5 Jsp4 jc4 y0 y1 y2 xa0 xa1 ya2 ya3 ya5 ya6 ya7 ys10 y3 y4) as K'. rewrite <- Ecst, EB in K'. cbn [fst snd] in K'.
        replace (ge + 1 <? nMTF)%Z with true in K' by (symmetry; apply Z.ltb_lt; lia).
        enter_with K'; [st_eq| exact LJ4| exact Lj4| exact Hbt| exact Hbc| eassumption| eassumption| eassumption| exact HI5| eassumption| eassumption| assumption| assumption| assumption].
      - (* [comment removed for export] *)
        intros m5 xa0 xa1 Hge HI5 MI5 MU5 WM5. clear HI4 MI4. transport_after_call b0segs m4 m5 MU5 WM5. clear MU5 WM5.
        pose proof (K m5 Jsp4 jc4 y0 y1 y2 xa0 xa1 ya2 ya3 ya5 ya6 ya7 ys10 y3 y4) as K'. rewrite <- Ecst, EB in K'. cbn [fst snd] in K'.
        replace (ge + 1 <? nMTF)%Z with false in K' by (symmetry; apply Z.ltb_ge; lia).
        enter_with K'; [st_eq| exact LJ4| exact Lj4| exact Hbt| exact Hbc| eassumption| eassumption| eassumption| exact HI5| eassumption| eassumption| assumption| assumption| assumption]. }
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply B0_sm_head with (gs := gs) (jc := jc) (mf := m) (P := P) (CO := CO) (FV := FV)].
    all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
    { st_eq. }
    - (* [comment removed for export] *)
      clear COST HI MI. intros m1 xa0 xa1. cbv zeta. fold ge. intros FB COST HI MI MU1 WM1.
      transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
      assert (NG6 : nG = 6%Z) by (unfold fastb in FB; destruct (Z.eqb_spec nG 6); [assumption| cbn in FB; discriminate]).
      assert (G49 : (ge - gs = 49)%Z).
      { unfold fastb in FB. fold ge in FB. destruct (Z.eqb_spec (ge - gs) 49); [assumption|]. rewrite NG6 in FB. cbn in FB. discriminate. }
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply B0_fc with (me := m1) (lp := lp) (cb := znew) (gs := gs) (CO := CO) (P := P)].
      all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      { intros k Hk. unfold QV. apply MV. lia. }
      { intros k j Hk Hj. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. exact (proj2 (LPF NG6 _ _ Hq Hj)). }
      { intros k j Hk Hj. unfold QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. exact (proj1 (LPF NG6 _ _ Hq Hj)). }
      clear SPL COST MI.
      intros m2 S0 S1 S2 Jsp2 yt0 yt1 yt2 ya0 ya2 ya3 ya5 ya7 ys10 yt3 yt4 ES0 ES1 ES2 SPL LJ2 COST MI MU2 WM2.
      transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
      assert (HS0 : (0 <= S0)%Z). { rewrite ES0. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      assert (HS1 : (0 <= S1)%Z). { rewrite ES1. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      assert (HS2 : (0 <= S2)%Z). { rewrite ES2. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      pose proof (COSTREL_le _ _ 6 nG (COSTREL_fast6 cost S0 S1 S2 HS0 HS1 HS2) ltac:(lia)) as CR.
      pose proof (COSTC_fast arr1 len lp nG nMTF gs cost FB) as CF. rewrite <- ES0, <- ES1, <- ES2 in CF. rewrite <- CF in CR. clear CF. fold ge in CR.
      remember (COSTC arr1 len lp nG gs ge cost) as cst eqn:Ecst.
      assert (HC : forall t, (0 <= t < nG)%Z -> (0 <= zget cst t <= 65535)%Z).
      { destruct CR as [CBOK CREL]. intros t' Ht'. rewrite <- (CREL t' ltac:(lia)). pose proof (zbok_rd16 _ (2 * t') CBOK). lia. }
      (* [comment removed for export] *)
      lazymatch type of COST with u8arr _ _ _ (zb8 ?cbx 12) =>
        eapply evt_eq; [| eapply B0_sm_bt with (cb := cbx) (cost := cst) (CO := CO) (P := P)] end.
      all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      intros za2 za3.
      destruct (B0_cmp_smBa.BEST cst (Z.to_nat nG)) as [bc bt] eqn:EB. unfold B0_cmp_smBa.BEST in EB. cbn [fst snd].
      pose proof (B0_cmp_smBa.BEST_range cst (Z.to_nat nG) ltac:(lia) ltac:(intros t' Ht'; apply HC; lia)) as BR. unfold B0_cmp_smBa.BEST in BR. rewrite EB in BR. cbn [fst snd] in BR. destruct BR as [Hbc Hbt].
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply B0_sm_post with (gs := gs) (bt := bt) (bc := bc) (totc := totc) (nSel := nSel) (fave := fave) (sel := sel) (mf := m2) (P := P) (CO := CO) (FV := FV)].
      all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      { pose proof (FVB bt ltac:(lia)). lia. }
      2:{ intros; exfalso; congruence. }
      clear FAVE SEL HI MI. intros m3 wa0 wa2 wa3 _ FAVE SEL HI MI MU3 WM3.
      transport_after_call b0segs m2 m3 MU3 WM3. clear MU3 WM3.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply B0_fr with (me := m3) (rf0 := rf) (gs := gs) (bt := bt) (B := gs) (P := P)].
      all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      { intros k Hk. unfold QV. apply MV. lia. }
      { apply RFR. lia. }
      clear RFQ MI. intros m4 rf4 za0 za1 zza2 zza3 za5 za7 RFQ ERF4 RFF4 MI MU4 WM4.
      transport_after_call b0segs m3 m4 MU4 WM4. clear MU4 WM4.
      rewrite ERF4 in RFQ. replace 50%nat with (Z.to_nat (ge - gs + 1)) in RFQ by lia.
      (* [comment removed for export] *)
      lazymatch type of COST with u8arr _ _ _ ?jj =>
        enter_with (KT bc bt cst m4 Jsp2 jj _ _ _ _ _ _ _ _ _ _ _ _ _);
          [st_eq| reflexivity| exact EB| lia| exact Hbc| exact LJ2| rewrite zb8_length_nat; reflexivity| exact RFQ| exact SEL| exact SPL| exact HI| exact FAVE| exact COST| exact MI| exact MU| exact WM] end.
    - (* [comment removed for export] *)
      clear COST HI MI. intros m1 xa0 xa1. cbv zeta. fold ge. intros FB COST HI MI MU1 WM1.
      transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
      pose proof (COSTREL_zero cost nG ltac:(lia)) as CR0.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply B0_sm_csg with (gs := gs) (ge := ge) (cb := znew) (cost := zero6 cost) (len := len) (mf := m1) (P := P) (CO := CO) (FV := FV)].
      all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      clear COST MI. intros m2 cb2 yt0 yt1 yt2 ya0 ya2 ya3 ya5 ya7 yt3 yt4 COST CR MI MU2 WM2.
      transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
      replace (Z.to_nat (ge + 1 - gs)) with (Z.to_nat (ge - gs + 1)) in CR by lia.
      pose proof (COSTC_slow arr1 len lp nG nMTF gs cost FB) as CS. fold ge in CS. rewrite <- CS in CR. clear CS.
      remember (COSTC arr1 len lp nG gs ge cost) as cst eqn:Ecst.
      assert (HC : forall t, (0 <= t < nG)%Z -> (0 <= zget cst t <= 65535)%Z).
      { destruct CR as [CBOK CREL]. intros t' Ht'. rewrite <- (CREL t' ltac:(lia)). pose proof (zbok_rd16 _ (2 * t') CBOK). lia. }
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply B0_sm_bt with (cb := cb2) (cost := cst) (CO := CO) (P := P)].
      all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      intros za2 za3.
      destruct (B0_cmp_smBa.BEST cst (Z.to_nat nG)) as [bc bt] eqn:EB. unfold B0_cmp_smBa.BEST in EB. cbn [fst snd].
      pose proof (B0_cmp_smBa.BEST_range cst (Z.to_nat nG) ltac:(lia) ltac:(intros t' Ht'; apply HC; lia)) as BR. unfold B0_cmp_smBa.BEST in BR. rewrite EB in BR. cbn [fst snd] in BR. destruct BR as [Hbc Hbt].
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply B0_sm_post with (gs := gs) (bt := bt) (bc := bc) (totc := totc) (nSel := nSel) (fave := fave) (sel := sel) (mf := m2) (P := P) (CO := CO) (FV := FV)].
      all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      { pose proof (FVB bt ltac:(lia)). lia. }
      1:{ intros; exfalso; congruence. }
      clear FAVE SEL HI MI. intros m3 wa0 wa2 wa3 _ FAVE SEL HI MI MU3 WM3.
      transport_after_call b0segs m2 m3 MU3 WM3. clear MU3 WM3.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply B0_sm_rfsg with (gs := gs) (ge := ge) (bt := bt) (B := gs) (rf := rf) (mf := m3) (P := P) (CO := CO) (FV := FV)].
      all: gside MU HI VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc.
      { st_eq. }
      { apply RFR. lia. }
      clear RFQ MI. intros m4 rf4 zt0 zt1 za0 za1 zza2 zza3 za5 za7 RFQ ERF4 RFF4 MI MU4 WM4.
      transport_after_call b0segs m3 m4 MU4 WM4. clear MU4 WM4.
      rewrite ERF4 in RFQ. replace (ge + 1 - gs)%Z with (ge - gs + 1)%Z in RFQ by lia.
      (* [comment removed for export] *)
      lazymatch type of COST with u8arr _ _ _ ?jj =>
        enter_with (KT bc bt cst m4 Jsp jj _ _ _ _ _ _ _ _ _ _ _ _ _);
          [st_eq| reflexivity| exact EB| lia| exact Hbc| exact LJsp| rewrite zb8_length_nat; reflexivity| exact RFQ| exact SEL| exact SPL| exact HI| exact FAVE| exact COST| exact MI| exact MU| exact WM] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_gloop : forall (n j : nat) (s : sits) (Jsp jc : list byte) (v32 v88 : word) (m me : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s10 t3 t4 : word),
    smB_grp e s -> it_len s = len -> it_lpk e s = lp ->
    (1 <= KSEL e <= 18002)%Z -> (50 * (KSEL e - 1) < nMTF <= 50 * KSEL e)%Z ->
    (Z.of_nat j + Z.of_nat n = KSEL e)%Z -> (1 <= n)%nat ->
    length Jsp = 1128%nat -> length jc = 12%nat ->
    u32arr b0segs m (E + 45448) (ovw (g_rfreq (Gj e s j)) (jseg J 45448 6192) 1548) ->
    u8arr b0segs m (E + 1704) (ovb (g_sel (Gj e s j)) (jseg J 1704 18002) 18002) ->
    u8arr b0segs m (P + 136) Jsp ->
    rw_cells b0segs m (P + 1384) (HIG v32 (g_totc (Gj e s j)) v88 (g_nSel (Gj e s j))) ->
    u32arr b0segs m FV (zw32 (g_fave (Gj e s j)) 6) ->
    u8arr b0segs m CO jc ->
    mem_inv b0segs m -> munch Wg me m -> wmono b0segs me m ->
    (forall m', munch Wg me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wg me m' -> u8arr b0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    (forall m', munch Wg me m' -> u32arr b0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    frdW b0segs Wg me (P + 128) [C8 (Z_to_bv 64 (E + 51640))] -> frdW b0segs Wg me (P + 1264) (sm_set cx FV) ->
    shzW b0segs Wg me A1 (A1 + ARR1_SIZE) -> shzW b0segs Wg me E (E + ESTATE_SIZE) -> shzW b0segs Wg me FV (FV + 24) -> shpW b0segs Wg me CO (CO + 12) ->
    (forall m' (Jsp' jc' : list byte) (v32' v88' : word) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' : word),
      length Jsp' = 1128%nat -> length jc' = 12%nat ->
      u32arr b0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
      u8arr b0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
      u8arr b0segs m' (P + 136) Jsp' ->
      rw_cells b0segs m' (P + 1384) (HIG v32' (g_totc (Gend e s)) v88' (g_nSel (Gend e s))) ->
      u32arr b0segs m' FV (zw32 (g_fave (Gend e s)) 6) ->
      u8arr b0segs m' CO jc' ->
      mem_inv b0segs m' -> munch Wg me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (GRB t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4')
                       F (Z_to_bv 64 0x9394c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (g_gs (Gj e s j))) a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8c7a4) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros j s Jsp jc v32 v88 m me t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s10 t3 t4
           HGF Elen Elp HK1 HK2 Hj Hn LJsp Ljc RFQ SEL SPL HI FAVE COST MI MU WM VAR1 VLEN VLPK V128 VSET SHa SHe SHf SHc K.
    destruct HGF as [GF GEND].
    pose proof (GF j ltac:(lia)) as Fj. cbv zeta in Fj. cps_destruct Fj as (Egs & EnS & Htc & RFF & FVB & SLF).
    remember (Gj e s j) as gj eqn:EGJ.
    destruct gj as [rf sel cost fave nSel totc gs]. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in *.
    subst nSel. assert (Egs' : gs = (50 * Z.of_nat j)%Z) by (rewrite Egs; apply Z.min_l; lia).
    eapply (B0_sm_grp rf sel cost fave gs (Z.of_nat j) totc Jsp jc v32 v88 m me);
      [lia| lia| lia| | | exact LJsp| exact Ljc| exact RFQ| exact SEL| exact SPL| exact HI| exact FAVE| exact COST| exact MI| exact MU| exact WM
      | exact VAR1| exact VLEN| exact VLPK| exact V128| exact VSET| exact SHa| exact SHe| exact SHf| exact SHc|].
    { intros t Ht v Hv. apply RFF; lia. }
    { intros t Ht. apply FVB. lia. }
    clear RFQ SEL SPL HI FAVE COST MI MU WM.
    intros m' Jsp' jc' t0' t1' t2' a0' a1' a2' a3' a5' a6' a7' s10' t3' t4'. cbv zeta.
    intros LJsp' Ljc' Hbt Hbc RFQ SEL SPL HI FAVE COST MI MU WM.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    (* [comment removed for export] *)
    assert (EG' : Gj e s (S j) = sm_group_iter arr1 len lp nG nMTF (SGS rf sel cost fave (Z.of_nat j) totc gs)).
    { rewrite Gj_S, Elen, Elp, <- EGJ. reflexivity. }
    rewrite sm_group_iter_eq in EG'. cbv zeta in EG'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in EG'.
    destruct (Z.ltb_spec (GE nMTF gs + 1) nMTF) as [LT|GEQ].
    - (* [comment removed for export] *)
      assert (Hj1 : (Z.of_nat (S j) < KSEL e)%Z) by (destruct (Z.lt_ge_cases (Z.of_nat (S j)) (KSEL e)); [assumption| exfalso; nia]).
      pose proof (IH (S j) s Jsp' jc' (Z_to_bv 64 (GE nMTF gs)) (Z_to_bv 64 (gs + 50)) m' me) as IH'. rewrite EG' in IH'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in IH'.
      enter_with IH';
        [st_eq| split; [exact GF| exact GEND]| exact Elen| exact Elp| lia| lia| lia| lia| exact LJsp'| exact Ljc'
        | exact RFQ| exact SEL| exact SPL| exact HI| exact FAVE| exact COST| exact MI| exact MU| exact WM
        | exact VAR1| exact VLEN| exact VLPK| exact V128| exact VSET| exact SHa| exact SHe| exact SHf| exact SHc| exact K].
    - (* [comment removed for export] *)
      assert (Hj1 : (Z.of_nat (S j) = KSEL e)%Z) by (destruct (Z.eq_dec (Z.of_nat (S j)) (KSEL e)); [assumption| exfalso; nia]).
      assert (EEND : Gend e s = Gj e s (S j)) by (unfold Gend; f_equal; lia).
      pose proof (K m' Jsp' jc' (Z_to_bv 64 (GE nMTF gs)) (Z_to_bv 64 (gs + 50))) as K'. rewrite EEND, EG' in K'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in K'.
      enter_with K';
        [st_eq| exact LJsp'| exact Ljc'| exact RFQ| exact SEL| exact SPL| exact HI| exact FAVE| exact COST| exact MI| exact MU| exact WM].
  Qed.
End GGB.
End ACeilS1.
