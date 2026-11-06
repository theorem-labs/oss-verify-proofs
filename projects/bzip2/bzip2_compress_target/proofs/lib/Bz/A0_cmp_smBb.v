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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV A0_cmp_smBa A0_cmp_smBfz A0_cmp_smBrz.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GG.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32) (lp len : zarr).
  Variables (P SHE CO FV : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
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
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation GA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 (E + 37708)) cSB s5 s6 (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) (Z_to_bv 64 (E + 668)) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition Wg : list (Z * Z) :=
    [(E + 1704, E + 19706); (E + 45448, E + 51640); (P + 232, P + 1344); (P + 1360, P + 1368); (P + 1424, P + 1440); (FV, FV + 24); (CO, CO + 12)]%Z.
  (* [comment removed for export] *)
  Ltac gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc :=
    first [ eassumption |
    lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- forall _, munch _ _ _ -> u8arr _ _ A1 _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VAR1; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); unfold Wg; a_sub_fp
    | |- forall _, munch _ _ _ -> u8arr _ _ (E + 37708)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VLEN; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); unfold Wg; a_sub_fp
    | |- forall _, munch _ _ _ -> u32arr _ _ (E + 51640)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VLPK; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); unfold Wg; a_sub_fp
    | |- shzW _ _ _ A1 _ => eapply (shzW_sub a0segs Wg); [exact SHa| exact MU| unfold Wg; a_sub_fp| lia| lia]
    | |- shzW _ _ _ E _ => eapply (shzW_sub a0segs Wg); [exact SHe| exact MU| unfold Wg; a_sub_fp| lia| lia]
    | |- shzW _ _ _ FV _ => eapply (shzW_sub a0segs Wg); [exact SHf| exact MU| unfold Wg; a_sub_fp| lia| lia]
    | |- shpW _ _ _ CO _ => eapply (shpW_sub a0segs Wg); [exact SHc| exact MU| unfold Wg; a_sub_fp| lia| lia]
    | |- frdW _ _ _ (E + 640)%Z _ => eapply (frdW_sub a0segs Wg); [exact VEH2| exact MU| unfold Wg; a_sub_fp]
    | |- frdW _ _ _ (P + ?o)%Z _ =>
        let lo := eval vm_compute in (Z.ltb o 232) in
        lazymatch lo with
        | true => let k := eval vm_compute in (Z.to_nat (o - 160)) in
                  eapply (frdW_cell_at a0segs _ _ (P + 160)%Z (sm_loB cx e SHE) k); [eapply (frdW_sub a0segs Wg); [exact VLO| exact MU| unfold Wg; a_sub_fp]| reflexivity| lia]
        | false => let k := eval vm_compute in (Z.to_nat (o - 1344)) in
                   eapply (frdW_cell_at a0segs _ _ (P + 1344)%Z _ k); [apply frdW_intro; [exact HI| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]
        end
    | |- (_ <= _)%Z => first [lia | idtac]
    | |- (_ < _)%Z => first [lia | idtac]
    | |- (_ /\ _) => first [lia | idtac]
    | |- (_ \/ _) => first [lia | idtac]
    | |- (@eq Z _ _) => first [lia | idtac]
    | |- _ => idtac
    end ].

  Notation COSTQ cost gs := (COSTC arr1 len lp nG gs (GE nMTF gs) cost).
  Notation BESTQ cost gs := (sm_best (Z.to_nat nG) (COSTQ cost gs) 0 999999999 (-1)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_grp : forall (rf sel cost fave : zarr) (gs nSel totc : Z) (Jsp : list byte) (w1360 : word) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (0 <= gs < nMTF)%Z -> (0 <= nSel < 18001)%Z -> (0 <= totc <= 65535 * nSel)%Z ->
    (forall t, (0 <= t < nG)%Z -> RFrow rf t A gs) -> (forall t, (0 <= t < 6)%Z -> (0 <= zget fave t <= nSel)%Z) ->
    length Jsp = 1112%nat ->
    u32arr a0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    u8arr a0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    u8arr a0segs m (P + 232) Jsp ->
    rw_cells a0segs m (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
    u32arr a0segs m FV (zw32 fave 6) ->
    u8arr a0segs m CO (zb8 znew 12) ->
    mem_inv a0segs m -> munch Wg me m -> wmono a0segs me m ->
    (forall m', munch Wg me m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wg me m' -> u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    (forall m', munch Wg me m' -> u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    frdW a0segs Wg me (P + 160) (sm_loB cx e SHE) -> frdW a0segs Wg me (E + 640) (EHEAD2 cx g e) ->
    shzW a0segs Wg me A1 (A1 + ARR1_SIZE) -> shzW a0segs Wg me E (E + ESTATE_SIZE) -> shzW a0segs Wg me FV (FV + 24) -> shpW a0segs Wg me CO (CO + 12) ->
    (* [comment removed for export] *)
    (forall m' (Jsp' : list byte) (w1360' : word) (cb' : zarr) (t0' t1' a3' a4' a5' a6' a7' t3' t5' t6' : word),
      let ge := GE nMTF gs in let r := BESTQ cost gs in
      (ge + 1 < nMTF)%Z -> length Jsp' = 1112%nat -> (0 <= snd r < nG)%Z -> (0 <= fst r <= 65535)%Z ->
      u32arr a0segs m' (E + 45448) (ovw (sm_rfreq_inc (Z.to_nat (ge - gs + 1)) rf arr1 (snd r) gs) (jseg J 45448 6192) 1548) ->
      u8arr a0segs m' (E + 1704) (ovb (zset sel nSel (snd r mod 256)) (jseg J 1704 18002) 18002) ->
      u8arr a0segs m' (P + 232) Jsp' ->
      rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV w1360' (totc + fst r) (ge + 1)) ->
      u32arr a0segs m' FV (zw32 (zincr fave (snd r)) 6) ->
      u8arr a0segs m' CO (zb8 cb' 12) ->
      mem_inv a0segs m' -> munch Wg me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (GA (Z_to_bv 64 0x8ac34) t0' t1' (Z_to_bv 64 CO) (Z_to_bv 64 CO) (Z_to_bv 64 0) (Z_to_bv 64 12) a3' a4' a5' a6' a7'
                           (Z_to_bv 64 nMTF) (Z_to_bv 64 (nSel + 1)) (Z_to_bv 64 (ge + 1 + 49)) t3' (Z_to_bv 64 (ge + 1)) t5' t6')
                       F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (Jsp' : list byte) (w1360' : word) (cb' : zarr) (ra' t0' t1' a3' a4' a5' a6' a7' t3' t5' t6' : word),
      let ge := GE nMTF gs in let r := BESTQ cost gs in
      (ge + 1 = nMTF)%Z -> length Jsp' = 1112%nat -> (0 <= snd r < nG)%Z -> (0 <= fst r <= 65535)%Z ->
      u32arr a0segs m' (E + 45448) (ovw (sm_rfreq_inc (Z.to_nat (ge - gs + 1)) rf arr1 (snd r) gs) (jseg J 45448 6192) 1548) ->
      u8arr a0segs m' (E + 1704) (ovb (zset sel nSel (snd r mod 256)) (jseg J 1704 18002) 18002) ->
      u8arr a0segs m' (P + 232) Jsp' ->
      rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV w1360' totc gs) ->
      u32arr a0segs m' FV (zw32 (zincr fave (snd r)) 6) ->
      u8arr a0segs m' CO (zb8 cb' 12) ->
      mem_inv a0segs m' -> munch Wg me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (GA ra' t0' t1' (Z_to_bv 64 CO) (Z_to_bv 64 (totc + fst r)) (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 (fst r)) a3' a4' a5' a6' a7'
                           (Z_to_bv 64 nMTF) (Z_to_bv 64 (nSel + 1)) (Z_to_bv 64 (E + 668)) t3' (Z_to_bv 64 (ge + 1)) t5' t6')
                       F (Z_to_bv 64 0x8f16c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 nMTF) (Z_to_bv 64 nSel) (Z_to_bv 64 (gs + 49)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8ac34) fc None m (seg_rom a0segs)).
  Proof.
    intros rf sel cost fave gs nSel totc Jsp w1360 m me ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           Hgs HnS Htc RFR FVB LJsp RFQ SEL SPL HI FAVE COST MI MU WM VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc KN KX.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold sm_hi in HI. cbv zeta in HI. unfold Wg in *.
    pose proof CEP as CEP'. pose proof COH as COH'. pose proof FVH as FVH'. unfold CEIL in CEP', COH', FVH'.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    set (ge := GE nMTF gs) in *.
    (* [comment removed for export] *)
    eapply A0_sm_head with (gs := gs).
    all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
    all: intros xa0; cbv zeta; intros Hff; fold ge in Hff |- *.
    - (* [comment removed for export] *)
      assert (NG6 : nG = 6%Z) by (unfold fastf, fastb in Hff; destruct (Z.eqb_spec nG 6); [assumption| cbn in Hff; lia]).
      assert (G49 : (ge - gs = 49)%Z).
      { unfold fastf in Hff. fold ge in Hff. destruct (Z.eqb_spec (ge - gs) 49); [assumption|]. rewrite NG6 in Hff. cbn in Hff. lia. }
      assert (FB : fastb nG nMTF gs = true).
      { unfold fastb. fold ge. rewrite NG6. replace (ge - gs =? 49)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply A0_fc with (me := m) (lp := lp) (cb := znew) (gs := gs) (nSel := nSel) (totc := totc) (CO := CO) (FV := FV) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      { intros k Hk. unfold QV. apply MV. lia. }
      { intros k j Hk Hj. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. exact (proj2 (LPF NG6 _ _ Hq Hj)). }
      { intros k j Hk Hj. unfold QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. exact (proj1 (LPF NG6 _ _ Hq Hj)). }
      clear SPL HI COST MI.
      intros m2 S0 S1 S2 Jsp2 yra yt0 yt1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ES0 ES1 ES2 SPL LJ2 HI COST MI MU2 WM2.
      transport_after_call a0segs m m2 MU2 WM2. clear MU2 WM2.
      assert (HS0 : (0 <= S0)%Z). { rewrite ES0. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      assert (HS1 : (0 <= S1)%Z). { rewrite ES1. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      assert (HS2 : (0 <= S2)%Z). { rewrite ES2. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      pose proof (COSTREL_le _ _ 6 nG (COSTREL_fast6 cost S0 S1 S2 HS0 HS1 HS2) ltac:(lia)) as CR.
      pose proof (COSTC_fast arr1 len lp nG nMTF gs cost FB) as CF. rewrite <- ES0, <- ES1, <- ES2 in CF. rewrite <- CF in CR. clear CF. fold ge in CR.
      set (cst := COSTC arr1 len lp nG gs ge cost) in *.
      pose proof (COSTC_0 arr1 len lp nG gs ge cost) as C0. fold cst in C0.
      (* [comment removed for export] *)
      lazymatch type of COST with u8arr _ _ _ (zb8 ?cbx 12) =>
        eapply evt_eq; [| eapply A0_sm_btg with (cb := cbx) (cost := cst) (CO := CO) (P := P) (SHE := SHE)] end.
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      intros bc bt yt1' ya3' EB Hbc Hbt.
      pose proof (sm_best_hit (Z.to_nat nG) cst 0 999999999 (-1) ltac:(lia) ltac:(lia)) as BH. rewrite EB in BH. cbn [snd] in BH.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply A0_sm_self with (bt := bt) (nSel := nSel) (ff := 1%Z) (fave := fave) (sel := sel) (mf := m2) (FV := FV) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      { pose proof (FVB bt ltac:(lia)). lia. }
      2:{ intros; exfalso; lia. }
      clear FAVE SEL MI. intros m3 ya1' _ FAVE SEL MI MU3 WM3.
      transport_after_call a0segs m2 m3 MU3 WM3. clear MU3 WM3.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply A0_fr with (me := m3) (rf0 := rf) (gs := gs) (bt := bt) (bc := bc) (nSel := nSel) (B := gs) (CO := CO) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      { intros k Hk. unfold QV. apply MV. lia. }
      { apply RFR. lia. }
      clear RFQ MI. intros m4 rf4 zra zt0 zt1 za0 za1 za3 za4 za5 za6 za7 RFQ ERF4 RFF4 MI MU4 WM4.
      transport_after_call a0segs m3 m4 MU4 WM4. clear MU4 WM4.
      (* [comment removed for export] *)
      assert (Hbc2 : (0 <= bc <= 65535)%Z).
      { destruct CR as [CBOK CREL]. pose proof (sm_best_fst_bound (Z.to_nat nG) cst 0 999999999 (-1) 65535 ltac:(lia) ltac:(lia)) as X.
        rewrite EB in X. cbn [fst] in X. apply X. intros t' Ht'. rewrite <- (CREL t' ltac:(lia)). pose proof (zbok_rd16 _ (2 * t') CBOK). lia. }
      rewrite ERF4 in RFQ. replace 50%nat with (Z.to_nat (ge - gs + 1)) in RFQ by lia.
      eapply evt_eq; [| eapply A0_sm_tail with (g := g) (gs := gs) (ge1 := (ge + 1)%Z) (bc := bc) (totc := totc) (nSel := nSel) (mf := m4) (CO := CO) (FV := FV) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      + (* [comment removed for export] *)
        intros Hc m5 HI5 MI5 MU5 WM5. clear HI MI. transport_after_call a0segs m4 m5 MU5 WM5. clear MU5 WM5.
        eapply evt_eq; [| eapply (KN m5 Jsp2 _ _)]; cbv zeta; fold ge; fold cst.
        all: try (rewrite EB; cbn [fst snd]).
        all: gside MU HI5 VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
        st_eq.
      + (* [comment removed for export] *)
        intros Hc.
        eapply evt_eq; [| eapply (KX m4 Jsp2 _ _)]; cbv zeta; fold ge; fold cst.
        all: try (rewrite EB; cbn [fst snd]).
        all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
        st_eq.
    - (* [comment removed for export] *)
      assert (FB : fastb nG nMTF gs = false).
      { unfold fastf in Hff. fold ge in Hff. unfold fastb. fold ge. destruct ((nG =? 6) && (ge - gs =? 49))%bool; [cbn in Hff; lia| reflexivity]. }
      pose proof (COSTREL_zero cost nG ltac:(lia)) as CR0.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply A0_sm_csg with (gs := gs) (ge := ge) (cb := znew) (cost := zero6 cost) (len := len) (mf := m) (CO := CO) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      clear COST MI. intros m2 cb2 yt0 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 COST CR MI MU2 WM2.
      transport_after_call a0segs m m2 MU2 WM2. clear MU2 WM2.
      replace (Z.to_nat (ge + 1 - gs)) with (Z.to_nat (ge - gs + 1)) in CR by lia.
      pose proof (COSTC_slow arr1 len lp nG nMTF gs cost FB) as CS. fold ge in CS. rewrite <- CS in CR. clear CS.
      set (cst := COSTC arr1 len lp nG gs ge cost) in *.
      pose proof (COSTC_0 arr1 len lp nG gs ge cost) as C0. fold cst in C0.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply A0_sm_btg with (cb := cb2) (cost := cst) (CO := CO) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      intros bc bt yt1' ya3' EB Hbc Hbt.
      pose proof (sm_best_hit (Z.to_nat nG) cst 0 999999999 (-1) ltac:(lia) ltac:(lia)) as BH. rewrite EB in BH. cbn [snd] in BH.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply A0_sm_self with (bt := bt) (nSel := nSel) (ff := 0%Z) (fave := fave) (sel := sel) (mf := m2) (FV := FV) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      { pose proof (FVB bt ltac:(lia)). lia. }
      1:{ intros; exfalso; lia. }
      clear FAVE SEL MI. intros m3 ya1' _ FAVE SEL MI MU3 WM3.
      transport_after_call a0segs m2 m3 MU3 WM3. clear MU3 WM3.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply A0_sm_rfsg with (gs := gs) (ge := ge) (bt := bt) (B := gs) (rf := rf) (mf := m3) (FV := FV) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      { apply RFR. lia. }
      clear RFQ MI. intros m4 rf4 za0 za1 za3 za5 za6 za7 RFQ ERF4 RFF4 MI MU4 WM4.
      transport_after_call a0segs m3 m4 MU4 WM4. clear MU4 WM4.
      (* [comment removed for export] *)
      assert (Hbc2 : (0 <= bc <= 65535)%Z).
      { destruct CR as [CBOK CREL]. pose proof (sm_best_fst_bound (Z.to_nat nG) cst 0 999999999 (-1) 65535 ltac:(lia) ltac:(lia)) as X.
        rewrite EB in X. cbn [fst] in X. apply X. intros t' Ht'. rewrite <- (CREL t' ltac:(lia)). pose proof (zbok_rd16 _ (2 * t') CBOK). lia. }
      rewrite ERF4 in RFQ. replace (ge + 1 - gs)%Z with (ge - gs + 1)%Z in RFQ by lia.
      eapply evt_eq; [| eapply A0_sm_tail with (g := g) (gs := gs) (ge1 := (ge + 1)%Z) (bc := bc) (totc := totc) (nSel := nSel) (mf := m4) (CO := CO) (FV := FV) (P := P) (SHE := SHE)].
      all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
      { st_eq. }
      + (* [comment removed for export] *)
        intros Hc m5 HI5 MI5 MU5 WM5. clear HI MI. transport_after_call a0segs m4 m5 MU5 WM5. clear MU5 WM5.
        eapply evt_eq; [| eapply (KN m5 Jsp _ _)]; cbv zeta; fold ge; fold cst.
        all: try (rewrite EB; cbn [fst snd]).
        all: gside MU HI5 VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
        st_eq.
      + (* [comment removed for export] *)
        intros Hc.
        eapply evt_eq; [| eapply (KX m4 Jsp _ _)]; cbv zeta; fold ge; fold cst.
        all: try (rewrite EB; cbn [fst snd]).
        all: gside MU HI VAR1 VLEN VLPK VLO VEH2 SHa SHe SHf SHc.
        st_eq.
  Qed.
End GG.
End ACeilS1.
