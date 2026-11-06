(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsA Od_cpsA Od_hkit0A Od_deldtorA Od_lkitA Od_tailwA Od_bodyA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition tl_locals (F : Z) (j0 j208 j224 j400 : list byte) : list cell :=
  [CB 192 j0; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F); CB 8 j208; C8 (Z_to_bv 64 (F + 104)); CB 176 j224; CB 8 j400].

Ltac tl_dispatch Hx F A kS kF kH kV :=
  lazymatch type of Hx with
  | (?a <= _ < _) =>
      lazymatch a with
      | context [Z.div F 8] => kH
      | context [F] => kF
      | context [A] => kV
      | _ => kS
      end
  end.

Section Tail.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis DTOR : deldtor_cps RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Notation aevt := (aevt RT PMc).
Local Ltac ul := unfold ATPA_DESTROY_STACK, OD_NEED in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Definition od_ret_k (K : config -> Prop) (usp lo : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (L0 : list (Z * Z)) (sp0 cr : Z) (m : mem) : Prop :=
  forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
    ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo usp ->
    rt_pres_fp L0 [] usp [] m m' ->
    rt_live RT Σ' = L0 -> rt_frames RT Σ' = [] -> rt_sp0 RT Σ' = sp0 -> rt_credit RT Σ' = cr ->
    aevt Σ' K (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x6488f0) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom asegs)).

Lemma od_tail : forall (Σ : rts RT) (K : config -> Prop) (usp S1 F lo IMPL idx oc ia nidx noc nia A cap size : Z)
    (els : list (Z * Z)) (L0 : list (Z * Z))
    (cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) FR fc (m : mem)
    (j0 j208 j224 j400 h0 l12 l13 l14 l15 l16 l17 l18 pre8 mid rest : list byte),
  S1 mod 32 = 0 -> usp - 528 <= S1 <= usp - 512 -> usp mod 16 = 0 -> usp + 16 <= USTACK_TOP ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + OD_NEED <= S1 -> frm0 fc ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo S1 ->
  rt_frames RT Σ = [(F, 3%nat)] ->
  rt_live RT Σ = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (IMPL, 96) :: vblockA A cap size ++ L0 ->
  0 < nia -> 0 < noc -> 0 < nidx -> (forall p n, In (p, n) L0 -> 0 < n) -> IMPL mod 8 = 0 ->
  rw_cells asegs m S1 [CB 192 j0] ->
  rw_cells asegs m (S1 + 192) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)] ->
  rw_cells asegs m (S1 + 208) [CB 8 j208] ->
  rw_cells asegs m (S1 + 216) [C8 (Z_to_bv 64 (F + 104))] ->
  rw_cells asegs m (S1 + 224) [CB 176 j224] ->
  rw_cells asegs m (S1 + 400) [CB 8 j400] ->
  stk asegs m (S1 + 408) (usp - 104) ->
  rw_cells asegs m (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells asegs m F [CB 8 h0] ->
  rw_cells asegs m (F + 104) [C8 (Z_to_bv 64 IMPL)] ->
  vrepA m (F + 32) A cap size els -> 1 <= cap -> 1 <= size ->
  wr_at asegs m (F / 8 + 2147450880) 64 ->
  rw_cells asegs m (F / 8 + 2147450880 + 4) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F / 8 + 2147450880 + 12) [CB 1 l12; CB 1 l13; CB 1 l14; CB 1 l15; CB 1 l16; CB 1 l17; CB 1 l18] ->
  rw_cells asegs m IMPL (dl_cells (Z_to_bv 64 OD_DPI_VPTR) pre8 (Z_to_bv 64 idx) mid (Z_to_bv 64 oc) (Z_to_bv 64 ia) rest) ->
  od_ret_k K usp lo cra cgp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 L0 (rt_sp0 RT Σ) (rt_credit RT Σ) m ->
  aevt Σ K (tx_regs OD_TAIL ra S1 cgp (Z_to_bv 64 0x6488f0) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 F s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 FR fc m).
Proof using AF FDO MST RTF DTOR VDES AFV.
  intros until rest.
  intros S32 S1R U16 UT LOW LOR FRM ART0 MI0 ST0 FRS LV NIA NOC NIDX LPOS IM8 LCa LCf LCb LC216 LCm LC4 STp FRs FH PIM VR CAP1 SZ1 WRS SHv SHp DPI HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (INF : In (F, 3%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m F 3 ART0 INF) as (F0 & FR1 & _ & FLV).
  pose proof (af_frames_align RT AF Σ m F 3 ART0 INF) as (F64 & FSEG).
  pose proof (fframe_ranges RT AF Σ m F 3 ART0 INF) as (_ & _ & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF Σ m F 3 ART0 INF) as (FSL & FSF). pose proof (FSF F 3%nat INF) as FSELF.
  change (fs_size 3) with 512 in *.
  assert (SHF : shad (F + 512) = shad F + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL.
  assert (INI : In (IMPL, 96) (rt_live RT Σ)) by (rewrite LV; right; right; right; left; reflexivity).
  assert (INA : In (ia, nia) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  assert (INO : In (oc, noc) (rt_live RT Σ)) by (rewrite LV; right; left; reflexivity).
  assert (INX : In (idx, nidx) (rt_live RT Σ)) by (rewrite LV; right; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ m IMPL 96 ART0 INI) as (IM0 & IM1 & _).
  pose proof (FLV IMPL 96 INI) as FIM.
  assert (EU : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).

  assert (LPX : lposx (vblockA A cap size ++ L0)).
  { apply lposx_app; [| apply lposx_of_pos; exact LPOS]. unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|].
    apply lposx_ann_block. lia. }
  destruct (pos_prefix_facts RT AF Σ m [(ia, nia); (oc, noc); (idx, nidx); (IMPL, 96)] [] (vblockA A cap size ++ L0) ART0 LV
              ltac:(intros e [<-|[<-|[<-|[<-|[]]]]]; cbn [snd]; lia) LPX) as (ND4 & NDL).
  assert (N4 : ia <> oc /\ ia <> idx /\ ia <> IMPL /\ oc <> idx /\ oc <> IMPL /\ idx <> IMPL).
  { cbn [map fst] in ND4. inversion ND4 as [|? ? X1 Y1]; subst. inversion Y1 as [|? ? X2 Y2]; subst. inversion Y2 as [|? ? X3 Y3]; subst.
    cbn [In] in X1, X2, X3. repeat split; intros E; subst; tauto. }
  destruct N4 as (N1 & N2 & N3 & N4 & N5 & N6).
  assert (LVR : live_remove IMPL (live_remove idx (live_remove oc (live_remove ia (rt_live RT Σ)))) = vblockA A cap size ++ L0).
  { rewrite LV.
    assert (RL : forall x, In x [ia; oc; idx; IMPL] -> forall e, In e (vblockA A cap size ++ L0) -> fst e <> x).
    { intros x Hx e He E. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|[]]]]].
      - exact (NDL (ia, nia) e ltac:(left; reflexivity) He (eq_sym E)).
      - exact (NDL (oc, noc) e ltac:(right; left; reflexivity) He (eq_sym E)).
      - exact (NDL (idx, nidx) e ltac:(right; right; left; reflexivity) He (eq_sym E)).
      - exact (NDL (IMPL, 96) e ltac:(right; right; right; left; reflexivity) He (eq_sym E)). }
    rewrite (live_remove_one ia nia [] [(oc, noc); (idx, nidx); (IMPL, 96)] (vblockA A cap size ++ L0));
      [| intros e [] | intros e [<-|[<-|[<-|[]]]]; cbn [fst]; congruence | exact (RL ia ltac:(cbn; tauto))].
    cbn [app].
    rewrite (live_remove_one oc noc [] [(idx, nidx); (IMPL, 96)] (vblockA A cap size ++ L0));
      [| intros e [] | intros e [<-|[<-|[]]]; cbn [fst]; congruence | exact (RL oc ltac:(cbn; tauto))].
    cbn [app].
    rewrite (live_remove_one idx nidx [] [(IMPL, 96)] (vblockA A cap size ++ L0));
      [| intros e [] | intros e [<-|[]]; cbn [fst]; congruence | exact (RL idx ltac:(cbn; tauto))].
    cbn [app].
    rewrite (live_remove_one IMPL 96 [] [] (vblockA A cap size ++ L0));
      [| intros e [] | intros e [] | exact (RL IMPL ltac:(cbn; tauto))].
    reflexivity. }

  assert (CALLER : forall x, aclient L0 [] usp x ->
            ~ (F <= x < F + 512) /\ ~ (F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64) /\ ~ (lo <= x < usp)
            /\ aclient (vblockA A cap size ++ L0) (rt_frames RT Σ) S1 x /\ aclient L0 (rt_frames RT Σ) S1 x).
  { intros x [H|[H|[H|[H|H]]]].
    - split; [clear - H FR1 LOW LOR S1R; ul|]. split; [clear - H SHT LOW LOR S1R; ul|]. split; [lia|].
      split; left; clear - H S1R; lia.
    - pose proof (client_static_range x H) as CR.
      split; [clear - CR FSEG; ul|]. split; [clear - CR SHB0; ul|]. split; [clear - CR SP0R LOW; ul|]. split; right; left; exact H.
    - destruct H as (p & n & Hin & Hp).
      assert (HinL : In (p, n) (rt_live RT Σ)) by (rewrite LV; do 4 right; apply in_or_app; right; exact Hin).
      pose proof (FLV p n HinL) as D1. pose proof (FSL p n HinL) as D2. pose proof (af_live_range RT AF Σ m p n ART0 HinL) as (_ & D3 & _).
      split; [clear - Hp D1; lia|]. split; [clear - Hp D2; lia|]. split; [clear - Hp D3 LOW; lia|].
      split; right; right; left; exists p, n; (split; [| exact Hp]); [apply in_or_app; right; exact Hin| exact Hin].
    - destruct H as (f & k & [] & _).
    - destruct H as (f & k & [] & _). }

  assert (FP1 : fp_ok RT Σ lo [(F + 104, F + 112)]).
  { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. lia. }
  assert (SZI : forall m', munch [(F + 104, F + 112)] m m' -> wmono asegs m m' -> shz m' IMPL 96).
  { intros m' MU WM. exact (shz_live RT AF Σ m' IMPL 96 (art_of_munch RT AF Σ m m' lo _ ART0 LOW FP1 MU WM) INI IM8). }
  assert (SZV : forall m', munch [(F + 104, F + 112)] m m' -> wmono asegs m m' -> shz m' OD_DPI_VT 96).
  { intros m' MU WM. apply (od_shz_lit RT AF Σ m' OD_DPI_VT 96 (art_of_munch RT AF Σ m m' lo _ ART0 LOW FP1 MU WM));
      [unfold ACC_LITS, OD_DPI_VT; repeat (first [left; reflexivity | right])| reflexivity| unfold OD_DPI_VT; lia| reflexivity]. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkT1 usp S1 F IMPL ra cgp (Z_to_bv 64 0x6488f0) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
              pre8 mid rest (Z_to_bv 64 idx) (Z_to_bv 64 oc) (Z_to_bv 64 ia) FR fc m);
      [ul| ul| ul| ul| ul| lia| ul| lia| exact LC216| exact PIM| exact DPI| exact (AFV Σ m ART0)| exact SZI| exact SZV| exact MI0]. }
  cbv beta. intros ms1 (m1 & a1' & a2' & -> & MU1 & WM1 & MI1 & PIM1).
  apply evt_done.

  pose proof (art_of_munch RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  assert (AG1 : agree_on (fun x => ~ (F + 104 <= x < F + 112)) m m1)
    by (apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  destruct VR as (VSZ & VSC & VCAP & VA0 & VAT & VS & VB).
  destruct VB as [(B1 & B2)|(_ & A16 & APOS & VEL)]; [lia|].
  assert (INV : In (A, 16 * size) (vblockA A cap size)).
  { unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|]. apply ann_block_vis. }
  assert (INVL : In (A, 16 * size) (rt_live RT Σ)) by (rewrite LV; do 4 right; apply in_or_app; left; exact INV).
  pose proof (FLV A (16 * size) INVL) as FAV.
  pose proof (af_live_range RT AF Σ m A (16 * size) ART0 INVL) as (_ & AV1 & _).
  pose proof (velts_size els) as VSZE. unfold zlength in VSZ.
  assert (ST1 : stk asegs m1 lo S1).
  { apply (stk_agree asegs m m1 _ _ ST0); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. ul. }
  assert (STp1 : stk asegs m1 (S1 + 408) (usp - 104)).
  { apply (stk_agree asegs m m1 _ _ STp); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. ul. }
  clear ST0 STp PIM.
  unfold fa_saved, dl_cells in *.
  pose proof (FSL A (16 * size) INVL) as SAV.
  assert (GS : F + 512 <= S1 /\ IMPL + 96 <= S1 /\ F / 8 + 2147450880 + 64 <= S1 /\ A + 16 * size <= S1)
    by (clear - FR1 IM1 LOW LOR SHT AV1; ul).
  assert (GL : F + 512 <= lo /\ IMPL + 96 <= lo /\ F / 8 + 2147450880 + 64 <= lo /\ A + 16 * size <= lo /\ lo <= S1)
    by (clear - FR1 IM1 LOW LOR SHT AV1; ul).
  rt_transport_with m m1 AG1 WM1 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(first [clear - Hx GS S1R; lia | clear - Hx FIM; lia]) ltac:(clear - Hx; lia) ltac:(clear - Hx FSELF; lia)
                         ltac:(clear - Hx FAV VSZ; lia)).
  assert (CP1 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. pose proof (CALLER _ Ha) as (C1 & _). clear - C1. lia. }
  clear AG1 MU1 SZI SZV FP1.
  unfold tx_regs.
  eapply (aevt_deldtor RT PMc FDO MST DTOR Σ K) with (THIS := IMPL) (idx := idx) (oc := oc) (ia := ia) (nidx := nidx) (noc := noc) (nia := nia) (lo := lo);
    rewrite ?EU;
    [ reflexivity | reflexivity | exact INI | exact IM8 | exact DPI | exact INA | exact INO | exact INX
    | exact N1 | exact N2 | exact N3 | exact N4 | exact N5 | exact N6 | lia | lia | lia | exact ART1 | exact MI1 | exact ST1 | exact LOW
    | ul | ul | clear - S32; Z.div_mod_to_equations; lia | unfold unwind_ok; rewrite EU, EUS; right; right; lia | exact FRM | ].
  intros Σ2 v2 t0' t1' t2' a1'' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 FRM2 (ART2 & MI2 & ST2) PR2 LV2 FRS2 SP2 CR2.
  rewrite LVR in LV2.
  assert (INF2 : In (F, 3%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  assert (INV2 : In (A, 16 * size) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; left; exact INV).
  assert (AG2 : agree_on (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x) m1 m2)
    by (intros a Ha; exact (PR2 a Ha I)).
  assert (CP2 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (CP1 a Ha). apply (PR2 a); [| exact I]. rewrite LV2. exact (proj1 (proj2 (proj2 (proj2 (CALLER _ Ha))))). }
  clear CP1.
  assert (ACS : forall x, S1 <= x < USTACK_TOP -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x) by (intros x Hx; left; exact Hx).
  assert (ACF : forall x, F <= x < F + 504 -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. lia. }
  assert (ACH : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. lia. }
  assert (ACV : forall x, A <= x < A + 16 * size -> aclient (rt_live RT Σ2) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; left. exists A, (16 * size). split; [exact INV2| lia]. }
  clear DPI ST1.
  rt_transport_nw m1 m2 AG2 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(apply ACS; clear - Hx S1R UT; unfold USTACK_TOP in *; lia) ltac:(apply ACF; clear - Hx; lia)
                         ltac:(apply ACH; clear - Hx; lia) ltac:(apply ACV; clear - Hx VSZ; lia)).
  replace (ret_pc (Z_to_bv 64 0x99d8c)) with (Z_to_bv 64 0x99d8c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  assert (FP2 : fp_ok RT Σ2 lo [(F / 8 + 2147450880 + 12, F / 8 + 2147450880 + 19); (S1 + 400, S1 + 408)]).
  { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
    - right; right; right. exists F, 3%nat. split; [exact INF2|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. lia.
    - left. ul. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkT2 usp S1 F (Z_to_bv 64 0x99d8c) cgp (Z_to_bv 64 0x6488f0) t0' t1' t2' v2 a1'' a2'' a3' a4' a5' a6' a7' s2 s5 s6 s7 s9 s10 s11 t3' t4' t5' t6'
              l12 l13 l14 l15 l16 l17 l18 j400 F2 fc2 m2); [ul| ul| ul| ul| ul| exact SHp| exact LC4| exact MI2]. }
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & SHp3 & LC43). cbn [map repeat] in SHp3.
  apply evt_done.
  assert (SP2' : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW).
  pose proof (art_of_munch RT AF Σ2 m2 m3 lo _ ART2 SP2' FP2 MU3 WM3) as ART3.
  assert (AG3 : agree_on (fun x => ~ (F / 8 + 2147450880 + 12 <= x < F / 8 + 2147450880 + 19) /\ ~ (S1 + 400 <= x < S1 + 408)) m2 m3)
    by (apply (agree_of_munch _ _ _ _ MU3); intros x [H1 H2]; cbn [outside]; split; [exact H1| split; [exact H2| exact I]]).
  assert (ST3 : stk asegs m3 lo S1).
  { apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. ul. }
  assert (STp3 : stk asegs m3 (S1 + 408) (usp - 104)).
  { apply (stk_agree asegs m2 m3 _ _ STp1); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. ul. }
  clear ST2 STp1 SHp LC4.
  rt_transport_with m2 m3 AG3 WM3 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?VSZE in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(clear - Hx GS S1R; lia) ltac:(clear - Hx GS FSELF; lia) ltac:(clear - Hx GS; lia)
                         ltac:(clear - Hx GS SAV VSZ; lia)).
  assert (CP3 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m3 a = m a).
  { intros a Ha. rewrite <- (CP2 a Ha). apply MU3. cbn [outside]. pose proof (CALLER _ Ha) as (_ & C2 & C3 & _).
    split; [clear - C2; lia|]. split; [clear - C3 GL S1R; lia| exact I]. }
  clear CP2 AG3 MU3 FP2.
  assert (FOBJ3 : fobj RT Σ2 m3 (F + 32) 24).
  { split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [lia|].
    split; [exists F, 3%nat; split; [exact INF2|]; change (fs_size 3) with 512; change ((24 + 7) / 8) with 3; lia|].
    change (Z.to_nat ((24 + 7) / 8)) with 3%nat. cbn [repeat].
    replace (shad (F + 32)) with (F / 8 + 2147450880 + 4) by (unfold shad, SHB; clear - F64; Z.div_mod_to_equations; lia).
    destruct SHv as [[_ B] _]. exact B. }
  assert (VR3 : vrepA m3 (F + 32) A cap size els).
  { unfold vrepA, zlength. split; [exact VSZ|]. split; [exact VSC|]. split; [exact VCAP|]. split; [exact VA0|]. split; [exact VAT|].
    split; [exact VS|]. right. split; [exact CAP1|]. split; [exact A16|]. split; [exact APOS| exact VEL]. }
  eapply (aevt_vdestroy RT PMc FDO MST VDES Σ2 K) with (C := S1 + 400) (V := F + 32) (A := A) (cap := cap) (size := size) (els := els) (L0 := L0) (lo := lo);
    rewrite ?EU;
    [ reflexivity | reflexivity | lia | ul | clear - S32; Z.div_mod_to_equations; lia | exact LC43 | exact VR3
    | unfold vliveA; exact LV2 | exact LPOS | exact CAP1 | exact FOBJ3 | exact ART3 | exact MI3 | exact ST3 | exact SP2'
    | ul | ul | clear - S32; Z.div_mod_to_equations; lia | unfold unwind_ok; rewrite EU, EUS; right; right; lia | exact FRM2 | ].
  intros Σ4 v4 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4 fc4 m4 FRM4 (ART4 & MI4 & ST4) PR4 LV4 FRS4 SP4 CR4.
  assert (AG4 : agree_on (fun x => aclient L0 (rt_frames RT Σ2) S1 x /\ outside [(F + 32, F + 32 + 24)] x) m3 m4)
    by (intros a [H1 H2]; exact (PR4 a H1 H2)).
  assert (CP4 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m4 a = m a).
  { intros a Ha. rewrite <- (CP3 a Ha). pose proof (CALLER _ Ha) as (C1 & _ & _ & _ & C5). apply (PR4 a); [rewrite FRS2; exact C5|].
    cbn [outside]. split; [clear - C1; lia| exact I]. }
  clear CP3.
  assert (ACS4 : forall x, S1 <= x < USTACK_TOP -> aclient L0 (rt_frames RT Σ2) S1 x /\ outside [(F + 32, F + 32 + 24)] x).
  { intros x Hx. split; [left; exact Hx|]. cbn [outside]. split; [clear - Hx GS; lia| exact I]. }
  assert (ACF4 : forall x, F <= x < F + 32 \/ F + 56 <= x < F + 504 -> aclient L0 (rt_frames RT Σ2) S1 x /\ outside [(F + 32, F + 32 + 24)] x).
  { intros x Hx. split; [right; right; right; left; exists F, 3%nat; split; [exact INF2|]; change (fs_size 3) with 512; lia|].
    cbn [outside]. split; [lia| exact I]. }
  assert (ACH4 : forall x, F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64 -> aclient L0 (rt_frames RT Σ2) S1 x /\ outside [(F + 32, F + 32 + 24)] x).
  { intros x Hx. split; [right; right; right; right; exists F, 3%nat; split; [exact INF2|]; change (fs_size 3) with 512; rewrite SHF; unfold shad, SHB; lia|].
    cbn [outside]. split; [clear - Hx FSELF; lia| exact I]. }
  clear VS VEL VR3 FOBJ3 ST3.
  rt_transport_nw m3 m4 AG4 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(apply ACS4; clear - Hx S1R UT; unfold USTACK_TOP in *; lia) ltac:(apply ACF4; clear - Hx; lia)
                         ltac:(apply ACH4; clear - Hx; lia) ltac:(fail)).
  replace (ret_pc (Z_to_bv 64 0x99db8)) with (Z_to_bv 64 0x99db8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (INF4 : In (F, 3%nat) (rt_frames RT Σ4)) by (rewrite FRS4; exact INF2).
  assert (SP4' : rt_sp0 RT Σ4 - STACK_WIN <= lo) by (rewrite SP4; exact SP2').

  assert (FP5 : fp_ok RT Σ4 lo [(F / 8 + 2147450880 + 4, F / 8 + 2147450880 + 7); (F, F + 8)]).
  { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
    - right; right; right. exists F, 3%nat. split; [exact INF4|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. lia.
    - right; right; left. exists F, 3%nat. split; [exact INF4|]. change (fs_size 3) with 512. lia. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkT3 usp S1 F (Z_to_bv 64 0x99db8) cgp (Z_to_bv 64 0x6488f0) u0 u1 u2 v4 b1 b2 b3 b4 b5 b6 b7 s5 s6 s7 s9 s10 s11 u3 u4 u5 u6
              (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) h0 F4 fc4 m4); [ul| ul| ul| ul| ul| ul| exact FSELF| exact SHv| exact LCf| exact FH| exact MI4]. }
  cbv beta. intros ms5 (m5 & a2x & -> & MU5 & WM5 & MI5 & SHv5 & FH5). cbn [map repeat] in SHv5.
  apply evt_done.
  pose proof (art_of_munch RT AF Σ4 m4 m5 lo _ ART4 SP4' FP5 MU5 WM5) as ART5.
  assert (AG5 : agree_on (fun x => ~ (F / 8 + 2147450880 + 4 <= x < F / 8 + 2147450880 + 7) /\ ~ (F <= x < F + 8)) m4 m5)
    by (apply (agree_of_munch _ _ _ _ MU5); intros x [H1 H2]; cbn [outside]; split; [exact H1| split; [exact H2| exact I]]).
  assert (ST5 : stk asegs m5 lo S1).
  { apply (stk_agree asegs m4 m5 _ _ ST4); [| exact WM5]. eapply agree_sub; [exact AG5|]. intros x Hx. cbv beta in *. clear - Hx GS GL S1R. lia. }
  assert (STp5 : stk asegs m5 (S1 + 408) (usp - 104)).
  { apply (stk_agree asegs m4 m5 _ _ STp3); [| exact WM5]. eapply agree_sub; [exact AG5|]. intros x Hx. cbv beta in *. clear - Hx GS GL S1R. lia. }
  clear ST4 STp3 SHv FH.
  rt_transport_with m4 m5 AG5 WM5 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
      tl_dispatch Hx F A ltac:(clear - Hx GS S1R; lia) ltac:(clear - Hx GS FSELF; lia) ltac:(clear - Hx GS FSELF; lia) ltac:(fail)).
  assert (CP5 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m5 a = m a).
  { intros a Ha. rewrite <- (CP4 a Ha). apply MU5. cbn [outside]. pose proof (CALLER _ Ha) as (C1 & C2 & _).
    split; [clear - C2; lia|]. split; [clear - C1; lia| exact I]. }
  clear CP4 AG5 MU5 FP5.
  assert (FRS4' : rt_frames RT Σ4 = [(F, 3%nat)]) by (rewrite FRS4, FRS2; exact FRS).
  unfold tx_regs.
  eapply (aevt_set_shadow RT RTF PMc FDO MST Σ4 K 0xf5) with (d := F / 8 + 2147450880) (n := 64) (lo := lo);
    [ unfold set_shadow_vals; do 11 right; left; reflexivity | reflexivity | reflexivity | lia
    | intros i Hi; exists F, 3%nat; split; [exact INF4|]; change (fs_size 3) with 512; rewrite SHF; unfold shad, SHB; lia
    | exact WRS | exact ART5 | exact MI5
    | unfold call_ok; rewrite EU; split; [exact ST5|]; split; [exact SP4'|]; split; [ul|]; split; [ul| clear - S32; Z.div_mod_to_equations; lia]
    | exact FRM4 | ].
  intros v6 w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F6 fc6 m6 FRM6 (ART6 & MI6 & WM6 & ST6) PR6 BY6.
  rewrite EU in ST6, PR6.
  assert (AG6 : agree_on (fun x => aclient (rt_live RT Σ4) (rt_frames RT Σ4) S1 x /\ ~ (F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64)) m5 m6)
    by (intros a [H1 H2]; exact (PR6 a H1 H2)).
  assert (CP6 : forall a : word, aclient L0 [] usp (bv_unsigned a) -> m6 a = m a).
  { intros a Ha. rewrite <- (CP5 a Ha). pose proof (CALLER _ Ha) as (_ & C2 & _ & _ & C5). apply (PR6 a); [| exact C2].
    rewrite LV4, FRS4, FRS2. exact C5. }
  clear CP5.
  assert (ACS6 : forall x, S1 <= x < USTACK_TOP -> aclient (rt_live RT Σ4) (rt_frames RT Σ4) S1 x /\ ~ (F / 8 + 2147450880 <= x < F / 8 + 2147450880 + 64)).
  { intros x Hx. split; [left; exact Hx|]. clear - Hx GS. lia. }
  clear SHv5 SHp3 WRS FH5 PIM1 ST5.
  rt_transport_with m5 m6 AG6 WM6 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
                                        apply ACS6; clear - Hx S1R UT; unfold USTACK_TOP in *; lia).
  assert (STp6 : stk asegs m6 (S1 + 408) (usp - 104)).
  { apply (stk_agree asegs m5 m6 _ _ STp5); [| exact WM6]. eapply agree_sub; [exact AG6|]. intros x Hx. cbv beta in *.
    apply ACS6. clear - Hx S1R UT. unfold USTACK_TOP in *. lia. }
  clear STp5.
  replace (ret_pc (Z_to_bv 64 0x99de8)) with (Z_to_bv 64 0x99de8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  destruct (af_frame_release RT AF Σ4 m6 F 3 [] ART6 FRS4') as (Σ7 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 3) with 512 in FW. replace (F + 512 - 8) with (F + 504) in FW by lia.
  assert (LC6 : rw_cells asegs m6 S1 ([CB 192 j0] ++ [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)] ++ [CB 8 j208] ++ [C8 (Z_to_bv 64 (F + 104))]
                                       ++ [CB 176 j224] ++ [C8 (Z_to_bv 64 (F + 32))])).
  { apply rw_cells_app. split; [exact LCa|]. cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat 192) with (S1 + 192) by lia.
    apply rw_cells_app. split; [exact LCf|]. cbn [cells_size csize Nat.add]. replace (S1 + 192 + Z.of_nat 16) with (S1 + 208) by lia.
    apply rw_cells_app. split; [exact LCb|]. cbn [cells_size csize Nat.add]. replace (S1 + 208 + Z.of_nat 8) with (S1 + 216) by lia.
    apply rw_cells_app. split; [exact LC216|]. cbn [cells_size csize Nat.add]. replace (S1 + 216 + Z.of_nat 8) with (S1 + 224) by lia.
    apply rw_cells_app. split; [exact LCm|]. cbn [cells_size csize Nat.add]. replace (S1 + 224 + Z.of_nat 176) with (S1 + 400) by lia.
    exact LC43. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (od_walkT4 usp S1 F fl lo (Z_to_bv 64 0x99de8) cgp (Z_to_bv 64 0x6488f0) w0 w1 w2 v6 c1 c2 c3 c4 c5 c6 c7 s5 s6 s7 s9 s10 s11 w3 w4 w5 w6
              cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
              ([CB 192 j0] ++ [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)] ++ [CB 8 j208] ++ [C8 (Z_to_bv 64 (F + 104))] ++ [CB 176 j224] ++ [C8 (Z_to_bv 64 (F + 32))])
              F6 fc6 m6);
      [ lia | clear - GL; lia | exact FL0 | rewrite SP4, SP2 in FLW; clear - FLW LOW; lia | clear - SP0R LOW; ul | clear - GL; lia
      | reflexivity | clear - S1R; lia | clear - S1R; lia | ul | exact ST6 | exact LC6 | exact STp6 | exact FRs | exact FW | exact FLC | exact MI6 ]. }
  cbv beta. intros ms8 (m8 & RS8 & FC8 & MU8 & WM8 & MI8 & ST8 & FLC8).
  destruct (REL m8 MU8 WM8 FLC8) as (ART8 & FRS8 & LV8 & SP8 & CR8 & AL8 & AM8).
  apply evt_done.
  apply (aevt_switch RT PMc Σ4 Σ7 K ms8 AL8 AM8).
  revert FC8.
  apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 ms8 (fun ms => ms_fcsr ms = fc6 -> aevt Σ7 K ms) RS8).
  intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F8 fc8 FC8. change (fc8 = fc6) in FC8. subst fc8.
  apply (HK Σ7 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F8 fc6 m8 FRM6 ART8 MI8 ST8).
  - intros a Ha _. rewrite <- (CP6 a Ha). apply MU8. cbn [outside]. split; [| exact I]. intros Hfl.
    apply NAC. assert (E : bv_unsigned a = fl) by lia. rewrite <- E.
    pose proof (CALLER _ Ha) as (_ & _ & C3 & _ & C5).
    destruct Ha as [H|[H|[H|[H|H]]]].
    + exfalso. rewrite SP4, SP2 in FLW. clear - H E FLW LOW S1R LOR. ul.
    + right; left. exact H.
    + right; right; left. rewrite LV4. exact H.
    + destruct H as (f & k & [] & _).
    + destruct H as (f & k & [] & _).
  - rewrite LV8. exact LV4.
  - exact FRS8.
  - rewrite SP8, SP4. exact SP2.
  - rewrite CR8, CR4. exact CR2.
Qed.

End Tail.
