(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import IcptSpec D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_num_amem Sj_num_aframe I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA Atp_objpA Atp_objkA Z6j Atp_objxA Atp_objcA Atp_objnA Z67 Atp_objsA Atp_objuA Z6i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma live_remove_fresh : forall (L : list (Z * Z)) p n, (forall e, In e L -> fst e <> p) -> live_remove p ((p, n) :: L) = L.
Proof. intros L p n H. apply live_remove_hd. exact H. Qed.

Section ObjE.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variables (Σ Σ1 : rts RT) (I : objI).
  Hypothesis CTX : octx RT E d Σ Σ1 I.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -288 - dd) in *.
  Local Ltac olia := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end; unfold oi_b, oi_L in *; flia.

  Section SCtx.
  Variables (lg : bool) (D cap Lk sl L0 : Z) (rest : list Z) (Σ2 : rts RT).

  Record sctx : Prop := mkSC {
    sc_ef : rt_frames RT Σ2 = (oi_f I, 1%nat) :: rt_frames RT Σ;
    sc_es : rt_sp0 RT Σ2 = rt_sp0 RT Σ;
    sc_eptr : oi_ptr I = 47 :: rest;
    sc_zl0 : zlength rest = L0;
    sc_l0 : L0 < 2^26;
    sc_min : (sl < L0 /\ Lk = sl) \/ (L0 <= sl /\ Lk = L0);
    sc_slr : sl = 18446744073709551615 \/ 0 <= sl < L0;
    sc_lk : 0 < Lk;
    sc_short : lg = false -> D = oi_f I + 33 /\ cap = 23 /\ Lk < 23 /\ Σ2 = Σ1;
    sc_long : lg = true -> rt_live RT Σ2 = (D, cap) :: rt_live RT Σ /\ cap = str_sz Lk /\ 23 <= Lk /\ D mod 16 = 0 /\ rt_credit RT Σ2 = rt_credit RT Σ - 1 - mcost cap
                           /\ 0 < D /\ D + cap <= rt_sp0 RT Σ - STACK_WIN /\ (oi_f I + 128 <= D \/ D + cap <= oi_f I)
                           /\ (D + cap <= shad (oi_f I) \/ shad (oi_f I) + 16 <= D) }.
  Hypothesis SC : sctx.

  Lemma sc_el : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ2).
  Proof using SC CTX.
    intros x Hx. destruct lg eqn:LG.
    - destruct (sc_long SC LG) as (EL & _). rewrite EL. right. exact Hx.
    - destruct (sc_short SC LG) as (_ & _ & _ & ->). rewrite (oc_live1 _ _ _ _ _ _ CTX). exact Hx.
  Qed.

  Lemma sc_num : 0 < D /\ D + cap <= ae_lo E /\ 23 <= cap < 2^40 /\ Lk < cap /\ 0 < Lk <= L0 /\ 0 <= L0 < 2^26 /\ (lg = false \/ oi_f I + 56 <= D \/ D + cap <= oi_f I + 32).
  Proof using SC CTX AF OK.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof LV as (_ & _ & _ & _ & LWIN). pose proof (zlength_nonneg rest) as ZLN. rewrite (sc_zl0 SC) in ZLN.
    pose proof (lvl_ptr_range E OK (oi_P I) (oi_ptr I) PAT ltac:(rewrite (sc_eptr SC); discriminate)) as (PB0 & PB1 & PB2 & PB3).
    rewrite (sc_eptr SC), zlength_cons, (sc_zl0 SC) in PB2.
    pose proof (sc_min SC) as MIN. pose proof (sc_slr SC) as SLR. pose proof (sc_lk SC) as LK.
    destruct lg eqn:LG.
    - destruct (sc_long SC LG) as (EL & ECAP & LK23 & D16 & EC & D0 & DHI & DSEP & DSH).
      pose proof (str_sz_bound Lk ltac:(lia)) as SZB. rewrite <- ECAP in SZB. pose proof (sc_l0 SC) as L026. clear - LWIN ZLN PB2 MIN SLR LK LK23 SZB D0 DHI DSEP L026. lia.
    - destruct (sc_short SC LG) as (ED & ECAP & LK23 & _). pose proof (sc_l0 SC) as L026. clear - ZLN PB2 MIN SLR LK ED ECAP LK23 F0 FHI L026. lia.
  Qed.

  Lemma sc_cls : lstr_cls RT Σ2 D cap /\ lstr_cls RT Σ2 (oi_f I + 32) 24 /\ (lg = true -> In (D, cap) (rt_live RT Σ2)) /\ In (oi_f I, 1%nat) (rt_frames RT Σ2).
  Proof using SC CTX.
    assert (HinF : In (oi_f I, 1%nat) (rt_frames RT Σ2)) by (rewrite (sc_ef SC); left; reflexivity).
    assert (CLS : lstr_cls RT Σ2 (oi_f I + 32) 24) by (left; exists (oi_f I), 1%nat; split; [exact HinF| rewrite fs1; lia]).
    destruct lg eqn:LG.
    - destruct (sc_long SC LG) as (EL & _). assert (IND : In (D, cap) (rt_live RT Σ2)) by (rewrite EL; left; reflexivity).
      split; [right; exists D, cap; split; [exact IND| lia]|]. split; [exact CLS|]. split; [intros _; exact IND| exact HinF].
    - destruct (sc_short SC LG) as (ED & ECAP & _).
      split; [left; exists (oi_f I), 1%nat; split; [exact HinF| rewrite fs1; lia]|]. split; [exact CLS|]. split; [intros X; discriminate X| exact HinF].
  Qed.

  Lemma sh_apart : forall a, shad (oi_f I) <= a < shad (oi_f I) + 16 -> ~ (oi_f I + 24 <= a < oi_f I + 120) /\ ~ (D <= a < D + cap).
  Proof using SC CTX.
    intros a Ha. pose proof (oc_fsh _ _ _ _ _ _ CTX) as FSH.
    destruct lg eqn:LG.
    - destruct (sc_long SC LG) as (_ & _ & _ & _ & _ & _ & _ & _ & DSH). clear - Ha FSH DSH. lia.
    - destruct (sc_short SC LG) as (ED & ECAP & _). clear - Ha FSH ED ECAP. lia.
  Qed.

  Lemma sh_apartI : D + cap <= shad (oi_f I) \/ shad (oi_f I) + 16 <= D.
  Proof using SC CTX.
    pose proof (oc_fsh _ _ _ _ _ _ CTX) as FSH.
    destruct lg eqn:LG.
    - destruct (sc_long SC LG) as (_ & _ & _ & _ & _ & _ & _ & _ & DSH). exact DSH.
    - destruct (sc_short SC LG) as (ED & ECAP & _). clear - FSH ED ECAP. lia.
  Qed.

  Lemma str_apart : forall (m : mem) a, ART RT Σ2 m ->
    aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> ~ (oi_f I <= a < oi_f I + 128) /\ ~ (shad (oi_f I) <= a < shad (oi_f I) + 16) /\ ~ (D <= a < D + cap).
  Proof using SC CTX AF OK.
    intros m a ART2 Ha.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof LV as (_ & _ & _ & _ & LWIN). pose proof (ok_lo E OK) as LOW.
    assert (QW : rt_sp0 RT Σ - STACK_WIN <= oi_q I) by (unfold obj_needA, elem_needA, ATP_LEAFB, RT_STACK in LOR; lia).
    pose proof (newframe_apartI RT AF Σ Σ2 m (oi_f I) 1%nat (oi_q I) a ART2 (sc_ef SC) sc_el (sc_es SC) QW Ha) as [N1 N2].
    rewrite fs1s in N2. rewrite fs1 in N1.
    split; [exact N1|]. split; [exact N2|].
    destruct lg eqn:LG.
    - destruct (sc_long SC LG) as (EL & _ & _ & _ & _ & D0 & DHI & _).
      pose proof (sc_es SC) as ES2.
      assert (Ha2 : aclient (rt_live RT Σ) (rt_frames RT Σ2) (oi_q I) a).
      { rewrite (sc_ef SC). apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros x Hx; right; exact Hx| lia]. }
      intros Hin. destruct Ha2 as [H|[H|[H|[H|H]]]].
      + unfold USTACK_TOP in *. lia.
      + pose proof (client_static_range a H). pose proof (af_live_range RT AF Σ2 m D cap ART2 ltac:(rewrite EL; left; reflexivity)). unfold SEGTOP_A in *. lia.
      + destruct H as (p2 & n2 & Hin2 & Hp2). pose proof (af_live_disj RT AF Σ2 m D cap p2 n2 [] (rt_live RT Σ) ART2 EL Hin2). lia.
      + destruct H as (f2 & k2 & Hin2 & Hf2). pose proof (af_frames_range RT AF Σ2 m f2 k2 ART2 Hin2) as (_ & _ & _ & X).
        destruct (X D cap ltac:(rewrite EL; left; reflexivity)); lia.
      + destruct H as (f2 & k2 & Hin2 & Hf2). pose proof (af_fshadow_apart RT AF Σ2 m f2 k2 ART2 Hin2) as [X _].
        destruct (X D cap ltac:(rewrite EL; left; reflexivity)); lia.
    - destruct (sc_short SC LG) as (ED & ECAP & _). lia.
  Qed.

  Lemma live_restore : forall (m : mem), lg = true -> ART RT Σ2 m -> live_remove D (rt_live RT Σ2) = rt_live RT Σ.
  Proof using SC CTX AF.
    intros m LG ART2. pose proof (proj2 (oc_lvb _ _ _ _ _ _ CTX)) as LPOS. destruct (sc_long SC LG) as (EL & ECAP & LK23 & _ & _ & D0 & _).
    pose proof (str_sz_bound Lk ltac:(lia)) as SZB.
    rewrite EL. apply live_remove_fresh. intros [p n] Hin. cbn [fst]. intros ->.
    destruct (LPOS D n Hin) as (n' & Hin' & Hn').
    pose proof (af_live_disj RT AF Σ2 m D cap D n' [] (rt_live RT Σ) ART2 EL Hin'). lia.
  Qed.

  Lemma obase_agree : forall (Σc Σc' : rts RT) (m m' : mem),
    obase RT E Σ I Σc m -> rt_frames RT Σc' = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc')) -> rt_sp0 RT Σc' = rt_sp0 RT Σ ->
    ART RT Σc' m' -> mem_inv asegs m' -> stk asegs m' (ae_lo E) (oi_b I) ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σc') (oi_b I) (bv_unsigned a) ->
       ~ (oi_f I + 24 <= bv_unsigned a < oi_f I + 120) -> ~ (D <= bv_unsigned a < D + cap) -> m' a = m a) ->
    (forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a) ->
    obase RT E Σ I Σc' m'.
  Proof using SC CTX AF OK.
    intros Σc Σc' m m' OB EF' EL' ES' ART' MI' ST' AG DAP.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σc' m' ART') as SP0R. rewrite ES' in SP0R.
    pose proof sc_num as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σc')) by (rewrite EF'; left; reflexivity).
    assert (QW : rt_sp0 RT Σ - STACK_WIN <= q) by ul.

    assert (AGC : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a /\ ~ (out <= a < out + 24)) m m').
    { intros a [Ha Ho]. pose proof (newframe_apartI RT AF Σ Σc' m' f 1%nat q (bv_unsigned a) ART' EF' EL' ES' QW Ha) as [N1 _]. rewrite fs1 in N1.
      apply AG; [| clear - N1; lia| exact (DAP _ ltac:(idtac) ) || (intros X; exact (DAP _ X Ha))].
      rewrite EF'. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros x Hx; right; exact Hx| lia]. }
    split; [exact MI'|]. split; [exact ART'|]. split; [exact ST'|].
    split. { apply (AINV_A_agree E m m' AI). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX.
             pose proof (ainv_rng_lo E (bv_unsigned x) OK Hx). apply AGC. split; [exact CX| lia]. }
    split. { apply (rw_cells_agree_nw asegs m m' _ _ SAVED). intros a Ha. cbn [cells_size csize Nat.add length obj_saved] in Ha. apply AG; [left; unfold USTACK_TOP in *; lia| lia| lia]. }
    split. { apply (rw_cells_agree_nw asegs m m' _ _ HIGH). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AG; [left; unfold USTACK_TOP in *; lia| lia| lia]. }
    split. { apply (rw_cells_agree_nw asegs m m' _ _ HDR). intros a Ha. cbn [cells_size csize Nat.add length obj_hdr] in Ha.
             apply AG; [right; right; right; left; exists f, 1%nat; split; [exact HinF| rewrite fs1; lia]| lia|].
             destruct lg eqn:LG; [| destruct (sc_short SC LG) as (ED & ECAP & _); lia].
             destruct (sc_long SC LG) as (_ & _ & _ & _ & _ & _ & _ & DSEP & _). clear - Ha DSEP CAPR. lia. }
    eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply AGC. cbn [outside] in Ho. split; [exact Ha| lia].
  Qed.

  Lemma sc_budget : rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σ2
                    /\ (0 <= sl < L0 -> rt_credit RT Σ - obj_costA d (oi_L I) + elem_costA d (L0 - sl) <= rt_credit RT Σ2).
  Proof using SC CTX AF OK.
    pose proof (oc_credit1 _ _ _ _ _ _ CTX) as EC1.
    pose proof sc_num as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof (sc_min SC) as MIN. pose proof (sc_slr SC) as SLR.
    assert (ZL : oi_L I = L0 + 1) by (unfold oi_L; rewrite (sc_eptr SC), zlength_cons, (sc_zl0 SC); lia).
    rewrite ZL. unfold obj_costA, elem_costA, LVL_C1.
    destruct lg eqn:LG.
    - destruct (sc_long SC LG) as (_ & ECAP & LK23 & _ & EC & _).
      pose proof (str_sz_bound Lk ltac:(lia)) as SZB. rewrite <- ECAP in SZB. rewrite EC. unfold mcost, DCOST.
      destruct (cap <=? 64512) eqn:CS; [apply Z.leb_le in CS| apply Z.leb_gt in CS]; split; try intros; nia.
    - destruct (sc_short SC LG) as (_ & _ & _ & E21). rewrite E21, EC1. unfold DCOST. split; try intros; nia.
  Qed.

  Lemma esc_reck : forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x24 x25 x26 x28 x29 x30 x31 : word)
      (w24 w32 w40 w48 w88 w96 w120 w128 : word) (F : bvmap 5 word) (fc : bv 32) (rd ri err : Z) (js4 jo j0 jco jt : list byte),
    obase RT E Σ I Σc m -> frm0 fc ->
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ -> rt_credit RT Σ2 <= rt_credit RT Σc ->
    (err = 20 \/ (err = 0 /\ rd = ae_DOC E /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d ri j' /\ 0 <= ri /\ j' <= ae_n E - 1)) ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl) w88 w96 (Z_to_bv 64 (oi_P I + 1)) (Z_to_bv 64 (oi_out I)) w120 w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 rd); C8 (Z_to_bv 64 ri); C4 (Z_to_bv 64 err); CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σc (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (wz (shad (oi_f I))) x20 (wz (oi_P I + 1)) x22 (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb6790) fc None m (seg_rom asegs)).
  Proof using SC AF CTX FDO MST OK RC2 HELEM.
    intros until jt. intros OB FRM EF EL ES CR HERR LOC COUT REC SH OUT.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof sc_num as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof sc_budget as [BUD1 BUD2].
    pose proof (sc_eptr SC) as EPTR. pose proof (sc_zl0 SC) as ZL0. pose proof (sc_slr SC) as SLR.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (ERR : err = 0 \/ err = 20) by (destruct HERR as [X|[X _]]; [right| left]; exact X).
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w788 E OK _ q b P L0 f rd ri err); [exact MI| exact LO| lia| lia| lia| exact ERR| exact FLO| exact FHI| clear - FSH; lia| exact S0| lia| exact LOC| exact REC| exact SH|].
    intros m1 xa1 MU1 WM1 MI1 SH1.
    assert (OW1 : Forall (ownW I) [(shad f, shad f + 16)]) by (constructor; [right; right; left; cbn; fold f; lia| constructor]).
    pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σc _ m m1 OB0 EF ltac:(rewrite EL; auto) ES MU1 WM1 MI1 OW1) as OB1.
    mport LOC MU1 WM1. mport COUT MU1 WM1. mport REC MU1 WM1. mport OUT MU1 WM1.
    split.
    -
      intros E20.
      eapply (obj_copyout RT AF RC2 E OK d PMc FDO MST Σ Σ1 I CTX Σc m1); [exact OB1| exact FRM| exact EF| exact EL| exact ES| olia
        | exact LOC| exact COUT| reflexivity| exact REC| reflexivity| exact SH1| exact OUT].
    -
      intros E0. destruct HERR as [X|(_ & ERD & j' & ELV & VJ0 & JN)]; [exfalso; lia|]. subst rd. rewrite E0 in REC.
      eapply (obj_tails RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX Σc m1); [exact OB1| exact FRM| exact EF| exact EL| exact ES| exact EPTR| exact ZL0| | exact ELV| exact VJ0| exact JN
        | exact LOC| exact COUT| exact REC| exact SH1| exact OUT].
      destruct SLR as [X|X]; [left| right]; split; [exact X| olia| exact X| pose proof (BUD2 X); olia].
  Qed.

  Lemma esc_rec : forall (m : mem) (x1 x5 x6 x7 x12 x13 x15 x16 x17 x20 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (w24 w32 w40 w48 w88 w96 w120 w128 w0 w1 we : word) (F : bvmap 5 word) (fc : bv 32) (rd ri err sz : Z) (js4 jo j0 jco jt : list byte),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz ->
    (err = 20 \/ (err = 0 /\ rd = ae_DOC E /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d ri j' /\ 0 <= ri /\ j' <= ae_n E - 1)) ->
    0 <= rd < 2^64 -> 0 <= ri < 2^64 ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl) w88 w96 (Z_to_bv 64 (oi_P I + 1)) (Z_to_bv 64 (oi_out I)) w120 w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 w0; C8 w1; C4 we; CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz rd) (wz err) x12 x13 (wz (if lg then 1 else 0)) x15 x16 x17
               (wz ri) (wz (shad (oi_f I))) x20 (wz (oi_P I + 1)) (wz (oi_f I + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb676c) fc None m (seg_rom asegs)).
  Proof using SC AF CTX FDO MST OK RC2 HELEM.
    intros until jt. intros OB FRM LS HERR RD RI LOC COUT REC SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof sc_num as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof sc_cls as (CLD & CLS & IND & HinF).
    pose proof (sc_ef SC) as EF2. pose proof (sc_es SC) as ES2. pose proof sc_el as EL2.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    assert (ERR : err = 0 \/ err = 20) by (destruct HERR as [X|[X _]]; [right| left]; exact X).
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w764 E OK _ q b P L0 f D cap sz rd ri err lg); [exact MI| exact LO| lia| lia| lia| exact RD| exact RI| exact ERR| exact FLO| exact FHI| exact LS| exact LOC| exact REC| |].
    -
      intros m1 LG MU1 WM1 MI1 REC1.
      assert (OW1 : Forall (ownW I) [(b + 160, b + 184)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ2 _ m m1 OB0 EF2 EL2 ES2 MU1 WM1 MI1 OW1) as OB1.
      mport LOC MU1 WM1. mport COUT MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      destruct (sc_short SC LG) as (_ & _ & _ & E21).
      eapply (esc_reck Σ2 m1); [exact OB1| exact FRM| exact EF2| rewrite E21; exact EL1| exact ES2| lia| exact HERR| exact LOC| exact COUT| exact REC1| exact SH| exact OUT].
    -
      intros m1 xa1 LG MU1 WM1 MI1 REC1.
      assert (OW1 : Forall (ownW I) [(b + 160, b + 184)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ2 _ m m1 OB0 EF2 EL2 ES2 MU1 WM1 MI1 OW1) as OB1.
      pose proof OB1 as (_ & ART1 & ST1 & _).
      mport LOC MU1 WM1. mport COUT MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m1 ES2 ST1) as COK1. fold b in COK1.
      eapply (aevt_opdel RT AF RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D cap (ae_lo E));
        [exact (IND LG)| reflexivity| exact ART1| exact MI1| exact COK1| unfold unwind_ok; rewrite !unsigned_lit by ul; right; right; lia|].
      intros Σ3 v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & ST2) PR2 EL3 EF3 ES3 EC3.
      rewrite EU in ST2, PR2. rewrite (ret_pc_even 0xb6790) by lia.
      rewrite (live_restore m1 LG ART1) in EL3. rewrite EF2 in EF3. rewrite ES2 in ES3.
      assert (AG2 : agree_on (fun x => aclient (rt_live RT Σ3) (rt_frames RT Σ3) b x /\ ~ (0 <= x < 0 + 0)) m1 m2).
      { intros a [Ha _]. apply PR2. rewrite EF2, <- EF3. exact Ha. }
      assert (HinF3 : In (f, 1%nat) (rt_frames RT Σ3)) by (rewrite EF3; left; reflexivity).
      assert (DAP1 : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (str_apart m1 a ART1 Hc)) Hd)).
      pose proof (obase_agree Σ2 Σ3 m1 m2 OB1 EF3 ltac:(rewrite EL3; auto) ES3 ART2 MI2 ST2 ltac:(intros a Ha X Y; apply PR2; rewrite EL3, EF2, <- EF3; exact Ha) DAP1) as OB2.
      xport_stack LOC AG2. xport_stack COUT AG2. xport_stack REC1 AG2. xport_shadow SH AG2 HinF3. xport_stack OUT AG2.
      eapply (esc_reck Σ3 m2); [exact OB2| exact FRM| exact EF3| exact EL3| exact ES3| lia| exact HERR| exact LOC| exact COUT| exact REC1| exact SH| exact OUT].
  Qed.

  Lemma esc_bad : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x28 x29 x30 x31 : word)
      (w24 w32 w40 w48 w88 w96 w120 w128 : word) (F : bvmap 5 word) (fc : bv 32) (sz : Z) (js4 jo j0 jco : list byte) (cR : list cell),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl) w88 w96 (Z_to_bv 64 (oi_P I + 1)) (Z_to_bv 64 (oi_out I)) w120 w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) cR -> cells_size cR = 24%nat ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz 49) (wz (shad (oi_f I))) x20 (wz LIT_SLASH_A) (wz (oi_f I + 32)) (wz LIT_TILDE_A) (wz (oi_f I + 33)) x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb645c) fc None m (seg_rom asegs)).
  Proof using SC AF CTX FDO MST OK RC2.
    intros until cR. intros OB FRM LS LOC COUT REC SZR SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof sc_num as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof sc_cls as (CLD & CLS & IND & HinF). pose proof sc_budget as [BUD1 _].
    pose proof (sc_ef SC) as EF2. pose proof (sc_es SC) as ES2. pose proof sc_el as EL2.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ2 m ART0) as SP0R. rewrite ES2 in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (a_live_mono RT Σ Σ2 E LV EL2 ltac:(rewrite EF2; intros x Hx; right; exact Hx) ES2) as LV2.

    assert (BTAIL : forall (Σc : rts RT) (mx : mem) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y23 y24 y25 y26 y28 y29 y30 y31 : word) (Fx : bvmap 5 word) (nbs jC : list byte),
      obase RT E Σ I Σc mx -> rt_frames RT Σc = (f, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ -> rt_credit RT Σ2 <= rt_credit RT Σc ->
      rw_cells asegs mx b (obj_locA j0 w24 w32 w40 w48 (wz L0) (wz f) (wz f) (wz sl) w88 w96 (wz (P + 1)) (wz out) w120 w128) ->
      rw_cells asegs mx (b + 136) [CB 24 jco] -> rw_cells asegs mx (b + 160) cR -> rw_cells asegs mx (shad f) (obj_sh 0 0 0 js4) ->
      rw_cells asegs mx out [CB 16 nbs; C4 (Z_to_bv 64 22); CB 4 jC] ->
      aevt RT PMc Σc (Kpost RT E d Σ I PMc)
        (MS (mkR y1 (wz b) gp (wz TPV) y5 y6 y7 (wz q) (wz b) y10 y11 y12 y13 y14 y15 y16 y17
                 (wz 49) (wz (shad f)) y20 y21 (wz (f + 32)) y23 y24 y25 y26 (wz 2147450880) y28 y29 y30 y31)
            Fx (wz 0xb64a4) fc None mx (seg_rom asegs))).
    { intros Σc mx y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y23 y24 y25 y26 y28 y29 y30 y31 Fx nbs jC OBx EF EL ES CR LOCx COUTx RECx SHx OUTx.
      pose proof OBx as (MIx & _).
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_b3 E OK _ q b f); [exact MIx| exact LO| lia| lia| lia| exact FLO| exact FHI| clear - FSH; lia| exact S0| lia| exact LOCx| exact SHx|].
      intros m5 MU5 WM5 MI5 SH5.
      assert (OW5 : Forall (ownW I) [(shad f, shad f + 16)]) by (constructor; [right; right; left; cbn; fold f; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σc _ mx m5 OBx EF ltac:(rewrite EL; auto) ES MU5 WM5 MI5 OW5) as OB5.
      mport LOCx MU5 WM5. mport COUTx MU5 WM5. mport RECx MU5 WM5. mport OUTx MU5 WM5.
      destruct (rw_cells_forget _ _ _ _ OUTx) as [jo' OUT5]. cbn [cells_size csize Nat.add] in OUT5.
      eapply (obj_fin RT AF E OK d PMc FDO MST Σ Σ1 I CTX Σc m5); [exact OB5| exact FRM| exact EF| exact EL| exact ES| olia
        | exact LOCx| reflexivity| exact COUTx| reflexivity| exact RECx| exact SZR| exact SH5| exact OUT5]. }

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_b1 E OK _ q b f out); [exact MI| exact LO| lia| lia| lia| lia| ul| exact LOC|].
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m ES2 ST) as COK. fold b in COK.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m out 16 (Z_to_bv 8 0) (ae_lo E));
      [reflexivity| reflexivity| reflexivity| ul| lia| | exact ART0| exact MI| exact COK|].
    { apply (checked_dst_stack RT AF Σ2 m _ out 16 ART0); [rewrite ES2; ul| ul| rewrite EU; lia| exact (wr_at_sub m out 24 out 16 (proj2 OUT) ltac:(lia) ltac:(lia) ltac:(lia))]. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
    rewrite EU in ST2, PR2. change (Z.to_nat 16) with 16%nat in BY2. rewrite (ret_pc_even 0xb6470) by lia.
    assert (NCL2 : forall a, out <= a < out + 16 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24) by (intros a Ha _; clear - Ha; subst out; lia).
    pose proof (obase_call RT AF E OK d Σ Σ1 I CTX Σ2 out 16 m m2 OB0 EF2 EL2 ES2 ART2 MI2 ST2 PR2 NCL2 ltac:(right; left; clear - QO; lia) ltac:(right; left; flia)) as OB2.
    pose proof (agree_of_pres_ex _ _ _ _ _ m m2 (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (out <= x < out + 16)) PR2 (fun x H => H)) as AG.
    apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT; [| reflexivity]. cbn [mk_CB_cells app] in OUT.
    lazymatch type of OUT with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (joA := xa) in OUT; set (joB := xb) in OUT; set (joC := xc) in OUT end. clearbody joA joB joC.
    pose proof (rec_copy16 m m2 out [CB 16 joA] (CB 4 joB) joC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT eq_refl eq_refl BY2 eq_refl WM2 PR2 ltac:(lia) ltac:(ul)) as OUT2. clear OUT.
    xport_stack LOC AG. xport_shadow SH AG HinF. xport_stack COUT AG. xport_stack REC AG sz SZR.
    assert (LS2 : lstrA m2 (f + 32) lg D cap sz).
    { apply (lstrA_agree m m2 _ _ _ _ _ LS). intros a Ha. apply AG. split; [| clear - Ha DLO FHI LO QO DDR; lia].
      destruct Ha as [Ha|Ha]; [exact (lstr_cls_client RT Σ2 b _ _ _ CLS Ha)| exact (lstr_cls_client RT Σ2 b _ _ _ CLD Ha)]. }

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_b2 E OK _ q b f D cap sz out lg); [exact MI2| lia| lia| exact O8| exact (lvl_shz_rec RT AF E OK Σ2 m2 out 24 ART2 LV2 ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia))
      | exact FLO| exact FHI| exact LS2| exact OUT2| |].
    -
      intros m3 LG MU3 WM3 MI3 OUT3.
      assert (OW3 : Forall (ownW I) [(out, out + 24)]) by (constructor; [right; right; right; cbn; fold out; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ2 _ m2 m3 OB2 EF2 EL2 ES2 MU3 WM3 MI3 OW3) as OB3.
      mport LOC MU3 WM3. mport SH MU3 WM3. mport COUT MU3 WM3. mport REC MU3 WM3.
      destruct (sc_short SC LG) as (_ & _ & _ & E21).
      eapply (BTAIL Σ2 m3); [exact OB3| exact EF2| rewrite E21; exact EL1| exact ES2| lia| exact LOC| exact COUT| exact REC| exact SH| exact OUT3].
    -
      intros m3 xa1 LG MU3 WM3 MI3 OUT3.
      assert (OW3 : Forall (ownW I) [(out, out + 24)]) by (constructor; [right; right; right; cbn; fold out; lia| constructor]).
      pose proof (obase_munch RT AF E OK d Σ Σ1 I CTX Σ2 _ m2 m3 OB2 EF2 EL2 ES2 MU3 WM3 MI3 OW3) as OB3.
      pose proof OB3 as (_ & ART3 & ST3 & _).
      mport LOC MU3 WM3. mport SH MU3 WM3. mport COUT MU3 WM3. mport REC MU3 WM3.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m3 ES2 ST3) as COK3. fold b in COK3.
      eapply (aevt_opdel RT AF RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m3 D cap (ae_lo E));
        [exact (IND LG)| reflexivity| exact ART3| exact MI3| exact COK3| unfold unwind_ok; rewrite !unsigned_lit by ul; right; right; lia|].
      intros Σ3 v t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' m4 (ART4 & MI4 & ST4) PR4 EL3 EF3 ES3 EC3.
      rewrite EU in ST4, PR4. rewrite (ret_pc_even 0xb64a4) by lia.
      rewrite (live_restore m3 LG ART3) in EL3. rewrite EF2 in EF3. rewrite ES2 in ES3.
      assert (AG4 : agree_on (fun x => aclient (rt_live RT Σ3) (rt_frames RT Σ3) b x /\ ~ (0 <= x < 0 + 0)) m3 m4).
      { intros a [Ha _]. apply PR4. rewrite EF2, <- EF3. exact Ha. }
      assert (HinF3 : In (f, 1%nat) (rt_frames RT Σ3)) by (rewrite EF3; left; reflexivity).
      assert (DAP3 : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (str_apart m3 a ART3 Hc)) Hd)).
      pose proof (obase_agree Σ2 Σ3 m3 m4 OB3 EF3 ltac:(rewrite EL3; auto) ES3 ART4 MI4 ST4 ltac:(intros a Ha X Y; apply PR4; rewrite EL3, EF2, <- EF3; exact Ha) DAP3) as OB4.
      xport_stack LOC AG4. xport_stack COUT AG4. xport_stack REC AG4 sz SZR. xport_shadow SH AG4 HinF3. xport_stack OUT3 AG4.
      eapply (BTAIL Σ3 m4); [exact OB4| exact EF3| exact EL3| exact ES3| lia| exact LOC| exact COUT| exact REC| exact SH| exact OUT3].
  Qed.

  End SCtx.
End ObjE.
