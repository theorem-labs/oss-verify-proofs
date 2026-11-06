(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow Zcn.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Zq3
     Zqc Zqd Zqb I_lkit Z45 Z5k Z5q Z6b Z60 Z5o Z5w
     Z6e Z6h.
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

  Hypothesis LPOS : forall p n, In (p, n) (rt_live RT Σ) -> exists n', In (p, n') (rt_live RT Σ) /\ 0 < n'.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -256 - dd) in *.
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
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
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
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
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
  Proof using SC CTX AF LPOS.
    intros m LG ART2. destruct (sc_long SC LG) as (EL & ECAP & LK23 & _ & _ & D0 & _).
    pose proof (str_sz_bound Lk ltac:(lia)) as SZB.
    rewrite EL. apply live_remove_fresh. intros [p n] Hin. cbn [fst]. intros ->.
    destruct (LPOS D n Hin) as (n' & Hin' & Hn').
    pose proof (af_live_disj RT AF Σ2 m D cap D n' [] (rt_live RT Σ) ART2 EL Hin'). lia.
  Qed.

  Lemma obase_agree : forall (Σc Σc' : rts RT) (m m' : mem),
    obase RT E Σ I Σc m -> rt_frames RT Σc' = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc')) -> rt_sp0 RT Σc' = rt_sp0 RT Σ ->
    ART RT Σc' m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) (oi_b I) ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σc') (oi_b I) (bv_unsigned a) ->
       ~ (oi_f I + 24 <= bv_unsigned a < oi_f I + 120) -> ~ (D <= bv_unsigned a < D + cap) -> m' a = m a) ->
    (forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a) ->
    obase RT E Σ I Σc' m'.
  Proof using SC CTX AF OK.
    intros Σc Σc' m m' OB EF' EL' ES' ART' MI' ST' AG DAP.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σc' m' ART') as SP0R. rewrite ES' in SP0R.
    pose proof sc_num as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1. fold q dd b in R1, R2, R3.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σc')) by (rewrite EF'; left; reflexivity).
    assert (QW : rt_sp0 RT Σ - STACK_WIN <= q) by ul.

    assert (AGC : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a /\ ~ (out <= a < out + 24)) m m').
    { intros a [Ha Ho]. pose proof (newframe_apartI RT AF Σ Σc' m' f 1%nat q (bv_unsigned a) ART' EF' EL' ES' QW Ha) as [N1 _]. rewrite fs1 in N1.
      apply AG; [| clear - N1; lia| exact (DAP _ ltac:(idtac) ) || (intros X; exact (DAP _ X Ha))].
      rewrite EF'. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros x Hx; right; exact Hx| lia]. }
    split; [| exact ST']. split; [exact MI'|]. split; [exact ART'|].
    split. { apply (AINV_A_agree E m m' AI). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX.
             pose proof (ainv_rng_lo E (bv_unsigned x) OK Hx). apply AGC. split; [exact CX| lia]. }
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ SAVED). intros a Ha. cbn [cells_size csize Nat.add length obj_saved] in Ha. apply AG; [left; unfold USTACK_TOP in *; lia| lia| lia]. }
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ HIGH). intros a Ha. cbn [cells_size csize Nat.add length] in Ha. apply AG; [left; unfold USTACK_TOP in *; lia| lia| lia]. }
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ HDR). intros a Ha. cbn [cells_size csize Nat.add length obj_hdrB] in Ha.
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

  Lemma obase_munchE : forall (Σc : rts RT) (W : list (Z * Z)) (m m' : mem),
    obase RT E Σ I Σc m -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> Forall (ownW I) W -> Forall (fun r => oi_b I <= fst r \/ snd r <= ae_lo E) W ->
    obase RT E Σ I Σc m'.
  Proof using SC CTX AF OK.
    intros Σc W m m' OB EF EL ES MU WM MI' HW HW2. destruct OB as [OBK ST].
    split; [exact (obaseK_munch RT AF E OK d Σ Σ1 I CTX Σc W m m' OBK EF EL ES MU WM MI' HW)|].
    apply (stk_transport_disjoint _ W m m' _ _ ST MU WM). clear - HW2.
    induction W as [|[l h] W IH]; [exact Logic.I|]. inversion HW2 as [|x l' H1 H3]; subst. cbn [fst snd] in H1. cbn [disjoint_from fst snd].
    split; [lia| exact (IH H3)].
  Qed.

  Definition tails_stmtB : Prop :=
    forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
           (F : bvmap 5 word) (fc : bv 32) (rd ri code v4 v5 v6 : Z) (js4 jo j0 j2 : list byte) (cS : list cell),
      obase RT E Σ I Σc m -> frm0 fc ->
      rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
      rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σc ->
      (0 <= sl < L0 -> rt_credit RT Σ - obj_costA d (oi_L I) + elem_costA d (L0 - sl) <= rt_credit RT Σc) ->
      0 <= code < 64 -> (code = 20 \/ (code = 0 /\ rd = ae_DOC E /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d ri j' /\ 0 <= ri /\ j' <= ae_n E - 1)) ->
      rw_cells bsegs m (oi_b I) (obj_loc72 j0 (Z_to_bv 64 sl) (Z_to_bv 64 (oi_node I)) (oi_f I) (oi_out I)) ->
      rw_cells bsegs m (oi_b I + 72) cS -> cells_size cS = 24%nat ->
      rw_cells bsegs m (oi_b I + 96) [C8 (Z_to_bv 64 rd); C8 (Z_to_bv 64 ri); C4 (Z_to_bv 64 code); CB 4 j2] ->
      rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
      rw_cells bsegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
      aevt RT PMc Σc (Kpost RT E d Σ I PMc)
        (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz code) x11 x12 x13 x14 x15 x16 x17
                 (wz sl) (wz (shad (oi_f I))) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
            F (wz 0x99f40) fc None m (seg_rom bsegs)).

  Definition fin_stmtB : Prop :=
    forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (w24 w32 : word)
           (F : bvmap 5 word) (fc : bv 32) (v4 v5 v6 : Z) (js4 jC j0 : list byte) (cS cC cV : list cell),
      obase RT E Σ I Σc m -> frm0 fc ->
      rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
      rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σc ->
      rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
      rw_cells bsegs m (oi_b I + 72) cS -> cells_size cS = 24%nat -> rw_cells bsegs m (oi_b I + 96) cC -> cells_size cC = 24%nat ->
      rw_cells bsegs m (oi_b I + 120) cV -> cells_size cV = 32%nat ->
      rw_cells bsegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) ->
      rw_cells bsegs m (oi_out I) [CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 22); CB 4 jC] ->
      aevt RT PMc Σc (Kpost RT E d Σ I PMc)
        (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (wz (shad (oi_f I))) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
            F (wz 0x99fc8) fc None m (seg_rom bsegs)).
  Hypothesis HTAILS : tails_stmtB.
  Hypothesis HFIN : fin_stmtB.

  Lemma esc_recB : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) (cw : word)
      (F : bvmap 5 word) (fc : bv 32) (rd ri code sz : Z) (js4 jo j0 jt j2 : list byte),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz -> 0 <= code < 64 ->
    (code = 20 \/ (code = 0 /\ rd = ae_DOC E /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d ri j' /\ 0 <= ri /\ j' <= ae_n E - 1)) ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 (Z_to_bv 64 sl) (Z_to_bv 64 (oi_node I)) (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) [C8 (Z_to_bv 64 rd); C8 (Z_to_bv 64 ri); C4 (Z_to_bv 64 code); CB 4 jt] ->
    rw_cells bsegs m (oi_b I + 96) [CB 16 (le8 (Z_to_bv 64 rd) ++ le8 (Z_to_bv 64 ri)); C4 cw; CB 4 j2] ->
    rw_cells bsegs m (oi_b I + 120) [C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 (oi_P I + 1)); C8 (Z_to_bv 64 L0)] ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz sl) (wz (shad (oi_f I))) x20 x21 (wz (oi_f I + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0x99ee4) fc None m (seg_rom bsegs)).
  Proof using SC AF CTX FDO MST OK RC2 LPOS HTAILS.
    intros until j2. intros OB FRM LS CODE HERR LOC SRET CHILD SV SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof sc_num as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof sc_cls as (CLD & CLS & IND & HinF). pose proof sc_budget as [BUD1 BUD2].
    pose proof (sc_ef SC) as EF2. pose proof (sc_es SC) as ES2. pose proof sc_el as EL2.
    pose proof (sh_apartI) as SHDI. pose proof (str_apart) as STAP.
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    unfold obj_loc72 in LOC. unfold obj_sh, pz in SH.
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_wa4B E OK _ q b f D cap sz code lg); [exact MI| ul| lia| lia| lia| exact CODE| exact FLO| exact FHI| clear - FSH; lia| exact S0| lia| exact LS| exact SRET| exact CHILD| unfold obj_sh, pz; exact SH| |].
    -
      intros m1 LG MU1 WM1 MI1 CHILD1 SH1.
      assert (OW1 : Forall (ownW I) [(b + 112, b + 116); (shad f, shad f + 16)]).
      { constructor; [left; unfold oi_b; cbn; lia|]. constructor; [right; right; left; cbn; fold f; lia| constructor]. }
      pose proof (obase_munchE Σ2 _ m m1 OB0 EF2 EL2 ES2 MU1 WM1 MI1 OW1 ltac:(constructor; [left; cbn [fst snd]; unfold oi_b; lia|]; constructor; [right; cbn [fst snd]; clear - SHI; lia| constructor])) as OB1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ LOC MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as LOC1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ SRET MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as SRET1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ SV MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as SV1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ OUT MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI HL QO R1 R2 R3 DDR; lia)) as OUT1.
      apply rec_node16 in CHILD1.
      destruct (sc_short SC LG) as (_ & _ & _ & E21).
      eapply (HTAILS Σ2 m1); [exact OB1| exact FRM| exact EF2| rewrite E21; exact EL1| exact ES2| exact BUD1| exact BUD2| exact CODE| exact HERR| exact LOC1| exact SRET1| reflexivity
        | exact CHILD1| exact SV1| exact SH1| exact OUT1].
    -
      intros m1 xa1 LG MU1 WM1 MI1 CHILD1 SH1.
      assert (OW1 : Forall (ownW I) [(b + 112, b + 116); (shad f, shad f + 16)]).
      { constructor; [left; unfold oi_b; cbn; lia|]. constructor; [right; right; left; cbn; fold f; lia| constructor]. }
      pose proof (obase_munchE Σ2 _ m m1 OB0 EF2 EL2 ES2 MU1 WM1 MI1 OW1 ltac:(constructor; [left; cbn [fst snd]; unfold oi_b; lia|]; constructor; [right; cbn [fst snd]; clear - SHI; lia| constructor])) as OB1.
      pose proof OB1 as [(_ & ART1 & _) ST1].
      pose proof (rw_cells_transport bsegs _ m m1 _ _ LOC MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as LOC1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ SRET MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as SRET1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ SV MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as SV1.
      pose proof (rw_cells_transport bsegs _ m m1 _ _ OUT MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI HL QO R1 R2 R3 DDR; lia)) as OUT1.
      clear LOC SRET SV OUT CHILD.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m1 b ES2 ST1 ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK1.
      eapply (aevt_opdel RT AF RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D cap (ae_lo E));
        [exact (IND LG)| reflexivity| exact ART1| exact MI1| exact COK1| unfold unwind_ok; rewrite !unsigned_lit by ul; right; right; lia|].
      intros Σ3 v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & ST2) PR2 EL3 EF3 ES3 EC3.
      rewrite EU in ST2, PR2. rewrite (ret_pc_even 0x99f24) by lia.
      rewrite (live_restore m1 LG ART1) in EL3. rewrite EF2 in EF3. rewrite ES2 in ES3.
      assert (AG2 : agree_on (fun x => aclient (rt_live RT Σ3) (rt_frames RT Σ3) b x /\ ~ (0 <= x < 0 + 0)) m1 m2).
      { intros a [Ha _]. apply PR2. rewrite EF2, <- EF3. exact Ha. }
      assert (HinF3 : In (f, 1%nat) (rt_frames RT Σ3)) by (rewrite EF3; left; reflexivity).
      assert (DAP1 : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (STAP m1 a ART1 Hc)) Hd)).
      pose proof (obase_agree Σ2 Σ3 m1 m2 OB1 EF3 ltac:(rewrite EL3; auto) ES3 ART2 MI2 ST2 ltac:(intros a Ha X Y; apply PR2; rewrite EL3, EF2, <- EF3; exact Ha) DAP1) as OB2.
      unfold obj_sh, pz in SH1. xport_stack LOC1 AG2. xport_stack SRET1 AG2. xport_stack CHILD1 AG2. xport_stack SV1 AG2. xport_shadow SH1 AG2 HinF3. xport_stack OUT1 AG2.
      pose proof OB2 as [(_ & _ & _) _]. pose proof MI2 as MI2'.
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_we4B E OK _ q b f code); [exact MI2| ul| lia| lia| lia| exact CODE| exact FLO| exact FHI| clear - FSH; lia| exact S0| lia| exact CHILD1| unfold obj_sh, pz; exact SH1|].
      intros m3 MU3 WM3 MI3 SH3.
      assert (OW3 : Forall (ownW I) [(shad f, shad f + 16)]) by (constructor; [right; right; left; cbn; fold f; lia| constructor]).
      pose proof (obase_munchE Σ3 _ m2 m3 OB2 EF3 ltac:(rewrite EL3; auto) ES3 MU3 WM3 MI3 OW3 ltac:(constructor; [right; cbn [fst snd]; clear - SHI; lia| constructor])) as OB3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ LOC1 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as LOC3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SRET1 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as SRET3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ CHILD1 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as CHILD3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SV1 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as SV3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ OUT1 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI HL QO R1 R2 R3 DDR; lia)) as OUT3.
      apply rec_node16 in CHILD3.
      eapply (HTAILS Σ3 m3); [exact OB3| exact FRM| exact EF3| exact EL3| exact ES3| clear - BUD1 EC3; unfold oi_L in *; cbv delta [ptr] in *; lia| intros X; pose proof (BUD2 X); clear - H EC3; unfold oi_L in *; cbv delta [ptr] in *; lia| exact CODE| exact HERR| exact LOC3| exact SRET3| reflexivity
        | exact CHILD3| exact SV3| exact SH3| exact OUT3].
  Qed.

  Lemma esc_badB : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) (w24 w32 : word)
      (F : bvmap 5 word) (fc : bv 32) (sz : Z) (js4 jo j0 : list byte) (cS cC cV : list cell),
    obase RT E Σ I Σ2 m -> frm0 fc -> lstrA m (oi_f I + 32) lg D cap sz ->
    rw_cells bsegs m (oi_b I) (obj_loc72 j0 w24 w32 (oi_f I) (oi_out I)) ->
    rw_cells bsegs m (oi_b I + 72) cS -> cells_size cS = 24%nat -> rw_cells bsegs m (oi_b I + 96) cC -> cells_size cC = 24%nat ->
    rw_cells bsegs m (oi_b I + 120) cV -> cells_size cV = 32%nat ->
    rw_cells bsegs m (shad (oi_f I)) (obj_sh 0 0 0 js4) -> rw_cells bsegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ2 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (wz (shad (oi_f I))) x20 x21 (wz (oi_f I + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0x99e58) fc None m (seg_rom bsegs)).
  Proof using SC AF CTX FDO MST OK RC2 LPOS HFIN.
    intros until cV. intros OB FRM LS LOC SRET SZS CHILD SZC SV SZV SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as [(MI & ART0 & AI & SAVED & HIGH & HDR & PRES) ST].
    pose proof sc_num as (D0 & DLO & CAPR & LKC & LKR & L0R & SEP). pose proof sc_cls as (CLD & CLS & IND & HinF). pose proof sc_budget as [BUD1 _].
    pose proof (sc_ef SC) as EF2. pose proof (sc_es SC) as ES2. pose proof sc_el as EL2.
    pose proof (str_apart) as STAP.
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (a_live_mono RT Σ Σ2 E LV EL2 ltac:(rewrite EF2; intros x Hx; right; exact Hx) ES2) as LV2.
    unfold obj_loc72 in LOC. unfold obj_sh, pz in SH.

    assert (BTAIL : forall (Σc : rts RT) (mx : mem) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y23 y24 y25 y26 y28 y29 y30 y31 : word) (Fx : bvmap 5 word) (jC : list byte),
      obase RT E Σ I Σc mx -> rt_frames RT Σc = (f, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ -> rt_credit RT Σ2 <= rt_credit RT Σc ->
      rw_cells bsegs mx b [CB 24 j0; C8 w24; C8 w32; C8 (wz f); C8 (wz out); C8 (wz f); C8 (wz f)] ->
      rw_cells bsegs mx (b + 72) cS -> rw_cells bsegs mx (b + 96) cC -> rw_cells bsegs mx (b + 120) cV ->
      rw_cells bsegs mx (shad f) (obj_sh 0 0 0 js4) -> rw_cells bsegs mx out [CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 22); CB 4 jC] ->
      aevt RT PMc Σc (Kpost RT E d Σ I PMc)
        (MS (mkR y1 (wz b) gp (wz TPV) y5 y6 y7 (wz q) (wz b) y10 y11 y12 y13 y14 y15 y16 y17
                 y18 (wz (shad f)) y20 y21 (wz (f + 32)) y23 y24 y25 y26 (wz 2147450880) y28 y29 y30 y31)
            Fx (wz 0x99ea4) fc None mx (seg_rom bsegs))).
    { intros Σc mx y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y23 y24 y25 y26 y28 y29 y30 y31 Fx jC OBx EF EL ES CR LOCx SRETx CHILDx SVx SHx OUTx.
      pose proof OBx as [(MIx & _) _].
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_b3B E OK _ q b f); [exact MIx| exact FLO| exact FHI| clear - FSH; lia| exact S0| lia| exact SHx|].
      intros m5 MU5 WM5 MI5 SH5.
      assert (OW5 : Forall (ownW I) [(shad f, shad f + 16)]) by (constructor; [right; right; left; cbn; fold f; lia| constructor]).
      pose proof (obase_munchE Σc _ mx m5 OBx EF ltac:(rewrite EL; auto) ES MU5 WM5 MI5 OW5 ltac:(constructor; [right; cbn [fst snd]; clear - SHI; lia| constructor])) as OB5.
      pose proof (rw_cells_transport bsegs _ mx m5 _ _ LOCx MU5 WM5 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as LOC5.
      pose proof (rw_cells_transport bsegs _ mx m5 _ _ SRETx MU5 WM5 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZS; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as SRET5.
      pose proof (rw_cells_transport bsegs _ mx m5 _ _ CHILDx MU5 WM5 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZC; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as CHILD5.
      pose proof (rw_cells_transport bsegs _ mx m5 _ _ SVx MU5 WM5 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZV; unfold shad in *; clear - SHI FHI R1 R2 R3 DDR; lia)) as SV5.
      pose proof (rw_cells_transport bsegs _ mx m5 _ _ OUTx MU5 WM5 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; unfold shad in *; clear - SHI HL QO R1 R2 R3 DDR; lia)) as OUT5.
      eapply (HFIN Σc m5); [exact OB5| exact FRM| exact EF| exact EL| exact ES| clear - CR BUD1; unfold oi_L in *; cbv delta [ptr] in *; lia
        | unfold obj_loc72; exact LOC5| exact SRET5| exact SZS| exact CHILD5| exact SZC| exact SV5| exact SZV| exact SH5| exact OUT5]. }

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_b1B E OK _ q b f out); [exact MI| ul| lia| lia| lia| lia| ul| unfold obj_loc72; exact LOC|].
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m b ES2 ST ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m out 16 (Z_to_bv 8 0) (ae_lo E));
      [reflexivity| reflexivity| reflexivity| ul| lia| | exact ART0| exact MI| exact COK|].
    { apply (checked_dst_stack RT AF Σ2 m _ out 16 ART0); [rewrite ES2; ul| ul| rewrite EU; lia| exact (wr_at_sub m out 24 out 16 (proj2 OUT) ltac:(lia) ltac:(lia) ltac:(lia))]. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
    rewrite EU in ST2, PR2. change (Z.to_nat 16) with 16%nat in BY2. rewrite (ret_pc_even 0x99e70) by lia.
    assert (NCL2 : forall a, out <= a < out + 16 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24) by (intros a Ha _; clear - Ha; subst out; lia).
    pose proof (obaseK_call RT AF E OK d Σ Σ1 I CTX Σ2 b out 16 m m2 (proj1 OB0) EF2 EL2 ES2 ART2 MI2 ltac:(unfold oi_b; lia) PR2 NCL2 ltac:(right; left; clear - QO; lia) ltac:(right; left; flia)) as OBK2.
    pose proof (obase_of_K RT E Σ I Σ2 m2 OBK2 ST2) as OB2.
    pose proof (agree_of_pres_ex _ _ _ _ _ m m2 (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) b x /\ ~ (out <= x < out + 16)) PR2 (fun x H => H)) as AG.
    apply (rw_cells_split_CB bsegs _ _ [] 24 jo [] [16; 4; 4]%nat) in OUT; [| reflexivity]. cbn [mk_CB_cells app] in OUT.
    lazymatch type of OUT with rw_cells _ _ _ [CB 16 ?xa; CB 4 ?xb; CB 4 ?xc] => set (joA := xa) in OUT; set (joB := xb) in OUT; set (joC := xc) in OUT end. clearbody joA joB joC.
    pose proof (rec_copy16 m m2 out [CB 16 joA] (CB 4 joB) joC (repeat (Z_to_bv 8 0) 16) _ _ _ OUT eq_refl eq_refl BY2 eq_refl WM2 PR2 ltac:(lia) ltac:(ul)) as OUT2. clear OUT.
    xport_stack LOC AG. xport_shadow SH AG HinF. xport_stack SRET AG sz SZS. xport_stack CHILD AG sz SZC. xport_stack SV AG sz SZV.
    assert (LS2 : lstrA m2 (f + 32) lg D cap sz).
    { apply (lstrA_agree m m2 _ _ _ _ _ LS). intros a Ha. apply AG. split; [| clear - Ha DLO FHI R1 R2 R3 QO DDR; lia].
      destruct Ha as [Ha|Ha]; [exact (lstr_cls_client RT Σ2 b _ _ _ CLS Ha)| exact (lstr_cls_client RT Σ2 b _ _ _ CLD Ha)]. }

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_b2B E OK _ q b f D cap sz out lg); [exact MI2| lia| lia| exact O8| exact (lvl_shz_rec RT AF E OK Σ2 m2 out 24 ART2 LV2 ltac:(lia) ltac:(lia) O8 eq_refl ltac:(lia))
      | exact FLO| exact FHI| exact LS2| exact OUT2| |].
    -
      intros m3 LG MU3 WM3 MI3 OUT3.
      assert (OW3 : Forall (ownW I) [(out, out + 24)]) by (constructor; [right; right; right; cbn; fold out; lia| constructor]).
      pose proof (obase_munchE Σ2 _ m2 m3 OB2 EF2 EL2 ES2 MU3 WM3 MI3 OW3 ltac:(constructor; [left; cbn [fst snd]; unfold oi_b; clear - QO R2 R3 DDR; lia| constructor])) as OB3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ LOC MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - QO R1 R2 R3 DDR; lia)) as LOC3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SRET MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZS; clear - QO R1 R2 R3 DDR; lia)) as SRET3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ CHILD MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZC; clear - QO R1 R2 R3 DDR; lia)) as CHILD3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SV MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZV; clear - QO R1 R2 R3 DDR; lia)) as SV3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SH MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - QO SHI R1; lia)) as SH3.
      destruct (sc_short SC LG) as (_ & _ & _ & E21).
      eapply (BTAIL Σ2 m3); [exact OB3| exact EF2| rewrite E21; exact EL1| exact ES2| lia| exact LOC3| exact SRET3| exact CHILD3| exact SV3| unfold obj_sh, pz; exact SH3| exact OUT3].
    -
      intros m3 xa1 LG MU3 WM3 MI3 OUT3.
      assert (OW3 : Forall (ownW I) [(out, out + 24)]) by (constructor; [right; right; right; cbn; fold out; lia| constructor]).
      pose proof (obase_munchE Σ2 _ m2 m3 OB2 EF2 EL2 ES2 MU3 WM3 MI3 OW3 ltac:(constructor; [left; cbn [fst snd]; unfold oi_b; clear - QO R2 R3 DDR; lia| constructor])) as OB3.
      pose proof OB3 as [(_ & ART3 & _) ST3].
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ LOC MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - QO R1 R2 R3 DDR; lia)) as LOC3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SRET MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZS; clear - QO R1 R2 R3 DDR; lia)) as SRET3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ CHILD MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZC; clear - QO R1 R2 R3 DDR; lia)) as CHILD3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SV MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; rewrite SZV; clear - QO R1 R2 R3 DDR; lia)) as SV3.
      pose proof (rw_cells_transport bsegs _ m2 m3 _ _ SH MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; clear - QO SHI R1; lia)) as SH3.
      clear LOC SRET CHILD SV SH.
      pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ2 m3 b ES2 ST3 ltac:(unfold oi_b; lia) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK3.
      eapply (aevt_opdel RT AF RC PMc FDO MST Σ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc m3 D cap (ae_lo E));
        [exact (IND LG)| reflexivity| exact ART3| exact MI3| exact COK3| unfold unwind_ok; rewrite !unsigned_lit by ul; right; right; lia|].
      intros Σ3 v t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' m4 (ART4 & MI4 & ST4) PR4 EL3 EF3 ES3 EC3.
      rewrite EU in ST4, PR4. rewrite (ret_pc_even 0x99ea4) by lia.
      rewrite (live_restore m3 LG ART3) in EL3. rewrite EF2 in EF3. rewrite ES2 in ES3.
      assert (AG4 : agree_on (fun x => aclient (rt_live RT Σ3) (rt_frames RT Σ3) b x /\ ~ (0 <= x < 0 + 0)) m3 m4).
      { intros a [Ha _]. apply PR4. rewrite EF2, <- EF3. exact Ha. }
      assert (HinF3 : In (f, 1%nat) (rt_frames RT Σ3)) by (rewrite EF3; left; reflexivity).
      assert (DAP3 : forall a, D <= a < D + cap -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) q a) by (intros a Hd Hc; exact (proj2 (proj2 (STAP m3 a ART3 Hc)) Hd)).
      pose proof (obase_agree Σ2 Σ3 m3 m4 OB3 EF3 ltac:(rewrite EL3; auto) ES3 ART4 MI4 ST4 ltac:(intros a Ha X Y; apply PR4; rewrite EL3, EF2, <- EF3; exact Ha) DAP3) as OB4.
      xport_stack LOC3 AG4. xport_stack SRET3 AG4 sz SZS. xport_stack CHILD3 AG4 sz SZC. xport_stack SV3 AG4 sz SZV. xport_shadow SH3 AG4 HinF3. xport_stack OUT3 AG4.
      eapply (BTAIL Σ3 m4); [exact OB4| exact EF3| exact EL3| exact ES3| lia| exact LOC3| exact SRET3| exact CHILD3| exact SV3| unfold obj_sh, pz; exact SH3| exact OUT3].
  Qed.

  End SCtx.
End ObjE.
