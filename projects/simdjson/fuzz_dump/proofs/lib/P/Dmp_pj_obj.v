(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjDmp.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_objl Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_defs Dmp_defs Dmp_pj_iface Dmp_pj_kit Dmp_pj_leaf Dmp_pj Dmp_pj_arr.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac retlit := try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Body.
  Variable D : pjenv.
  Hypothesis DOK : pjenv_ok D.
  Hypothesis PUT : os_putX_stmt.
  Variable d : nat.
  Hypothesis PJ : pj_stmt d.
  Variable j32 : list byte.
  Notation lcj := [CB 32 j32].
  Notation LCJ := (junk32 j32).
  Notation n := (pe_n D).
  Notation T := (Tf (pe_tws D)).
  Notation S := (Tf (pe_sbs D)).
  Notation sn := (pe_sn D).

  Definition OLS (e it : Z) (x1 gp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x24 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) x9 (Z_to_bv 64 (pe_TAPE D)) x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (pe_DOC D)) (Z_to_bv 64 DMP_LIT_QUOTE) (Z_to_bv 64 DMP_LIT_QCOLON) x21 (Z_to_bv 64 it) (Z_to_bv 64 e) x24 (Z_to_bv 64 72057594037927935)
            x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 DMP_PJ_OBJ_LOOP) fc None m (seg_rom psegs).
  Definition KOLOOP (K : machine_state -> Prop) (gp : word) (e it : Z) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x24 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      PINV pjolits D m' -> frm0 fc' -> evt psegs K (OLS e it x1 gp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x24 x26 x27 x28 x29 x30 x31 F' fc' m').

  Definition KOEND (K : machine_state -> Prop) (gp : word) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      PINV pjolits D m' -> frm0 fc' ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x25 x26 x27 x28 x29 x30 x31) F' (Z_to_bv 64 0x3aefc) fc' None m' (seg_rom psegs)).

  Lemma pj_obj_end : forall (K : machine_state -> Prop) (gp : word), KEXIT D pjolits K gp -> KOEND K gp.
  Proof.
    intros K gp HK. unfold KOEND. intros until fc'. intros DI FRM.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & (scr & FR) & _). unfold pjolits, pjsaves, DMP_LIT_RBRACE in FR. cbn [app] in FR.
    pose proof (munch_refl ([] : list (Z * Z)) m') as MU. pose proof (wmono_refl psegs m') as WM.

    step. step. step. step. step.
    lit_at 0x104d1 1%nat m' MI LIT LITL.
    eapply (put_call pjolits pjolits32 D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    unfold KEXIT, DMP_PJ_EXIT in HK. eapply HK; [exact DI2| exact FRM].
  Qed.

  Lemma pj_obj_head : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (i e cv : Z),
    PINV lcj D m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX -> T i = cword t_obj (e + 1) cv ->
    KEXIT D lcj K gp -> (i + 1 <> e -> KOLOOP K gp e (i + 1)) ->
    evt psegs K (DST D i t_obj x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until cv. intros DI FRM I0 IE EN CV E HK HL. unfold DST, DMP_PJ_DISPATCH, t_obj.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, CNT_MAX in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & SB & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    assert (TIR : 0 <= T i < 2^64) by (rewrite E; unfold cword, tword, t_obj in *; lia).

    step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_false.

    step. step. step. step. step.
    lit_at 0x13072 1%nat m MI LIT LITL.
    eapply (put_call lcj LCJ D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & SB2 & DOCC2 & _).
    pose proof (tape_read_type m2 (pe_TAPE D) (pe_tws D) i TB2 ltac:(lia) TIR) as RTY.
    pose proof (tape_read m2 (pe_TAPE D) (pe_tws D) i TB2 ltac:(lia)) as RDT.
    rewrite E in RTY. rewrite ttype_cword in RTY by (unfold CNT_MAX; lia). unfold t_obj in RTY.

    step. astep. astep. astep. astep. astep. astep. rewrite mask_all by lia.

    step. astep. rewrite mask_all by lia. astep. astep. step. astep. astep. rewrite E, ttype_cword by (unfold CNT_MAX; lia). unfold t_obj. astep. step. step. step. if_false.

    astep. astep. astep. astep. step. if_true.

    step. astep. astep. astep. astep. step. step. if_false. astep. astep. rewrite low32_cword by (unfold CNT_MAX; lia). astep.
    replace (e + 1 + -1) with e by lia. step. step. step.
    if_cases KE; zify_cond KE.
    -
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU'.

      step. step. step. step.
      lit_at 0x104d1 1%nat m2 MI2 LIT LITL.
      eapply (put_call lcj LCJ D DOK PUT); [exact DI2| exact LIT| exact LITL| lia| lia| lia| left; lia|].
      clear MU WM LIT LITL. intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 DI3. retlit.
      unfold KEXIT, DMP_PJ_EXIT in HK. eapply HK; [exact DI3| exact FRM].
    -
      pose proof DI2 as (_ & _ & _ & _ & _ & _ & _ & _ & (scr & FR) & _). unfold pjsaves in FR. cbn [app] in FR.
      apply (rw_cells_split_CB psegs _ _ [] 32 j32 _ [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      clear MU. pose proof (munch_refl [(dsp D, dsp D + 40)]%Z m2) as MU.

      hstep. step. step. step. step. step. astep. astep. hstep. step. step. astep. hstep. astep. astep. hstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv psegs mx |- _ =>
        pose proof (PINV_reframe pjolits pjolits32 lcj D m2 mx [CB 8 scr] DOK DI2 MU WM MIx eq_refl FR) as DI3 end end.
      unfold KOLOOP, OLS, DMP_PJ_OBJ_LOOP, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL.
      eapply evt_eq; [| eapply HL; [rewrite ?unsigned_lit in KE by lia; lia| exact DI3| exact FRM]]. cbn. atp_st_eq.
  Qed.

  Lemma pj_obj_step : forall (K : machine_state -> Prop) (e it j : Z) (x1 gp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x24 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV pjolits D m -> frm0 fc -> is_str T S sn it -> elem T S sn ck_any d (it + 1) j -> 0 <= it -> j <= e -> e + 1 <= n -> pe_lo D + pj_need d <= dsp D ->
    (j <> e -> KOLOOP K gp e j) -> (j = e -> KOEND K gp) ->
    evt psegs K (OLS e it x1 gp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x24 x26 x27 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM STRI EL I0 JE EN NEED HL HE. unfold OLS, DMP_PJ_OBJ_LOOP, DMP_LIT_QUOTE, DMP_LIT_QCOLON.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, CNT_MAX in *.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & SB & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (key_word_range _ _ _ _ STRI SNR) as (KWR & KM & KT).
    destruct (is_str_read _ _ _ SNR _ STRI) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ SNR _ _ SA) as (O0 & L0 & OL & LE & O56).
    set (o := tval (T it)) in *.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) it TB ltac:(lia)) as RDT.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) o SB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 1) SB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 2) SB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 3) SB ltac:(lia)) as RB3.
    assert (B0 : 0 <= S o < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B1 : 0 <= S (o + 1) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B2 : 0 <= S (o + 2) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B3 : 0 <= S (o + 3) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).

    astep. astep. step. step. astep. rewrite KM. astep. step. step. step. step.

    step. step. step. step.
    lit_at 0x1233a 1%nat m MI LIT LITL.
    eapply (put_call pjolits pjolits32 D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL RDT RB0 RB1 RB2 RB3. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & SB2 & DOCC2 & _).

    astep. astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
    change (S o + 2 ^ 8 * S (o + 1) + 2 ^ 16 * S (o + 2) + 2 ^ 24 * S (o + 3)) with (le32 S o). rewrite LE.
    step.
    destruct (sbuf_slice m2 (pe_SBUF D) (pe_sbs D) o l SB2 ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
    eapply (put_call pjolits pjolits32 D DOK PUT); [exact DI2| exact QB| exact QL| lia| lia| lia| left; lia|].
    clear MU WM QB QL TB2 SB2 DOCC2. intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 DI3. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    pose proof DI3 as (_ & _ & _ & _ & _ & _ & MI3 & _).

    step. step. step.
    lit_at 0x13205 3%nat m3 MI3 LIT LITL.
    eapply (put_call pjolits pjolits32 D DOK PUT); [exact DI3| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m4 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI4. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl psegs m4) as WM.

    astep. step. step. step. step.
    eapply (pj_call pjolits pjolits32 D DOK d PJ); [exact DI4| exact FRM| exact EL| lia| lia| exact NEED|].
    clear MU WM. intros m5 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F5 fc5 DI5 FRM5. retlit.
    pose proof DI5 as (_ & _ & _ & _ & _ & _ & MI5 & _ & (scr5 & FR5) & TB5 & _ & DOCC5 & _). unfold pjolits, pjsaves, DMP_LIT_RBRACE in FR5. cbn [app] in FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl psegs m5) as WM.
    pose proof (tape_read m5 (pe_TAPE D) (pe_tws D) (it + 1) TB5 ltac:(lia)) as RDT.

    destruct (elem_cases _ _ _ _ _ _ EL) as [[-> TY]|[[-> TY]|[[-> STRV]|(d' & e' & c' & cv' & Hd & -> & CV' & CO)]]].
    -
      assert (TIR : 0 <= T (it + 1) < 2^64) by (destruct TY as [E'|[E'|E']]; rewrite E'; unfold tword, t_true, t_false, t_null; lia).

      step. astep. astep. step. astep.
      destruct TY as [E'|[E'|E']]; rewrite E', ttype_tword by lia; unfold t_true, t_false, t_null; astep;

        (step; step; if_false; step; astep; astep; step; if_true; step; astep; astep; step; if_true; astep; step);
        (if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia;
         [ unfold KOLOOP, OLS, DMP_PJ_OBJ_LOOP, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL; eapply evt_eq; [| eapply HL; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq
         | unfold KOEND in HE; eapply evt_eq; [| eapply HE; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq ]).
    -
      assert (TIR : 0 <= T (it + 1) < 2^64) by (destruct TY as [E'|[E'|E']]; rewrite E'; unfold tword, t_i64, t_u64, t_dbl; lia).
      step. astep. astep. step. astep.
      destruct TY as [E'|[E'|E']]; rewrite E', ttype_tword by lia; unfold t_i64, t_u64, t_dbl; astep;
        (step; step; if_false; step; astep; astep; step; if_false; astep; step);
        (if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia;
         [ unfold KOLOOP, OLS, DMP_PJ_OBJ_LOOP, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL; eapply evt_eq; [| eapply HL; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq
         | step; unfold KOEND in HE; eapply evt_eq; [| eapply HE; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq ]).
    -
      pose proof (key_word_range _ _ _ _ STRV SNR) as (TIR & _ & KT').
      step. astep. astep. step. astep. rewrite KT'. unfold t_str. astep.
      step. step. if_true. astep. step.
      if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia;
         [ unfold KOLOOP, OLS, DMP_PJ_OBJ_LOOP, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL; eapply evt_eq; [| eapply HL; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq
         | unfold KOEND in HE; eapply evt_eq; [| eapply HE; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq ].
    -
      assert (LT' : it + 1 < e').
      { destruct CO as [(_ & _ & HT')|(_ & _ & HT')].
        - pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ HT'). lia.
        - pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ HT'). lia. }
      unfold CNT_MAX in CV'.
      destruct CO as [(E' & _ & _)|(E' & _ & _)];
        (assert (TIR : 0 <= T (it + 1) < 2^64) by (rewrite E'; unfold cword, tword, t_arr, t_obj; lia));
        step; astep; astep; step; astep; rewrite E', ttype_cword by (unfold CNT_MAX; lia); unfold t_arr, t_obj; astep;
        (step; step; if_false; step; astep; astep; step; if_true; step; astep; astep; step; if_false; step; astep);
        [rewrite (low32_cword 91) by (unfold CNT_MAX; lia)| rewrite (low32_cword 123) by (unfold CNT_MAX; lia)]; step;
        (if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia;
         [ unfold KOLOOP, OLS, DMP_PJ_OBJ_LOOP, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL; eapply evt_eq; [| eapply HL; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq
         | step; unfold KOEND in HE; eapply evt_eq; [| eapply HE; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq ]).
  Qed.

  Lemma pj_obj_loop : forall (K : machine_state -> Prop) (gp : word) (e c it : Z),
    tiles (field T S sn (elem T S sn ck_any d)) it e c -> it <> e -> 0 <= it -> e + 1 <= n -> pe_lo D + pj_need d <= dsp D ->
    KOEND K gp -> KOLOOP K gp e it.
  Proof.
    intros K gp e c it HT. induction HT as [it0|it0 j0 e0 c0 FEL HT' IH]; intros NE I0 EN NEED HE; [congruence|].
    destruct FEL as [STRI EL].
    unfold KOLOOP. intros until fc'. intros DI FRM.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ HT') as [JE _].
    eapply pj_obj_step; [exact DI| exact FRM| exact STRI| exact EL| exact I0| exact JE| exact EN| exact NEED| | intros _; exact HE].
    intros NJ. eapply IH; [exact NJ| lia| exact EN| exact NEED| exact HE].
  Qed.
End Body.

Theorem pj_obj_proof : forall d, pj_obj_case d.
Proof.
  intros d. unfold pj_obj_case. intros until cv. intros DOK PUT IB IL IUL INSD PJ DI FRM I0 IE EN CV E EE HT NEED [HKJ HKO].
  assert (NEEDd : pe_lo D + pj_need d <= dsp D) by (rewrite pj_need_S in NEED; unfold DMP_PJ_FRAME in NEED; lia).
  eapply (pj_obj_head D DOK PUT j32); [exact DI| exact FRM| exact I0| exact IE| exact EN| exact CV| exact E| exact HKJ|].
  intros NE. eapply (pj_obj_loop D DOK PUT d PJ); [exact HT| exact NE| lia| exact EN| exact NEEDd| apply (pj_obj_end D DOK PUT); exact HKO].
Qed.
End WithCeiling0.
