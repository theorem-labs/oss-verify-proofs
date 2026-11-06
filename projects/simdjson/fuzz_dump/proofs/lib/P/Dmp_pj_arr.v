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
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_objl Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_defs Dmp_defs Dmp_pj_iface Dmp_pj_kit Dmp_pj_leaf Dmp_pj.
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

Lemma mask_all : forall x, 0 <= x < 2^64 -> Z.land (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) x = x.
Proof. intros x Hx. change (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma low32_cword : forall t nxt cv, 0 <= t < 256 -> 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX ->
  Z.land (Z.land (cword t nxt cv) 18446744073709551615) 4294967295 = nxt.
Proof.
  intros t nxt cv Ht Hn Hc. assert (R : 0 <= cword t nxt cv < 2^64) by (unfold cword, tword, CNT_MAX in *; lia).
  change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32).
  rewrite !Z.land_ones by lia. rewrite (Z.mod_small _ (2^64)) by lia.
  pose proof (tnext_cword t nxt cv Hn) as E. unfold tnext in E. exact E.
Qed.
Lemma low32_cword' : forall t nxt cv, 0 <= t < 256 -> 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX ->
  Z.land (cword t nxt cv) 4294967295 = nxt.
Proof.
  intros t nxt cv Ht Hn Hc. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by (unfold cword, tword, CNT_MAX in *; lia).
  pose proof (tnext_cword t nxt cv Hn) as E. unfold tnext in E. exact E.
Qed.

Section Body.
  Variable D : pjenv.
  Hypothesis DOK : pjenv_ok D.
  Hypothesis PUT : os_putX_stmt.
  Variable d : nat.
  Hypothesis PJ : pj_stmt d.
  Variable j32 : list byte.
  Notation lc := [CB 32 j32].
  Notation LCS := (junk32 j32).
  Notation n := (pe_n D).
  Notation T := (Tf (pe_tws D)).
  Notation S := (Tf (pe_sbs D)).
  Notation sn := (pe_sn D).

  Definition ALS (e it : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 e) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (pe_DOC D)) (Z_to_bv 64 it) (Z_to_bv 64 DMP_LIT_COMMA) (Z_to_bv 64 32) (Z_to_bv 64 4294967295) (Z_to_bv 64 0x4020200) (Z_to_bv 64 0x100000001)
            (Z_to_bv 64 DMP_LIT_RBRACK) x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 DMP_PJ_ARR_LOOP) fc None m (seg_rom psegs).

  Definition KCLOSE (K : machine_state -> Prop) (gp : word) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      PINV lc D m' -> frm0 fc' ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           (Z_to_bv 64 DMP_LIT_RBRACK) x26 x27 x28 x29 x30 x31) F' (Z_to_bv 64 DMP_PJ_CLOSE) fc' None m' (seg_rom psegs)).
  Definition KLOOP (K : machine_state -> Prop) (gp : word) (e it : Z) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      PINV lc D m' -> frm0 fc' -> evt psegs K (ALS e it x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 F' fc' m').

  Lemma pj_arr_close : forall (K : machine_state -> Prop) (gp : word), KEXIT D lc K gp -> KCLOSE K gp.
  Proof.
    intros K gp HK. unfold KCLOSE. intros until fc'. intros DI FRM. unfold DMP_PJ_CLOSE, DMP_LIT_RBRACK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _).
    pose proof (munch_refl ([] : list (Z * Z)) m') as MU. pose proof (wmono_refl psegs m') as WM.

    step. step. step. step.
    lit_at 0x12082 1%nat m' MI LIT LITL.
    eapply (put_call lc LCS D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    unfold KEXIT, DMP_PJ_EXIT in HK. eapply HK; [exact DI2| exact FRM].
  Qed.

  Lemma pj_arr_head : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (i e cv : Z),
    PINV lc D m -> frm0 fc -> 0 <= i -> i < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX -> T i = cword t_arr (e + 1) cv ->
    KCLOSE K gp -> (i + 1 <> e -> KLOOP K gp e (i + 1)) ->
    evt psegs K (DST D i t_arr x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until cv. intros DI FRM I0 IE EN CV E HC HL. unfold DST, DMP_PJ_DISPATCH, t_arr.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, CNT_MAX in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & SB & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    assert (TIR : 0 <= T i < 2^64) by (rewrite E; unfold cword, tword, t_arr, CNT_MAX in *; lia).

    step. step. if_true. step. step. if_true. step. step. if_true.

    step. step. step. step. step.
    lit_at 0x1117a 1%nat m MI LIT LITL.
    eapply (put_call lc LCS D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & SB2 & DOCC2 & _).
    pose proof (tape_read_type m2 (pe_TAPE D) (pe_tws D) i TB2 ltac:(lia) TIR) as RTY.
    pose proof (tape_read m2 (pe_TAPE D) (pe_tws D) i TB2 ltac:(lia)) as RDT.
    rewrite E in RTY. rewrite ttype_cword in RTY by (unfold CNT_MAX; lia). unfold t_arr in RTY.

    step. astep. astep. astep. astep. astep. astep. rewrite mask_all by lia.

    step. astep. rewrite mask_all by lia. astep. astep. step. astep. astep. rewrite E, ttype_cword by (unfold CNT_MAX; lia). unfold t_arr. astep. step. step. step. if_false.

    astep. astep. astep. astep. step. if_true.

    step. astep. astep. astep. astep. step. step. if_false. astep. astep. rewrite low32_cword by (unfold CNT_MAX; lia). astep.
    replace (e + 1 + -1) with e by lia. step. step. step.
    if_cases KE; zify_cond KE.
    -
      unfold KCLOSE, DMP_PJ_CLOSE, DMP_LIT_RBRACK in HC. eapply HC; [exact DI2| exact FRM].
    -
      step. step. step. step. step. astep. step. astep. astep. astep.
      unfold KLOOP, ALS, DMP_PJ_ARR_LOOP, DMP_LIT_COMMA, DMP_LIT_RBRACK in HL.
      eapply evt_eq; [| eapply HL; [rewrite ?unsigned_lit in KE by lia; lia| exact DI2| exact FRM]]. cbn. atp_st_eq.
  Qed.

  Definition ATS (e j : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 e) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (pe_DOC D)) (Z_to_bv 64 j) (Z_to_bv 64 DMP_LIT_COMMA) (Z_to_bv 64 32) (Z_to_bv 64 4294967295) (Z_to_bv 64 0x4020200) (Z_to_bv 64 0x100000001)
            (Z_to_bv 64 DMP_LIT_RBRACK) x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x3ada4) fc None m (seg_rom psegs).

  Lemma pj_arr_step : forall (K : machine_state -> Prop) (e it j : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> frm0 fc -> elem T S sn ck_any d it j -> 0 <= it -> j <= e -> e + 1 <= n -> pe_lo D + pj_need d <= dsp D ->
    (forall (m' : mem) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y26 y27 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32),
        PINV lc D m' -> frm0 fc' -> evt psegs K (ATS e j y1 gp y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y26 y27 y28 y29 y30 y31 F' fc' m')) ->
    evt psegs K (ALS e it x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM EL I0 JE EN NEED HK. unfold ALS, DMP_PJ_ARR_LOOP, DMP_LIT_COMMA, DMP_LIT_RBRACK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, CNT_MAX in *.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.

    step. step. step. step.
    eapply (pj_call lc LCS D DOK d PJ); [exact DI| exact FRM| exact EL| exact I0| lia| exact NEED|].
    clear MU WM. intros m1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 DI1 FRM1. retlit.
    pose proof DI1 as (_ & _ & _ & _ & _ & _ & MI1 & _).
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl psegs m1) as WM.

    step. step. step. step.
    lit_at 0x1117c 1%nat m1 MI1 LIT LITL.
    eapply (put_call lc LCS D DOK PUT); [exact DI1| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & SB2 & DOCC2 & _).
    pose proof (tape_read m2 (pe_TAPE D) (pe_tws D) it TB2 ltac:(lia)) as RDT.

    destruct (elem_cases _ _ _ _ _ _ EL) as [[-> TY]|[[-> TY]|[[-> STRI]|(d' & e' & c' & cv' & Hd & -> & CV' & CO)]]].
    -
      assert (TIR : 0 <= T it < 2^64) by (destruct TY as [E'|[E'|E']]; rewrite E'; unfold tword, t_true, t_false, t_null; lia).

      step. astep. astep. step. astep.
      destruct TY as [E'|[E'|E']]; rewrite E', ttype_tword by lia; unfold t_true, t_false, t_null; astep;

        (step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep);
        (eapply HK; [exact DI2| exact FRM1]).
    -
      assert (TIR : 0 <= T it < 2^64) by (destruct TY as [E'|[E'|E']]; rewrite E'; unfold tword, t_i64, t_u64, t_dbl; lia).
      step. astep. astep. step. astep.
      destruct TY as [E'|[E'|E']]; rewrite E', ttype_tword by lia; unfold t_i64, t_u64, t_dbl; astep;

        (step; if_false; astep; astep; step; if_false; astep; step);
        (eapply HK; [exact DI2| exact FRM1]).
    -
      pose proof (key_word_range _ _ _ _ STRI SNR) as (TIR & _ & KT).
      step. astep. astep. step. astep. rewrite KT. unfold t_str. astep.
      step. if_true. astep.
      eapply HK; [exact DI2| exact FRM1].
    -
      assert (LT' : it < e').
      { destruct CO as [(_ & _ & HT')|(_ & _ & HT')].
        - pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ HT'). lia.
        - pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ HT'). lia. }
      unfold CNT_MAX in CV'.
      destruct CO as [(E' & _ & _)|(E' & _ & _)];
        (assert (TIR : 0 <= T it < 2^64) by (rewrite E'; unfold cword, tword, t_arr, t_obj; lia));
        step; astep; astep; step; astep; rewrite E', ttype_cword by (unfold CNT_MAX; lia); unfold t_arr, t_obj; astep;

        (step; if_false; astep; astep; step; if_true; astep; astep; step; if_false; astep);
        [rewrite (low32_cword 91) by (unfold CNT_MAX; lia)| rewrite (low32_cword 123) by (unfold CNT_MAX; lia)]; step;
        (eapply HK; [exact DI2| exact FRM1]).
  Qed.

  Lemma pj_arr_loop : forall (K : machine_state -> Prop) (gp : word) (e c it : Z),
    tiles (elem T S sn ck_any d) it e c -> it <> e -> 0 <= it -> e + 1 <= n -> pe_lo D + pj_need d <= dsp D ->
    KCLOSE K gp -> KLOOP K gp e it.
  Proof.
    intros K gp e c it HT. induction HT as [it0|it0 j0 e0 c0 EL HT' IH]; intros NE I0 EN NEED HC; [congruence|].
    unfold KLOOP. intros until fc'. intros DI FRM.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ HT') as [JE _].
    eapply pj_arr_step; [exact DI| exact FRM| exact EL| exact I0| exact JE| exact EN| exact NEED|].
    intros m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y26 y27 y28 y29 y30 y31 F2 fc2 DI2 FRM2. unfold ATS.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _).
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.

    step. if_cases KJ; zify_cond KJ.
    -
      rewrite ?unsigned_lit in KJ by lia.
      unfold KLOOP, ALS, DMP_PJ_ARR_LOOP, DMP_LIT_COMMA, DMP_LIT_RBRACK in IH.
      eapply IH; [lia| lia| exact EN| exact NEED| exact HC| exact DI2| exact FRM2].
    -
      step. unfold KCLOSE, DMP_PJ_CLOSE, DMP_LIT_RBRACK in HC. eapply HC; [exact DI2| exact FRM2].
  Qed.
End Body.

Theorem pj_arr_proof : forall d, pj_arr_case d.
Proof.
  intros d. unfold pj_arr_case. intros until cv. intros DOK PUT IB IL IUL INSD PJ DI FRM I0 IE EN CV E EE HT NEED HK.
  assert (NEEDd : pe_lo D + pj_need d <= dsp D) by (rewrite pj_need_S in NEED; unfold DMP_PJ_FRAME in NEED; lia).
  eapply (pj_arr_head D DOK PUT j32); [exact DI| exact FRM| exact I0| exact IE| exact EN| exact CV| exact E| apply (pj_arr_close D DOK PUT j32); exact HK|].
  intros NE. eapply (pj_arr_loop D DOK PUT d PJ j32); [exact HT| exact NE| lia| exact EN| exact NEEDd| apply (pj_arr_close D DOK PUT j32); exact HK].
Qed.
End WithCeiling0.
