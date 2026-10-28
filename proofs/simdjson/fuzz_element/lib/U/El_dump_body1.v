(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_h_defs Pj_loc_defs Pj_os_defs El_os_defs El_ins_iface El_defs El_dump_iface El_dump_kit.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
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
  Variable D : denv.
  Variable j0 : list byte.
  Hypothesis DOK : denv_ok D.
  Hypothesis PUT : os_putX_stmt.
  Hypothesis IUL : ins_ul_stmt.
  Hypothesis IU : ins_u_stmt.
  Hypothesis IL : ins_l_stmt.
  Hypothesis INSD : ins_d_stmt.

  Notation n := (Z.of_nat (length (de_tws D))).
  Notation T := (Tf (de_tws D)).

  Definition LST (pc i : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 (de_DOC D)) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 0x10c45) x21 (Z_to_bv 64 116) (Z_to_bv 64 0x13a08) x24 (Z_to_bv 64 72057594037927935)
            (Z_to_bv 64 107) (Z_to_bv 64 92) x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom usegs).

  Definition KLOOP (K : machine_state -> Prop) (gp : word) (j : Z) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      DINV (dlits j0) D m' -> frm0 fc' -> evt usegs K (LST 0x400c0 j x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F' fc' m').

  Lemma dump_head : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV (dlits j0) D m -> frm0 fc -> 1 <= i < n -> 0 <= T i < 2^64 ->
    (forall (m' : mem) (x1' x5' x6' x7' x11 x12 x14' x15' x16' x17' x21' x28' x29' x30' x31' : word) (F' : bvmap 5 word) (fc' : bv 32), DINV (dlits j0) D m' -> frm0 fc' ->
       evt usegs K (MS (mkR x1' (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5' x6' x7' (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 (de_DOC D))
                            (Z_to_bv 64 0) x11 x12 (Z_to_bv 64 (ttype (T i))) x14' x15' x16' x17'
                            (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 0x10c45) x21' (Z_to_bv 64 116) (Z_to_bv 64 0x13a08) (Z_to_bv 64 (T i)) (Z_to_bv 64 72057594037927935)
                            (Z_to_bv 64 107) (Z_to_bv 64 92) x28' x29' x30' x31') F' (Z_to_bv 64 0x400f0) fc' None m' (seg_rom usegs))) ->
    evt usegs K (LST 0x400c0 i x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM Hi TIR HK. unfold LST.
    assert (TTR : 0 <= ttype (T i) < 256) by (unfold ttype; lia).
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    destruct WF as (NR & SNR & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. step.
    eapply (ins_call (dlits j0) (dlits72 j0) D DOK EL_INS_UL _ IUL); [exact DI| exact FRM| cbv beta; lia|].
    intros m1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 DI1 FRM1. retlit.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    pose proof DI1 as (_ & _ & _ & _ & _ & MI1 & _).

    step. step. step.
    lit_at 0x10c45 3%nat m1 MI1 LIT LITL.
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI1| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    clear MU WM LIT LITL. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & _ & DOCC2 & _).
    pose proof (tape_read m2 (de_TAPE D) (de_tws D) i TB2 ltac:(lia)) as RDT.

    step. step. step.
    eapply (tix_call (dlits j0) (dlits72 j0) D DOK); [exact DI2| lia| lia| reflexivity|]. intros xa1 xa2 xa3 xa4.

    step. astep. step.
    eapply HK; [exact DI2| exact FRM1].
  Qed.

  Lemma dump_join : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV (dlits j0) D m -> frm0 fc -> 0 <= i -> i + 1 < n -> KLOOP K gp (i + 1) ->
    evt usegs K (LST 0x403e0 i x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM I0 IN HK. unfold LST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    destruct WF as (NR & SNR & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    astep. step. if_cases KB; zify_cond KB; [eapply HK; [exact DI| exact FRM]| exfalso; rewrite ?unsigned_lit in KB by lia; lia].
  Qed.

  Lemma dump_putjoin : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (BUF N CAP : Z) (bs : list byte),
    DINV (dlits j0) D m -> frm0 fc -> 0 <= i -> i + 1 < n ->
    bytes_at usegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> 0 < BUF -> BUF + CAP < 2 ^ 62 ->
    (BUF + CAP <= de_lo D \/ de_OS D + 288 <= BUF \/ (dsp D <= BUF /\ BUF + CAP <= de_OS D)) ->
    KLOOP K gp (i + 1) ->
    evt usegs K (LST 0x403dc i x1 gp x5 x6 x7 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 BUF) (Z_to_bv 64 N) x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc m).
  Proof.
    intros until bs. intros DI FRM I0 IN BB BL NR B0 BH LOC HK. unfold LST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    step.
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI| exact BB| exact BL| exact NR| exact B0| exact BH| exact LOC|].
    intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    eapply dump_join; [exact DI2| exact FRM| exact I0| exact IN| exact HK].
  Qed.

  Ltac open_frame DI FR scr := let X := fresh in pose proof DI as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & (scr & FR) & _); unfold dlits, dsaves in FR; cbn [app] in FR.

  Lemma dump_atom : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV (dlits j0) D m -> frm0 fc -> 1 <= i -> i + 1 < n ->
    (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0) ->
    KLOOP K gp (i + 1) ->
    evt usegs K (MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 (de_DOC D))
                         (Z_to_bv 64 0) x11 x12 (Z_to_bv 64 (ttype (T i))) x14 x15 x16 x17
                         (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 0x10c45) x21 (Z_to_bv 64 116) (Z_to_bv 64 0x13a08) (Z_to_bv 64 (T i)) (Z_to_bv 64 72057594037927935)
                         (Z_to_bv 64 107) (Z_to_bv 64 92) x28 x29 x30 x31) F (Z_to_bv 64 0x400f0) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros DI FRM I1 IN TY HK.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). open_frame DI FR scr.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct TY as [TY|[TY|TY]]; rewrite TY, ttype_tword by lia; unfold t_true, t_false, t_null.
    -
      step. if_true. step. if_false. step. step. if_false. step. step. step. if_false. step. if_false. step. step. step. step.
      lit_at 0x11478 5%nat m MI LIT LITL.
      eapply dump_putjoin; [exact DI| exact FRM| lia| exact IN| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK].
    -
      step. if_false. step. if_true. step. step. if_false. step. step. if_false. step. step. if_false. step. step. step. step.
      lit_at 0x1126b 6%nat m MI LIT LITL.
      eapply dump_putjoin; [exact DI| exact FRM| lia| exact IN| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK].
    -
      step. if_true. step. if_false. step. step. if_false. step. step. step. if_true. step. step. step.
      lit_at 0x12f42 5%nat m MI LIT LITL.
      eapply dump_putjoin; [exact DI| exact FRM| lia| exact IN| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK].
  Qed.

  Definition DST (i : Z) (x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 (de_DOC D))
            (Z_to_bv 64 0) x11 x12 (Z_to_bv 64 (ttype (T i))) x14 x15 x16 x17
            (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 0x10c45) x21 (Z_to_bv 64 116) (Z_to_bv 64 0x13a08) (Z_to_bv 64 (T i)) (Z_to_bv 64 72057594037927935)
            (Z_to_bv 64 107) (Z_to_bv 64 92) x28 x29 x30 x31) F (Z_to_bv 64 0x400f0) fc None m (seg_rom usegs).

  Lemma dump_nl_join : forall (pc : Z) (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    (pc = 0x403a4 \/ pc = 0x40424) -> DINV (dlits j0) D m -> frm0 fc -> 0 <= i -> i + 1 < n -> KLOOP K gp (i + 1) ->
    evt usegs K (LST pc i x1 gp x5 x6 x7 (Z_to_bv 64 (de_OS D + 128)) x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros PC DI FRM I0 IN HK. unfold LST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    lit_at 0x12863 1%nat m MI LIT LITL.
    destruct PC as [-> | ->]; (step; step; step; step;
      eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|];
      intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2; retlit;
      clear MU WM; pose proof (munch_refl ([] : list (Z * Z)) m2) as MU; pose proof (wmono_refl usegs m2) as WM;
      step; eapply dump_join; [exact DI2| exact FRM| exact I0| exact IN| exact HK]).
  Qed.

  Lemma dump_num_ul : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV (dlits j0) D m -> frm0 fc -> 1 <= i -> i + 2 < n -> (T i = tword t_u64 0 \/ T i = tword t_i64 0) ->
    KLOOP K gp (i + 2) ->
    evt usegs K (DST i x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM I1 IN TY HK. unfold DST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    destruct WF as (NR & SNR & _).
    pose proof DI as (_ & _ & _ & _ & _ & MI & _ & _ & TB & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct TY as [TY|TY]; rewrite TY, ttype_tword by lia; unfold t_u64, t_i64.
    -
      step. if_true. step. if_true. step. step. if_true.
      astep. step. if_cases KG; zify_cond KG; [exfalso; rewrite ?unsigned_lit in KG by lia; lia|].
      step. step. step. step. step.
      lit_at 0x129e5 17%nat m MI LIT LITL.
      eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
      intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
      clear MU WM LIT LITL. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof DI2 as (_ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & _ & DOCC2 & _).
      pose proof (tape_read m2 (de_TAPE D) (de_tws D) (i + 1) TB2 ltac:(lia)) as RDT.

      step. step. step. step.
      eapply (tix_call (dlits j0) (dlits72 j0) D DOK); [exact DI2| lia| lia| reflexivity|]. intros xa1 xa2 xa3 xa4.
      step. step. step.
      replace (Z_to_bv 64 (T (i + 1))) with (Z_to_bv 64 ((T (i + 1)) mod 2 ^ 64)) by (apply Z_to_bv64_eqm; rewrite Z.mod_mod by lia; reflexivity).
      eapply (ins_call (dlits j0) (dlits72 j0) D DOK EL_INS_UL _ IUL); [exact DI2| exact FRM| cbv beta; apply Z.mod_pos_bound; lia|].
      intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 DI3 FRM3. retlit.
      eapply (dump_nl_join 0x40424); [right; reflexivity| exact DI3| exact FRM3| lia| lia| replace (i + 1 + 1) with (i + 2) by lia; exact HK].
    -
      step. if_true. step. if_false. step. step. if_true.
      astep. step. if_cases KG; zify_cond KG; [exfalso; rewrite ?unsigned_lit in KG by lia; lia|].
      step. step. step. step. step.
      lit_at 0x131b1 8%nat m MI LIT LITL.
      eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
      intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
      clear MU WM LIT LITL. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof DI2 as (_ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & _ & DOCC2 & _).
      pose proof (tape_read m2 (de_TAPE D) (de_tws D) (i + 1) TB2 ltac:(lia)) as RDT.

      step. step. step. step.
      eapply (tix_call (dlits j0) (dlits72 j0) D DOK); [exact DI2| lia| lia| reflexivity|]. intros xa1 xa2 xa3 xa4.
      step. step. step.
      replace (Z_to_bv 64 (T (i + 1))) with (Z_to_bv 64 ((T (i + 1) + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63))
        by (apply Z_to_bv64_eqm; rewrite Zminus_mod_idemp_l; f_equal; lia).
      eapply (ins_call (dlits j0) (dlits72 j0) D DOK EL_INS_L _ IL); [exact DI2| exact FRM| cbv beta; pose proof (Z.mod_pos_bound (T (i + 1) + 2 ^ 63) (2 ^ 64) ltac:(lia)); lia|].
      intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 DI3 FRM3. retlit.
      eapply (dump_nl_join 0x403a4); [left; reflexivity| exact DI3| exact FRM3| lia| lia| replace (i + 1 + 1) with (i + 2) by lia; exact HK].
  Qed.

  Lemma dump_num_d : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV (dlits j0) D m -> frm0 fc -> 1 <= i -> i + 2 < n -> T i = tword t_dbl 0 ->
    KLOOP K gp (i + 2) ->
    evt usegs K (DST i x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM I1 IN TY HK. unfold DST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    destruct WF as (NR & SNR & _).
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). open_frame DI FR scr.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    rewrite TY, ttype_tword by lia; unfold t_dbl.

    step. if_false. step. if_true. step. step. if_false. step. step. if_true.
    step. step. step. step.
    lit_at 0x10ac6 6%nat m MI LIT LITL.
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    clear MU WM LIT LITL FR. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & _ & DOCC2 & _).

    astep. step. if_cases KG; zify_cond KG; [exfalso; rewrite ?unsigned_lit in KG by lia; lia|].
    pose proof (tape_read m2 (de_TAPE D) (de_tws D) (i + 1) TB2 ltac:(lia)) as RDT.

    step. step. step.
    eapply (tix_call (dlits j0) (dlits72 j0) D DOK); [exact DI2| lia| lia| reflexivity|]. intros xa1 xa2 xa3 xa4.
    step. step. step.
    eapply (insd_call (dlits j0) (dlits72 j0) D DOK INSD); [exact DI2| exact FRM|].
    intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 DI3 FRM3. retlit.
    clear MU WM RDT TB2 DOCC2. pose proof (munch_refl [(dsp D + 72, dsp D + 88)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof DI3 as (_ & _ & _ & _ & _ & MI3 & _). open_frame DI3 FR3 scr3.
    apply (rw_cells_split_CB usegs _ _ [_; _; _; _; _; _; _; _; _] 16 scr3 _ [1; 15]%nat) in FR3; [| reflexivity]. cbn [mk_CB_cells app] in FR3.

    step. hstep. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv usegs mx |- _ =>
        pose proof (DINV_rescratch (dlits j0) (dlits72 j0) D m3 mx [C1 (Z_to_bv 8 10); CB 15 (take 15 (drop 1 scr3))] DOK DI3 MU WM MIx eq_refl FR3) as DI4;
        pose proof (frame_scratch (dlits j0) (dlits72 j0) D mx [C1 (Z_to_bv 8 10); CB 15 (take 15 (drop 1 scr3))] eq_refl FR3) as SCR end end.
    destruct (proj1 (rw_cells_app _ _ [_] _) SCR) as [[[_ B1] _] _]. cbn [cells_bytes cbytes app] in B1.
    replace (Z_to_bv 64 (dsp D + 72)) with (Z_to_bv 64 (dsp D + 72)) by reflexivity.
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT) with (bs := [Z_to_bv 8 10]) (CAP := 1); [exact DI4| exact B1| reflexivity| lia| lia| lia| right; right; lia|].
    intros m5 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI5. retlit.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.

    step. eapply dump_join; [exact DI5| exact FRM3| lia| lia| replace (i + 1 + 1) with (i + 2) by lia; exact HK].
  Qed.
End Body.
End WithCeiling0.
