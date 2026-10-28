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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Atp_objl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_h_defs Pj_loc_defs Pj_os_defs El_os_defs El_ins_iface El_esc_iface El_defs El_dump_iface El_dump_kit El_dump_body1.
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

Ltac reg_as_unsigned k :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
    lazymatch v with Some ?t => rewrite <- (Z_to_bv_bv_unsigned t) end end.

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
  Hypothesis ESC : esc_stmt.

  Notation n := (Z.of_nat (length (de_tws D))).
  Notation T := (Tf (de_tws D)).
  Notation S := (Tf (de_sbs D)).
  Notation sn := (Z.of_nat (length (de_sbs D))).

  Ltac open_frame DI FR scr := let X := fresh in pose proof DI as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & (scr & FR) & _); unfold dlits, dsaves in FR; cbn [app] in FR.

  Lemma dump_open_tail : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (LIT : Z),
    DINV (dlits j0) D m -> frm0 fc -> 1 <= i -> i + 1 < n -> 0 <= T i < 2^64 -> (LIT = 0x13a08 \/ LIT = 0x131ba) ->
    KLOOP D j0 K gp (i + 1) ->
    evt usegs K (LST D 0x40194 i x1 gp x5 x6 x7 x10 (Z_to_bv 64 LIT) x12 x13 x14 x15 x16 x17 x21 (Z_to_bv 64 (T i)) x28 x29 x30 x31 F fc m).
  Proof.
    intros until LIT. intros DI FRM I1 IN TIR HL HK. unfold LST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. step.
    assert (LB36 : exists bs, bytes_at usegs m LIT bs /\ Z.of_nat (length bs) = 36).
    { destruct HL as [-> | ->]; [lit_at 0x13a08 36%nat m MI L1 L1L; exists (lit 0x13a08 36); auto| lit_at 0x131ba 36%nat m MI L1 L1L; exists (lit 0x131ba 36); auto]. }
    destruct LB36 as (bs36 & B36 & L36).
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI| exact B36| exact L36| lia| lia| lia| left; lia|].
    intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    clear MU WM B36. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.

    step. step.
    reg_as_unsigned 11.
    eapply (ins_call (dlits j0) (dlits72 j0) D DOK EL_INS_U _ IU); [exact DI2| exact FRM| cbv beta; apply (bv_unsigned_in_range 64)|].
    intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 DI3 FRM3. retlit.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof DI3 as (_ & _ & _ & _ & _ & MI3 & _).

    step. step. step. step.
    lit_at 0x120c9 31%nat m3 MI3 L2 L2L.
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI3| exact L2| exact L2L| lia| lia| lia| left; lia|].
    intros m4 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI4. retlit.
    clear MU WM L2 L2L. pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    pose proof DI4 as (_ & _ & _ & _ & _ & MI4 & _).

    step. step. step. step.
    lit_at 0x129f7 17%nat m4 MI4 L3 L3L.
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI4| exact L3| exact L3L| lia| lia| lia| left; lia|].
    intros m5 z0 z1 z2 f1 f2 f3 f4 f5 f6 f7 z3 z4 z5 z6 DI5. retlit.
    clear MU WM L3 L3L. pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.

    step. step. step.
    reg_as_unsigned 11.
    eapply (ins_call (dlits j0) (dlits72 j0) D DOK EL_INS_UL _ IUL); [exact DI5| exact FRM3| cbv beta; apply (bv_unsigned_in_range 64)|].
    intros m6 k0 k1 k2 g1 g2 g3 g4 g5 g6 g7 k3 k4 k5 k6 F6 fc6 DI6 FRM6. retlit.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    pose proof DI6 as (_ & _ & _ & _ & _ & MI6 & _).

    step. step. step. step.
    lit_at 0x12863 1%nat m6 MI6 L4 L4L.
    eapply dump_putjoin; [exact DOK| exact PUT| exact DI6| exact FRM6| lia| exact IN| exact L4| exact L4L| lia| lia| lia| left; lia| exact HK].
  Qed.

  Lemma dump_open : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV (dlits j0) D m -> frm0 fc -> 1 <= i -> i + 1 < n -> 0 <= T i < 2^64 -> (ttype (T i) = t_obj \/ ttype (T i) = t_arr) ->
    KLOOP D j0 K gp (i + 1) ->
    evt usegs K (DST D i x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM I1 IN TIR TY HK. unfold DST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    open_frame DI FR scr.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct TY as [TY|TY]; rewrite TY; unfold t_obj, t_arr.
    -
      step. if_true. step. if_true. step. step. if_false. step. step. step. if_true.
      eapply dump_open_tail; [exact DI| exact FRM| exact I1| exact IN| exact TIR| left; reflexivity| exact HK].
    -
      step. if_false. step. if_false. astep. step. step. if_false. step. step. if_false. step. step. if_false. step. step.
      eapply dump_open_tail; [exact DI| exact FRM| exact I1| exact IN| exact TIR| right; reflexivity| exact HK].
  Qed.

  Lemma dump_close : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV (dlits j0) D m -> frm0 fc -> 1 <= i -> i + 1 < n -> 0 <= T i < 2^64 -> (ttype (T i) = t_obj_end \/ ttype (T i) = t_arr_end) ->
    KLOOP D j0 K gp (i + 1) ->
    evt usegs K (DST D i x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM I1 IN TIR TY HK. unfold DST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). open_frame DI FR scr.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (TAIL : forall (LIT : Z) (y1 y12 : word), (LIT = 0x11272 \/ LIT = 0x104d1) ->
      evt usegs K (LST D 0x403bc i y1 gp x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 LIT) y12 (Z_to_bv 64 (ttype (T i))) x14 x15 x16 x17 x21 (Z_to_bv 64 (T i)) x28 x29 x30 x31 F fc m)).
    { intros LIT y1 y12 HL. unfold LST.
      assert (LB40 : exists bs, bytes_at usegs m LIT bs /\ Z.of_nat (length bs) = 40).
      { destruct HL as [-> | ->]; [lit_at 0x11272 40%nat m MI L1 L1L; exists (lit 0x11272 40); auto| lit_at 0x104d1 40%nat m MI L1 L1L; exists (lit 0x104d1 40); auto]. }
      destruct LB40 as (bs40 & B40 & L40).

      step. step. step.
      eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI| exact B40| exact L40| lia| lia| lia| left; lia|].
      intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
      clear MU WM B40. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.

      step. step.
      reg_as_unsigned 11.
      eapply (ins_call (dlits j0) (dlits72 j0) D DOK EL_INS_U _ IU); [exact DI2| exact FRM| cbv beta; apply (bv_unsigned_in_range 64)|].
      intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 DI3 FRM3. retlit.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      pose proof DI3 as (_ & _ & _ & _ & _ & MI3 & _).

      step. step. step.
      lit_at 0x1183e 22%nat m3 MI3 L2 L2L.
      eapply dump_putjoin; [exact DOK| exact PUT| exact DI3| exact FRM3| lia| exact IN| exact L2| exact L2L| lia| lia| lia| left; lia| exact HK]. }
    destruct TY as [TY|TY]; rewrite TY; unfold t_obj_end, t_arr_end.
    -
      step. if_true. step. if_true. step. step. if_false. step. step. step. if_false. step. step. step. if_false. step.
      rewrite TY in TAIL. unfold t_obj_end, t_arr_end in TAIL. apply TAIL. left; reflexivity.
    -
      step. if_false. step. if_true. step. step. if_true. step.
      rewrite TY in TAIL. unfold t_obj_end, t_arr_end in TAIL. apply TAIL. right; reflexivity.
  Qed.

  Lemma sbuf_slice : forall m (SBUF : Z) (sbs : list Z) (o l : Z),
    bytes_at usegs m SBUF (map (Z_to_bv 8) sbs) -> 0 <= o -> 0 <= l -> o + 4 + l < Z.of_nat (length sbs) ->
    bytes_at usegs m (SBUF + o + 4) (firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) sbs)))
    /\ Z.of_nat (length (firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) sbs)))) = l.
  Proof.
    intros m SBUF sbs o l HB Ho Hl Hol. split.
    - replace (SBUF + o + 4) with (SBUF + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
    - rewrite firstn_length_le; [lia|]. rewrite length_skipn, length_map. lia.
  Qed.

  Lemma dump_putc : forall (K : machine_state -> Prop) (RA : Z) (gp t0 t1 t2 a3 a4 a5 a6 a7 x19 x21 x24 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (c : Z) (cs15 : list cell),
    DINV (dlits j0) D m0 -> munch [(dsp D + 72, dsp D + 88)] m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
    rw_cells usegs m (dsp D) (dlits j0 ++ (C1 (Z_to_bv 8 c) :: cs15) ++ dsaves (de_ra D) (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D) (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D)) ->
    cells_size cs15 = 15%nat -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), DINV (dlits j0) D m' ->
       evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 (de_DOC D)) (Z_to_bv 64 (de_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          (Z_to_bv 64 n) x19 (Z_to_bv 64 0x10c45) x21 (Z_to_bv 64 116) (Z_to_bv 64 0x13a08) x24 (Z_to_bv 64 72057594037927935) (Z_to_bv 64 107) (Z_to_bv 64 92) u3 u4 u5 u6)
                    F (Z_to_bv 64 RA) fc None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 (de_DOC D)) (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 (dsp D + 72)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                       (Z_to_bv 64 n) x19 (Z_to_bv 64 0x10c45) x21 (Z_to_bv 64 116) (Z_to_bv 64 0x13a08) x24 (Z_to_bv 64 72057594037927935) (Z_to_bv 64 107) (Z_to_bv 64 92) t3 t4 t5 t6)
                    F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom usegs)).
  Proof.
    intros until cs15. intros DI0 MU WM MI FR SZ RAH RAE HK.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof (DINV_rescratch (dlits j0) (dlits72 j0) D m0 m (C1 (Z_to_bv 8 c) :: cs15) DOK DI0 MU WM MI ltac:(cbn [cells_size csize]; rewrite SZ; reflexivity) FR) as DI.
    pose proof (frame_scratch (dlits j0) (dlits72 j0) D m (C1 (Z_to_bv 8 c) :: cs15) ltac:(cbn [cells_size csize]; rewrite SZ; reflexivity) FR) as SCR.
    destruct (proj1 (rw_cells_app _ _ [_] _) SCR) as [[[_ B1] _] _]. cbn [cells_bytes cbytes app] in B1.
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT) with (bs := [Z_to_bv 8 c]) (CAP := 1); [exact DI| exact B1| reflexivity| lia| lia| lia| right; right; lia|].
    intros m5 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI5.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RAH| exact RAE]).
    apply HK. exact DI5.
  Qed.

  Lemma dump_str : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV (dlits j0) D m -> frm0 fc -> 1 <= i -> i + 1 < n -> is_str T S sn i ->
    KLOOP D j0 K gp (i + 1) ->
    evt usegs K (DST D i x1 gp x5 x6 x7 x11 x12 x14 x15 x16 x17 x21 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM I1 IN STR HK. unfold DST.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof WF as (NR & SNR & _).
    assert (HSN : sn < 2^56) by lia.
    pose proof (key_word_range _ _ _ _ STR HSN) as (KWR & KM & KT).
    destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
    set (o := tval (T i)) in *.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _ & _ & TB & SB & DOCC & _). open_frame DI FR scr.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    rewrite KT. unfold t_str.

    step. if_false. step. if_false. astep. rewrite KM. step. step. if_true.
    step. step. step. step.
    lit_at 0x12dc8 8%nat m MI L1 L1L.
    eapply (put_call (dlits j0) (dlits72 j0) D DOK PUT); [exact DI| exact L1| exact L1L| lia| lia| lia| left; lia|].
    intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    clear MU WM L1 L1L FR TB SB DOCC MI. pose proof (munch_refl [(dsp D + 72, dsp D + 88)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & SB2 & DOCC2 & _). open_frame DI2 FR2 scr2.
    apply (rw_cells_split_CB usegs _ _ [_; _; _; _; _; _; _; _; _] 16 scr2 _ [8; 8]%nat) in FR2; [| reflexivity]. cbn [mk_CB_cells app] in FR2.

    pose proof (sbuf_read1 m2 (de_SBUF D) (de_sbs D) o SB2 ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m2 (de_SBUF D) (de_sbs D) (o + 1) SB2 ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m2 (de_SBUF D) (de_sbs D) (o + 2) SB2 ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m2 (de_SBUF D) (de_sbs D) (o + 3) SB2 ltac:(lia)) as RB3.
    assert (B0 : 0 <= S o < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B1 : 0 <= S (o + 1) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B2 : 0 <= S (o + 2) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B3 : 0 <= S (o + 3) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).

    step. astep. replace (o + de_SBUF D) with (de_SBUF D + o) by lia.

    step. if_lia. astep. astep. astep.
    replace (0 <? de_SBUF D) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (de_SBUF D + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
    step. if_false. step. if_lia. step. step. if_lia.

    astep. astep. astep. astep. astep. astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
    change (S o + 2 ^ 8 * S (o + 1) + 2 ^ 16 * S (o + 2) + 2 ^ 24 * S (o + 3)) with (le32 S o). rewrite LE.
    destruct (sbuf_slice m2 (de_SBUF D) (de_sbs D) o l SB2 ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL]. hide QB. clear TB2 SB2 DOCC2.

    hstep. hstep. step. step. step. unhide QB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv usegs mx |- _ =>
        pose proof (DINV_rescratch (dlits j0) (dlits72 j0) D m2 mx [C8 (Z_to_bv 64 (de_SBUF D + o + 4)); C8 (Z_to_bv 64 l)] DOK DI2 MU WM MIx eq_refl FR2) as DI3;
        pose proof (frame_scratch (dlits j0) (dlits72 j0) D mx [C8 (Z_to_bv 64 (de_SBUF D + o + 4)); C8 (Z_to_bv 64 l)] eq_refl FR2) as SV;
        apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in QB; [| rewrite QL by lia; intros a Ha; cbn [outside]; lia] end end.
    eapply (esc_call (dlits j0) (dlits72 j0) D DOK ESC); [exact DI3| exact FRM| exact SV| exact QB| exact QL| lia| lia| clear - SI SH O0 L0 OL; lia|].
    intros m4 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F4 fc4 DI4 FRM4. retlit.
    clear MU WM RB0 RB1 RB2 RB3 QB SV FR2.

    pose proof (munch_refl [(dsp D + 72, dsp D + 88)]%Z m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    pose proof DI4 as (_ & _ & _ & _ & _ & MI4 & _). open_frame DI4 FR4 scr4.
    apply (rw_cells_split_CB usegs _ _ [_; _; _; _; _; _; _; _; _] 16 scr4 _ [1; 15]%nat) in FR4; [| reflexivity]. cbn [mk_CB_cells app] in FR4.
    step. hstep. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv usegs mx |- _ =>
      eapply (dump_putc K 0x40350) with (m0 := m4) (cs15 := [CB 15 (take 15 (drop 1 scr4))]);
        [exact DI4| exact MU| exact WM| exact MIx| exact FR4| reflexivity| lia| reflexivity|] end end.
    intros m5 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI5.
    clear MU WM FR4. pose proof (munch_refl [(dsp D + 72, dsp D + 88)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    pose proof DI5 as (_ & _ & _ & _ & _ & MI5 & _). open_frame DI5 FR5 scr5.
    apply (rw_cells_split_CB usegs _ _ [_; _; _; _; _; _; _; _; _] 16 scr5 _ [1; 15]%nat) in FR5; [| reflexivity]. cbn [mk_CB_cells app] in FR5.

    step. hstep. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv usegs mx |- _ =>
      eapply (dump_putc K 0x40368) with (m0 := m5) (cs15 := [CB 15 (take 15 (drop 1 scr5))]);
        [exact DI5| exact MU| exact WM| exact MIx| exact FR5| reflexivity| lia| reflexivity|] end end.
    intros m6 z0 z1 z2 f1 f2 f3 f4 f5 f6 f7 z3 z4 z5 z6 DI6.
    clear MU WM FR5. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.

    step. eapply dump_join; [exact DOK| exact DI6| exact FRM4| lia| exact IN| exact HK].
  Qed.
End Body.
End WithCeiling0.
