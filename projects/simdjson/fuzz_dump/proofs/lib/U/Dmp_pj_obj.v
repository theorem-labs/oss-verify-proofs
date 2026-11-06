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
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjDmp.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_h_arith Atp_objl.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_kitu Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_defs Dmp_defs Dmp_pj_iface Dmp_pj_kit Dmp_pj_leaf Dmp_pj Dmp_pj_arr.
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

Lemma land7_of_mod8 : forall A, 0 <= A -> A mod 8 = 0 -> Z.land A 7 = 0.
Proof. intros A H0 H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Definition pjolitsU : list cell :=
  [C8 (Z_to_bv 64 DMP_LIT_RBRACE); C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 0x100000001); C8 (Z_to_bv 64 0x4020200)].
Lemma pjolitsU32 : cells_size pjolitsU = 32%nat. Proof. reflexivity. Qed.
Lemma tval_str : forall o, 0 <= o < 2^56 -> Z.land (tword t_str o) 72057594037927935 = o.
Proof. intros o Ho. change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword, t_str; lia). unfold tword, t_str. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia. Qed.

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

  Ltac open_frame DI FR := let X := fresh in pose proof DI as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & (? & ? & ? & ? & FR) & _); unfold uframe, pjsaves, pjolitsU, DMP_LIT_RBRACE in FR; cbn [app] in FR.

  Definition OLS (e it : Z) (x1 gp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) x9 x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (pe_DOC D)) (Z_to_bv 64 it) (Z_to_bv 64 DMP_LIT_QUOTE) (Z_to_bv 64 DMP_LIT_QCOLON) x22 (Z_to_bv 64 e) x24 (Z_to_bv 64 72057594037927935)
            x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x3acdc) fc None m (seg_rom usegs).
  Definition KOLOOP (K : machine_state -> Prop) (gp : word) (e it : Z) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      PINV pjolitsU D m' -> frm0 fc' -> evt usegs K (OLS e it x1 gp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 F' fc' m').
  Definition KOEND (K : machine_state -> Prop) (gp : word) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      PINV pjolitsU D m' -> frm0 fc' ->
      evt usegs K (MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x25 x26 x27 x28 x29 x30 x31) F' (Z_to_bv 64 0x3ae0c) fc' None m' (seg_rom usegs)).

  Lemma pj_obj_end : forall (K : machine_state -> Prop) (gp : word), KEXIT D pjolitsU K gp -> KOEND K gp.
  Proof.
    intros K gp HK. unfold KOEND. intros until fc'. intros DI FRM.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _). open_frame DI FR.
    pose proof (munch_refl ([] : list (Z * Z)) m') as MU. pose proof (wmono_refl usegs m') as WM.

    step. step. step. step. step.
    lit_at 0x104d1 1%nat m' MI LIT LITL.
    eapply (put_call pjolitsU pjolitsU32 D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    unfold KEXIT, DMP_PJ_EXIT in HK. eapply HK; [exact DI2| exact FRM].
  Qed.

  Lemma pj_obj_head : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (e cv : Z),
    PINV lcj D m -> frm0 fc -> pe_i D < e -> e + 1 <= n -> 0 <= cv <= CNT_MAX -> T (pe_i D) = cword t_obj (e + 1) cv ->
    KEXIT D lcj K gp -> (pe_i D + 1 <> e -> KOLOOP K gp e (pe_i D + 1)) ->
    evt usegs K (DST D (pe_i D) t_obj x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until cv. intros DI FRM IE EN CV E HK HL. unfold DST, DMP_PJ_DISPATCH, t_obj.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, CNT_MAX in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (TIR : 0 <= T (pe_i D) < 2^64) by (rewrite E; unfold cword, tword, t_obj in *; lia).

    step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_false. step. step. step. step. step.
    lit_at 0x13072 1%nat m MI LIT LITL.
    eapply (put_call lcj LCJ D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & SB2 & DOCC2 & _).
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & _ & _ & (j0 & out & j56 & j80 & FR2) & _). unfold uframe, pjsaves in FR2. cbn [app] in FR2.
    pose proof (tape_read_type m2 (pe_TAPE D) (pe_tws D) (pe_i D) TB2 ltac:(lia) TIR) as RTY. rewrite E, ttype_cword in RTY by (unfold CNT_MAX; lia). unfold t_obj in RTY.
    pose proof (tape_read_lo32 D m2 (pe_i D) TB2 ltac:(lia)) as RD4.

    step. step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. rewrite (land7_of_mod8 (pe_DOC D) ltac:(lia) D8). step. if_false. step. step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3a8dc [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC2| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    step. step. step. if_false. astep. step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3a8f8 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC2| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.

    astep. astep. step. step. step. if_false. astep. astep. astep. astep. step. if_true.
    step. astep. astep. astep. astep. step. step. if_false. step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3ac88 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC2| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros za1 za2 za3 za4.

    step. rewrite zx32_tnext by lia. rewrite E, tnext_cword by lia. astep. replace (e + 1 + -1) with e by lia. step. step. step.
    if_cases KE; zify_cond KE.
    -
      step. step. step. step.
      lit_at 0x104d1 1%nat m2 MI2 LIT LITL.
      eapply (put_call lcj LCJ D DOK PUT); [exact DI2| exact LIT| exact LITL| lia| lia| lia| left; lia|].
      clear MU WM LIT LITL. intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 DI3. retlit.
      unfold KEXIT, DMP_PJ_EXIT in HK. eapply HK; [exact DI3| exact FRM].
    -
      apply (rw_cells_split_CB usegs _ _ [_] 32 j32 _ [8; 8; 8; 8]%nat) in FR2; [| reflexivity]. cbn [mk_CB_cells app] in FR2.
      clear MU. pose proof (munch_refl [(dsp D, dsp D + 88)]%Z m2) as MU.

      hstep. step. step. step. step. step. astep. astep. hstep. step. step. astep. hstep. astep. astep. hstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (FRU : rw_cells usegs mx (dsp D) (uframe D j0 pjolitsU out j56 j80)) by (unfold uframe, pjolitsU, pjsaves, DMP_LIT_RBRACE; cbn [app]; exact FR2) end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv usegs mx, MUx : munch _ m2 mx, WMx : wmono usegs m2 mx |- _ =>
        pose proof (PINV_reframe pjolitsU pjolitsU32 lcj D m2 mx j0 out j56 j80 DOK DI2 MUx WMx MIx FRU) as DI3 end end.
      unfold KOLOOP, OLS, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL.
      eapply evt_eq; [| eapply HL; [rewrite ?unsigned_lit in KE by lia; lia| exact DI3| exact FRM]]. cbn. atp_st_eq.
  Qed.

  Lemma pj_obj_step : forall (K : machine_state -> Prop) (e it j : Z) (x1 gp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV pjolitsU D m -> frm0 fc -> is_str T S sn it -> elem T S sn ck_any d (it + 1) j -> 0 <= it -> j <= e -> e + 1 <= n -> pe_lo D + pj_need d <= dsp D ->
    (j <> e -> KOLOOP K gp e j) -> (j = e -> KOEND K gp) ->
    evt usegs K (OLS e it x1 gp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM STRI EL I0 JE EN NEED HL HE. unfold OLS, DMP_LIT_QUOTE, DMP_LIT_QCOLON.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, CNT_MAX in *.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & SB & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct STRI as (o & l & KE & SA). pose proof (str_at_bounds _ _ SNR _ _ SA) as (O0 & L0 & OL & LE & O56).
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) it TB ltac:(lia)) as RDT. rewrite KE in RDT.
    assert (TWR : 0 <= tword t_str o < 2^64) by (unfold tword, t_str; lia).
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) o SB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 1) SB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 2) SB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 3) SB ltac:(lia)) as RB3.
    assert (B0 : 0 <= S o < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B1 : 0 <= S (o + 1) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B2 : 0 <= S (o + 2) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B3 : 0 <= S (o + 3) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).

    step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (pe_DOC D) (pe_TAPE D) it 0x3ace8 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    step. step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    step. astep. rewrite tval_str by lia. astep. astep.
    step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
    step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. clear K3.

    step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (pe_DOC D) (pe_TAPE D) it 0x3ad14 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.

    step. step. astep. rewrite tval_str by lia. astep.
    step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. clear K4.
    astep. astep. astep.
    replace (0 <? pe_SBUF D) with true by (symmetry; apply Z.ltb_lt; lia).
    lazymatch goal with |- context [Z.b2z (?x <? 1)] => replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia) end.
    change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
    step. if_false. step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. clear K5.

    step. step. step. step. step. step. step. step.
    lit_at 0x1233a 1%nat m MI LIT LITL.
    eapply (put_call pjolitsU pjolitsU32 D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL RDT RB0 RB1 RB2 RB3. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _ & _ & TB2 & SB2 & DOCC2 & _).

    astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
    change (S o + 2 ^ 8 * S (o + 1) + 2 ^ 16 * S (o + 2) + 2 ^ 24 * S (o + 3)) with (le32 S o). rewrite LE.
    step. step. replace (o + pe_SBUF D + 4) with (pe_SBUF D + o + 4) by lia.
    destruct (sbuf_slice m2 (pe_SBUF D) (pe_sbs D) o l SB2 ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
    eapply (put_call pjolitsU pjolitsU32 D DOK PUT); [exact DI2| exact QB| exact QL| lia| lia| lia| left; lia|].
    clear MU WM QB QL TB2 SB2 DOCC2. intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 DI3. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof DI3 as (_ & _ & _ & _ & _ & _ & MI3 & _).

    step. step. step.
    lit_at 0x13205 3%nat m3 MI3 LIT LITL.
    eapply (put_call pjolitsU pjolitsU32 D DOK PUT); [exact DI3| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m4 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI4. retlit.
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl usegs m4) as WM.

    astep. step. step. step. step.
    eapply (pj_call pjolitsU pjolitsU32 D DOK d PJ); [exact DI4| exact FRM| exact EL| lia| lia| exact NEED|].
    clear MU WM. intros m5 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F5 fc5 DI5 FRM5. retlit.
    pose proof DI5 as (_ & _ & _ & _ & _ & _ & MI5 & _ & _ & TB5 & _ & DOCC5 & _). open_frame DI5 FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.

    step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 m5 (pe_DOC D) (pe_TAPE D) (it + 1) 0x3ada8 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC5| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros za1 za2 za3 za4.
    destruct (elem_cases _ _ _ _ _ _ EL) as [[-> TY]|[[-> TY]|[[-> STRV]|(d' & e' & c' & cv' & Hd & -> & CV' & CO)]]].
    - assert (TIR : 0 <= T (it + 1) < 2^64) by (destruct TY as [E'|[E'|E']]; rewrite E'; unfold tword, t_true, t_false, t_null; lia).
      pose proof (tape_read_type m5 (pe_TAPE D) (pe_tws D) (it + 1) TB5 ltac:(lia) TIR) as RTY.
      destruct TY as [E'|[E'|E']]; rewrite E', ttype_tword in RTY by lia; unfold t_true, t_false, t_null in RTY;

        (step; astep; step; step; if_false; step; astep; astep; step; if_true; step; astep; astep; step; if_true; astep; step);
        (if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia;
         [ unfold KOLOOP, OLS, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL; eapply evt_eq; [| eapply HL; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq
         | unfold KOEND in HE; eapply evt_eq; [| eapply HE; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq ]).
    - assert (TIR : 0 <= T (it + 1) < 2^64) by (destruct TY as [E'|[E'|E']]; rewrite E'; unfold tword, t_i64, t_u64, t_dbl; lia).
      pose proof (tape_read_type m5 (pe_TAPE D) (pe_tws D) (it + 1) TB5 ltac:(lia) TIR) as RTY.
      destruct TY as [E'|[E'|E']]; rewrite E', ttype_tword in RTY by lia; unfold t_i64, t_u64, t_dbl in RTY;

        (step; astep; step; step; if_false; step; astep; astep; step; if_false; astep; step);
        (if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia;
         [ unfold KOLOOP, OLS, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL; eapply evt_eq; [| eapply HL; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq
         | step; unfold KOEND in HE; eapply evt_eq; [| eapply HE; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq ]).
    - pose proof (key_word_range _ _ _ _ STRV SNR) as (TIR & _ & KT').
      pose proof (tape_read_type m5 (pe_TAPE D) (pe_tws D) (it + 1) TB5 ltac:(lia) TIR) as RTY. rewrite KT' in RTY. unfold t_str in RTY.

      step. astep. step. step. if_true. astep. step.
      if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia;
         [ unfold KOLOOP, OLS, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL; eapply evt_eq; [| eapply HL; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq
         | unfold KOEND in HE; eapply evt_eq; [| eapply HE; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq ].
    - assert (LT' : it + 1 < e').
      { destruct CO as [(_ & _ & HT')|(_ & _ & HT')].
        - pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ HT'). lia.
        - pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ HT'). lia. }
      unfold CNT_MAX in CV'.
      destruct CO as [(E' & _ & _)|(E' & _ & _)];
        (assert (TIR : 0 <= T (it + 1) < 2^64) by (rewrite E'; unfold cword, tword, t_arr, t_obj; lia));
        (pose proof (tape_read_type m5 (pe_TAPE D) (pe_tws D) (it + 1) TB5 ltac:(lia) TIR) as RTY);
        (pose proof (tape_read m5 (pe_TAPE D) (pe_tws D) (it + 1) TB5 ltac:(lia)) as RDT);
        rewrite E', ttype_cword in RTY by (unfold CNT_MAX; lia); unfold t_arr, t_obj in RTY; rewrite E' in RDT;

        (step; astep; step; step; if_false; step; astep; astep; step; if_true; step; astep; astep; step; if_false; step; step; step);
        (eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 m5 (pe_DOC D) (pe_TAPE D) (it + 1) 0x3adf0 [C8 (Z_to_bv 64 (pe_SBUF D))]);
        [exact DOCC5| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|]);
        intros wa1 wa2 wa3 wa4;

        step; step; astep;
        [rewrite (low32_cword' t_arr) by (unfold t_arr, CNT_MAX; lia)| rewrite (low32_cword' t_obj) by (unfold t_obj, CNT_MAX; lia)]; step;
        (if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia;
         [ unfold KOLOOP, OLS, DMP_LIT_QUOTE, DMP_LIT_QCOLON in HL; eapply evt_eq; [| eapply HL; [lia| exact DI5| exact FRM5]]; cbn; atp_st_eq
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
  intros d. unfold pj_obj_case. intros until cv. intros DOK PUT IB IL IUL INSD PJ DI FRM IE EN CV E EE HT NEED HK.
  pose proof DOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IR & _).
  assert (NEEDd : pe_lo D + pj_need d <= dsp D) by (rewrite pj_need_S in NEED; unfold DMP_PJ_FRAME in NEED; lia).
  eapply (pj_obj_head D DOK PUT j32); [exact DI| exact FRM| exact IE| exact EN| exact CV| exact E| apply HK; reflexivity|].
  intros NE. eapply (pj_obj_loop D DOK PUT d PJ); [exact HT| exact NE| lia| exact EN| exact NEEDd| apply (pj_obj_end D DOK PUT); apply HK; reflexivity].
Qed.
End WithCeiling0.
