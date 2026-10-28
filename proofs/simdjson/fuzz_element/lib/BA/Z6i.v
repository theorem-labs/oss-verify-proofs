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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import IcptSpec D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA Atp_objpA Z6j Atp_objnA Atp_objkA Atp_objsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjV.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma obj_v1 : forall (K : machine_state -> Prop) (q b P L0 f D cap sz i e node : Z) (lg : bool)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w80 w88 w96 w112 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E ->
    0x6ca000 <= f -> f + 120 <= ae_lo E -> lstrA m (f + 32) lg D cap sz ->
    AINV_A E m -> rw_cells asegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_hi E ->
    ty (ae_T E) i = t_obj -> tnext (ae_T E i) = e + 1 -> 0 <= i -> e + 1 <= ae_n E - 1 -> i + 1 <= e ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) (Z_to_bv 64 f) (Z_to_bv 64 f) w80 w88 w96 (Z_to_bv 64 (P + 1)) w112 (Z_to_bv 64 node) w128) ->
    (forall m', munch [(b, b + 136)] m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch [(b, b + 136)] m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch [(b, b + 136)] m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->

    (forall (xa2 xa3 : word), e = i + 1 ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz 0) (wz 20) xa2 xa3 (wz (if lg then 1 else 0)) x15 (wz (ae_DOC E)) (wz (ae_TAPE E))
                  (wz 0) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz LIT_TILDE_A) (wz D) (wz e) (wz sz) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb676c) fc None m (seg_rom asegs))) ->

    (forall (m1 : mem) (xa0 xa1 xa2 xa3 : word), i + 1 <> e -> munch [(b, b + 136)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b (obj_locA j0 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 (if lg then 1 else 0)) (Z_to_bv 64 4294967295) (Z_to_bv 64 4294967297) (Z_to_bv 64 L0) (Z_to_bv 64 f) (Z_to_bv 64 f) w80
                               (Z_to_bv 64 (f + 32)) (Z_to_bv 64 67240448) (Z_to_bv 64 (P + 1)) w112 (Z_to_bv 64 node) w128) ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) xa0 xa1 xa2 xa3 (wz (if lg then 1 else 0)) x15 (wz (ae_DOC E)) (wz (ae_TAPE E))
                  (wz (i + 1)) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
             F (wz 0xb65f4) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz 49) (wz (shad f)) x20 (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz 18446744073709551615) x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb6448) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH FLO FHI LS AI NODE QN NB TY NXT I0 EN IE LOCA SHZN SHZD SHZT KEMP KL2.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    unfold USTACK_TOP in HT. unfold SEGTOP_A in *. unfold LIT_SLASH_A, LIT_TILDE_A in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (munch_refl [(b, b + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_locA in LOCA.
    pose proof AI as (TAPEB & SBUFB & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
    unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_obj; lia) ltac:(unfold t_obj; lia)) as TIR.
    pose proof LS as (SZ0 & SZC & CAP & D0 & DC & (bs & BS & LBS & NUL) & REP).
    hide TAPEB. hide SBUFB. hide BS.

    assert (J : evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (if lg then (cap + 1) mod 256 else 2 * sz)) x11 x12 x13 (wz (if lg then 1 else 0)) x15 x16 x17
                                  (wz 49) (wz (shad f)) x20 (wz 0x23800) (wz (f + 32)) (wz 0x23820) (wz D) (wz 18446744073709551615) (wz sz) (wz 2147450880) x28 x29 x30 x31)
                              F (wz 0xb64c8) fc None m (seg_rom asegs))).
    2:{ destruct lg.
        - destruct REP as [HDR EV]. pose proof (rw_cells_C8_read1A _ _ _ _ HDR) as RD0.

          astep. rewrite u8_modA. astep. rewrite long_byte0A by lia. step. if_true. step. step.
          eapply evt_eq; [| exact J]. atp_st_eq.
        - destruct REP as (HDR & ED & ECAP).

          astep. astep. rewrite short_byte0A. step. if_false. astep. rewrite short_sizeA by lia. step.
          eapply evt_eq; [| exact J]. atp_st_eq. }
    clear REP.

    step. step. chk0 SHZN node. step. if_false.

    astep. chk0 SHZN (node + 8). step. if_false.

    step. chk0 SHZD (ae_DOC E). step. if_false.

    unhide TAPEB.
    step. step. astep. astep. chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.

    step. astep. rewrite TY. unfold t_obj. astep. astep. astep. step. if_false.
    hide TAPEB.

    astep. astep. astep. astep. step. if_true. astep. astep. astep. astep. astep. step. if_false. astep. astep.
    rewrite ?mod32_tnext, ?land32_tnext by lia. rewrite NXT. step.

    astep. replace (e + 1 + -1) with e by lia. astep. step. if_cases KE; zify_cond KE.
    2:{
        astep. astep. step.
        eapply evt_eq; [| apply evt_done; apply KEMP; lia]. atp_st_eq. }

    step. name_mem m1. step.

    astep. chk0 SHZD (ae_DOC E + 8). step. if_false.

    astep. astep. step. astep. astep. astep. astep. lstep. astep. lstep. astep. astep. astep. lstep. step. name_mem m2.
    eapply evt_eq; [| apply evt_done; apply (KL2 m2); [lia| exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

  Definition obj_loc2 (j0 : list byte) (lgv L0 f P : Z) (w80 w112 w120 w128 : word) : list cell :=
    obj_locA j0 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 lgv) (Z_to_bv 64 4294967295) (Z_to_bv 64 4294967297) (Z_to_bv 64 L0) (Z_to_bv 64 f) (Z_to_bv 64 f) w80
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 67240448) (Z_to_bv 64 (P + 1)) w112 w120 w128.

  Lemma obj_l2adv : forall (K : machine_state -> Prop) (q b P L0 lgv f D sz e it j' : Z)
      (gp x1 x5 x10 x11 x12 x13 x14 x15 x16 x21 x29 x30 x31 : word) (w80 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 <= lgv <= 1 ->
    AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> 0 <= it -> it + 1 < j' -> j' <= e -> e + 1 <= ae_n E - 1 ->
    rw_cells asegs m b (obj_loc2 j0 lgv L0 f P w80 w112 w120 w128) ->

    (forall (xa0 xa1 xa2 : word), j' <> e ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) xa0 xa1 xa2 x13 x14 x15 x16 (wz (ae_TAPE E))
                  (wz j') (wz (shad f)) (wz (8 * it)) x21 (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
             F (wz 0xb65f4) fc None m (seg_rom asegs))) ->

    (forall (xa2 : word), j' = e ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) (wz 0) (wz 20) xa2 x13 (wz lgv) x15 x16 (wz (ae_TAPE E))
                  (wz 0) (wz (shad f)) (wz (8 * it)) (wz (P + 1)) (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
             F (wz 0xb676c) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 (wz (ae_TAPE E))
                       (wz it) (wz (shad f)) (wz (8 * it)) x21 (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
                   F (wz 0xb66b4) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH LGV AI SHZT EL I0 IJ JE EN LOCA KNEXT KNF.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_loc2, obj_locA in LOCA.
    pose proof AI as (TAPEB & _ & _ & _ & _).
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (it + 1) TAPEB ltac:(lia)) as RDV.
    replace (ae_TAPE E + 8 * (it + 1)) with (ae_TAPE E + 8 + 8 * it) in RDV by lia.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E (it + 1)) < 256) by (unfold ttype; lia).

    astep. chk0 SHZT (ae_TAPE E + 8 + 8 * it). step. if_false. step. astep. astep.

    assert (LT : forall (pc : Z) (xa0 xa1 xa2 : word), (pc = 0xb66ec \/ pc = 0xb670c \/ pc = 0xb6718) ->
      evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) xa0 xa1 xa2 x13 x14 x15 x16 (wz (ae_TAPE E))
                         (wz j') (wz (shad f)) (wz (8 * it)) x21 (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
                     F (wz pc) fc None m (seg_rom asegs))).
    { intros pc xa0 xa1 xa2 PC.
      assert (NF : forall xa2' : word, j' = e ->
        evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) xa0 xa1 xa2' x13 x14 x15 x16 (wz (ae_TAPE E))
                           (wz j') (wz (shad f)) (wz (8 * it)) x21 (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
                       F (wz 0xb6740) fc None m (seg_rom asegs))).
      { intros xa2' JE'.
        astep. astep. step. step. astep. step.
        eapply evt_eq; [| apply evt_done; apply (KNF xa2' JE')]. atp_st_eq. }
      destruct PC as [-> |[-> | ->]]; (step; if_cases KLT; zify_cond KLT;
        [ eapply evt_eq; [| apply evt_done; apply (KNEXT xa0 xa1 xa2); rewrite ?land64_mod in KLT; lia]; atp_st_eq
        | first [apply NF; rewrite ?land64_mod in KLT; lia | step; apply NF; rewrite ?land64_mod in KLT; lia] ]). }
    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d (it + 1) j' EL ltac:(lia) ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR2|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    -
      unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; step; astep; astep; step; if_true; step; astep; astep; step; if_true; astep;
         eapply evt_eq; [| eapply (LT 0xb6718)]; [atp_st_eq| do 2 right; reflexivity]).
    -
      unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (step; if_false; step; astep; astep; step; if_false; astep;
         eapply evt_eq; [| eapply (LT 0xb66ec)]; [atp_st_eq| left; reflexivity]).
    -
      unfold t_str in TY. rewrite TY.
      step. if_true. astep.
      eapply evt_eq; [| eapply (LT 0xb6718)]; [atp_st_eq| do 2 right; reflexivity].
    -
      unfold t_arr in TY. rewrite TY.
      step. if_false. step. astep. astep. step. if_true. step. astep. astep. step. if_false. step. astep.
      rewrite ?land32_tnext, ?mod32_tnext by lia. rewrite NXT.
      eapply evt_eq; [| eapply (LT 0xb670c)]; [atp_st_eq| right; left; reflexivity].
    -
      unfold t_obj in TY. rewrite TY.
      step. if_false. step. astep. astep. step. if_true. step. astep. astep. step. if_false. step. astep.
      rewrite ?land32_tnext, ?mod32_tnext by lia. rewrite NXT.
      eapply evt_eq; [| eapply (LT 0xb670c)]; [atp_st_eq| right; left; reflexivity].
  Qed.

  Lemma obj_l2body : forall (K : machine_state -> Prop) (q b P L0 lgv f D sz e it : Z)
      (gp x1 x5 x10 x11 x12 x13 x14 x15 x16 x20 x21 x29 x30 x31 : word) (w80 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 <= sz < 2^47 -> 0 < D -> D < 2^47 ->
    AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_SBUF E) (ae_NS E) ->
    is_str (ae_T E) (ae_S E) (ae_sn E) it -> 0 <= it -> it + 1 <= e -> e + 1 <= ae_n E - 1 ->
    rw_cells asegs m b (obj_loc2 j0 lgv L0 f P w80 w112 w120 w128) ->

    (forall (m1 : mem) (l : Z) (xa3 xa4 : word), str_at (ae_S E) (ae_sn E) (tval (ae_T E it)) l -> l = sz ->
       munch [(b, b + 136)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b (obj_loc2 j0 lgv L0 f P w80 w112 (Z_to_bv 64 it) w128) ->
       K (MS (mkR (wz 0xb6690) (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) (wz D) (wz (ae_SBUF E + tval (ae_T E it) + 4)) (wz sz) xa3 xa4 x15 x16 (wz (ae_TAPE E))
                  (wz D) (wz (shad f)) (wz (8 * it)) (wz (ae_TAPE E)) (wz 2147450880) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz e) (wz sz) (wz 72057594037927935) (wz 72057594037927935) x29 x30 x31)
             F (wz e_memcmp) fc None m1 (seg_rom asegs))) ->

    (forall (l : Z) (xa1 xa2 xa3 xa4 : word), str_at (ae_S E) (ae_sn E) (tval (ae_T E it)) l -> l <> sz ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) (wz (ae_SBUF E + tval (ae_T E it))) xa1 xa2 xa3 xa4 x15 x16 (wz (ae_TAPE E))
                  (wz it) (wz (shad f)) (wz (8 * it)) x21 (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
             F (wz 0xb66b4) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 (wz (ae_TAPE E))
                       (wz it) (wz (shad f)) x20 x21 (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
                   F (wz 0xb65f4) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH SZR D0 DH AI SHZT SHZS STR I0 IE EN LOCA KCMP KADV.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    unfold USTACK_TOP in HT. unfold SEGTOP_A in *. unfold e_memcmp in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (munch_refl [(b, b + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_loc2, obj_locA in LOCA. unfold obj_loc2, obj_locA in KCMP.
    pose proof AI as (TAPEB & SBUFB & _ & _ & _).
    pose proof (key_word_rangeA _ _ _ _ STR HSN) as (KR & KM & KT).
    destruct (is_str_read _ _ _ HSN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0' & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDK.

    astep. astep. chk0 SHZT (ae_TAPE E + 8 * it). step. if_false. step. astep. rewrite KM. astep.

    chk0 SHZS (ae_SBUF E + o). step. if_false.
    astep. chk0 SHZS (ae_SBUF E + o + 3). step. if_false.

    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
    pose proof (sbs_byteA E OK o ltac:(lia)) as Y0. pose proof (sbs_byteA E OK (o + 1) ltac:(lia)) as Y1.
    pose proof (sbs_byteA E OK (o + 2) ltac:(lia)) as Y2. pose proof (sbs_byteA E OK (o + 3) ltac:(lia)) as Y3.

    hide LOCA. hide TAPEB. hide SBUFB. clear SHRD SHRD0 SHRD1 RDK.
    do 10 zstep.
    rewrite ?(a_u8_small (ae_S E o)), ?(a_u8_small (ae_S E (o + 1))), ?(a_u8_small (ae_S E (o + 2))), ?(a_u8_small (ae_S E (o + 3))) by lia.
    rewrite ?shl_mod_smallA by lia. rewrite le32_of_lbu4A by lia.
    change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.
    unhide LOCA. clear RB0 RB1 RB2 RB3.

    step. if_cases KEQ; zify_cond KEQ.
    { eapply evt_eq; [| apply evt_done; eapply (KADV l _ _ _ _ SA); rewrite ?land64_mod in KEQ; lia]. atp_st_eq. }
    assert (ELS : l = sz) by (rewrite ?land64_mod in KEQ; lia).

    astep. step. step. step. step. name_mem m1. step. step. step. step. step.
    eapply evt_eq; [| apply evt_done; eapply (KCMP m1 l _ _ SA ELS MU WM ltac:(assumption) ltac:(assumption))]. atp_st_eq.
  Qed.

  Lemma obj_l2ret : forall (K : machine_state -> Prop) (q b P L0 lgv f D sz e it : Z) (r : word)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (w80 w112 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 <= it < 2^62 -> 0 <= lgv <= 1 ->
    rw_cells asegs m b (obj_loc2 j0 lgv L0 f P w80 w112 (Z_to_bv 64 it) w128) ->

    (bv_unsigned r = 0 ->
       K (MS (mkR (wz 0xb6690) (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) (wz (ae_DOC E)) (wz 0) x12 x13 (wz lgv) x15 x16 (wz (ae_TAPE E))
                  (wz (it + 1)) (wz (shad f)) (wz (8 * it)) (wz (P + 1)) (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
             F (wz 0xb676c) fc None m (seg_rom asegs))) ->

    (bv_unsigned r <> 0 ->
       K (MS (mkR (wz 0xb6690) (wz b) gp (wz TPV) x5 (wz (ae_SBUF E)) (wz 32) (wz q) (wz b) r x11 x12 x13 x14 x15 x16 (wz (ae_TAPE E))
                  (wz it) (wz (shad f)) (wz (8 * it)) (wz (ae_TAPE E)) (wz (f + 32)) (wz (ae_TAPE E + 8)) (wz D) (wz e) (wz sz) (wz 2147450880) (wz 72057594037927935) x29 x30 x31)
             F (wz 0xb66b4) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6690) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) r x11 x12 x13 x14 x15 x16 x17
                       (wz D) (wz (shad f)) (wz (8 * it)) (wz (ae_TAPE E)) (wz 2147450880) (wz (ae_TAPE E + 8)) (wz (ae_SBUF E)) (wz e) (wz sz) (wz 72057594037927935) x28 x29 x30 x31)
                   F (wz 0xb6690) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH ITR LGV LOCA KF KADV.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL') _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
    unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_loc2, obj_locA in LOCA.

    step. step. astep. step. step. step. step. step. step. if_cases K0; zify_cond K0.
    -
      astep. astep. step. step. step.
      eapply evt_eq; [| apply evt_done; apply (KF K0)]. atp_st_eq.
    - eapply evt_eq; [| apply evt_done; apply (KADV K0)]. atp_st_eq.
  Qed.

End ObjV.
