(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA Atp_objpA Z6j Atp_objkA Atp_objsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjU.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_u1 : forall (K : machine_state -> Prop) (q b f D cap sz esc zn : Z) (lg : bool)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv asegs m -> 0x6ca000 <= f -> f + 120 < 2^47 -> lstrA m (f + 32) lg D cap sz -> 0 <= esc < sz -> shz m D zn -> sz < zn ->

    (forall (c : Z) (xa2 : word), c <> 48 -> c <> 49 ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz c) (wz 48) xa2 (wz LIT_SLASH_A) x14 x15 x16 x17
                  (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz esc) (wz (esc + 1)) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb645c) fc None m (seg_rom asegs))) ->

    (forall (lit : Z), (lit = LIT_SLASH_A \/ lit = LIT_TILDE_A) -> esc + 2 <= sz ->
       K (MS (mkR (wz 0xb6420) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (f + 32)) (wz esc) (wz 2) (wz lit) x14 x15 x16 x17
                  (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz esc) (wz (esc + 1)) (wz 2147450880) x28 x29 x30 x31)
             F (wz STR_REPLACE_A) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz esc) x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb63c8) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until m. intros MI FLO FHI LS ESC SZ ZN KBAD KREP.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold STR_REPLACE_A, LIT_SLASH_A, LIT_TILDE_A in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof LS as (SZ0 & SZC & CAP & D0 & DC & (bs & BS & LBS & NUL) & REP).

    set (cb := nth (Z.to_nat (esc + 1)) bs (Z_to_bv 8 1)). set (c := bv_unsigned cb).
    assert (CR : 0 <= c < 256) by (subst c; pose proof (bv_unsigned_in_range 8 cb) as X; unfold bv_modulus in X; cbn in X; lia).
    assert (CNUL : esc + 1 = sz -> c = 0).
    { intros EQ. subst c cb. replace (Z.to_nat (esc + 1)) with (Z.to_nat sz) by lia. rewrite NUL. reflexivity. }
    assert (RDC : ov_read_bytes asegs m (wa (D + (esc + 1))) 1 = Some [cb]).
    { apply (u8arr_read asegs m D bs (esc + 1) cb _ BS); [apply nth_error_nth'; lia| lia| reflexivity]. }
    assert (EZ : zxb cb = Z_to_bv 64 c) by reflexivity.

    assert (J : evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz D) (wz (if lg then 1 else 0)) x12 x13 x14 x15 x16 x17
                                  (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz 0x23800) (wz (f + 32)) (wz 0x23820) (wz (f + 33)) (wz esc) x26 (wz 2147450880) x28 x29 x30 x31)
                              F (wz 0xb63dc) fc None m (seg_rom asegs))).
    2:{ destruct lg.
        - destruct REP as [HDR EV]. pose proof (rw_cells_C8_read1A _ _ _ _ HDR) as RD0.

          astep. rewrite u8_modA. astep. rewrite long_byte0A by lia. step. step. if_false. step.
          eapply evt_eq; [| exact J]. atp_st_eq.
        - destruct REP as (HDR & ED & ECAP).
          astep. astep. rewrite short_byte0A. step. step. if_true.
          eapply evt_eq; [| exact J]. atp_st_eq. }
    clear REP.

    astep. astep. chk0 SZ (D + (esc + 1)). step. if_false.
    step. rewrite EZ.

    step. if_cases K1; zify_cond K1.
    -
      assert (E49 : c = 49) by (rewrite ?land64_mod in K1; lia).
      destruct (Z.eq_dec (esc + 1) sz) as [EQ|NE]; [exfalso; rewrite (CNUL EQ) in E49; lia|].
      step. astep. step. step. step.
      eapply evt_eq; [| apply evt_done; apply (KREP 0x23820); [right; reflexivity| lia]]. atp_st_eq.
    -
      step. astep. step. if_cases K0; zify_cond K0.
      + eapply evt_eq; [| apply evt_done; apply (KBAD c x12); rewrite ?land64_mod in K0, K1; lia]. atp_st_eq.
      + assert (E48 : c = 48) by (rewrite ?land64_mod in K0; lia).
        destruct (Z.eq_dec (esc + 1) sz) as [EQ|NE]; [exfalso; rewrite (CNUL EQ) in E48; lia|].
        step. astep. step. step. step.
        eapply evt_eq; [| apply evt_done; apply (KREP 0x23800); [left; reflexivity| lia]]. atp_st_eq.
  Qed.

  Lemma obj_u2 : forall (K : machine_state -> Prop) (q b f esc : Z)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    0 <= esc -> esc + 1 < 2^62 -> 0x6ca000 <= f -> f + 120 < 2^47 ->
    K (MS (mkR (wz 0xb6430) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (f + 32)) (wz 126) (wz (esc + 1)) x13 x14 x15 x16 x17
               (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz esc) (wz (esc + 1)) (wz 2147450880) x28 x29 x30 x31)
         F (wz STR_FIND_A) fc None m (seg_rom asegs)) ->
    evt asegs K (MS (mkR (wz 0xb6420) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (f + 32)) x11 x12 x13 x14 x15 x16 x17
                       (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz esc) (wz (esc + 1)) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb6420) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros E0 E62 FLO FHI HK. unfold STR_FIND_A, LIT_SLASH_A, LIT_TILDE_A in *.

    astep. step. step. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_u3 : forall (K : machine_state -> Prop) (q b f esc r : Z)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    (r = 18446744073709551615 \/ 0 <= r < 2^62) -> 0x6ca000 <= f -> f + 120 < 2^47 ->
    (r <> 18446744073709551615 ->
       K (MS (mkR (wz 0xb6430) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz r) x11 x12 x13 x14 x15 x16 x17
                  (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz r) (wz (esc + 1)) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb63c8) fc None m (seg_rom asegs))) ->
    (r = 18446744073709551615 ->
       K (MS (mkR (wz 0xb6430) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz r) x11 x12 x13 x14 x15 x16 x17
                  (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz r) (wz (esc + 1)) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb6448) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6430) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz r) x11 x12 x13 x14 x15 x16 x17
                       (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz esc) (wz (esc + 1)) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb6430) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros HR FLO FHI KLOOP KDONE. unfold LIT_SLASH_A, LIT_TILDE_A in *.

    step. step. if_cases K0; zify_cond K0; rewrite ?land64_mod in K0.
    - eapply evt_eq; [| apply evt_done; apply KLOOP; lia]. atp_st_eq.
    - step. eapply evt_eq; [| apply evt_done; apply KDONE; lia]. atp_st_eq.
  Qed.

  Lemma obj_w764 : forall (K : machine_state -> Prop) (q b P L0 f D cap sz rd ri err : Z) (lg : bool) (w0 w1 we : word)
      (gp x1 x5 x6 x7 x12 x13 x15 x16 x17 x20 x23 x24 x25 x26 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w64 w72 w80 w88 w96 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 jt : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 <= rd < 2^64 -> 0 <= ri < 2^64 -> (err = 0 \/ err = 20) ->
    0x6ca000 <= f -> f + 120 <= ae_lo E -> lstrA m (f + 32) lg D cap sz ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) w64 w72 w80 w88 w96 (Z_to_bv 64 (P + 1)) w112 w120 w128) ->
    rw_cells asegs m (b + 160) [C8 w0; C8 w1; C4 we; CB 4 jt] ->

    (forall (m1 : mem), lg = false -> munch [(b + 160, b + 184)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (b + 160) [C8 (Z_to_bv 64 rd); C8 (Z_to_bv 64 ri); C4 (Z_to_bv 64 err); CB 4 jt] ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz rd) (wz err) x12 x13 (wz 0) x15 x16 x17
                  (wz ri) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb6790) fc None m1 (seg_rom asegs))) ->

    (forall (m1 : mem) (xa1 : word), lg = true -> munch [(b + 160, b + 184)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (b + 160) [C8 (Z_to_bv 64 rd); C8 (Z_to_bv 64 ri); C4 (Z_to_bv 64 err); CB 4 jt] ->
       K (MS (mkR (wz 0xb6790) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz D) xa1 x12 x13 (wz 1) x15 x16 x17
                  (wz ri) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz OPDEL_A) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz rd) (wz err) x12 x13 (wz (if lg then 1 else 0)) x15 x16 x17
                       (wz ri) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb676c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jt. intros MI LO B0 B1 QH RD RI ERR FLO FHI LS LOCA REC KS KL.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OPDEL_A in *.
    pose proof (munch_refl [(b + 160, b + 184)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof LS as (SZ0 & SZC & CAP & D0 & DC & (bs & BS & LBS & NUL) & REP).
    unfold obj_locA in LOCA. hide BS.
    destruct lg.
    - destruct REP as [HDR EV].

      step. step. step. name_mem m1. step. step. if_false.

      step. step. astep. step.
      eapply evt_eq; [| apply evt_done; eapply (KL m1 _ eq_refl); [exact MU| exact WM| assumption| ]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells asegs m1 (b + 160) _ |- _ => exact H end.
    -
      step. step. step. name_mem m1. step. step. if_true.
      eapply evt_eq; [| apply evt_done; eapply (KS m1 eq_refl); [exact MU| exact WM| assumption| ]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells asegs m1 (b + 160) _ |- _ => exact H end.
  Qed.

  Lemma obj_w788 : forall (K : machine_state -> Prop) (q b P L0 f rd ri err : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x24 x25 x26 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w80 w88 w96 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 jt js4 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> (err = 0 \/ err = 20) ->
    0x6ca000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) (Z_to_bv 64 f) (Z_to_bv 64 f) w80 w88 w96 (Z_to_bv 64 (P + 1)) w112 w120 w128) ->
    rw_cells asegs m (b + 160) [C8 (Z_to_bv 64 rd); C8 (Z_to_bv 64 ri); C4 (Z_to_bv 64 err); CB 4 jt] ->
    rw_cells asegs m (shad f) (obj_sh 0 0 0 js4) ->
    (forall (m1 : mem) (xa1 : word), munch [(shad f, shad f + 16)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (shad f) (obj_sh (-8) (-8) (-8) js4) ->
       (err = 20 ->
        K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (-8)) xa1 x12 x13 x14 x15 x16 x17
                   (wz f) (wz (shad f)) x20 (wz (P + 1)) (wz f) (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
              F (wz 0xb67ec) fc None m1 (seg_rom asegs))) /\
       (err = 0 ->
        K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (-8)) xa1 x12 x13 x14 x15 x16 x17
                   (wz f) (wz (shad f)) x20 (wz (P + 1)) (wz f) (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
              F (wz 0xb67b0) fc None m1 (seg_rom asegs)))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (wz (shad f)) x20 (wz (P + 1)) x22 (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb6790) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until js4. intros MI LO B0 B1 QH ERR FLO FHI FSH S0 SHI LOCA REC SH HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(shad f, shad f + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_locA in LOCA. unfold obj_sh, pz in SH. unfold obj_sh, pz in HK. unfold shad, SHB in *.

    astep. nstep. nstep. nstep. name_mem m1.

    step. step. step. step. if_cases K0; zify_cond K0.
    - eapply evt_eq; [| apply evt_done; eapply (proj1 (HK m1 _ MU WM ltac:(assumption) ltac:(assumption)))].
      + atp_st_eq.
      + rewrite a_sx32_small, a_u64_small in K0 by lia. destruct ERR as [E0|E20]; [exfalso; lia| exact E20].
    - eapply evt_eq; [| apply evt_done; eapply (proj2 (HK m1 _ MU WM ltac:(assumption) ltac:(assumption)))].
      + atp_st_eq.
      + rewrite a_sx32_small, a_u64_small in K0 by lia. destruct ERR as [E0|E20]; [exact E0| exfalso; lia].
  Qed.

  Lemma obj_b1 : forall (K : machine_state -> Prop) (q b f out : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 <= out -> out + 24 < 2^64 ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 out) w120 w128) ->
    K (MS (mkR (wz 0xb6470) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz out) (wz 0) (wz 16) x13 x14 x15 x16 x17
               (wz 49) (wz (shad f)) (wz (out + 16)) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz e_asan_memset) fc None m (seg_rom asegs)) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz 49) (wz (shad f)) x20 (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb645c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH O0 OH LOCA HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_asan_memset, LIT_SLASH_A, LIT_TILDE_A in *.
    unfold obj_locA in LOCA.

    step. astep. astep. astep. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_b2 : forall (K : machine_state -> Prop) (q b f D cap sz out : Z) (lg : bool)
      (gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (nbs jB jC : list byte),
    mem_inv asegs m -> ae_lo E <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> shz m out 24 ->
    0x6ca000 <= f -> f + 120 <= ae_lo E -> lstrA m (f + 32) lg D cap sz ->
    rw_cells asegs m out [CB 16 nbs; CB 4 jB; CB 4 jC] ->
    (forall (m1 : mem), lg = false -> munch [(out, out + 24)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 out [CB 16 nbs; C4 (Z_to_bv 64 22); CB 4 jC] ->
       K (MS (mkR (wz 0xb6470) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz 0) x11 x12 x13 x14 x15 x16 x17
                  (wz 49) (wz (shad f)) (wz (out + 16)) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb64a4) fc None m1 (seg_rom asegs))) ->
    (forall (m1 : mem) (xa1 : word), lg = true -> munch [(out, out + 24)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 out [CB 16 nbs; C4 (Z_to_bv 64 22); CB 4 jC] ->
       K (MS (mkR (wz 0xb64a4) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz D) xa1 x12 x13 x14 x15 x16 x17
                  (wz 49) (wz (shad f)) (wz (out + 16)) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz OPDEL_A) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6470) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz 49) (wz (shad f)) (wz (out + 16)) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb6470) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jC. intros MI OLO OHI O8 SZ FLO FHI LS OUT KS KL.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OPDEL_A, LIT_SLASH_A, LIT_TILDE_A in *.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof LS as (SZ0 & SZC & CAP & D0 & DC & (bs & BS & LBS & NUL) & REP). hide BS.
    destruct lg.
    - destruct REP as [HDR EV].

      chk0 SZ (out + 16). step. if_false. astep. lstep. name_mem m1.

      pose proof (rw_cells_C8_read1A _ _ _ _ ltac:(lazymatch goal with H : rw_cells asegs m1 (f + 32) _ |- _ => exact H end)) as RD0.
      astep. rewrite u8_modA. astep. rewrite long_byte0A by lia. step. if_false.
      step. step. astep. step.
      eapply evt_eq; [| apply evt_done; eapply (KL m1 _ eq_refl); [exact MU| exact WM| assumption| ]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells asegs m1 out _ |- _ => exact H end.
    - destruct REP as (HDR & ED & ECAP).
      chk0 SZ (out + 16). step. if_false. astep. lstep. name_mem m1.

      astep. astep. rewrite short_byte0A. step. if_true.
      eapply evt_eq; [| apply evt_done; eapply (KS m1 eq_refl); [exact MU| exact WM| assumption| ]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells asegs m1 out _ |- _ => exact H end.
  Qed.

  Lemma obj_b3 : forall (K : machine_state -> Prop) (q b f : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w56 w80 w88 w96 w104 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 js4 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E ->
    0x6ca000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 w56 (Z_to_bv 64 f) (Z_to_bv 64 f) w80 w88 w96 w104 w112 w120 w128) ->
    rw_cells asegs m (shad f) (obj_sh 0 0 0 js4) ->
    (forall (m1 : mem), munch [(shad f, shad f + 16)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (shad f) (obj_sh (-8) (-8) (-8) js4) ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (-8)) x11 x12 x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) x20 x21 (wz f) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb67fc) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz 49) (wz (shad f)) x20 x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb64a4) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until js4. intros MI LO B0 B1 QH FLO FHI FSH S0 SHI LOCA SH HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(shad f, shad f + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_locA in LOCA. unfold obj_sh, pz in SH. unfold obj_sh, pz in HK. unfold shad, SHB in *.

    astep. nstep. nstep. nstep. name_mem m1. step. step. step.
    eapply evt_eq; [| apply evt_done; apply (HK m1 MU WM ltac:(assumption) ltac:(assumption))]. atp_st_eq.
  Qed.

  Lemma obj_p6bx : forall (K : machine_state -> Prop) (q b P L0 Lk f D : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128) ->
    (forall (m1 : mem), munch [(b, b + 136)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) w64 w72 w80 w88 w96 (Z_to_bv 64 (P + 1)) w112 w120 w128) ->
       K (MS (mkR (wz 0xb6394) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz D) (wz (P + 1)) (wz Lk) x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) x25 (wz D) (wz 2147450880) x28 x29 x30 x31)
             F (wz e_asan_memmove) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz f) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) x25 (wz D) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb637c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH LOCA HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_asan_memmove in *.
    pose proof (munch_refl [(b, b + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_locA in LOCA.

    step. step. step. step. step. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

End ObjU.
