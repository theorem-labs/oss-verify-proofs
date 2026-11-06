(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_events_fields (fuzz/fuzz_decode.c:187-263), fuzz_decode.plain 0x13870 (48-byte
   frame), against lib/Prog/check_events_fields_c.v. The maker flag s4 (0x13894-0x138c4) is 0 or
   the model's maker test, so the device test at 0x13964 compares a register with itself whenever it
   runs. The kind at 0x138c8 is split into its literal values 1..11 and the rest; for each literal
   kind the model's field equalities of check_events_fields_ok are rewritten into the event's cells,
   so each bne to the `jal abort` at 0x13a8c compares a register with itself and each beq is taken.
   Kinds 7..11 go through the jump table at 0x103c4 (image words). The counter's 8 digits (0x13a1c)
   and a scribble's len characters (0x13a78) are compared by bcmp (bcmp_holds), which returns 0 by
   the model's bytes_eq; a scribble's text[len] is 0 by the model. Any other kind skips every field
   test (the three unsigned range tests at 0x138d4, 0x1393c, 0x13998 are taken). The maker test and
   the epilogue (0x13960-0x1398c) are proved once (TAIL), the dispatch from 0x138c8 once (K1).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout DgnChkLib FrameBytes
  bcmp_c bcmp check_events_fields_c.
Import ListNotations.
Open Scope Z_scope.

(* the cells i .. i + j - 1 of a cell list, at their byte offset *)
Lemma cells_slice : forall m A cs (i j : nat),
  ro_cells rsegs m A cs ->
  ro_cells rsegs m (A + Z.of_nat (cells_size (firstn i cs))) (firstn j (skipn i cs)).
Proof.
  intros m A cs i j [Hwf Hb].
  rewrite <- (firstn_skipn i cs) in Hwf, Hb.
  rewrite <- (firstn_skipn j (skipn i cs)) in Hwf, Hb.
  apply cells_wf_app in Hwf as [W1 W23]. apply cells_wf_app in W23 as [W2 W3].
  rewrite !cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb].
  apply bytes_at_app in Hb as [Hb _]. rewrite cells_bytes_length in Hb by exact W1.
  split; assumption.
Qed.

(* bltu of two values in [0, 2^64) *)
Lemma ltu_lit64 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. rewrite bv_ltu_Z, !unsigned_lit by lia. reflexivity. Qed.

(* b[i] of the model is the byte at index i of the body *)
Lemma byte_at_bz : forall bb i, byte_at (map bz bb) i = bz (nth (Z.to_nat i) bb (Z_to_bv 8 0)).
Proof. intros bb i. unfold byte_at. rewrite <- (map_nth bz bb (Z_to_bv 8 0)). reflexivity. Qed.

(* addiw rd, rs, c; bltu n, rd: taken when the int k + c is negative or above n *)
Lemma ltu_addiw_out : forall k c n, -2^31 <= k < 2^31 -> -8 <= c <= 0 -> 0 <= n <= 8 ->
  (k + c < 0 \/ n < k + c) ->
  bv_ltu (Z_to_bv 64 n) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 k) + c))) = true.
Proof.
  intros k c n Hk Hc Hn Hout. rewrite bv_ltu_Z. apply Z.ltb_lt. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  replace (2^31) with 2147483648 in Hk by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* bltu n, x of a signed 64-bit x: taken when x is negative or above n *)
Lemma ltu_out : forall x n, -2^63 <= x < 2^63 -> 0 <= n < 2^63 -> (x < 0 \/ n < x) ->
  bv_ltu (Z_to_bv 64 n) (Z_to_bv 64 x) = true.
Proof.
  intros x n Hx Hn Hout. rewrite bv_ltu_Z. apply Z.ltb_lt. rewrite !unsigned_lit_wrap.
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^63) with 9223372036854775808 in Hx, Hn by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* bytes_eq n x y: the first n elements agree *)
Lemma bytes_eq_nth : forall n x y, bytes_eq n x y = true ->
  forall i, (i < Z.to_nat n)%nat -> nth i x 0 = nth i y 0.
Proof.
  intros n x y H i Hi. unfold bytes_eq in H. rewrite forallb_forall in H.
  specialize (H (Z.of_nat i)). unfold byte_at in H. rewrite Nat2Z.id in H.
  apply Z.eqb_eq. apply H. unfold zseq. apply in_map. apply in_seq. lia.
Qed.

(* bcmp over two byte arrays whose first n elements agree returns 0 *)
Lemma memcmp_arr : forall (n s nx ny : nat) (x y : list Z),
  (forall i, (i < n)%nat -> nth (s + i) x 0 = nth (s + i) y 0) ->
  (n <= nx)%nat -> (n <= ny)%nat ->
  memcmp_model (map (fun i => b8 (nth i x 0)) (seq s nx)) (map (fun i => b8 (nth i y 0)) (seq s ny)) n
  = Some 0.
Proof.
  induction n as [|n IH]; intros s nx ny x y H Hx Hy; [reflexivity|].
  destruct nx as [|nx]; [lia|]. destruct ny as [|ny]; [lia|].
  cbn [seq map memcmp_model].
  pose proof (H 0%nat ltac:(lia)) as H0. rewrite Nat.add_0_r in H0.
  rewrite H0, Z.eqb_refl.
  apply IH; [| lia | lia].
  intros i Hi. replace (S s + i)%nat with (s + S i)%nat by lia. apply H. lia.
Qed.

Lemma nth_map_seq : forall (f : nat -> byte) n k d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros f n k d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

(* the byte at index k of an array of one-byte cells *)
Lemma rd_arr : forall m A n l k,
  ro_cells rsegs m A (map (fun i => C1 (b8 (nth i l 0))) (seq 0 n)) -> (k < n)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat k)) 1 = Some [b8 (nth k l 0)].
Proof.
  intros m A n l k [_ Hb] Hk.
  assert (E : forall s, cells_bytes (map (fun i => C1 (b8 (nth i l 0))) s) = map (fun i => b8 (nth i l 0)) s).
  { induction s as [|i s IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity. }
  rewrite E in Hb.
  rewrite (rd1 _ _ _ k Hb) by (rewrite length_map, length_seq; lia).
  rewrite nth_map_seq by lia. reflexivity.
Qed.

(* a test whose condition is closed *)
Local Ltac lit_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in
      replace cnd with v by (vm_compute; reflexivity); cbv iota
  end.

(* a pc that is a closed term, as a literal *)
Local Ltac norm_pc :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
      let v := eval vm_compute in (bv_unsigned pc) in
      replace pc with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
  end.

(* a bne / beq of a register with itself *)
Local Ltac same := step; rewrite ?eqb_same; cbv beta iota delta [negb].

(* ld ra, s0 .. s4; addi sp; ret; then the postcondition *)
Local Ltac epilogue FR ST sp :=
  do 8 step;
  apply evt_done; do 16 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  release_frame FR ST (bv_unsigned sp); exact ST.

(* the model's facts for the kind Hk fixes: check_events_fields_ok with the kind's tests decided, the
   true conjuncts dropped and the maker conjunct set aside *)
Local Ltac kind_facts OK Hk H :=
  pose proof OK as H; unfold check_events_fields_ok in H; cbv zeta in H; rewrite Hk in H;
  unfold SPEC_EV_FADER, SPEC_EV_TOUCH, SPEC_EV_STRIP_BUTTON, SPEC_EV_SECTION_BUTTON, SPEC_EV_VPOT,
    SPEC_EV_JOG, SPEC_EV_RING, SPEC_EV_METER, SPEC_EV_STRIP_LEDS, SPEC_EV_SCRIBBLE, SPEC_EV_COUNTER in H;
  cbn [implb orb andb Z.eqb Pos.eqb] in H; rewrite ?andb_true_r in H;
  apply andb_prop in H as [H _]; rewrite ?andb_true_iff in H.

(* jal bcmp with the two byte lists and the result 0 *)
Local Ltac bcall BC LS RS :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply BC with (ls := LS) (rs := RS) (v := 0) | post_call segs mm ]
  end.

Theorem check_events_fields_holds : check_events_fields_contract.
Proof.
  unfold check_events_fields_contract, CHECK_EVENTS_FIELDS, CHECK_EVENTS_FIELDS_FRAME, OW_SIZE, DE_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b o e lo bb ow ev p1 p2 mpad OK RK RS RL RA RLM RSC BB MO ME ST HLO DB DO DE MI.
  pose proof bcmp_holds as BCMP. unfold bcmp_contract in BCMP.
  cbv beta iota delta [owed_cells spec_msg_cells spec_event_cells arr_cells app map seq] in MO.
  cbv beta iota delta [event_cells dmsg_cells arr_cells app map seq] in ME.
  pose proof (cells_slice _ _ _ 32 1 ME) as DVE.
  pose proof (cells_slice _ _ _ 20 1 MO) as DVO.
  pose proof (cells_slice _ _ _ 14 9 ME) as TXE.
  pose proof (cells_slice _ _ _ 28 8 MO) as TXO.
  pose proof (cells_slice _ _ _ 23 8 ME) as SGE.
  pose proof (cells_slice _ _ _ 36 8 MO) as SGO.
  cbn [firstn skipn cells_size csize Nat.add] in DVE, DVO, TXE, TXO, SGE, SGO.
  change (Z.of_nat 38) with 38 in DVE. change (Z.of_nat 66) with 66 in DVO.
  change (Z.of_nat 20) with 20 in TXE. change (Z.of_nat 77) with 77 in TXO.
  change (Z.of_nat 29) with 29 in SGE. change (Z.of_nat 85) with 85 in SGO.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 9 step.                       (* addi sp; sd ra, s0 .. s4; mv s1, a2; mv s0, a1 *)
  (* ---- 0x13960 .. 0x1398c: the maker test, then the epilogue ---- *)
  lazymatch goal with
  | |- evt _ ?Q _ =>
  assert (TAIL : forall (mm : word -> option byte)
                        (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r28 r29 r30 r31 : word),
    (r20 = Z_to_bv 64 0 \/ de_device ev = se_device (ow_e ow)) ->
    rw_cells rsegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp + -48, bv_unsigned sp)] m mm -> wmono rsegs m mm -> mem_inv rsegs mm ->
    ro_cells rsegs mm (e + 38) [C1 (b8 (de_device ev))] ->
    ro_cells rsegs mm (o + 66) [C1 (b8 (se_device (ow_e ow)))] ->
    evt rsegs Q (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp r5 r6 r7 (Z_to_bv 64 o) (Z_to_bv 64 e)
                       r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31)
                  F (Z_to_bv 64 0x13960) fc None mm (seg_rom rsegs)))
  end.
  { clear - HLO.
    intros mm r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r28 r29 r30 r31 HY FR ST MU WM MI DVE DVO.
    step.                                                  (* 0x13960 beqz s4 *)
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Z4 end;
      cbv iota.
    - epilogue FR ST sp.
    - destruct HY as [HY|HY]; [subst r20; rewrite eqb_same in Z4; discriminate|].
      step. step. rewrite HY. same.                        (* e->device != ev->device *)
      epilogue FR ST sp. }
  (* ---- 0x138c8 .. : the kind dispatch; each kind's tests, then the maker test ---- *)
  lazymatch goal with
  | |- evt _ ?Q (MS _ _ _ _ _ ?m1 _) =>
  assert (K1 : forall r10 r11 r12 r20 : word,
    (r20 = Z_to_bv 64 0 \/ de_device ev = se_device (ow_e ow)) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 e)
                       r10 r11 r12 a3 a4 a5 a6 a7 s2 s3 r20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x138c8) fc None m1 (seg_rom rsegs)))
  end.
  { intros r10 r11 r12 r20 HY.
    step. rewrite (sx32_int (se_kind (ow_e ow))) by lia.   (* lw a0, 0x38(s0) *)
    step. step. step.                                      (* addiw a1, a0, -2; addi a2, 2; bltu a2, a1 *)
    assert (KC : se_kind (ow_e ow) = 1 \/ se_kind (ow_e ow) = 2 \/ se_kind (ow_e ow) = 3 \/
                 se_kind (ow_e ow) = 4 \/ se_kind (ow_e ow) = 5 \/ se_kind (ow_e ow) = 6 \/
                 se_kind (ow_e ow) = 7 \/ se_kind (ow_e ow) = 8 \/ se_kind (ow_e ow) = 9 \/
                 se_kind (ow_e ow) = 10 \/ se_kind (ow_e ow) = 11 \/
                 (se_kind (ow_e ow) < 1 \/ 11 < se_kind (ow_e ow))) by lia.
    destruct KC as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]]]]]].
    - (* 1, fader: strip, value, lsb_missing (fuzz_decode.c:207-209) *)
      kind_facts OK Hk FK. destruct FK as [[E1 E2] E3].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. rewrite E1, E2, E3 in ME.
      rewrite Hk. lit_if.                                  (* kind - 2 > 2: to 0x13908 *)
      step. step. lit_if.                                  (* kind = 1 *)
      step. step. same.                                    (* strip *)
      step. step. same.                                    (* value *)
      step. step. rewrite (zxb_b8 (ow_lsb_missing ow)), (sx32_int (ow_lsb_missing ow)) by lia.
      same.                                                (* lsb_missing; beq to 0x13960 *)
      eapply TAIL; eassumption.
    - (* 2, touch: button, on, strip (fuzz_decode.c:196-198) *)
      kind_facts OK Hk FK. destruct FK as [[E1 E2] E3].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. rewrite E1, E2, E3 in ME.
      rewrite Hk. lit_if.                                  (* kind - 2 <= 2: on to 0x138d8 *)
      step. step. same.                                    (* button *)
      step. step. same.                                    (* on *)
      step. step. lit_if.                                  (* kind <> 4: to 0x13954 *)
      step. step. same.                                    (* strip *)
      eapply TAIL; eassumption.
    - (* 3, strip button: button, on, strip *)
      kind_facts OK Hk FK. destruct FK as [[E1 E2] E3].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. rewrite E1, E2, E3 in ME.
      rewrite Hk. lit_if.
      step. step. same.                                    (* button *)
      step. step. same.                                    (* on *)
      step. step. lit_if.                                  (* kind <> 4: to 0x13954 *)
      step. step. same.                                    (* strip *)
      eapply TAIL; eassumption.
    - (* 4, section button: button, on, zone *)
      kind_facts OK Hk FK. destruct FK as [[E1 E2] E3].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. rewrite E1, E2, E3 in ME.
      rewrite Hk. lit_if.
      step. step. same.                                    (* button *)
      step. step. same.                                    (* on *)
      step. step. lit_if.                                  (* kind = 4: on to 0x138f8 *)
      step. step. same.                                    (* zone; beq to 0x13960 *)
      eapply TAIL; eassumption.
    - (* 5, vpot: delta, strip (fuzz_decode.c:214-216) *)
      kind_facts OK Hk FK. destruct FK as [E1 E2].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. rewrite E1, E2 in ME.
      rewrite Hk. lit_if.                                  (* to 0x13908 *)
      step. step. lit_if.                                  (* kind <> 1: to 0x13938 *)
      step. step. lit_if.                                  (* kind - 5 <= 1: on to 0x13940 *)
      step. step. same.                                    (* delta *)
      step. step. lit_if.                                  (* kind = 5: on to 0x13954 *)
      step. step. same.                                    (* strip *)
      eapply TAIL; eassumption.
    - (* 6, jog: delta *)
      kind_facts OK Hk FK.
      apply Z.eqb_eq in FK. rewrite FK in ME.
      rewrite Hk. lit_if.
      step. step. lit_if.
      step. step. lit_if.
      step. step. same.                                    (* delta *)
      step. step. lit_if.                                  (* kind <> 5: to 0x13960 *)
      eapply TAIL; eassumption.
    - (* 7, ring: strip, mask (fuzz_decode.c:221-222), table entry 0x13a34 *)
      kind_facts OK Hk FK. destruct FK as [E1 E2].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. rewrite E1, E2 in ME.
      rewrite Hk. lit_if.
      step. step. lit_if.
      step. step. lit_if.                                  (* kind - 5 > 1: to 0x13990 *)
      step. step. step. lit_if.                            (* kind - 7 <= 4: on to the table *)
      do 7 step. norm_pc.
      step. step. same.                                    (* strip *)
      step. step. same.                                    (* mask; beq to 0x13960 *)
      eapply TAIL; eassumption.
    - (* 8, meter: addr, strip, right, mask, segments (fuzz_decode.c:231-234), entry 0x139b8 *)
      kind_facts OK Hk FK. destruct FK as [[[[E1 E2] E3] E4] E5].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. apply Z.eqb_eq in E4.
      apply Z.eqb_eq in E5. rewrite E1, E2, E3, E4, E5 in ME.
      rewrite Hk. lit_if.
      step. step. lit_if.
      step. step. lit_if.
      step. step. step. lit_if.
      do 7 step. norm_pc.
      step. step. same.                                    (* addr *)
      step. step. same.                                    (* strip *)
      step. step. same.                                    (* right *)
      step. step. same.                                    (* mask *)
      step. step. same.                                    (* segments; beq to 0x13960 *)
      eapply TAIL; eassumption.
    - (* 9, strip leds: addr, strip, mask (fuzz_decode.c:239-241), entry 0x13a28 *)
      kind_facts OK Hk FK. destruct FK as [[E1 E2] E3].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. rewrite E1, E2, E3 in ME.
      rewrite Hk. lit_if.
      step. step. lit_if.
      step. step. lit_if.
      step. step. step. lit_if.
      do 7 step. norm_pc.
      step. step. same.                                    (* addr *)
      step. step. same.                                    (* strip *)
      step. step. same.                                    (* mask; beq to 0x13960 *)
      eapply TAIL; eassumption.
    - (* 10, scribble: addr, len, memcmp of len characters, text[len] = 0 (fuzz_decode.c:246-249),
         entry 0x13a50 *)
      pose proof (RSC Hk) as RLN.
      kind_facts OK Hk FK. destruct FK as [[[E1 E2] BE] NZ].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in NZ. rewrite E1, E2 in ME.
      rewrite Hk. lit_if.
      step. step. lit_if.
      step. step. lit_if.
      step. step. step. lit_if.
      do 7 step. norm_pc.
      step. step. same.                                    (* addr *)
      step. step. rewrite (zxb_b8 (se_len (ow_e ow))) by lia.
      same.                                                (* len *)
      do 5 step.                                           (* addi s3; addi a1; mv a0; mv a2; jal bcmp *)
      pose proof (ro_cells_bound _ _ _ _ TXE) as BTE. pose proof (ro_cells_bound _ _ _ _ TXO) as BTO.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BTE, BTO.
      bcall BCMP (map (fun i => b8 (nth i (de_text ev) 0)) (seq 0 9))
                 (map (fun i => b8 (nth i (se_text (ow_e ow)) 0)) (seq 0 8)).
      + rewrite unsigned_lit by lia. exact (proj2 TXE).
      + rewrite unsigned_lit by lia. exact (proj2 TXO).
      + rewrite unsigned_lit by lia. apply memcmp_arr; [| lia | lia].
        intros i Hi. exact (bytes_eq_nth _ _ _ BE i Hi).
      + eassumption.
      + step. lit_if.                                      (* bnez a0: bcmp returned 0 *)
        step.                                              (* add s2, s3, s2 *)
        pose proof (rd_arr _ _ 9 (de_text ev) (Z.to_nat (se_len (ow_e ow))) TXE ltac:(lia)) as HR.
        rewrite Z2Nat.id in HR by lia. unfold byte_at in NZ. rewrite NZ in HR.
        step. step. lit_if.                                (* lbu a0, 0(s2); beqz a0 to 0x13960 *)
        eapply TAIL; eassumption.
    - (* 11, counter: addr, dots, memcmp of the 8 digits (fuzz_decode.c:254-256), entry 0x139f8 *)
      kind_facts OK Hk FK. destruct FK as [[E1 E2] BE].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. rewrite E1, E2 in ME.
      rewrite Hk. lit_if.
      step. step. lit_if.
      step. step. lit_if.
      step. step. step. lit_if.
      do 7 step. norm_pc.
      step. step. same.                                    (* addr *)
      step. step. same.                                    (* dots *)
      do 4 step.                                           (* addi a0; addi a1; addi a2, 8; jal bcmp *)
      pose proof (ro_cells_bound _ _ _ _ SGE) as BSE. pose proof (ro_cells_bound _ _ _ _ SGO) as BSO.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BSE, BSO.
      bcall BCMP (map (fun i => b8 (nth i (de_seg ev) 0)) (seq 0 8))
                 (map (fun i => b8 (nth i (se_seg (ow_e ow)) 0)) (seq 0 8)).
      + rewrite unsigned_lit by lia. exact (proj2 SGE).
      + rewrite unsigned_lit by lia. exact (proj2 SGO).
      + rewrite unsigned_lit by lia. apply memcmp_arr; [| lia | lia].
        intros i Hi. exact (bytes_eq_nth _ _ _ BE i Hi).
      + eassumption.
      + step. lit_if.                                      (* beqz a0 to 0x13960 *)
        eapply TAIL; eassumption.
    - (* any other kind: every field test is skipped *)
      rewrite (ltu_addiw_out (se_kind (ow_e ow)) (-2) 2) by lia. cbv iota.   (* to 0x13908 *)
      step. step.                                          (* addi a1, 1; bne a0, a1 *)
      rewrite (eqb_int64 (se_kind (ow_e ow)) 1) by lia.
      replace (se_kind (ow_e ow) =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      cbv beta iota delta [negb].                          (* to 0x13938 *)
      step. step.                                          (* addiw a2, a0, -5; bltu a1, a2 *)
      rewrite (ltu_addiw_out (se_kind (ow_e ow)) (-5) 1) by lia. cbv iota.   (* to 0x13990 *)
      step. step. step.                                    (* addi a0, a0, -7; addi a1, 4; bltu a1, a0 *)
      rewrite (ltu_out (se_kind (ow_e ow) + -7) 4) by lia. cbv iota.        (* to 0x13960 *)
      eapply TAIL; eassumption. }
  (* ---- 0x13894 .. 0x138c4: s4 = the maker flag (fuzz_decode.c:190) ---- *)
  step. rewrite (zxb_b8 (sm_status (ow_m ow))) by lia.     (* lbu a1, 0x20(a1) *)
  step. step.                                              (* addi a2, 0xf0; bne a1, a2 *)
  rewrite (eqb_int64 (sm_status (ow_m ow)) 240) by lia.
  destruct (Z.eqb_spec (sm_status (ow_m ow)) 240) as [HS|HS]; cbv beta iota delta [negb].
  2: { step. eapply K1. left. reflexivity. }               (* status <> F0: mv s4, zero *)
  step. step. step.                                        (* ld a1, 0x30(s0); addi a2, 3; bltu a1, a2 *)
  rewrite (ltu_lit64 (sm_sysex_len (ow_m ow)) 3) by lia.
  destruct (Z.ltb_spec (sm_sysex_len (ow_m ow)) 3) as [HL|HL]; cbv iota.
  { step. eapply K1. left. reflexivity. }                  (* sysex_len < 3: mv s4, zero *)
  pose proof (RA HS) as RAt.
  pose proof (rd1 _ _ _ (Z.to_nat (sm_sysex_at (ow_m ow))) BB ltac:(lia)) as HR.
  rewrite Z2Nat.id in HR by lia.
  step. step. step.                                        (* ld a1, 0x28(s0); add a0, a0, a1; lbu a0, 0(a0) *)
  step. step.                                              (* addi a0, a0, -0x13; seqz s4, a0 *)
  lazymatch goal with |- context [zxb ?X] =>
    pose proof (byte_range X) as RX; unfold zxb; rewrite (zxb_u X);
    rewrite (sltiu1_int (bv_unsigned X + -19)) by lia;
    step;                                                  (* j 0x138c8 *)
    eapply K1;
    destruct (Z.eqb_spec (bv_unsigned X + -19) 0) as [H19|H19]; [right | left; reflexivity];
    pose proof OK as MK; unfold check_events_fields_ok in MK; cbv zeta in MK;
    apply andb_prop in MK as [_ MK];
    rewrite byte_at_bz in MK; unfold bz in MK;
    replace (sm_status (ow_m ow) =? 240) with true in MK by (symmetry; apply Z.eqb_eq; exact HS);
    replace (3 <=? sm_sysex_len (ow_m ow)) with true in MK by (symmetry; apply Z.leb_le; lia);
    replace (bv_unsigned X =? SPEC_MAKER) with true in MK by (symmetry; apply Z.eqb_eq; unfold SPEC_MAKER; lia);
    cbn [andb implb] in MK; apply Z.eqb_eq in MK; exact MK
  end.
Qed.
