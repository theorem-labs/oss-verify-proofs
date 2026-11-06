(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the two set-up segments of LLVMFuzzerTestOneInput (plain image) stated in
   LLVMFuzzerTestOneInput_seg2.v.
   setup_holds : setup_stmt, 0x12d38 .. 0x12ddc: the NULL test of buf, sd buf / sel, memcpy (buf, data + 1, n)
     (skipped for n = 0), the frame-mode tests (sel >= 0: the body is the copy; else n < 30, be16 (buf + 12) <>
     0x885f, be16 (buf + 14) < 16 or n - 14 < be16 (buf + 14) give the empty body; else the body is the frame's
     be16 (buf + 14) - 16 bytes at buf + 30), diginet_cursor_init (&c, body, len) and the loop's registers.
   dsetup_holds : dsetup_stmt, 0x13024 .. 0x1309c: DESK[sel % 3] (the mul 0xab / srli 9 remainder, checked over
     the 256 values of sel), diginet_personality_of, diginet_decoder_init (&d, p, body, len), the loop's
     registers and the jump table base 0x103a4 at 8(sp). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout
  diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c diginet_decoder_init_c diginet_decoder_next_c
  check_cursor_step_c check_cursor_message_c check_events_step_c check_events_fields_c
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_seg2.
Import ListNotations.
Open Scope Z_scope.

Local Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Local Ltac solve_c := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; usub; fold_lit_ux; solve_cond_rec.
(* take the branch b of the conditional pc *)
Local Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* ---- frame pieces: take a sub-struct out of the frame's rw_cells, put it back after a call ---- *)

Section FH.
Variable segs : list Segment.

Lemma setup_fh_app : forall m A cs1 cs2, rw_cells segs m A cs1 ->
  rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (R1a & R1b & R1)] [[W2 B2] (R2a & R2b & R2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [H|H]; [apply R1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply R2. lia.
Qed.

Lemma setup_fh_split : forall m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (Ra & Rb & R)].
  apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in Rb, R.
  pose proof (cells_bytes_length cs1 W1) as L1.
  pose proof (bytes_at_bound segs _ _ _ B2) as BB2.
  rewrite cells_bytes_length in BB2 by exact W2.
  split.
  - unfold rw_cells, cells_at, wr_at. split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi. apply R. lia.
  - unfold rw_cells, cells_at, wr_at. split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply R. lia.
Qed.

Lemma setup_fh_mid : forall m A pre mid post, rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m (A + Z.of_nat (cells_size pre)) mid.
Proof.
  intros m A pre mid post H. apply setup_fh_split in H as [_ H]. apply setup_fh_split in H as [H _]. exact H.
Qed.

Lemma setup_fh_put : forall W m m' A pre mid mid' post,
  rw_cells segs m A (pre ++ mid ++ post) -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (Z.of_nat (cells_size pre)) ->
  disjoint_from W (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) (Z.of_nat (cells_size post)) ->
  rw_cells segs m' (A + Z.of_nat (cells_size pre)) mid' -> cells_size mid' = cells_size mid ->
  rw_cells segs m' A (pre ++ mid' ++ post).
Proof.
  intros W m m' A pre mid mid' post H MU WM D1 D2 HM E.
  apply setup_fh_split in H as [Hpre H]. apply setup_fh_split in H as [_ Hpost].
  apply setup_fh_app; [exact (rw_cells_transport segs W m m' A pre Hpre MU WM D1)|].
  apply setup_fh_app; [exact HM|]. rewrite E.
  exact (rw_cells_transport segs W m m' _ post Hpost MU WM D2).
Qed.

End FH.

(* ---- bytes ---- *)

(* a boolean fact of every byte, checked over the 256 values *)
Lemma setup_byte_all : forall (P : byte -> bool),
  forallb (fun z => P (Z_to_bv 8 z)) (map Z.of_nat (seq 0 256)) = true -> forall b, P b = true.
Proof.
  intros P H b. rewrite forallb_forall in H.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  replace b with (Z_to_bv 8 (bv_unsigned b)).
  - apply H. apply in_map_iff. exists (Z.to_nat (bv_unsigned b)). split; [lia|]. apply in_seq. lia.
  - apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma setup_bz_range : forall b : byte, 0 <= bz b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

(* bgez on the sign-extended sel: bit 7 *)
Lemma setup_sxb_lts : forall b : byte, bv_lts (sxb b) (Z_to_bv 64 0) = (128 <=? bz b).
Proof.
  intros b. apply Bool.eqb_prop.
  apply (setup_byte_all (fun b => Bool.eqb (bv_lts (sxb b) (Z_to_bv 64 0)) (128 <=? bz b))).
  vm_compute. reflexivity.
Qed.

(* the big-endian 16-bit value the frame-mode tests compute from two bytes *)
Lemma setup_be16 : forall b1 b2 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8))) (bv_unsigned (zxb b2))) =
  Z_to_bv 64 (bz b1 * 256 + bz b2).
Proof.
  intros b1 b2. pose proof (setup_bz_range b1) as R1. pose proof (setup_bz_range b2) as R2. unfold bz in R1, R2.
  unfold zxb. rewrite (unsigned_lit (bv_unsigned b1)), (unsigned_lit (bv_unsigned b2)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned b1 * 2 ^ 8)) by lia.
  rewrite lk_lor_mul_pow2 by lia. unfold bz. f_equal; lia.
Qed.

Lemma setup_rd_nat : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)).
  rewrite (bytes_at_ov_read rsegs m a bs i 1 H ltac:(lia)).
  f_equal. clear H. revert i Hi. induction bs as [|x bs IH]; intros [|i] Hi; cbn [length] in Hi.
  - lia.
  - lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

(* the byte the machine reads at a + i of a body in memory *)
Lemma setup_rd : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + i)) 1 = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi. pose proof (setup_rd_nat m a bs (Z.to_nat i) H ltac:(lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma setup_rw_bytes : forall segs m A k bs, rw_cells segs m A [CB k bs] -> bytes_at segs m A bs.
Proof.
  intros segs m A k bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma setup_skip1 : forall segs m p pl, (1 <= length pl)%nat -> bytes_at segs m p pl ->
  bytes_at segs m (p + 1) (skipn 1 pl).
Proof.
  intros segs m p [|b pl] HL H; [cbn [length] in HL; lia|].
  change (b :: pl) with ([b] ++ pl) in H. apply bytes_at_app in H as [_ H]. exact H.
Qed.

Lemma setup_bytes_sub : forall segs m a bs i k, bytes_at segs m a bs -> (i + k <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros segs m a bs i k H Hik.
  rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min i (length bs)) with i in H by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* ---- the set-up of the cursor loop ---- *)

(* the 344 bytes below the saved registers as the cursor loop's cells *)
Lemma setup_frame8 : forall segs m Sp j saved, rw_cells segs m Sp (CB 344 j :: saved) ->
  exists j0 j1 j2 j3 mj jA jc cpad, rw_cells segs m Sp
    (CB 8 j0 :: CB 8 j1 :: CB 8 j2 :: CB 8 j3 :: CB 56 mj :: CB 224 jA :: CB 25 jc :: CB 7 cpad :: saved).
Proof.
  intros segs m Sp j saved H.
  apply (rw_cells_split_CB segs m Sp [] 344 j saved [8;8;8;8;56;224;25;7]%nat) in H; [|reflexivity].
  cbn [mk_CB_cells app] in H. do 8 eexists. exact H.
Qed.

(* from 0x12da8 (s5 = body, s2 = len): diginet_cursor_init (&c, body, len) and the loop's registers *)
Lemma setup_tail : diginet_cursor_init_contract ->
  forall (r1 x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp lo buf n body L : Z) (bb j0 j3 mj jA jc cpad : list byte) (w8 : word) (saved : list cell)
    (Q : machine_state -> Prop),
  L = Z.of_nat (length bb) ->
  seg_ok Sp body bb -> lo_ok lo Sp body bb ->
  buf <= body -> body + L <= buf + dup_size n ->
  munch [(lo, Sp + 448); (buf, buf + dup_size n)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo Sp -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp
    (CB 8 j0 :: C8 w8 :: C8 (Z_to_bv 64 buf) :: CB 8 j3 :: CB 56 mj :: CB 224 jA :: CB 25 jc :: CB 7 cpad :: saved) ->
  chead0 Q x3 x4 F fc m0 Sp lo buf n w8 saved ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 L) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x12da8) fc None m (seg_rom rsegs)).
Proof.
  intros CINIT r1 x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
    F fc m0 m Sp lo buf n body L bb j0 j3 mj jA jc cpad w8 saved Q HL SEG LO Hb0 Hb1 MU WM MI ST BA FR K.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26). pose proof LO as (LO0 & LO1 & LO2).
  step. step. step. step.
  pose proof (setup_fh_mid rsegs m Sp [CB 8 j0; C8 w8; C8 (Z_to_bv 64 buf); CB 8 j3; CB 56 mj; CB 224 jA] [CB 25 jc]
    (CB 7 cpad :: saved) FR) as FC.
  change (Sp + Z.of_nat (cells_size [CB 8 j0; C8 w8; C8 (Z_to_bv 64 buf); CB 8 j3; CB 56 mj; CB 224 jA]))
    with (Sp + 312) in FC.
  eapply evt_cut.
  { apply (CINIT (Z_to_bv 64 77240) (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 L) r19 r20
      (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F fc m (Sp + 312) body L jc);
      [lia | lia | lia | exact FC | exact MI]. }
  intros ms' (a2' & a3' & m1 & -> & MU1 & WM1 & MI1 & RC).
  replace (ret_pc (Z_to_bv 64 77240)) with (Z_to_bv 64 77240) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (body =? 0) with false in RC by (symmetry; apply Z.eqb_neq; lia).
  pose proof (setup_fh_put rsegs [(Sp + 312, Sp + 312 + 25)] m m1 Sp
    [CB 8 j0; C8 w8; C8 (Z_to_bv 64 buf); CB 8 j3; CB 56 mj; CB 224 jA] [CB 25 jc] (cursor_cells body L 0 0)
    (CB 7 cpad :: saved) FR MU1 WM1) as FR1.
  change (cells_size [CB 8 j0; C8 w8; C8 (Z_to_bv 64 buf); CB 8 j3; CB 56 mj; CB 224 jA]) with 312%nat in FR1.
  change (Z.of_nat 312) with 312 in FR1.
  specialize (FR1 ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from cells_size csize]; lia) RC eq_refl).
  clear FR FC RC.
  apply (bytes_at_transport rsegs [(Sp + 312, Sp + 312 + 25)] m m1) in BA; [| exact MU1 | cbn [disjoint_from]; lia].
  apply (stk_transport_disjoint rsegs [(Sp + 312, Sp + 312 + 25)] m m1) in ST;
    [| exact MU1 | exact WM1 | cbn [disjoint_from]; lia].
  apply (munch_trans _ m0 m m1) in MU;
    [| apply (munch_weaken [(Sp + 312, Sp + 312 + 25)]); [unfold sub_fp; cbn [outside]; intros; lia | exact MU1]].
  apply (wmono_trans rsegs m0 m m1) in WM; [| exact WM1].
  clear MU1 WM1 MI.
  unfold cursor_cells in FR1. cbn [app] in FR1.
  do 9 step.
  rewrite (unsigned_lit L) by lia.
  replace (0 - L) with (- Z.of_nat (length bb)) by lia.
  subst L.
  unfold chead0 in K.
  eapply K; [exact SEG | exact LO | exact Hb0 | exact Hb1 | exact MU | exact WM | exact MI1 | exact ST | exact BA | exact FR1].
Qed.

(* the end of a path with the empty body: setup_tail with bb = [] *)
Local Ltac setup_empty CI bf nn :=
  (eapply (setup_tail CI) with (bb := []) (L := 0) (buf := bf) (n := nn); try first [ eassumption | reflexivity ]);
  try first [ (apply bytes_at_nil; lia) | (unfold seg_ok; cbn [length]; repeat split; lia)
            | (unfold lo_ok; cbn [length]; repeat split; lia) | (cbn [length]; lia) ].

Theorem setup_holds : setup_stmt.
Proof.
  unfold setup_stmt.
  intros MCPY CINIT x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo p buf pl junk j saved Q HSp0 HSp1 Hlo0 Hlo1 Hpl HSV Hbuf0 Hbuf1 Hp0 Hp1 Hdisj BP BUF FR MI ST K.
  pose proof (munch_refl [(lo, Sp + 448); (buf, buf + dup_size (Z.of_nat (length pl) - 1))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (setup_frame8 rsegs m Sp j saved FR) as (j0 & j1 & j2 & j3 & mj & jA & jc & cpad & FR8). clear FR.
  assert (Hdup : 1 <= dup_size (Z.of_nat (length pl) - 1))
    by (unfold dup_size; destruct (Z.eqb_spec (Z.of_nat (length pl) - 1) 0); lia).
  (* beqz a0 (buf >= 4096), mv s5, sd buf, sd sel, beqz s2 *)
  step. take false. do 4 step.
  destruct (Z.eq_dec (Z.of_nat (length pl) - 1) 0) as [N0 | N0].
  - (* n = 0: no memcpy, the empty body *)
    take true.
    replace (Z_to_bv 64 (Z.of_nat (length pl) - 1)) with (Z_to_bv 64 0) by (f_equal; lia).
    setup_empty CINIT buf (Z.of_nat (length pl) - 1).
  - take false.
    assert (Hdn : dup_size (Z.of_nat (length pl) - 1) = Z.of_nat (length pl) - 1)
      by (unfold dup_size; destruct (Z.eqb_spec (Z.of_nat (length pl) - 1) 0); lia).
    (* memcpy (buf, data + 1, n) *)
    step. step. step. step.
    eapply evt_cut.
    { eapply MCPY with (src := skipn 1 pl) (junk := junk).
      - rewrite unsigned_lit by lia. apply setup_skip1; [lia | exact BP].
      - rewrite unsigned_lit by lia. rewrite length_skipn. lia.
      - rewrite !unsigned_lit by lia. rewrite Hdn in BUF. exact BUF.
      - rewrite !unsigned_lit by lia. lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
      -> & MU2 & WM2 & MI2 & RB & _).
    replace (ret_pc (Z_to_bv 64 77148)) with (Z_to_bv 64 77148) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite !unsigned_lit in MU2, RB by lia.
    apply (rw_cells_transport rsegs [(buf, buf + (Z.of_nat (length pl) - 1))] m1 m2) in FR8;
      [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; rewrite HSV; lia].
    apply (stk_transport_disjoint rsegs [(buf, buf + (Z.of_nat (length pl) - 1))] m1 m2) in ST;
      [| exact MU2 | exact WM2 | cbn [disjoint_from]; lia].
    apply (munch_trans _ m m1 m2) in MU;
      [| apply (munch_weaken [(buf, buf + (Z.of_nat (length pl) - 1))]);
         [unfold sub_fp; cbn [outside]; intros; lia | exact MU2]].
    apply (wmono_trans rsegs m m1 m2) in WM; [| exact WM2].
    pose proof (setup_rw_bytes rsegs m2 buf _ _ RB) as BB.
    clear BP BUF RB MU2 WM2 MI.
    (* bgez s4: body mode when bit 7 of sel is clear *)
    step.
    rewrite setup_sxb_lts.
    assert (Hsk : Z.of_nat (length (skipn 1 pl)) = Z.of_nat (length pl) - 1) by (rewrite length_skipn; lia).
    pose proof (setup_bz_range (nth 0 pl (Z_to_bv 8 0))) as R0.
    destruct (Z_lt_le_dec (bz (nth 0 pl (Z_to_bv 8 0))) 128) as [S7 | S7].
    + (* body mode: the body is the copy *)
      take true.
      eapply (setup_tail CINIT) with (bb := skipn 1 pl) (body := buf) (L := Z.of_nat (length pl) - 1)
        (n := Z.of_nat (length pl) - 1).
      all: try first [ exact FR8 | exact K | exact MU | exact WM | exact MI2 | exact ST | exact BB ].
      all: try first [ lia | (unfold seg_ok; rewrite Hsk; repeat split; lia)
                     | (unfold lo_ok; rewrite Hsk; repeat split; lia) ].
    + (* frame mode *)
      take false.
      do 2 step.
      destruct (Z_lt_le_dec (Z.of_nat (length pl) - 1) 30) as [N30 | N30].
      * take true. step.
        setup_empty CINIT buf (Z.of_nat (length pl) - 1).
      * take false.
        pose proof (setup_rd m2 buf (skipn 1 pl) 12 BB ltac:(lia)) as HR12.
        pose proof (setup_rd m2 buf (skipn 1 pl) 13 BB ltac:(lia)) as HR13.
        pose proof (setup_bz_range (nth (Z.to_nat 12) (skipn 1 pl) (Z_to_bv 8 0))) as R12.
        pose proof (setup_bz_range (nth (Z.to_nat 13) (skipn 1 pl) (Z_to_bv 8 0))) as R13.
        do 7 step. rewrite setup_be16.
        destruct (Z.eq_dec (bz (nth (Z.to_nat 12) (skipn 1 pl) (Z_to_bv 8 0)) * 256 +
                            bz (nth (Z.to_nat 13) (skipn 1 pl) (Z_to_bv 8 0))) 34911) as [M | M].
        -- take false.
           pose proof (setup_rd m2 buf (skipn 1 pl) 14 BB ltac:(lia)) as HR14.
           pose proof (setup_rd m2 buf (skipn 1 pl) 15 BB ltac:(lia)) as HR15.
           pose proof (setup_bz_range (nth (Z.to_nat 14) (skipn 1 pl) (Z_to_bv 8 0))) as R14.
           pose proof (setup_bz_range (nth (Z.to_nat 15) (skipn 1 pl) (Z_to_bv 8 0))) as R15.
           do 6 step. rewrite setup_be16.
           remember (bz (nth (Z.to_nat 14) (skipn 1 pl) (Z_to_bv 8 0)) * 256 +
                     bz (nth (Z.to_nat 15) (skipn 1 pl) (Z_to_bv 8 0))) as nb eqn:Hnb.
           destruct (Z_lt_le_dec nb 16) as [B16 | B16].
           ++ take true. step.
              setup_empty CINIT buf (Z.of_nat (length pl) - 1).
           ++ take false. do 2 step.
              destruct (Z_le_gt_dec nb (Z.of_nat (length pl) + -15)) as [G | G].
              ** (* the frame's nb - 16 bytes at buf + 30 *)
                 take true. do 3 step.
                 assert (Hbl : Z.of_nat (length (firstn (Z.to_nat (nb - 16)) (skipn 30 (skipn 1 pl)))) = nb - 16)
                   by (rewrite length_firstn, !length_skipn; lia).
                 pose proof (setup_bytes_sub rsegs m2 buf (skipn 1 pl) 30 (Z.to_nat (nb - 16)) BB
                   ltac:(rewrite length_skipn; lia)) as BF.
                 change (Z.of_nat 30) with 30 in BF.
                 eapply (setup_tail CINIT) with (bb := firstn (Z.to_nat (nb - 16)) (skipn 30 (skipn 1 pl)))
                   (body := buf + 30) (L := nb + -16) (buf := buf) (n := Z.of_nat (length pl) - 1).
                 all: try first [ exact FR8 | exact K | exact MU | exact WM | exact MI2 | exact ST | exact BF ].
                 all: try first [ lia | (unfold seg_ok; rewrite Hbl; repeat split; lia)
                                | (unfold lo_ok; rewrite Hbl; repeat split; lia) ].
              ** take false. step.
                 setup_empty CINIT buf (Z.of_nat (length pl) - 1).
        -- take true. step.
           setup_empty CINIT buf (Z.of_nat (length pl) - 1).
Qed.

(* ---- the set-up of the decoder loop ---- *)

(* the 312 bytes of structs as the decoder loop's cells *)
Lemma dsetup_frame5 : forall segs m Sp hd jj saved, rw_cells segs m Sp (hd ++ CB 312 jj :: saved) ->
  exists oj jE jM dj jC, rw_cells segs m Sp (hd ++ CB 120 oj :: CB 80 jE :: CB 40 jM :: CB 40 dj :: CB 32 jC :: saved).
Proof.
  intros segs m Sp hd jj saved H.
  apply (rw_cells_split_CB segs m Sp hd 312 jj saved [120;80;40;40;32]%nat) in H; [|reflexivity].
  cbn [mk_CB_cells app] in H. do 5 eexists. exact H.
Qed.

(* the personality index of a DESK entry is NULL, personalities[0] or personalities[1] *)
Lemma dsetup_pers_range : forall d, d = 0 \/ d = 1 \/ d = 2 ->
  forall i, diginet_personality_of d = Some i -> 0 <= i < 2.
Proof.
  intros d Hd i Hi. destruct Hd as [-> | [-> | ->]].
  - replace (diginet_personality_of 0) with (@None Z) in Hi by (vm_compute; reflexivity). discriminate.
  - replace (diginet_personality_of 1) with (Some 0) in Hi by (vm_compute; reflexivity). injection Hi as <-. lia.
  - replace (diginet_personality_of 2) with (Some 1) in Hi by (vm_compute; reflexivity). injection Hi as <-. lia.
Qed.

(* from 0x1305c (a0 = DESK[sel % 3]): diginet_personality_of, diginet_decoder_init and the loop's registers *)
Lemma dsetup_rest : diginet_personality_of_contract -> diginet_decoder_init_contract ->
  forall (desk : Z)
    (r1 x3 x4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp lo body : Z) (bb j0 oj jE jM dj jC : list byte) (w8 w10 : word) (saved : list cell)
    (Q : machine_state -> Prop),
  desk = 0 \/ desk = 1 \/ desk = 2 ->
  seg_ok Sp body bb -> lo_ok lo Sp body bb ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (CB 8 j0 :: C8 w8 :: C8 w10 :: C8 (Z_to_bv 64 (body + 1)) :: CB 120 oj :: CB 80 jE ::
    CB 40 jM :: CB 40 dj :: CB 32 jC :: saved) ->
  dhead0 Q x3 x4 F fc m0 Sp lo body bb j0 w10 saved ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 (Z_to_bv 64 desk) r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x1305c) fc None m (seg_rom rsegs)).
Proof.
  intros PERS DINIT desk r1 x3 x4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29
    r30 r31 F fc m0 m Sp lo body bb j0 oj jE jM dj jC w8 w10 saved Q HD SEG LO MU WM MI ST BA FR K.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26). pose proof LO as (LO0 & LO1 & LO2).
  (* p = diginet_personality_of (desk) *)
  step.
  eapply evt_cut.
  { apply (PERS (Z_to_bv 64 77920) (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15 r16 r17
      (Z_to_bv 64 (Z.of_nat (length bb))) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F fc m desk).
    lia. }
  intros ms' (a1' & a2' & ->).
  replace (ret_pc (Z_to_bv 64 77920)) with (Z_to_bv 64 77920) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* diginet_decoder_init (&d, p, body, len) *)
  do 5 step.
  pose proof (setup_fh_mid rsegs m Sp [CB 8 j0; C8 w8; C8 w10; C8 (Z_to_bv 64 (body + 1)); CB 120 oj; CB 80 jE; CB 40 jM]
    [CB 40 dj] (CB 32 jC :: saved) FR) as FD.
  change (Sp + Z.of_nat (cells_size [CB 8 j0; C8 w8; C8 w10; C8 (Z_to_bv 64 (body + 1)); CB 120 oj; CB 80 jE; CB 40 jM]))
    with (Sp + 272) in FD.
  eapply evt_cut.
  { eapply DINIT with (lo := lo) (dj := dj).
    - lia.
    - lia.
    - lia.
    - lia.
    - apply dsetup_pers_range. exact HD.
    - exact FD.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact MI. }
  intros ms' (a0' & a1'' & a2'' & a3' & m1 & -> & MU1 & WM1 & MI1 & ST1 & RD).
  rewrite !unsigned_lit in MU1, ST1 by lia.
  replace (ret_pc (Z_to_bv 64 77940)) with (Z_to_bv 64 77940) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (setup_fh_put rsegs [(Sp + 272, Sp + 272 + 40); (Sp - 32, Sp)] m m1 Sp
    [CB 8 j0; C8 w8; C8 w10; C8 (Z_to_bv 64 (body + 1)); CB 120 oj; CB 80 jE; CB 40 jM] [CB 40 dj]
    (decoder_cells body (firstn 7 (skipn 25 dj)) (diginet_decoder_init (diginet_personality_of desk) (Z.of_nat (length bb))))
    (CB 32 jC :: saved) FR MU1 WM1) as FR1.
  change (cells_size [CB 8 j0; C8 w8; C8 w10; C8 (Z_to_bv 64 (body + 1)); CB 120 oj; CB 80 jE; CB 40 jM]) with 272%nat in FR1.
  change (Z.of_nat 272) with 272 in FR1.
  specialize (FR1 ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from cells_size csize]; lia) RD eq_refl).
  clear FR FD RD.
  apply (bytes_at_transport rsegs [(Sp + 272, Sp + 272 + 40); (Sp - 32, Sp)] m m1) in BA;
    [| exact MU1 | cbn [disjoint_from]; lia].
  apply (munch_trans _ m0 m m1) in MU;
    [| apply (munch_weaken [(Sp + 272, Sp + 272 + 40); (Sp - 32, Sp)]);
       [unfold sub_fp, loop_fp; cbn [outside]; intros; lia | exact MU1]].
  apply (wmono_trans rsegs m0 m m1) in WM; [| exact WM1].
  clear MU1 WM1 MI ST.
  cbn [app] in FR1. unfold loop_fp in MU.
  (* the loop's registers and sd 0x103a4, 8(sp) *)
  do 10 step.
  rewrite (unsigned_lit (Z.of_nat (length bb))) by lia.
  replace (0 - Z.of_nat (length bb)) with (- Z.of_nat (length bb)) by lia.
  unfold dhead0 in K.
  eapply (K (dd_p (diginet_decoder_init (diginet_personality_of desk) (Z.of_nat (length bb)))) oj jE jM
    (firstn 7 (skipn 25 dj)) jC); [exact MU | exact WM | exact MI1 | exact ST1 | exact BA | exact FR1].
Qed.

Theorem dsetup_holds : dsetup_stmt.
Proof.
  unfold dsetup_stmt.
  intros PERS DINIT r1 x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29
    r30 r31 F fc m Sp lo body bb j0 jj sel w10 saved Q SEG LO HSV MI ST BA FR K.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26). pose proof LO as (LO0 & LO1 & LO2).
  pose proof (munch_refl (loop_fp lo Sp) m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold fr_head in FR.
  destruct (dsetup_frame5 rsegs m Sp _ jj saved FR) as (oj & jE & jM & dj & jC & FR5). clear FR.
  cbn [app] in FR5.
  (* ld sel, the remainder by mul 0xab / srli 9, the address of DESK[sel % 3] *)
  do 13 step.
  (* the address is 0x103d8 + 4 (sel mod 3): checked over the 256 values of sel *)
  match goal with |- context [Z_to_bv 64 (66520 + ?e)] =>
    let H := fresh "HA" in
    assert (H : Z_to_bv 64 (66520 + e) = Z_to_bv 64 (66520 + 4 * (bz sel mod 3)));
    [ generalize sel;
      match goal with |- forall b : byte, @?L b = @?R b =>
        let HB := fresh in
        assert (HB : forall b : byte, (fun b => Z.eqb (bv_unsigned (L b)) (bv_unsigned (R b))) b = true)
          by (apply setup_byte_all; vm_compute; reflexivity);
        let b := fresh "b" in
        intros b; specialize (HB b); cbv beta in HB; apply Z.eqb_eq in HB; apply bv_eq; exact HB
      end
    | rewrite H; clear H ]
  end.
  pose proof (setup_bz_range sel) as RS.
  assert (H3 : bz sel mod 3 = 0 \/ bz sel mod 3 = 1 \/ bz sel mod 3 = 2) by lia.
  (* lw DESK[sel % 3] from .rodata: 0, 1, 2 *)
  destruct H3 as [H3 | [H3 | H3]]; rewrite H3; change (66520 + 4 * 0) with 66520; change (66520 + 4 * 1) with 66524;
    change (66520 + 4 * 2) with 66528; step.
  - eapply (dsetup_rest PERS DINIT 0).
    all: first [ (left; reflexivity) | eassumption ].
  - eapply (dsetup_rest PERS DINIT 1).
    all: first [ (right; left; reflexivity) | eassumption ].
  - eapply (dsetup_rest PERS DINIT 2).
    all: first [ (right; right; reflexivity) | eassumption ].
Qed.
