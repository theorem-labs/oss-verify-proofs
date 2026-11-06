(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the instruction walks (evt) of the front of LLVMFuzzerTestOneInput on the UBSan
   image (fuzz_decode.ubsan, entry 0x12cfc), the two stretches on either side of the harness's one malloc call. For
   the payload size n (1 <= n < 2^26, a1 at the entry) the harness's own length is n - 1 and the block is
   max (n - 1) 1 bytes (fuzz.h fuzz_dup: malloc (n ? n : 1)).
   - ft_en1, 0x12cfc - 0x12d68: the prologue (frame 0x1f0, thirteen saves at sp + 0x188), the size test 0x12d44
     (not taken for 1 <= n < 2^26), the UBSan checks of data, 0x12d50 `beq s3, -1` and 0x12d54 `beqz s3`, not
     taken because data is the driver's block (4096 <= data, data + n below the stack), sel = data[0] (0x12d58
     `lb`), s1 = n - 1, a0 = s1 + (s1 = 0), and the call of malloc at 0x12d68 (ra 0x12d6c); it ends in q_f1.
   - ft_en2, 0x12d6c - 0x12df8: the NULL test 0x12d6c to the abort at 0x1345c (not taken: the block is at 4096
     or above), buf at sp + 8 (0x12d74), the copy memcpy (buf, data + 1, n - 1) at 0x12d88 (skipped for n = 1 at
     0x12d78), and the inlined spec_read_frame: the body-mode branch 0x12d8c `bgez s0`, the refusal tests 0x12d94
     (n - 1 < 30), 0x12dc0 (be16 (buf + 12) <> 0x885f), 0x12de4 / 0x12dec (nb < 16, n - 15 < nb, nb = be16
     (buf + 14)) that leave len = 0 at 0x12df0, and the accepted frame 0x133d8 - 0x13458 (body = buf + 30,
     len = nb - 16) back to 0x12df8; it ends in q_f2. Its UBSan checks are not taken because buf is the malloc
     block, so 4096 <= buf and buf + 31 < 2^63: 0x12d9c, 0x12da4, 0x12dc8, 0x12dcc (buf + 12 .. buf + 15), the
     twelve of 0x133dc - 0x13434 (buf + k, k <= 31) and 0x1344c in the spec_sum loop (ft_loop; buf + 30 + i for
     i below the body length, no load).
   q_f2 does not say which of the three outcomes (body mode, refused frame, accepted frame) happened: it gives the
   body in s2, its length in s1 and its bytes inside the block. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import memcpy_c FrameBytes.
Import ListNotations.
Open Scope Z_scope.

Lemma ft_uneg : forall e, -2 ^ 64 <= e < 0 -> bv_unsigned (Z_to_bv 64 e) = e + 2 ^ 64.
Proof.
  intros e He. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite <- (Z.mod_add e 1) by lia. apply Z.mod_small. lia.
Qed.

(* the unsigned value of every word literal in a branch condition *)
Ltac ft_ulit := repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (unsigned_lit e) by lia | rewrite (ft_uneg e) by lia ]
  end.

(* decide the branch at the pc by the arithmetic facts in the context *)
Ltac ft_cnd b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; ft_ulit;
                                    solve_cond_rec]
  end.

Ltac ft_cases H := if_cases H; cbv iota.

Lemma ft_bytes_nil : forall m a, 0 <= a <= 2 ^ 64 -> bytes_at rsegs m a [].
Proof. intros m a Ha. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma ft_cells_bytes : forall m A k bs, rw_cells rsegs m A [CB k bs] -> bytes_at rsegs m A bs.
Proof. intros m A k bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

(* s1 + (s1 = 0) (0x12d60 `seqz`, 0x12d64 `add`) is max s1 1 *)
Lemma ft_nn_eq : forall x, 0 <= x < 2 ^ 63 -> x + bv_unsigned (v_sltiu (Z_to_bv 64 x) 1) = Z.max x 1.
Proof.
  intros x Hx. unfold v_sltiu. rewrite (unsigned_lit x) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec x 1); [rewrite (unsigned_lit 1) by lia | rewrite (unsigned_lit 0) by lia]; lia.
Qed.

(* `not a1, s2` (0x13448) *)
Lemma ft_not : forall x, 0 <= x < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) = 18446744073709551615 - x.
Proof. intros x Hx. rewrite (unsigned_lit x) by lia. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia. Qed.

(* the state at the entry of malloc (0x15028, ra 0x12d6c): sp = Sp, s1 = n - 1, s2 = n, s3 = data, a0 the size of
   the block; the saved registers w at Sp + 0x188 under 392 bytes of junk; only the frame was written *)
Definition q_f1 (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp P n : Z) (w : list cell) (ms : machine_state) : Prop :=
  exists R m' j, ms = MS R F (Z_to_bv 64 0x15028) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12d6c /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 10 = Z_to_bv 64 (Z.max (n - 1) 1) /\ reg_get R 9 = Z_to_bv 64 (n - 1) /\
    reg_get R 18 = Z_to_bv 64 n /\ reg_get R 19 = Z_to_bv 64 P /\
    munch [(Sp, Sp + 496)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' Sp (CB 392 j :: w).

Lemma ft_en1 : forall (ra sp gp tp t0 t1 t2 s0 s1 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
    t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (pl : list byte),
  x10 = Z_to_bv 64 p -> x11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 496 <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 -> mem_inv rsegs m ->
  1 <= Z.of_nat (length pl) < 2 ^ 26 -> bytes_at rsegs m p pl -> 4096 <= p -> p + Z.of_nat (length pl) <= lo ->
  evt rsegs (q_f1 F fc gp tp m (bv_unsigned sp - 496) p (Z.of_nat (length pl))
              [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12cfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo p pl -> -> ST LO Hsp63 MI HN HP HPLO HPL.
  pose proof (munch_refl [(bv_unsigned sp - 496, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ HP) as HPB.
  carve_frame 496%nat ST.
  do 14 step.
  step. step. step. step. step. ft_cnd false.
  step. step. step. ft_cnd false. step. ft_cnd false.
  pose proof (rd1 _ _ _ 0 HP ltac:(lia)) as RB0.
  step. step. step. step. step.
  apply evt_done. unfold q_f1. do 3 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [simp_regs; rewrite ft_nn_eq by lia; f_equal; lia|].
  split; [simp_regs; f_equal; lia|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU]; intros x; cbn [outside]; intros [H _]; split; [lia | exact I]|].
  split; [exact WM | exact FR].
Qed.

(* the state at 0x12df8: sp = Sp, s1 = the body length, s2 = body; the block of nn bytes at buf holds the body's
   bytes bb; buf at Sp + 8; only the frame and the block were written *)
Definition q_f2 (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp buf nn : Z) (w : list cell) (ms : machine_state) : Prop :=
  exists R m' (body : Z) (bb j0 j1 : list byte), ms = MS R F (Z_to_bv 64 0x12df8) fc None m' (seg_rom rsegs) /\
    reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 9 = Z_to_bv 64 (Z.of_nat (length bb)) /\ reg_get R 18 = Z_to_bv 64 body /\
    munch [(Sp, Sp + 496); (buf, buf + nn)] m0 m' /\ wmono rsegs m0 m' /\
    rw_cells rsegs m' Sp (CB 8 j0 :: C8 (Z_to_bv 64 buf) :: CB 376 j1 :: w) /\
    bytes_at rsegs m' body bb /\ buf <= body /\ body + Z.of_nat (length bb) <= buf + nn.

Lemma ft_done : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp buf nn body : Z) (w : list cell) (bb j0 j1 : list byte),
  x2 = Z_to_bv 64 Sp -> x9 = Z_to_bv 64 (Z.of_nat (length bb)) -> x18 = Z_to_bv 64 body ->
  munch [(Sp, Sp + 496); (buf, buf + nn)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m Sp (CB 8 j0 :: C8 (Z_to_bv 64 buf) :: CB 376 j1 :: w) ->
  bytes_at rsegs m body bb -> buf <= body -> body + Z.of_nat (length bb) <= buf + nn ->
  evt rsegs (q_f2 F fc x3 x4 m0 Sp buf nn w)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31) F (Z_to_bv 64 0x12df8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m0 m Sp buf nn body w bb j0 j1 -> -> -> MU WM FR BB Hb1 Hb2.
  apply evt_done. unfold q_f2.
  exists (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (Z.of_nat (length bb))) x10 x11 x12 x13 x14 x15 x16
    x17 (Z_to_bv 64 body) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31), m, body, bb, j0, j1.
  split; [reflexivity|]. do 5 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM|]. split; [exact FR|]. split; [exact BB|]. split; lia.
Qed.

(* 0x1344c - 0x13458: the spec_sum guard loop of the accepted frame, i from the current a0 up to len; `bltu a1, a0`
   to the trap is not taken while i <= a1 (a1 = ~(buf + 30)) *)
Lemma ft_loop : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Q : machine_state -> Prop) (len : Z),
  x9 = Z_to_bv 64 len -> 0 < len -> len <= bv_unsigned x11 + 1 -> len < 2 ^ 64 ->
  (forall x10 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
     x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12df8) fc None m (seg_rom rsegs))) ->
  forall i, 0 <= i < len ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 i) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
     x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1344c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m Q len -> Hl0 Hl1 Hl2 K i Hi.
  pose proof (bv_unsigned_in_range 64 x11) as R11. unfold bv_modulus in R11.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R11.
  remember (Z.to_nat (len - i)) as k eqn:Ek. revert i Hi Ek.
  induction k as [|k IH]; intros i Hi Ek; [lia|].
  step. ft_cnd false.
  step. step.
  destruct (Z.eq_dec (i + 1) len) as [E|E].
  - ft_cnd false. step. apply K.
  - ft_cnd true. apply IH; lia.
Qed.

(* 0x133d8 - 0x13458: the accepted frame, nb = s1 with 16 <= nb and nb + 14 <= len0 (the bytes copied); the twelve
   UBSan checks of buf + k, s1 = nb - 16, s2 = buf + 30, and the spec_sum loop when nb > 16 *)
Lemma ft_acc : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp buf len0 : Z) (w : list cell) (bb0 j0 j1 : list byte),
  x2 = Z_to_bv 64 Sp -> x20 = Z_to_bv 64 buf ->
  16 <= bv_unsigned x9 -> bv_unsigned x9 + 14 <= len0 -> Z.of_nat (length bb0) = len0 ->
  4096 <= buf -> buf + len0 < 2 ^ 63 ->
  munch [(Sp, Sp + 496); (buf, buf + len0)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m Sp (CB 8 j0 :: C8 (Z_to_bv 64 buf) :: CB 376 j1 :: w) -> bytes_at rsegs m buf bb0 ->
  evt rsegs (q_f2 F fc x3 x4 m0 Sp buf len0 w)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31) F (Z_to_bv 64 0x133d8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m0 m Sp buf len0 w bb0 j0 j1 -> -> H16 H14 Hl Hb0 Hb1 MU WM FR BB.
  set (bbody := firstn (Z.to_nat (bv_unsigned x9 - 16)) (skipn 30 bb0)).
  assert (BBb : bytes_at rsegs m (buf + 30) bbody).
  { pose proof BB as BB'. rewrite <- (firstn_skipn 30 bb0) in BB'. apply bytes_at_app in BB' as [_ BB'].
    rewrite firstn_length_le in BB' by lia.
    rewrite <- (firstn_skipn (Z.to_nat (bv_unsigned x9 - 16)) (skipn 30 bb0)) in BB'.
    apply bytes_at_app in BB' as [BB' _]. exact BB'. }
  assert (Lb : Z.of_nat (length bbody) = bv_unsigned x9 - 16).
  { unfold bbody. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
  clearbody bbody.
  step. step. ft_cnd false.
  step. step. ft_cnd false. step. ft_cnd false.
  step. step. ft_cnd false.
  step. step. step. ft_cnd false.
  step. step. ft_cnd false.
  step. step. step. ft_cnd false.
  step. step. ft_cnd false. step. ft_cnd false.
  step. step. ft_cnd false.
  step. step. ft_cnd false.
  step. step. ft_cnd false.
  step. step. step.
  destruct (Z.eq_dec (bv_unsigned x9) 16) as [E16|E16].
  - ft_cnd true.
    eapply ft_done with (body := buf + 30) (bb := bbody); [reflexivity | rewrite Lb; f_equal; lia | reflexivity
      | exact MU | exact WM | exact FR | exact BBb | lia | lia].
  - ft_cnd false. step. step.
    eapply ft_loop with (len := bv_unsigned x9 - 16) (i := 0).
    + f_equal; lia.
    + lia.
    + rewrite ft_not by lia. lia.
    + lia.
    + intros x10'.
      eapply ft_done with (body := buf + 30) (bb := bbody); [reflexivity | rewrite Lb; f_equal; lia | reflexivity
        | exact MU | exact WM | exact FR | exact BBb | lia | lia].
    + lia.
Qed.

(* 0x12de0 - 0x12dec with nb = s1 (be16 (buf + 14)): nb < 16 (0x12de4) or n - 15 < nb (0x12dec) leave len = 0 at
   0x12df0 (body buf); else the accepted frame at 0x133d8 *)
Lemma ft_nb : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp buf n : Z) (w : list cell) (bb0 j0 j1 : list byte),
  x2 = Z_to_bv 64 Sp -> x18 = Z_to_bv 64 n -> x20 = Z_to_bv 64 buf ->
  31 <= n < 2 ^ 26 -> Z.of_nat (length bb0) = n - 1 -> 4096 <= buf -> buf + (n - 1) < 2 ^ 63 ->
  munch [(Sp, Sp + 496); (buf, buf + (n - 1))] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m Sp (CB 8 j0 :: C8 (Z_to_bv 64 buf) :: CB 376 j1 :: w) -> bytes_at rsegs m buf bb0 ->
  evt rsegs (q_f2 F fc x3 x4 m0 Sp buf (n - 1) w)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31) F (Z_to_bv 64 0x12de0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m0 m Sp buf n w bb0 j0 j1 -> -> -> Hn Hl Hb0 Hb1 MU WM FR BB.
  pose proof (bv_unsigned_in_range 64 x9) as R9. unfold bv_modulus in R9.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R9.
  step. step.
  destruct (Z_lt_le_dec (bv_unsigned x9) 16) as [L16|L16].
  - ft_cnd true. step. step.
    eapply ft_done with (body := buf) (bb := []); [reflexivity | reflexivity | reflexivity | exact MU | exact WM
      | exact FR | apply ft_bytes_nil; lia | lia | cbn; lia].
  - ft_cnd false. step. step.
    destruct (Z_le_gt_dec (bv_unsigned x9) (n - 15)) as [LE|GT].
    + ft_cnd true.
      eapply ft_acc with (bb0 := bb0); [reflexivity | reflexivity | lia | lia | exact Hl | lia | lia | exact MU
        | exact WM | exact FR | exact BB].
    + ft_cnd false. step. step.
      eapply ft_done with (body := buf) (bb := []); [reflexivity | reflexivity | reflexivity | exact MU | exact WM
        | exact FR | apply ft_bytes_nil; lia | lia | cbn; lia].
Qed.

(* 0x12d8c - 0x12ddc, after the copy of the n - 1 >= 1 bytes bb0 to buf: sel >= 0 (0x12d8c) is the body mode
   (body buf, len n - 1); else n - 1 < 30 (0x12d94) and be16 (buf + 12) <> 0x885f (0x12dc0) leave len = 0 at
   0x12df0; else nb = be16 (buf + 14) goes to ft_nb. The UBSan checks 0x12d9c, 0x12da4 (buf + 12, + 13) and
   0x12dc8, 0x12dcc (buf + 14, + 15) are not taken *)
Lemma ft_frame : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp buf n : Z) (w : list cell) (bb0 j0 j1 : list byte),
  x2 = Z_to_bv 64 Sp -> x9 = Z_to_bv 64 (n - 1) -> x18 = Z_to_bv 64 n -> x20 = Z_to_bv 64 buf ->
  2 <= n < 2 ^ 26 -> Z.of_nat (length bb0) = n - 1 -> 4096 <= buf -> buf + (n - 1) < 2 ^ 63 ->
  munch [(Sp, Sp + 496); (buf, buf + (n - 1))] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m Sp (CB 8 j0 :: C8 (Z_to_bv 64 buf) :: CB 376 j1 :: w) -> bytes_at rsegs m buf bb0 ->
  evt rsegs (q_f2 F fc x3 x4 m0 Sp buf (n - 1) w)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31) F (Z_to_bv 64 0x12d8c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m0 m Sp buf n w bb0 j0 j1 -> -> -> -> Hn Hl Hb0 Hb1 MU WM FR BB.
  step. ft_cases HC.
  - step.
    eapply ft_done with (body := buf) (bb := bb0); [reflexivity | rewrite Hl; reflexivity | reflexivity
      | exact MU | exact WM | exact FR | exact BB | lia | lia].
  - step. step.
    destruct (Z_lt_le_dec (n - 1) 30) as [L30|L30].
    + ft_cnd true. step. step.
      eapply ft_done with (body := buf) (bb := []); [reflexivity | reflexivity | reflexivity | exact MU | exact WM
        | exact FR | apply ft_bytes_nil; lia | lia | cbn; lia].
    + ft_cnd false.
      pose proof (rd1 _ _ _ 12 BB ltac:(lia)) as RB12. pose proof (rd1 _ _ _ 13 BB ltac:(lia)) as RB13.
      pose proof (rd1 _ _ _ 14 BB ltac:(lia)) as RB14. pose proof (rd1 _ _ _ 15 BB ltac:(lia)) as RB15.
      change (Z.of_nat 12) with 12 in RB12. change (Z.of_nat 13) with 13 in RB13.
      change (Z.of_nat 14) with 14 in RB14. change (Z.of_nat 15) with 15 in RB15.
      step. step. ft_cnd false.
      step. step. ft_cnd false.
      step. step. step. step. step. step. step.
      ft_cases HC2.
      * step. step.
        eapply ft_done with (body := buf) (bb := []); [reflexivity | reflexivity | reflexivity | exact MU
          | exact WM | exact FR | apply ft_bytes_nil; lia | lia | cbn; lia].
      * step. step. ft_cnd false. step. ft_cnd false.
        step. step. step. step.
        eapply ft_nb with (bb0 := bb0); [reflexivity | reflexivity | reflexivity | lia | exact Hl | lia | lia
          | exact MU | exact WM | exact FR | exact BB].
Qed.

(* 0x12d6c - 0x12d88 after malloc returned buf, then the copy and ft_frame. The block is nn = max (n - 1) 1 bytes;
   the frame cells and the payload are below Sp, apart from the block *)
Lemma ft_en2 : memcpy_contract ->
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sp buf n p : Z)
    (pl : list byte) (w : list cell) (j junk : list byte),
  x2 = Z_to_bv 64 Sp -> x9 = Z_to_bv 64 (n - 1) -> x10 = Z_to_bv 64 buf -> x18 = Z_to_bv 64 n ->
  x19 = Z_to_bv 64 p ->
  Z.of_nat (length pl) = n -> 1 <= n < 2 ^ 26 -> 4096 <= p -> 4096 <= buf ->
  buf + Z.max (n - 1) 1 <= Sp -> p + n <= Sp -> Sp + 496 < 2 ^ 63 ->
  p + n <= buf \/ buf + Z.max (n - 1) 1 <= p -> cells_size w = 104%nat ->
  mem_inv rsegs m -> bytes_at rsegs m p pl -> rw_cells rsegs m buf [CB (Z.to_nat (Z.max (n - 1) 1)) junk] ->
  rw_cells rsegs m Sp (CB 392 j :: w) ->
  evt rsegs (q_f2 F fc x3 x4 m Sp buf (Z.max (n - 1) 1) w)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31) F (Z_to_bv 64 0x12d6c) fc None m (seg_rom rsegs)).
Proof.
  intros MC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m Sp buf n p pl w j junk -> -> -> -> -> Hl Hn Hp Hb Hbs Hps Hsp Hd Hw MI HP HB FR.
  assert (HPs : bytes_at rsegs m (p + 1) (skipn 1 pl)).
  { pose proof HP as HP'. rewrite <- (firstn_skipn 1 pl) in HP'. apply bytes_at_app in HP' as [_ HP'].
    rewrite firstn_length_le in HP' by lia. exact HP'. }
  assert (Ls : Z.of_nat (length (skipn 1 pl)) = n - 1) by (rewrite length_skipn; lia).
  clear HP.
  pose proof (munch_refl [(Sp, Sp + 496); (buf, buf + Z.max (n - 1) 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. ft_cnd false.
  step. step.
  step.
  destruct (Z.eq_dec n 1) as [E1|E1].
  - ft_cnd true. step.
    eapply ft_done with (body := buf) (bb := []); [reflexivity | rewrite E1; reflexivity | reflexivity | exact MU
      | exact WM | exact FR | apply ft_bytes_nil; lia | lia | cbn; lia].
  - ft_cnd false.
    replace (Z.max (n - 1) 1) with (n - 1) in * by lia.
    step. step. step. step.
    eapply evt_cut.
    { eapply MC with (src := skipn 1 pl) (junk := junk).
      - rewrite (unsigned_lit (p + 1)) by lia. exact HPs.
      - rewrite (unsigned_lit (n - 1)) by lia. lia.
      - rewrite (unsigned_lit buf), (unsigned_lit (n - 1)) by lia. exact HB.
      - rewrite (unsigned_lit buf), (unsigned_lit (n - 1)), (unsigned_lit (p + 1)) by lia. lia.
      - exact MI. }
    intros ms1 (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1
      & HF1 & HS1).
    replace (ret_pc (Z_to_bv 64 77196)) with (Z_to_bv 64 77196) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite !unsigned_lit in MU1 by lia. rewrite !unsigned_lit in HF1 by lia.
    pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU1 WM1
      ltac:(cbn [disjoint_from cells_size csize]; rewrite Hw; split; [lia | exact I])) as FR1.
    assert (MU2 : munch [(Sp, Sp + 496); (buf, buf + (n - 1))] m m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU1].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & _). split; [exact H2 | exact I]. }
    pose proof (wmono_trans rsegs _ _ _ WM WM1) as WM2.
    pose proof (ft_cells_bytes _ _ _ _ HF1) as BB1.
    eapply ft_frame with (bb0 := skipn 1 pl); [reflexivity | reflexivity | reflexivity | reflexivity | lia
      | exact Ls | lia | lia | exact MU2 | exact WM2 | exact FR1 | exact BB1].
Qed.
