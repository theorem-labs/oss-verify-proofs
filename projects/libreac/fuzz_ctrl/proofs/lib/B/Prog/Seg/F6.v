(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1665 of its 1776 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F5.v, with its addresses and numbers changed; 477 of its 613 lines of code are new or changed and 1640 lines of the source are left out. *)
(* Segment F6 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan build of libreac v1.9.0, image B), frame-loop turn j:
   the 32-byte block sum of a long record (0x82098-0x820c4, back edge 0x820c4), the two instrumented byte checks of
   the record's bytes 16 and 17, the abort compare of 0x82138 and the second reac_ctrl_parse call. rule 24: no
   function proved (a slot segment).

   F6 is the long-frame arm. Its entry 0x82098 is the head of the byte-sum loop, its exit 0x8215c the return
   point of the parse call 0x82158:
     0x82098 add  a5,a3,a4      the ubsan end test of the cursor: a3 = -(Phi + 18), a4 = the turns left
     0x8209c beq  a5,a7,82fa0   a7 = 32; a5 = 32 - (Phi + 18 + i) is never 32 (Phi + 18 + i <> 0): not taken
     0x820a0 srli a5,a0,0x3     the instrumented 1-byte check of [a0] = [Phi + 18 + i]
     0x820a4 add  a5,a5,s10     s10 = ASAN_K (FRA)
     0x820a8 lb   a5,0(a5)
     0x820ac bnez a5,820cc      the slow path 0x820cc-0x820d0; its report 0x83048 is shown NOT reached
     0x820b0 lbu  a5,0(a2)      a1 += the byte; a4 counts 32 down; a0 and a2 advance
     0x820b4 addi a4,a4,-1
     0x820b8 addi a0,a0,1
     0x820bc add  a1,a1,a5
     0x820c0 addi a2,a2,1
     0x820c4 bnez a4,82098      the back edge: 32 turns, inside this lemma (the entry cut holds for the first
                                turn only, so no loop cut is handed to the assembly)
     0x820c8 j    820d8
     0x820d8 sd   t0,312(s1)    [A+312] = Phi + 18 (t0 from F4's 0x82074), the long arm's blk spill
     0x820dc-0x820e0            the ubsan pointer test `li a0,-17 ; bltu a0,s2,82fa0`: Phi <= 2^64 - 50, not taken
     0x820e4-0x820f4            the instrumented check of [Phi + 16] (slow path 0x82dd4, report 0x830b4 NOT reached)
     0x820f8-0x82104            byte 16 <> 0: [A+184] = 0 and on to 0x82130
     0x82108-0x8212c            byte 16 = 0: the same for [Phi + 17] (slow path 0x82e4c, report 0x830d4), then
                                [A+184] = (byte 17 = 0); so [A+184] = b2z (t_tfill j) on both arms
     0x82130 snez a0,s8         s8 = t_k j
     0x82134 ld   a2,272(s1)    [A+272] = b2z (t_8819 j) = (t_k j <> 0): the compare 0x82138 is NOT taken
     0x8213c-0x82148            s9 = (low byte of the sum = 0) = b2z (t_sum_ok j), [A+248] = its negation
     0x8214c-0x82158            the parse call block, proved once in lib/B/Prog/Seg/F5.v (seg_c)
   v1.9.0 against the patched image: the same loop and checks 0x70 bytes later; the fill flag is the spill [A+184]
   (was s5), the sum flag is s9 = b2z sum_ok (was [A+288]) and its negation the spill [A+248] (was s9).
   The three stores write the save-area words [A+312, A+320), [A+184, A+192) and [A+248, A+256): FRA and ENT move
   across them by F5's c_fra_spill (Tac_slot's sl_stk_run and ent_store), the frame-loop bundles by F5's
   c_spill_keep / c_lk_keep / c_fsj_keep / c_fturn_keep / c_rec0_keep / c_fps_keep.

   REUSE. The parse call 0x8214c-0x82158 is F5's seg_c (the join cut Inv_B8214c_join is F5's, internal to that
   unit; F5 and F6 compose through it), and every memory / register transport is one of F5's c_* lemmas. The
   loop induction follows image A's donor lib/A/Prog/Seg/F6.v (f6_loop, f6_e28_evt, seg_F6_e28 on
   a working branch 37567279f57): same model facts (f6_tf is the donor's f6_s9, f6_tfill / f6_sum /
   f6_8819_eq are its f6_tfill / f6_sum / f6_8819_eq), same per-turn shadow-check shape. Image B adds the ubsan
   tests (0x8209c, 0x820e0 and 0x8210c) the donor has not, and keeps the flags in the save area.

   CUTS. seg_F6 is S_F6 of a Theorem Labs lane's forms-asan-ubsan-v190.md (a working note, not in this delivery) over the official cuts of SlotInv.v (
   217aa9d4cd9): Inv_B82098_at is FCUTP at 0x82098 with 50 <= flen g j, s8 = t_k j, a0 = a2 = t0 = Phi + 18,
   a1 = 0, a3 = -(Phi + 18), a4 = a7 = 32, and Inv_B8215c_at is the parse return point. No cut text is defined
   here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib RcLib RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs F5.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* The value functions of the lib/Lib step engine (another loaded PropExec has the same short names;
   a Theorem Labs lane's F4.v binds it the same way). *)
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

(* ================= small bit and byte facts (image A's donor f6_* ) ================= *)

Lemma f6_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

(* seqz: v_sltiu w 1 is the 0/1 indicator of (w = 0). *)
Lemma f6_seqz : forall w : word, LP.v_sltiu w 1 = Z_to_bv 64 (if bv_unsigned w =? 0 then 1 else 0).
Proof.
  intros w. unfold LP.v_sltiu. change (bv_wrap 64 1) with 1%Z.
  pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr.
  replace (bv_unsigned w <? 1) with (bv_unsigned w =? 0)
    by (destruct (Z.eqb_spec (bv_unsigned w) 0); destruct (Z.ltb_spec (bv_unsigned w) 1); lia).
  destruct (bv_unsigned w =? 0); reflexivity.
Qed.

(* snez: v_sltu 0 w is the 0/1 indicator of (w <> 0). *)
Lemma f6_snez : forall w : word, LP.v_sltu (Z_to_bv 64 0) w = Z_to_bv 64 (if bv_unsigned w =? 0 then 0 else 1).
Proof.
  intros w. unfold LP.v_sltu, LP.c_ltu, bv_ltu. rewrite MState.unsigned_lit by lia.
  pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr.
  destruct (Z.eqb_spec (bv_unsigned w) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (0 <? bv_unsigned w) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* zext.b: the low byte of a value. *)
Lemma f6_land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma f6_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply MState.unsigned_lit. pose proof (f6_byte_range b). lia. Qed.

Lemma f6_nth_skipn : forall (A : Type) (d : A) (n : nat) (l : list A) (i : nat),
  nth i (skipn n l) d = nth (n + i) l d.
Proof.
  intros A d n. induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|a l]; cbn [skipn nth]; [destruct i; reflexivity | apply IH].
Qed.

(* One instrumented 1-byte shadow read of an addressable byte X: the shadow byte b is readable at
   (X >> 3) + ASAN_K and passes the check (b = 0, or X mod 8 < b). Image A's Tac_b5 sl_shadow1, over image B's
   AsanRTFacts.meta_byte. *)
Lemma f6_shadow1 : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

(* ================= the branch tests of the segment ================= *)

(* A branch of this segment whose two sides are 64-bit literals: the test reads the values modulo 2^64. *)
Ltac f6_cond :=
  unfold bv_eqb, bv_ltu, bv_leu; cbn [negb];
  rewrite ?MState.unsigned_lit_wrap;
  first [ reflexivity
        | apply Z.ltb_lt; try (Z.div_mod_to_equations); lia
        | apply Z.ltb_ge; try (Z.div_mod_to_equations); lia
        | apply Z.eqb_eq; try (Z.div_mod_to_equations); lia
        | apply Z.eqb_neq; try (Z.div_mod_to_equations); lia
        | apply (proj2 (Bool.negb_true_iff _));
          first [ apply Z.ltb_ge; try (Z.div_mod_to_equations); lia
                | apply Z.eqb_neq; try (Z.div_mod_to_equations); lia ]
        | apply (proj2 (Bool.negb_false_iff _));
          first [ apply Z.ltb_lt; try (Z.div_mod_to_equations); lia
                | apply Z.eqb_eq; try (Z.div_mod_to_equations); lia ] ].

(* The branch is not taken. *)
Ltac f6_nt :=
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; f6_cond]
  end.

(* The branch is taken. *)
Ltac f6_tk :=
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; f6_cond]
  end.

(* ================= the model flags the segment computes ================= *)

(* The tfill flag of a long record: both its bytes 16 and 17 are zero ([A+184] at 0x82100 / 0x8212c). *)
Definition f6_tf (bs : list byte) : Z :=
  if bv_unsigned (nth 16 bs (Z_to_bv 8 0)) =? 0
  then (if bv_unsigned (nth 17 bs (Z_to_bv 8 0)) =? 0 then 1 else 0) else 0.

Lemma f6_tfill : forall inp j, t_big inp j = true -> b2z (t_tfill inp j) = f6_tf (t_g inp j).
Proof.
  intros inp j Hb. unfold t_tfill, f6_tf, b2z, cp_v, cp_b, cp_z. rewrite Hb. cbn [andb].
  destruct (bv_unsigned (nth 16 (t_g inp j) (Z_to_bv 8 0)) =? 0);
    destruct (bv_unsigned (nth 17 (t_g inp j) (Z_to_bv 8 0)) =? 0); reflexivity.
Qed.

Lemma f6_sum : forall inp j, t_big inp j = true ->
  b2z (t_sum_ok inp j) = (if psum (skipn 18 (t_g inp j)) 32 mod 256 =? 0 then 1 else 0).
Proof.
  intros inp j Hb. unfold t_sum_ok, blocksum, b2z. rewrite Hb. cbn [andb].
  destruct (psum (skipn 18 (t_g inp j)) 32 mod 256 =? 0); reflexivity.
Qed.

Lemma f6_t8819_hdr : forall inp j, t_8819 inp j = cp_hdr (t_len inp j) (t_g inp j).
Proof. intros inp j. unfold t_8819, t_big, cp_hdr. reflexivity. Qed.

(* The 0x82138 abort comparison: snez s8 with s8 = t_k j equals the carried [A+272] = b2z (t_8819 j). *)
Lemma f6_8819_eq : forall inp j, (if bv_unsigned (Z_to_bv 64 (t_k inp j)) =? 0 then 0 else 1) = b2z (t_8819 inp j).
Proof.
  intros inp j. pose proof (ctrlparse_kind_range (t_len inp j) (t_g inp j)) as HR.
  unfold t_k in *. rewrite MState.unsigned_lit by lia.
  unfold b2z. rewrite f6_t8819_hdr.
  destruct (cp_hdr (t_len inp j) (t_g inp j)) eqn:E.
  - assert (Hne : fst (ctrlparse (t_len inp j) (t_g inp j)) <> 0).
    { intro Z0. apply (proj1 (ctrlparse_none _ _)) in Z0. apply Z0. apply (proj1 (cp_hdr_spec _ _)). exact E. }
    replace (fst (ctrlparse (t_len inp j) (t_g inp j)) =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
  - assert (H0 : fst (ctrlparse (t_len inp j) (t_g inp j)) = 0).
    { apply ctrlparse_none. rewrite <- cp_hdr_spec. rewrite E. discriminate. }
    rewrite H0. reflexivity.
Qed.

(* ================= the block-sum loop 0x82098 -> 0x820d8 ================= *)

(* 32 turns, accumulating a1 = psum over [Phi + 18, Phi + 50). Each turn runs the ubsan end test (a3 + a4 = 32
   only if Phi + 18 + i = 0, which the record's addressability excludes) and the instrumented shadow check of
   the byte (slow path 0x820cc, report 0x83048 shown NOT reached), then a1 += the byte. Image A's f6_loop. *)
Lemma f6_loop : forall (ra0 sp gp tp t1 t2 s0 s1v s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  (forall y0 y2 y4 y5 y6 : word,
     LE.evt rsegs Q (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 s1v
         y0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) y2 (Z_to_bv 64 (- (phi + 18))) y4 y5 y6 (Z_to_bv 64 32)
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x820d8) fc None m (seg_rom rsegs))) ->
  forall (n i : nat) (y0 y1 y2 y4 y5 y6 : word), (i + n = 32)%nat -> (0 < n)%nat ->
    y0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> y1 = Z_to_bv 64 (psum (skipn 18 bs) i) ->
    y2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> y4 = Z_to_bv 64 (32 - Z.of_nat i) ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 s1v
         y0 y1 y2 (Z_to_bv 64 (- (phi + 18))) y4 y5 y6 (Z_to_bv 64 32)
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x82098) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t1 t2 s0 s1v s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 Fr fc m phi bs Q
    Hphi0 Hphi50 Hlen HB HA Hjoin n.
  induction n as [|n IH]; intros i y0 y1 y2 y4 y5 y6 Hin Hn E0 E1 E2 E4; [lia|].
  subst y0 y1 y2 y4.
  assert (Hiz : 0 <= Z.of_nat i < 32) by lia.
  assert (Haddr1 : addressable m (phi + 18 + Z.of_nat i) 1).
  { replace (phi + 18 + Z.of_nat i) with (phi + (18 + Z.of_nat i)) by lia.
    apply (addressable_sub m phi 50 (18 + Z.of_nat i) 1 HA); lia. }
  destruct (f6_shadow1 m (phi + 18 + Z.of_nat i) Haddr1) as (sb & RDsb & OKsb & ISsb).
  pose proof (rd_byte rsegs m phi bs (18 + i)%nat HB ltac:(lia)) as RDb.
  replace (Z.of_nat (18 + i)) with (18 + Z.of_nat i) in RDb by lia.
  replace (phi + (18 + Z.of_nat i)) with (phi + 18 + Z.of_nat i) in RDb by lia.
  pose proof (psum_range (skipn 18 bs) i) as PR.
  (* the join at 0x820b0 (the shadow check passed), with the slow path's a5 / a6 generalized *)
  assert (G40 : forall z5 z6 : word,
    LE.evt rsegs Q (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 s1v
       (Z_to_bv 64 (phi + 18 + Z.of_nat i)) (Z_to_bv 64 (psum (skipn 18 bs) i))
       (Z_to_bv 64 (phi + 18 + Z.of_nat i)) (Z_to_bv 64 (- (phi + 18)))
       (Z_to_bv 64 (32 - Z.of_nat i)) z5 z6 (Z_to_bv 64 32)
       s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x820b0) fc None m (seg_rom rsegs))).
  { intros z5 z6.
    step. (* 820b0 lbu a5,0(a2) *)
    step. (* 820b4 addi a4,a4,-1 *)
    step. (* 820b8 addi a0,a0,1 *)
    step. (* 820bc add a1,a1,a5 *)
    rewrite <- (f6_nth_skipn byte (Z_to_bv 8 0) 18 bs i).
    rewrite psum_S_zxb.
    step. (* 820c0 addi a2,a2,1 *)
    step. (* 820c4 bnez a4,82098 *)
    destruct n as [|n'].
    - (* the last turn: a4 = 0, not taken; 0x820c8 j 820d8 *)
      replace i with 31%nat in * by lia.
      f6_nt.
      step. (* 820c8 j 820d8 *)
      apply Hjoin.
    - (* more turns: back to 0x82098 at i + 1 *)
      f6_tk.
      apply (IH (S i)); try lia; try reflexivity; try (f_equal; lia). }
  (* the ubsan end test and the shadow check 0x82098-0x820ac *)
  step. (* 82098 add a5,a3,a4 *)
  step. (* 8209c beq a5,a7,82fa0 *)
  f6_nt.
  step. (* 820a0 srli a5,a0,3 *)
  step. (* 820a4 add a5,a5,s10 *)
  rewrite (MState.unsigned_lit (phi + 18 + Z.of_nat i)) by lia.
  step. (* 820a8 lb a5,0(a5) *)
  step. (* 820ac bnez a5,820cc *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb)) by (pose proof (rc_byte_signed sb); lia).
  destruct (Z.eqb_spec (bv_signed sb) 0) as [Z0|Z0].
  - (* shadow 0: not taken, fall to 0x820b0 *)
    cbn [negb]. cbv iota. apply (G40 (Z_to_bv 64 (bv_signed sb)) y6).
  - (* shadow <> 0: the slow path 0x820cc-0x820d0, whose report 0x83048 is not reached *)
    cbn [negb]. cbv iota.
    step. (* 820cc andi a6,a0,7 *)
    rewrite (MState.unsigned_lit (phi + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
    step. (* 820d0 blt a6,a5,820b0 *)
    rewrite (rc_lts_signed ((phi + 18 + Z.of_nat i) mod 8) (bv_signed sb))
      by (pose proof (rc_byte_signed sb); pose proof (Z.mod_pos_bound (phi + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
    replace ((phi + 18 + Z.of_nat i) mod 8 <? bv_signed sb) with true
      by (symmetry; apply Z.ltb_lt; destruct OKsb as [H|H]; lia).
    cbv iota.
    apply (G40 (Z_to_bv 64 (bv_signed sb)) (Z_to_bv 64 ((phi + 18 + Z.of_nat i) mod 8))).
Qed.

(* ================= the run 0x82098 -> 0x8214c over explicit registers ================= *)

(* The 32-byte sum loop, the two instrumented byte checks of Phi+16 / Phi+17 (slow paths 0x82dd4 / 0x82e4c
   shown NOT reached), the three ubsan tests, the abort compare at 0x82138 shown NOT taken ([A+272] = e272 =
   (s8 <> 0)), and the three stores [A+312] = Phi + 18, [A+184] = the tfill flag and [A+248] = (low byte of the
   sum <> 0); s9 = (low byte of the sum = 0).  s8 = v8 (the parse kind), s2 = Phi, s1 = A. Image A's
   f6_e28_evt. *)
Lemma f6_run_evt :
  forall (ra0 sp gp tp t1 t2 s0 a5i a6i s3 s4v s5i s6 s7 s9i s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi A v8 e272 : Z) (bs : list byte),
    0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
    bytes_at rsegs m phi bs -> addressable m phi 50 ->
    0 <= A -> A + 448 <= 2 ^ 64 -> stk rsegs m (A + 184) (A + 320) ->
    0 <= v8 < 2 ^ 64 -> q64 m (A + 272) e272 -> e272 = (if v8 =? 0 then 0 else 1) ->
    phi + 50 <= A -> (forall x, phi <= x < phi + 50 -> shadow_addr x < A) ->
    LE.evt rsegs
      (fun ms' => exists b0 b1 b2 b3 b4 b5 b6 : word,
         ms' = MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
                       b0 b1 b2 b3 b4 b5 b6 (Z_to_bv 64 32)
                       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8)
                       (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 1 else 0))
                       (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x8214c) fc None
                  (write_to_mem
                     (write_to_mem (write_to_mem m (wa (A + 312)) (le8 (Z_to_bv 64 (phi + 18))))
                        (wa (A + 184)) (le8 (Z_to_bv 64 (f6_tf bs))))
                     (wa (A + 248))
                     (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 0 else 1))))
                  (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
               (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 0) (Z_to_bv 64 (phi + 18))
               (Z_to_bv 64 (- (phi + 18))) (Z_to_bv 64 32) a5i a6i (Z_to_bv 64 32)
               (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82098) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t1 t2 s0 a5i a6i s3 s4v s5i s6 s7 s9i s11 t3 t4 t5 t6 Fr fc m phi A v8 e272 bs
    Hphi0 Hphi50 Hlen HB HA HA0 HA448 Hstk Hv8 Hq272 He272 Hsep Hshadow.
  match goal with |- LE.evt _ ?Q _ => set (QE := Q) end.
  set (m1 := write_to_mem m (wa (A + 312)) (le8 (Z_to_bv 64 (phi + 18)))).
  set (m2 := write_to_mem m1 (wa (A + 184)) (le8 (Z_to_bv 64 (f6_tf bs)))).
  set (m3 := write_to_mem m2 (wa (A + 248))
               (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 0 else 1)))).
  (* the three save-area words are byte-backed and writable *)
  assert (HSO : forall m' off, wmono rsegs m m' -> 184 <= off -> off + 8 <= 320 ->
            store_ok rsegs m' (wa (A + off)) 8 = true).
  { intros m' off HW Ho1 Ho2. apply (c_store_ok m m' (A + off) 8); [| exact HW | lia | lia].
    intros k Hk. destruct Hstk as (_ & _ & Hs). change (Z.of_nat 8) with 8 in Hk.
    exact (proj1 (Hs (A + off + k) ltac:(lia))). }
  (* the record and the [A+272] word across the first two stores *)
  assert (MU1 : munch [(A + 312, A + 320)] m m1).
  { subst m1. apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia
      | rewrite length_le8; cbn [inside]; left; lia]. }
  assert (WM1 : wmono rsegs m m1) by (subst m1; apply wmono_write; apply wmono_refl).
  assert (WM2 : wmono rsegs m m2) by (subst m2 m1; apply wmono_write; apply wmono_write; apply wmono_refl).
  assert (HB1 : bytes_at rsegs m1 phi bs).
  { subst m1. apply c_ba_write; [exact HB | lia | rewrite length_le8; lia |].
    rewrite length_le8, Hlen. intros x Hx. left. cbn [Z.of_nat] in Hx. lia. }
  assert (HA1 : addressable m1 phi 50).
  { apply (c_addr_keep [(A + 312, A + 320)] m m1 phi 50 HA MU1).
    intros k Hk. pose proof (Hshadow (phi + k) ltac:(lia)) as Hsk. cbn [outside]. repeat split. lia. }
  assert (HQ272 : q64 m2 (A + 272) e272).
  { subst m2 m1. unfold q64. apply c_ba_write; [| lia | rewrite length_le8; lia |].
    - apply c_ba_write; [exact Hq272 | lia | rewrite length_le8; lia |].
      rewrite !length_le8. intros x Hx. left. cbn [Z.of_nat] in Hx. lia.
    - rewrite !length_le8. intros x Hx. right. cbn [Z.of_nat] in Hx. lia. }
  pose proof (bytes_at_ov_read rsegs m2 (A + 272) (le8 (Z_to_bv 64 e272)) 0 8 HQ272
                ltac:(rewrite length_le8; lia)) as RD272.
  cbn [Z.of_nat] in RD272. rewrite Z.add_0_r, skipn_O, firstn_all2 in RD272 by (rewrite length_le8; lia).
  pose proof (rd_byte rsegs m1 phi bs 16 HB1 ltac:(lia)) as RD16. change (Z.of_nat 16) with 16 in RD16.
  pose proof (rd_byte rsegs m1 phi bs 17 HB1 ltac:(lia)) as RD17. change (Z.of_nat 17) with 17 in RD17.
  assert (Ha16 : addressable m1 (phi + 16) 1) by (apply (addressable_sub m1 phi 50 16 1 HA1); lia).
  destruct (f6_shadow1 m1 (phi + 16) Ha16) as (sb16 & RDs16 & OK16 & IS16).
  assert (Ha17 : addressable m1 (phi + 17) 1) by (apply (addressable_sub m1 phi 50 17 1 HA1); lia).
  destruct (f6_shadow1 m1 (phi + 17) Ha17) as (sb17 & RDs17 & OK17 & IS17).
  assert (HS184 : store_ok rsegs m1 (wa (A + 184)) 8 = true) by (apply (HSO m1 184 WM1); lia).
  assert (HS248 : store_ok rsegs m2 (wa (A + 248)) 8 = true) by (apply (HSO m2 248 WM2); lia).
  pose proof (psum_range (skipn 18 bs) 32) as PRs. change (Z.of_nat 32) with 32 in PRs.
  pose proof (Z.mod_pos_bound (psum (skipn 18 bs) 32) 256 ltac:(lia)) as PRm.
  (* the join at 0x82130: both arms of the byte-16 / byte-17 test, [A+184] = the tfill flag *)
  assert (GA0 : forall d c0 c2 c3 c4 c5 c6 : word, d = Z_to_bv 64 (f6_tf bs) ->
    LE.evt rsegs QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
       c0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) c2 c3 c4 c5 c6 (Z_to_bv 64 32)
       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x82130) fc None (write_to_mem m1 (wa (A + 184)) (le8 d)) (seg_rom rsegs))).
  { intros d c0 c2 c3 c4 c5 c6 Ed. subst d. change (write_to_mem m1 _ _) with m2.
    step. (* 82130 snez a0,s8 *)
    rewrite f6_snez, (MState.unsigned_lit v8) by lia.
    step. (* 82134 ld a2,272(s1) *)
    step. (* 82138 bne a0,a2,82fa4 : not taken *)
    rewrite He272, bv_eqb_refl. cbn [negb]. cbv iota.
    step. (* 8213c andi a0,a1,0xff *)
    rewrite (MState.unsigned_lit (psum (skipn 18 bs) 32)) by lia. rewrite f6_land255.
    step. (* 82140 seqz s9,a0 *)
    rewrite f6_seqz, (MState.unsigned_lit (psum (skipn 18 bs) 32 mod 256)) by lia.
    step. (* 82144 snez a0,a0 *)
    rewrite f6_snez, (MState.unsigned_lit (psum (skipn 18 bs) 32 mod 256)) by lia.
    step. (* 82148 sd a0,248(s1) *)
    lazymatch goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) => change mm with m3 end.
    unfold QE. apply evt_done. do 7 eexists. reflexivity. }
  (* the join at 0x820f8 (the byte-16 shadow check passed) *)
  assert (G88 : forall c2 c3 c4 c5 c6 : word,
    LE.evt rsegs QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
       (Z_to_bv 64 (phi + 16)) (Z_to_bv 64 (psum (skipn 18 bs) 32)) c2 c3 c4 c5 c6 (Z_to_bv 64 32)
       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x820f8) fc None m1 (seg_rom rsegs))).
  { intros c2 c3 c4 c5 c6.
    step. (* 820f8 lbu a0,0(a0) : byte 16 *)
    step. (* 820fc beqz a0,82108 *)
    unfold zxb. rewrite (rc_eqb0_signed (bv_unsigned (nth 16 bs (Z_to_bv 8 0))))
      by (pose proof (f6_byte_range (nth 16 bs (Z_to_bv 8 0))); lia).
    destruct (Z.eqb_spec (bv_unsigned (nth 16 bs (Z_to_bv 8 0))) 0) as [B16|B16].
    - (* byte 16 = 0: the byte-17 check, [A+184] = seqz byte17 *)
      cbv iota.
      assert (GB4 : forall e3 e4 e5 e6 : word,
        LE.evt rsegs QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
           (Z_to_bv 64 (phi + 17)) (Z_to_bv 64 (psum (skipn 18 bs) 32)) (sxb sb17) e3 e4 e5 e6 (Z_to_bv 64 32)
           (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82124) fc None m1 (seg_rom rsegs))).
      { intros e3 e4 e5 e6.
        step. (* 82124 lbu a0,0(a0) : byte 17 *)
        step. (* 82128 seqz a0,a0 *)
        rewrite f6_seqz.
        step. (* 8212c sd a0,184(s1) *)
        apply GA0.
        unfold f6_tf. rewrite B16, Z.eqb_refl. rewrite ?f6_zxb_u.
        rewrite ?(MState.unsigned_lit (bv_unsigned (nth 17 bs (Z_to_bv 8 0))))
          by (pose proof (f6_byte_range (nth 17 bs (Z_to_bv 8 0))); lia).
        reflexivity. }
      step. (* 82108 li a0,-18 *)
      step. (* 8210c bltu a0,s2,82fa0 : not taken *)
      f6_nt.
      step. (* 82110 addi a0,s2,17 *)
      step. (* 82114 srli a2,a0,3 *)
      step. (* 82118 add a2,a2,s10 *)
      rewrite (MState.unsigned_lit (phi + 17)) by lia.
      step. (* 8211c lb a2,0(a2) *)
      step. (* 82120 bnez a2,82e4c *)
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb17)) by (pose proof (rc_byte_signed sb17); lia).
      destruct (Z.eqb_spec (bv_signed sb17) 0) as [Z17|Z17].
      + cbn [negb]. cbv iota. apply (GB4 c3 c4 c5 c6).
      + cbn [negb]. cbv iota.
        step. (* 82e4c andi a3,a0,7 *)
        rewrite (MState.unsigned_lit (phi + 17)) by lia. rewrite rc_land7.
        step. (* 82e50 bge a3,a2,830d4 : not taken *)
        rewrite (rc_lts_signed ((phi + 17) mod 8) (bv_signed sb17))
          by (pose proof (rc_byte_signed sb17); pose proof (Z.mod_pos_bound (phi + 17) 8 ltac:(lia)); lia).
        replace ((phi + 17) mod 8 <? bv_signed sb17) with true
          by (symmetry; apply Z.ltb_lt; destruct OK17 as [H|H]; lia).
        cbn [negb]. cbv iota.
        step. (* 82e54 j 82124 *)
        apply (GB4 (Z_to_bv 64 ((phi + 17) mod 8)) c4 c5 c6).
    - (* byte 16 <> 0: 0x82100 sd zero,184(s1) ; 0x82104 j 82130 *)
      cbv iota.
      step. (* 82100 sd zero,184(s1) *)
      step. (* 82104 j 82130 *)
      apply GA0. unfold f6_tf. rewrite (proj2 (Z.eqb_neq _ 0) B16).
      first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
  (* the tail 0x820d8 -> 0x820f8, the loop's join *)
  assert (Htail : forall c0 c2 c3 c4 c5 c6 : word,
    LE.evt rsegs QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
       c0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) c2 c3 c4 c5 c6 (Z_to_bv 64 32)
       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x820d8) fc None m (seg_rom rsegs))).
  { intros c0 c2 c3 c4 c5 c6.
    pose proof (HSO m 312 (wmono_refl rsegs m) ltac:(lia) ltac:(lia)) as HS312.
    step. (* 820d8 sd t0,312(s1) *)
    lazymatch goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) => change mm with m1 end.
    step. (* 820dc li a0,-17 *)
    step. (* 820e0 bltu a0,s2,82fa0 : not taken *)
    f6_nt.
    step. (* 820e4 addi a0,s2,16 *)
    step. (* 820e8 srli a2,a0,3 *)
    step. (* 820ec add a2,a2,s10 *)
    rewrite (MState.unsigned_lit (phi + 16)) by lia.
    step. (* 820f0 lb a2,0(a2) *)
    step. (* 820f4 bnez a2,82dd4 *)
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb16)) by (pose proof (rc_byte_signed sb16); lia).
    destruct (Z.eqb_spec (bv_signed sb16) 0) as [Z16|Z16].
    - cbn [negb]. cbv iota. apply (G88 (Z_to_bv 64 (bv_signed sb16)) c3 c4 c5 c6).
    - cbn [negb]. cbv iota.
      step. (* 82dd4 andi a3,a0,7 *)
      rewrite (MState.unsigned_lit (phi + 16)) by lia. rewrite rc_land7.
      step. (* 82dd8 bge a3,a2,830b4 : not taken *)
      rewrite (rc_lts_signed ((phi + 16) mod 8) (bv_signed sb16))
        by (pose proof (rc_byte_signed sb16); pose proof (Z.mod_pos_bound (phi + 16) 8 ltac:(lia)); lia).
      replace ((phi + 16) mod 8 <? bv_signed sb16) with true
        by (symmetry; apply Z.ltb_lt; destruct OK16 as [H|H]; lia).
      cbn [negb]. cbv iota.
      step. (* 82ddc j 820f8 *)
      apply (G88 (Z_to_bv 64 (bv_signed sb16)) (Z_to_bv 64 ((phi + 16) mod 8)) c4 c5 c6). }
  assert (Hjoin : forall y0 y2 y4 y5 y6 : word,
    LE.evt rsegs QE (MS (mkR ra0 sp gp tp (Z_to_bv 64 (phi + 18)) t1 t2 s0 (Z_to_bv 64 A)
       y0 (Z_to_bv 64 (psum (skipn 18 bs) 32)) y2 (Z_to_bv 64 (- (phi + 18))) y4 y5 y6 (Z_to_bv 64 32)
       (Z_to_bv 64 phi) s3 s4v s5i s6 s7 (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x820d8) fc None m (seg_rom rsegs)))
    by (intros y0 y2 y4 y5 y6; apply Htail).
  apply (f6_loop ra0 sp gp tp t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi) s3 s4v s5i s6 s7
           (Z_to_bv 64 v8) s9i s11 t3 t4 t5 t6 Fr fc m phi bs QE
           Hphi0 Hphi50 Hlen HB HA Hjoin 32%nat 0%nat
           (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 0) (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 32) a5i a6i);
    try reflexivity; try lia; try (f_equal; lia).
Qed.

(* ================= the segment lemmas ================= *)

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee of F5 and F6, reac_ctrl_parse (PARSE@0x82158), taken on its lib/B contract
   (lib/B/Prog/reac_ctrl_parse_c.v), never on its code. A normal callee premise, discharged at the top through
   callee_contracts_holds by the v1.9 image-B proof reac_ctrl_parse_holds (lib/B/Prog/reac_ctrl_parse.v (not in this delivery) on
   a working branch). F6 uses it only through F5's seg_c. *)
Hypothesis PARSE : reac_ctrl_parse_contract.

(* 0x82098 -> 0x8214c: the block-sum loop (32 turns inside this lemma), the two byte checks, the abort compare
   NOT taken and the three stores. *)
Lemma seg_F6_98 : forall j,
  Hat B APIf ra (Inv_B8214c_join B APIf ra) j -> Hat B APIf ra (Inv_B82098_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & Hs2 & Hs4 & HFT &
    HLK & H22 & HFS & HREC & HFPS & H272 & Hlen50 & Hs8 & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha7 & Ht0).
  subst c. rewrite SEGS.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhigh.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Happ).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  (* the turn is on the long path, so the 50 header bytes of the record lie at Phi *)
  assert (Hlen : 50 <= t_len (g_in g) j) by (unfold flen in Hlen50; lia).
  assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; lia).
  pose proof (fturn_g g j phi regs mem HFT Hlen) as Hbs.
  pose proof (c_tlen_nn (g_in g) j) as Htl0.
  assert (Haddr50 : addressable mem phi 50).
  { rewrite <- (Z.add_0_r phi).
    apply (addressable_sub mem phi (AC.a_size (flen g j)) 0 50 (proj2 HHB)); unfold AC.a_size, flen in *; lia. }
  assert (Hphi0 : 0 <= phi) by (destruct Haddr50 as (H & _); lia).
  assert (Hphi50 : phi + 50 <= 2 ^ 64) by (destruct Haddr50 as (_ & _ & H & _); lia).
  (* the live block lies below stklo, and stklo below the save area *)
  destruct (c_lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH ltac:(apply in_or_app; left; left; reflexivity))
    as (_ & Hp4096 & Hpstk & _ & Hpall).
  assert (Hblk : phi + t_len (g_in g) j <= A).
  { unfold AC.a_size, flen in Hpstk. lia. }
  assert (Hsep : phi + 50 <= A) by lia.
  assert (Hshadow : forall x, phi <= x < phi + 50 -> shadow_addr x < A).
  { intros x Hx.
    assert (Hsx : shadow_addr x <= x / 8 + ASAN_K) by (unfold shadow_addr; lia).
    assert (Hx8 : x / 8 <= A / 8) by (apply Z.div_le_mono; lia).
    assert (HA8 : A / 8 + ASAN_K < A) by (Z.div_mod_to_equations; lia).
    lia. }
  (* the save-area window the three stores write *)
  assert (HSTK : stk rsegs mem (A + 184) (A + 320)).
  { destruct Hwin as (Hw0 & Hw1 & Hws). split; [lia|]. split; [lia|]. intros x Hx. apply Hws. lia. }
  assert (Htk : 0 <= t_k (g_in g) j < 2 ^ 64)
    by (pose proof (ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)); unfold t_k; lia).
  (* [A+272] is the carried 0x88 0x19 flag, which is (t_k j <> 0) *)
  assert (Hq272 : q64 mem (A + 272) (b2z (t_8819 (g_in g) j))).
  { apply (c_spill_q64 regs mem 272 (b2z (t_8819 (g_in g) j)) A H272 Hr9); lia. }
  assert (He272 : b2z (t_8819 (g_in g) j) = (if t_k (g_in g) j =? 0 then 0 else 1)).
  { rewrite <- (f6_8819_eq (g_in g) j). rewrite MState.unsigned_lit by lia. reflexivity. }
  set (m1 := write_to_mem mem (wa (A + 312)) (le8 (Z_to_bv 64 (phi + 18)))).
  set (m2 := write_to_mem m1 (wa (A + 184)) (le8 (Z_to_bv 64 (f6_tf (t_g (g_in g) j))))).
  set (m3 := write_to_mem m2 (wa (A + 248))
               (le8 (Z_to_bv 64 (if psum (skipn 18 (t_g (g_in g) j)) 32 mod 256 =? 0 then 0 else 1)))).
  apply (c_run_lib regs (Z_to_bv 64 0x82098) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x8214c /\ mem' = m3 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 22 = getr regs 22 /\
       getr R0 24 = getr regs 24 /\ getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 25 = Z_to_bv 64 (if psum (skipn 18 (t_g (g_in g) j)) 32 mod 256 =? 0 then 1 else 0))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { rewrite c_mkR_expand.
      unfold a0v in Ha0.
      c_slot Hr9. c_slot Ha0. c_slot Ha1. c_slot Ha2. c_slot Ha3. c_slot Ha4. c_slot Ha7. c_slot Ht0.
      c_slot Hs2. c_slot Hs8. c_slot Hr26.
      apply (f6_run_evt (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 6) (getr regs 7)
               (getr regs 8) (getr regs 15) (getr regs 16) (getr regs 19) (getr regs 20) (getr regs 21)
               (getr regs 22) (getr regs 23) (getr regs 25) (getr regs 27)
               (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
               fp_regs fp_csr mem phi A (t_k (g_in g) j) (b2z (t_8819 (g_in g) j)) (t_g (g_in g) j));
        [ lia | lia | exact (c_tg_len (g_in g) j) | exact Hbs | exact Haddr50 | lia | lia | exact HSTK
        | lia | exact Hq272 | exact He272 | lia | exact Hshadow ]. }
    { intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & E).
      eexists _, (Z_to_bv 64 0x8214c), _. split; [exact E|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [symmetry; exact Hr9|]. split; [symmetry; exact Hs2|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [symmetry; exact Hs8|]. split; [symmetry; exact Hr26|]. split; reflexivity. }
  - intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er22 &
      Er24 & Er26 & Er27 & Er25) Hreg Hmat.
    subst pc' mem'.
    set (W := [(A + 312, A + 320); (A + 184, A + 192); (A + 248, A + 256)]).
    assert (MU : munch W mem m3).
    { subst m3 m2 m1 W.
      apply munch_write;
        [apply munch_write;
           [apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia
              | rewrite length_le8; cbn [inside]; left; lia]
           | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; left; lia]
        | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; right; left; lia]. }
    assert (WM : wmono rsegs mem m3)
      by (subst m3 m2 m1; apply wmono_write; apply wmono_write; apply wmono_write; apply wmono_refl).
    assert (HWIN' : stk rsegs m3 (g_S g - AF.SLOT_STACK) (g_S g)).
    { subst m3 m2 m1.
      apply stk_write; [apply stk_write; [apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]
        | lia | rewrite length_le8; lia] | lia | rewrite length_le8; lia]. }
    assert (HAW : all_app W).
    { subst W. cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia. }
    assert (HD : rt_disjoint W).
    { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [exact I | left; lia]. }
    assert (HWloc : forall x, ~ outside W x -> A + 72 <= x < A + 336).
    { intros x Hx. destruct (c_not_out W x Hx) as (r & Hin & Hr). subst W. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hr; lia. }
    assert (OW : forall x, ~ (A + 312 <= x < A + 320) -> ~ (A + 184 <= x < A + 192) ->
              ~ (A + 248 <= x < A + 256) -> outside W x).
    { intros x H1 H2 H3. subst W. cbn [outside]. repeat split; assumption. }
    assert (OWlo : forall x, x < A + 184 -> outside W x /\ outside W (shadow_addr x)).
    { intros x Hx. split; [apply OW; lia|].
      destruct (Z_lt_le_dec x 0) as [Hn|Hp].
      - apply OW; unfold shadow_addr; Z.div_mod_to_equations; lia.
      - assert (Hsx : shadow_addr x <= x / 8 + ASAN_K) by (unfold shadow_addr; lia).
        assert (Hx8 : x / 8 <= A / 8 + 23) by (Z.div_mod_to_equations; lia).
        assert (HA8 : A / 8 + ASAN_K + 23 < A) by (Z.div_mod_to_equations; lia).
        apply OW; lia. }
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr25 : getr regs' 25 = Z_to_bv 64 (if psum (skipn 18 (t_g (g_in g) j)) 32 mod 256 =? 0 then 1 else 0))
      by (rewrite Hreg; exact Er25).
    assert (HFE : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' m3 md' /\
                  ENT APIf g (hb1 phi (AC.a_size (flen g j))) m3 md').
    { eapply c_fra_spill; eassumption. }
    destruct HFE as (HFRA'' & HENT'').
    (* the three stored words (each later store is at another word) *)
    assert (Q248 : q64 m3 (A + 248) (if psum (skipn 18 (t_g (g_in g) j)) 32 mod 256 =? 0 then 0 else 1)).
    { subst m3. unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (Q184 : q64 m3 (A + 184) (f6_tf (t_g (g_in g) j))).
    { subst m3. unfold q64. apply c_ba_write; [| lia | rewrite length_le8; lia
        | rewrite !length_le8; intros x Hx; left; cbn [Z.of_nat] in Hx; lia].
      subst m2. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (Q312 : q64 m3 (A + 312) (phi + 18)).
    { subst m3. unfold q64. apply c_ba_write; [| lia | rewrite length_le8; lia
        | rewrite !length_le8; intros x Hx; right; cbn [Z.of_nat] in Hx; lia].
      subst m2. apply c_ba_write; [| lia | rewrite length_le8; lia
        | rewrite !length_le8; intros x Hx; right; cbn [Z.of_nat] in Hx; lia].
      subst m1. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (HA448' : A + 448 <= 2 ^ 64) by lia.
    assert (H9'' : rg regs' 9 A) by exact (c_rg_move regs regs' _ _ Hr9 Fr9).
    assert (Ofr : forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x))
      by (intros x Hx; apply OWlo; lia).
    assert (Olo : forall x, 0 <= x < AC.GT -> outside W x /\ outside W (shadow_addr x))
      by (intros x Hx; apply OWlo; lia).
    assert (Ophi : forall x, phi <= x < phi + t_len (g_in g) j -> outside W x)
      by (intros x Hx; exact (proj1 (OWlo x ltac:(lia)))).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', m3, md', fr.
    split; [reflexivity|]. split; [exact HFRA''|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      apply (c_addr_keep W mem m3 phi _ Hphiad MU). intros i Hi.
      unfold AC.a_size, flen in Hi.
      exact (proj2 (OWlo (phi + i) ltac:(lia))). }
    split.
    { apply (c_lk_keep g fr j A regs regs' mem m3 W HLK Hr9 ltac:(lia) HA448' Fr9 Fr27 MU WM).
      - intros x _ H1 H2 _ H4. exact (OW x H4 H1 H2).
      - exact Ofr.
      - exact Olo. }
    split; [exact (c_rg_move regs regs' _ _ Hs2 Fr18)|].
    split; [exact (c_rg_move regs regs' _ _ Hs4 Fr20)|].
    split.
    { (* FM: [A+184] = b2z tfill, s8 = t_k, s6 = 1, s9 = b2z sum_ok, [A+312] = Phi + 18 (t_big) *)
      unfold FM. rewrite (f6_tfill (g_in g) j Hbig), (f6_sum (g_in g) j Hbig), Hbig.
      split; [exists A; split; [exact H9'' | exact Q184]|].
      split; [exact (c_rg_move regs regs' _ _ Hs8 Fr24)|].
      split; [exact (c_rg_move regs regs' _ _ H22 Fr22)|].
      split; [unfold rg; exact Fr25 | exists A; split; [exact H9'' | exact Q312]]. }
    split; [exact (c_fsj_keep g fr j regs regs' mem m3 W HFS MU Ofr)|].
    split.
    { (* [A+248] = 1 - b2z sum_ok *)
      rewrite (f6_sum (g_in g) j Hbig). exists A. split; [exact H9''|].
      replace (1 - (if psum (skipn 18 (t_g (g_in g) j)) 32 mod 256 =? 0 then 1 else 0))
        with (if psum (skipn 18 (t_g (g_in g) j)) 32 mod 256 =? 0 then 0 else 1)
        by (destruct (psum (skipn 18 (t_g (g_in g) j)) 32 mod 256 =? 0); reflexivity).
      exact Q248. }
    split; [intros _; apply (fl_bytes W mem m3 phi _ Hbs MU);
            rewrite (c_tg_len (g_in g) j); intros x Hx; apply Ophi; lia|].
    split.
    { apply (c_fturn_keep g j phi A regs regs' mem m3 W HFT Hr9 ltac:(lia) HA448' Fr9 MU).
      - intros x Hx. apply OW; lia.
      - exact Ophi. }
    split; [exact (c_rec0_keep g fr j W mem m3 HREC MU (fun x Hx => proj1 (Ofr x Hx)))|].
    split; [exact (c_fps_keep g fr j W mem m3 HFPS MU Ofr)|].
    assert (HSP272 : spill regs mem 272 (b2z (t_8819 (g_in g) j)))
      by (exists A; split; [exact Hr9 | exact Hq272]).
    unfold F272. apply (c_spill_keep regs regs' A 272 (b2z (t_8819 (g_in g) j)) mem m3 W
      HSP272 Hr9 ltac:(lia) HA448' ltac:(lia) Fr9 MU).
    intros x Hx. apply OW; lia.
Qed.

(* seg_F6 (S_F6): the loop and the parse call (F5's seg_c) composed through F5's join cut. *)
Lemma seg_F6 : forall j : nat,
  Hat B APIf ra (Inv_B8215c_at B APIf ra) j -> Hat B APIf ra (Inv_B82098_at B APIf ra) j.
Proof.
  intros j Hexit. apply seg_F6_98. eapply seg_c; eassumption.
Qed.

End S.
