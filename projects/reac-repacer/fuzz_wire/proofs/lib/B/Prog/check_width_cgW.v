(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 647 of its 715 lines of code are new or changed and 396 lines of the source are left out. *)
(* check_width_cgW: wire_check_width_holds : forall fx rc B MT, wire_check_width_holds_stmt.

   The code (fuzz_wire.asan-ubsan 0x8057c = wire_sigma WS_check_width; objdump of record sha256 440b9550f4f5):
     0x8057c `addi sp, sp, -16`, `sd ra, 8(sp)`, `sd s0, 0(sp)`, `mv s0, a0`, 0x8058c `jal rp_frame_channels`;
     0x80590 .. 0x805c0 the inlined w_width(n): a1 = 2k, a2 = 2 + 2k, a5 = 126 + 72k - n, the loop at 0x805a8;
     0x805c4 `bne a0, a2` to the abort (not taken: rp_frame_channels_model n = w_width n for 0 <= n <= 1600);
     0x805c8 `not a0, s0`, 0x805cc `jal rp_frame_channels`;
     0x805d0 `li a1, -1`, `bne a0, a1` to the abort (not taken: -1 - n is negative, the model gives -1);
     0x805d8 `ld ra, 8(sp)`, `ld s0, 0(sp)`, `addi sp, sp, 16`, `ret`.
   The walk:
     1. an INNER journal at the entry (YCbq.v ajournal_sub_init): stack window [spZ regs - CW_STK, spZ regs), no
        footprint, no frame of the allocator;
     2. cw_seg1_F, the frame [spZ regs - 16, spZ regs) written with s0 and ra (the inner journal follows the write,
        YCbq.v ajournal_exec);
     3. rp_frame_channels(n) by the statement's leaf premise, through WireCcLeafb.v wcc_leafb_journal: its .rodata
        reads 0x10300 / 0x103b0 from the contract's wire_rom_view_rd kept by the inner journal, 0x10328 from
        wire_cells' row WIRE_RO_FCH;
     4. cw_seg2_F, the inlined w_width and the first test, up to the second call;
     5. rp_frame_channels(-1 - n), as 3.;
     6. cw_seg3_F, the second test, the reloads and the `ret`;
     7. the post: the outer journal by YCbq.v ajournal_sub, acall_kept by YCbq.v acall_kept_of_journal, no event and
        no meter charge (the allocator state is the call's). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ======================================================================== *)
(* 1. The footprint runs (lib/Lib/StepF.v)                                    *)
(* ======================================================================== *)

(* The entry, the two return addresses, the loop head and the first test (image B). *)
Definition CW_ENTRY : Z := 0x8057c.
Definition CW_RET1 : Z := 0x80590.
Definition CW_LOOP : Z := 0x805a8.
Definition CW_TEST : Z := 0x805c4.
Definition CW_RET2 : Z := 0x805d0.

(* fuzz.h's w_width, the frame law as the harness states it (lib/Prog/check_width.v w_width_from / w_width_model). *)
Fixpoint cw_w_width_from (fuel : nat) (nch len : Z) : Z :=
  match fuel with
  | O => -1
  | S f => if (len =? 52 + nch * 36) || (len =? 52 + nch * 36 + 2) then nch else cw_w_width_from f (nch + 2) len
  end.

Definition cw_w_width_model (len : Z) : Z := cw_w_width_from 20 2 len.

Lemma cw_frame_law_b :
  forallb (fun k => Z.eqb (cw_w_width_model (Z.of_nat k)) (rp_frame_channels_model (Z.of_nat k))) (seq 0 1601) = true.
Proof. vm_compute. reflexivity. Qed.

(* The harness's frame law and image B's rp_frame_channels agree on every length check_width is called with. *)
Lemma cw_frame_law : forall n, 0 <= n <= 1600 -> cw_w_width_model n = rp_frame_channels_model n.
Proof.
  intros n Hn. pose proof (proj1 (forallb_forall _ _) cw_frame_law_b (Z.to_nat n)) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia. apply Z.eqb_eq, H. apply in_seq. lia.
Qed.

Lemma cw_sw32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

(* rp_frame_channels_model is -1 at every negative long. *)
Lemma cw_model_neg : forall v : word, 2^63 <= bv_unsigned v -> rp_frame_channels_model (bv_signed v) = -1.
Proof.
  intros v Hv. pose proof (u64_range v). rewrite zb_signed. rewrite (proj2 (Z.ltb_ge _ _) Hv).
  unfold rp_frame_channels_model. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

(* The 16-byte frame, read as two words (UciCvSegs.v cv_le_bytes_to_Z .. cv_frame_words, at two words). *)
Lemma cw_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  assert (Hb : 0 <= bv_unsigned b < 256).
  { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. }
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma cw_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply cw_le_bytes_to_Z.
Qed.

Fixpoint cw_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: cw_c8s n' (skipn 8 bs)
  end.

Lemma cw_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (cw_c8s n bs) /\ cells_bytes (cw_c8s n bs) = bs /\ cells_size (cw_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [cw_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite cw_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma cw_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (cw_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (cw_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

Lemma cw_frame_words : forall m A bs, rw_cells rsegs m A [CB 16 bs] ->
  exists v0 v8 : word, rw_cells rsegs m A [C8 v0; C8 v8].
Proof.
  intros m A bs H. apply (cw_rw_c8s rsegs m A 2 bs) in H. cbn [cw_c8s] in H. do 2 eexists. exact H.
Qed.

Ltac cw_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cw_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cw_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac cw_w := cw_shift; cw_usub; cw_shift; cw_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].

(* ---- cw_seg1_F: CW_ENTRY -> rp_frame_channels (ra = CW_RET1): the frame, s0 := a0 = n ---- *)
Lemma cw_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n lo : Z),
    0 <= n <= 1600 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    ExecF.rng RNG (bv_unsigned sp - 16) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 CW_RET1) (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 (Z_to_bv 64 n) s1
                    (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RP_FRAME_CHANNELS) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 CW_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo
    HN ST LO RFR.
  unfold CW_ENTRY, CW_RET1, RP_FRAME_CHANNELS.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  destruct (cw_frame_words _ _ _ FR) as (v0 & v8 & FR'). clear FR. rename FR' into FR.
  do 5 step.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  try (replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia).
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; cw_regs; try cw_w.
Qed.

(* ---- the w_width loop, 0x805a8 .. 0x805c0 (lib/Prog/check_width.v width_loop at image B) ---- *)
Section Loop.
Variables (RNG : ExecF.footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (Q : machine_state -> Prop).
Hypothesis Hn : 0 <= n <= 1600.

Local Abbreviation ST pc a1 a2 a5 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 2) (Z_to_bv 64 38) a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* The loop's exit at 0x805c4 with a2 = w_width(n). *)
Hypothesis K : forall a1' a2' a5' : word, bv_unsigned a2' = cw_w_width_model n mod 2^64 ->
  ExecF.evtF rsegs RNG Q (ST 0x805c4 a1' a2' a5').

(* 0x805a8 with k passes done (k < 20) and none of them matched. *)
Lemma cw_width_loop : forall f k (a1 a2 a5 : word),
  (S f + k = 20)%nat ->
  cw_w_width_from (S f) (2 + 2 * Z.of_nat k) n = cw_w_width_model n ->
  bv_unsigned a1 = 2 * Z.of_nat k -> bv_unsigned a2 = 2 + 2 * Z.of_nat k ->
  bv_unsigned a5 = (126 + 72 * Z.of_nat k - n) mod 2^64 ->
  ExecF.evtF rsegs RNG Q (ST 0x805a8 a1 a2 a5).
Proof.
  induction f as [|f IH]; intros k a1 a2 a5 Hk Hw H1 H2 H5; cbn [cw_w_width_from] in Hw.
  all: step; if_cases HE;
    [ zify_cond HE; rewrite H5 in HE;
      assert (En : n = 52 + (2 + 2 * Z.of_nat k) * 36) by (Z.div_mod_to_equations; lia);
      rewrite (proj2 (Z.eqb_eq _ _) En) in Hw; cbn [orb] in Hw;
      apply K; rewrite <- Hw, H2; rewrite Z.mod_small by lia; reflexivity
    | step; if_cases HZ ].
  all: zify_cond HE; rewrite H5 in HE.
  1, 3: zify_cond HZ; rewrite H5 in HZ;
    assert (En : n = 52 + (2 + 2 * Z.of_nat k) * 36 + 2) by (Z.div_mod_to_equations; lia);
    rewrite (proj2 (Z.eqb_neq n (52 + (2 + 2 * Z.of_nat k) * 36))) in Hw by lia;
    rewrite (proj2 (Z.eqb_eq _ _) En) in Hw; cbn [orb] in Hw;
    apply K; rewrite <- Hw, H2; rewrite Z.mod_small by lia; reflexivity.
  all: zify_cond HZ; rewrite H5 in HZ.
  all: assert (N1 : n <> 52 + (2 + 2 * Z.of_nat k) * 36)
         by (intro E; apply HE; replace (126 + 72 * Z.of_nat k - n) with 2 by lia; reflexivity).
  all: assert (N2 : n <> 52 + (2 + 2 * Z.of_nat k) * 36 + 2)
         by (intro E; apply HZ; replace (126 + 72 * Z.of_nat k - n) with 0 by lia; reflexivity).
  all: rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in Hw; cbn [orb] in Hw.
  all: do 3 step; step; if_cases HC.
  - (* last pass, back-branch taken: impossible, a1 = 40 > 38 *)
    exfalso. zify_cond HC. rewrite ?unsigned_lit_wrap, ?H1 in HC. Z.div_mod_to_equations. lia.
  - (* last pass, the loop ends: w_width = -1 *)
    step. apply K. rewrite <- Hw. reflexivity.
  - apply (IH (S k)).
    + lia.
    + rewrite Nat2Z.inj_succ. replace (2 + 2 * Z.succ (Z.of_nat k)) with (2 + 2 * Z.of_nat k + 2) by lia. exact Hw.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H1. rewrite Z.mod_small by lia. lia.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H2, cw_sw32_id by lia. rewrite Z.mod_small by lia. lia.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H5, Zplus_mod_idemp_l. f_equal. lia.
  - (* the loop ends before the last pass: impossible, a1 <= 38 *)
    exfalso. zify_cond HC. rewrite ?unsigned_lit_wrap, ?H1 in HC. Z.div_mod_to_equations. lia.
Qed.

End Loop.

(* ---- cw_seg2_F: CW_RET1 (a0 = rp_frame_channels_model n, s0 = n) -> rp_frame_channels (ra = CW_RET2), a0 = -1 - n:
   the inlined w_width, the first test (not taken) and `not a0, s0` ---- *)
Lemma cw_seg2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
    0 <= n <= 1600 -> bv_unsigned s0 = n ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a0' a1' a2' a5' : word,
         ms' = MS (mkR (Z_to_bv 64 CW_RET2) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' (Z_to_bv 64 2) (Z_to_bv 64 38) a5'
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RP_FRAME_CHANNELS) fc None m (seg_rom rsegs) /\
         2 ^ 63 <= bv_unsigned a0')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rp_frame_channels_model n)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CW_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n
    HN HS0.
  subst n.
  unfold CW_RET1, CW_RET2, RP_FRAME_CHANNELS.
  rewrite <- (cw_frame_law (bv_unsigned s0) HN).
  do 6 step.
  eapply (cw_width_loop) with (f := 19%nat) (k := 0%nat) (n := bv_unsigned s0).
  all: lazymatch goal with
       | |- forall _ : word, _ => idtac
       | _ => first [ lia | reflexivity | (rewrite unsigned_lit_wrap; f_equal; lia) ]
       end.
  intros a1' a2' a5' H2'.
  replace a2' with (Z_to_bv 64 (cw_w_width_model (bv_unsigned s0)))
    by (apply bv_eq; rewrite unsigned_lit_wrap; symmetry; exact H2').
  step. first [if_true | if_false].
  do 2 step.
  apply evtF_done. do 4 eexists. split; [reflexivity|].
  rewrite ?unsigned_lit_wrap, ?zb_lxor_ones by lia; rewrite ?Z.mod_small by lia; lia.
Qed.

(* ---- cw_seg3_F: CW_RET2 (a0 = -1) -> the return: the second test (not taken), ra and s0 reloaded, sp += 16 ---- *)
Lemma cw_seg3_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 c0; C8 cra] ->
    bv_unsigned sp + 16 < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' : word,
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 c0 s1 (Z_to_bv 64 (-1)) a1' a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 CW_RET2) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c0 cra FR HSP RFR.
  unfold CW_RET2.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  step. step. first [if_true | if_false].
  do 4 step.
  apply evtF_done. eexists. reflexivity.
Qed.

(* ======================================================================== *)
(* 2. The walk in the caller-journal form                                     *)
(* ======================================================================== *)

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg WireCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import check_width_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WirePImg AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_frame_channels_cg.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.LeafCgKit.
Module LRFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_frame_channels_cg.
Module AKA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.AsanKA.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Lemma cw_entry_eq : wire_sigma WS_check_width = CW_ENTRY.
Proof. reflexivity. Qed.

Lemma cw_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma cw_signed_small : forall n, 0 <= n <= 1600 -> bv_signed (Z_to_bv 64 n) = n.
Proof.
  intros n Hn. rewrite zb_signed, cw_u64 by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma cw_rom_img : forall a, in_rom tfibsegs a -> in_img tfibsegs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.

Lemma cw_fp_avoids : forall (W : world tfibsegs),
  LCK.fp_avoids (@w_H tfibsegs W) (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Proof. intros W a n H. unfold LCK.RNG_W in H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (check_value_cgW.v cv_run). *)
Lemma cw_run {fx : YK11.FPState} : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (pc : Z) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  ExecF.evtF rsegs (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P (@LCK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms0, P ms0 /\ ms_eqv ms0 ms') -> same_but_materialized md md' ->
     SRr tfibsegs W (mkCfg ms' md') Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q Hrun K. unfold cfg_at.
  pose proof (LeafCgGlue.evtF_eqv rsegs _ P _ _ Hrun (@LeafCgGlue.ms_of_regs_eqv fx pc regs mem)) as Hrun'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n W _ md _ _ Q Hrun' (cw_fp_avoids W)).
  intros ms' md' (ms1 & HP & HE & _) Hs. apply K; [exists ms1; split; assumption | exact Hs].
Qed.

(* A state register-equivalent to an MS form with the cgif float state is that cgif state (cv_ms_shape). *)
Lemma cw_ms_shape {fx : YK11.FPState} : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms' : machine_state),
  ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (YK11.seg_rom tfibsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom tfibsegs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

Lemma cw_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof.
  intros R F pc fc rv m ro ms' r (HR & _). cbn [MS ms_regs] in HR. exact (LeafCgGlue.getr_xeqv _ _ HR r).
Qed.

(* The registers of a state register-equivalent to an `mkR` state (cv_regs_of). *)
Lemma cw_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YK11.getr (ms_regs ms') (Z_to_bv 5 1) = x1 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 2) = x2 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 3) = x3 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 4) = x4 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 8) = x8 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 9) = x9 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 10) = x10 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 11) = x11 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 12) = x12 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 18) = x18 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 19) = x19 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 20) = x20 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 21) = x21 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 22) = x22 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 23) = x23 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 24) = x24 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 25) = x25 /\ YK11.getr (ms_regs ms') (Z_to_bv 5 26) = x26 /\
  YK11.getr (ms_regs ms') (Z_to_bv 5 27) = x27.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (cw_ms_reg _ _ _ _ _ _ _ _ _ H) | reflexivity]).
Qed.

Lemma cw_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview tfibsegs H' m' a = aview tfibsegs H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma cw_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wl & Hw)] He.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
    assert (Hi' : A <= A + Z.of_nat i < A + Z.of_nat (cells_size cs)) by (rewrite <- L; lia).
    unfold mrd. rewrite (He _ Hi'). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wl|]. intros i Hi.
    unfold wview. rewrite (He (A + i)) by lia. exact (Hw i Hi).
Qed.

(* The 8 bytes of an image constant, as the image holds them (decided by vm_compute). *)
Definition cw_rom_chk (a K : Z) : bool :=
  forallb (fun i => match YK11.seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error (le8 (Z_to_bv 64 K)) i with
                    | Some b, Some c => (bv_unsigned b =? bv_unsigned c)
                    | _, _ => false
                    end) (seq 0 8).

Lemma cw_rom_chk_M : cw_rom_chk A_M KM = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cw_rom_chk_T : cw_rom_chk A_T KT = true.
Proof. vm_compute. reflexivity. Qed.

(* A constant the view shows as the image's bytes is bytes_at of the raw memory. *)
Lemma cw_rom_bytes : forall (W1 : world tfibsegs) m1 a K,
  cw_rom_chk a K = true -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> aview tfibsegs (w_H W1) m1 (a + i) =
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (a + i)))) ->
  bytes_at tfibsegs m1 a (le8 (Z_to_bv 64 K)).
Proof.
  intros W1 m1 a K HC H0 H8 HV.
  split; [exact H0|]. rewrite length_le8. split; [lia|].
  intros i Hi.
  unfold cw_rom_chk in HC. rewrite forallb_forall in HC.
  specialize (HC i ltac:(apply in_seq; lia)).
  specialize (HV (Z.of_nat i) ltac:(lia)).
  destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:Eb; [|discriminate HC].
  destruct (nth_error (le8 (Z_to_bv 64 K)) i) as [c|] eqn:Ec; [|discriminate HC].
  apply Z.eqb_eq in HC. cbn [option_map] in HV.
  destruct (wcc_leafb_mrd_aview W1 m1 _ _ HV) as (b' & Hb' & Hu).
  rewrite Hb'. f_equal. apply bv_eq. lia.
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : wire_cells B.
Hypothesis HOWN : wire_ro_rd_unowned B.
Hypothesis HERR : wire_rom_no_errno B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis LEAF : forall fx' : YK11.FPState, @wire_leaf_at rc B (@LRFC.wire_rp_frame_channels_cg) fx'.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).

(* A run that writes no memory: the journal follows its same_but_materialized (cv_aj_md). *)
Lemma cw_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (ajournal_exec segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc
            mdc' (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (n : Z).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 n.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - CW_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hn : 0 <= n <= CW_N_MAX.
Hypothesis Hrom : wire_rom_view_rd W memc.

Local Abbreviation POST := (wire_cw_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).
(* The inner journal: from the entry state, stack window [spZ regs - CW_STK, spZ regs); the allocator state and the
   world stay the call's (no call of the walk allocates). *)
Local Abbreviation JI m1 md1 := (ajournalA CW_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W m1 md1 0).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

(* The frame the prologue wrote: the caller's s0 at spZ regs - 16 and ra at spZ regs - 8. *)
Definition cw_frame (m : word -> option byte) : Prop :=
  rw_cells rsegs m (spZ regs - 16) [C8 (GR regs 8); C8 (GR regs 1)].

(* The registers the walk keeps from the prologue on: sp (the frame), gp, tp, s0 = n, s1 .. s11 untouched. *)
Definition cw_kept (rg : bvmap 5 word) : Prop :=
  GR rg 2 = w64 (spZ regs - 16) /\ GR rg 3 = GR regs 3 /\ GR rg 4 = GR regs 4 /\ GR rg 8 = w64 n /\
  GR rg 9 = GR regs 9 /\ GR rg 18 = GR regs 18 /\ GR rg 19 = GR regs 19 /\ GR rg 20 = GR regs 20 /\
  GR rg 21 = GR regs 21 /\ GR rg 22 = GR regs 22 /\ GR rg 23 = GR regs 23 /\ GR rg 24 = GR regs 24 /\
  GR rg 25 = GR regs 25 /\ GR rg 26 = GR regs 26 /\ GR rg 27 = GR regs 27.

Ltac kp_by HP i K := etransitivity; [apply (HP i); unfold acallee_saved; lia | exact K].

Lemma cw_kept_pres : forall r1 r2, cw_kept r1 -> aregs_preserved r1 r2 -> cw_kept r2.
Proof.
  intros r1 r2 (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27) HP.
  unfold cw_kept.
  split; [kp_by HP 2 K2|]. split; [kp_by HP 3 K3|]. split; [kp_by HP 4 K4|]. split; [kp_by HP 8 K8|].
  split; [kp_by HP 9 K9|]. split; [kp_by HP 18 K18|]. split; [kp_by HP 19 K19|]. split; [kp_by HP 20 K20|].
  split; [kp_by HP 21 K21|]. split; [kp_by HP 22 K22|]. split; [kp_by HP 23 K23|]. split; [kp_by HP 24 K24|].
  split; [kp_by HP 25 K25|]. split; [kp_by HP 26 K26|]. kp_by HP 27 K27.
Qed.

(* ---- facts of the entry ---- *)

Lemma cw_HARc : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cw_JI0 : JI memc mdc.
Proof.
  apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CW_STK (spZ regs) []
           (spZ regs - sp0) HJ).
  - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
    rewrite Zminus_mod, Hal, H16. reflexivity.
  - lia.
  - unfold CW_STK, CW_FRAME, ESTACK. lia.
  - lia.
Qed.

Lemma cw_sp_rng : YM05.alloc_ceiling + 16 + 4096 <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cw_JI0 as J. destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
  unfold CW_STK, CW_FRAME, ESTACK in Hlo. lia.
Qed.

Lemma cw_win : forall m1 md1, JI m1 md1 ->
  forall a, spZ regs - CW_STK <= a < spZ regs -> apresent (w_H W) m1 a.
Proof.
  intros m1 md1 J.
  destruct J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma cw_AR : forall m1 md1, JI m1 md1 -> AR segs B lyc Sc W m1 md1.
Proof. intros m1 md1 J. destruct J as (HAR & _). exact HAR. Qed.

(* The read-only constants keep their image bytes through the inner journal (its image clause), and the contract's
   wire_rom_view_rd says what they are at the entry. *)
Lemma cw_rom_at : forall m1 md1, JI m1 md1 -> forall a, wire_in_ro_rd a ->
  aview segs (w_H W) m1 a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a)).
Proof.
  intros m1 md1 J1 a Hin.
  pose proof J1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  destruct (wire_ro_rd_scoped B HOWN HERR a Hin) as [N1 N2].
  destruct (wire_ro_rd_rom_clean a Hin) as [HR _].
  rewrite (F3 a (cw_rom_img a HR) N1 N2 (fun Ho => False_ind _ (sink_closed_nil Ho))).
  exact (Hrom a Hin).
Qed.

(* The frame [spZ regs - 16, spZ regs) lies above every callee's window [spZ regs - 16 - ESTACK, spZ regs - 16). *)
Lemma cw_frame_kept : forall (m1 m2 : word -> option byte),
  cw_frame m1 ->
  (forall a, spZ regs - CW_STK <= a < spZ regs -> apresent (w_H W) m1 a) ->
  (forall a, spZ regs - CW_STK <= a < spZ regs -> apresent (w_H W) m2 a) ->
  (forall a, spZ regs - 16 <= a < spZ regs -> aview segs (w_H W) m2 a = aview segs (w_H W) m1 a) ->
  cw_frame m2.
Proof.
  intros m1 m2 F P1 P2 E.
  pose proof cw_sp_rng as [S1 S2].
  apply (cw_rw_cells_ext m1 m2 _ _ F). intros a Ha.
  change (Z.of_nat (cells_size [C8 (GR regs 8); C8 (GR regs 1)])) with 16 in Ha.
  unfold wa. apply (cw_byte_eq (w_H W) (w_H W) m1 m2 a); [apply P1 | apply P2 | apply E];
    unfold CW_STK, CW_FRAME, ESTACK in *; lia.
Qed.

(* ======================================================================== *)
(* The walk, backwards from the return                                        *)
(* ======================================================================== *)

(* At CW_RET2 (a0 = -1): cw_seg3_F, the return, and the post. *)
Lemma cw_at_ret2 : forall regs2 m2 md2,
  JI m2 md2 -> cw_frame m2 -> cw_kept regs2 -> GR regs2 10 = w64 (-1) ->
  SRr segs W (@cfg_at fx segs CW_RET2 regs2 m2 md2) POST.
Proof.
  intros regs2 m2 md2 J2 FR HK G10.
  destruct HK as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof cw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (SP2 : bv_unsigned (GR regs2 2) = spZ regs - 16).
  { rewrite K2. unfold w64. apply cw_u64. lia. }
  eapply (@cw_run fx W regs2 m2 md2 CW_RET2).
  { unfold LCK.ms_of_regs. rewrite G10. unfold w64. eapply cw_seg3_F.
    - rewrite SP2. exact FR.
    - rewrite SP2. lia.
    - rewrite SP2. apply (wcc_leafb_rng_vis W m2); [lia | lia |]. intros a Ha.
      apply (cw_win _ _ J2). unfold CW_STK, CW_FRAME, ESTACK. lia. }
  intros ms' md' (ms0 & (a1' & ->) & EQV) SBM.
  destruct (cw_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & _ & _ & _ & G18 & G19 & G20 & G21 & G22 & G23 &
    G24 & G25 & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1).
  { apply LeafCgFacts.ret_ok_stmt_YK0s. exact Hra. }
  rewrite Hret in EQV.
  rewrite (cw_ms_shape _ _ _ _ EQV).
  pose proof (cw_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J2 SBM) as J2'.
  apply SRr_ret. unfold wire_cw_post.
  exists lyc, Sc, (ms_regs ms'), m2, md'.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CW_STK (spZ regs) [] [] lyc Sc W m2 md' 0 HJ J2' Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. exact J. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact G2|]. rewrite SP2. replace (spZ regs - 16 + 16) with (spZ regs) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact G3|]. exact K3.
    - etransitivity; [exact G4|]. exact K4.
    - exact G8.
    - etransitivity; [exact G9|]. exact K9.
    - etransitivity; [exact G18|]. exact K18.
    - etransitivity; [exact G19|]. exact K19.
    - etransitivity; [exact G20|]. exact K20.
    - etransitivity; [exact G21|]. exact K21.
    - etransitivity; [exact G22|]. exact K22.
    - etransitivity; [exact G23|]. exact K23.
    - etransitivity; [exact G24|]. exact K24.
    - etransitivity; [exact G25|]. exact K25.
    - etransitivity; [exact G26|]. exact K26.
    - etransitivity; [exact G27|]. exact K27. }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B WirePImg.wire_segs_low CW_STK (spZ regs) [] [] lyc Sc W memc mdc lyc Sc W m2
             md' 0 (fun _ => False) J2' cw_HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  exact (mle_start MT Sc MTL).
Qed.

(* A call of rp_frame_channels from either call site: the statement's leaf premise through
   WireCcLeafb.v wcc_leafb_journal (no written range), and the walk's continuation at the return address rl. *)
Lemma cw_leaf_call : forall regsC m1 md1 (rl : Z),
  JI m1 md1 -> cw_frame m1 -> cw_kept regsC ->
  GR regsC 1 = Z_to_bv 64 rl -> YK0s.ret_ok (GR regsC 1) ->
  (forall regs' m' md', JI m' md' -> cw_frame m' -> cw_kept regs' ->
     GR regs' 10 = w64 (rp_frame_channels_model (bv_signed (GR regsC 10))) ->
     SRr segs W (@cfg_at fx segs rl regs' m' md') POST) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsC (Z_to_bv 64 RP_FRAME_CHANNELS) m1 (YK11.seg_rom segs)) md1) POST.
Proof.
  intros regsC m1 md1 rl J1 HF HK G1 Hret KONT.
  pose proof HK as (K2 & K3 & K4 & _).
  pose proof cw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  assert (SPC : spZ regsC = spZ regs + -16).
  { change (spZ regsC) with (bv_unsigned (GR regsC 2)). rewrite K2. unfold w64. rewrite cw_u64 by lia. lia. }
  eapply SRr_bind.
  { apply (wcc_leafb_journal B LAWS W regsC m1 CW_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc md1 0 (-16)
             RP_FRAME_CHANNELS (Some (rp_frame_channels_model (bv_signed (GR regsC 10)))) [] (fun _ => True) J1).
    - exact SPC.
    - reflexivity.
    - lia.
    - unfold CW_STK, CW_FRAME, ESTACK. lia.
    - exact Hret.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - intros a Ha. inversion Ha.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold wire_leaf_at, LRFC.wire_rp_frame_channels_cg in LF.
      specialize (LF lyc Sc W regsC m1 md1 (spZ regs - CW_STK) HPRE). cbv zeta in LF.
      assert (ESP : bv_unsigned (YK11.getr regsC (Z_to_bv 5 2)) = spZ regs - 16).
      { change (bv_unsigned (YK11.getr regsC (Z_to_bv 5 2))) with (spZ regsC). lia. }
      pose proof (cw_AR _ _ J1) as HAR1. destruct HAR1 as [HM _].
      assert (HKc : Forall (cell_holds B lyc (aview segs (w_H W) m1)) (as_const B lyc)) by (eapply am_const; exact HM).
      assert (VIS : forall a0 len, wire_seg_covers a0 len = true -> a0 + len <= 2 ^ 64 ->
                forall a, a0 <= a < a0 + len -> w_H W (Z_to_bv 64 a) = false).
      { intros a0 len Hc Ht a Ha. replace a with (a0 + (a - a0)) by lia.
        apply (wcc_leafb_covers_visible (w_H W) a0 len (a - a0) (w_Hoff W) Hc); lia. }
      apply LF; clear LF.
      + apply (cw_rom_bytes W m1 A_M KM cw_rom_chk_M); [unfold A_M; lia | unfold A_M; lia |].
        intros i Hi. apply (cw_rom_at m1 md1 J1).
        unfold wire_in_ro_rd, WIRE_RO_RD. apply Exists_cons_hd. unfold in_zr, A_M. cbn [fst snd]. lia.
      + apply (cw_rom_bytes W m1 A_T KT cw_rom_chk_T); [unfold A_T; lia | unfold A_T; lia |].
        intros i Hi. apply (cw_rom_at m1 md1 J1).
        unfold wire_in_ro_rd, WIRE_RO_RD. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr, A_T.
        cbn [fst snd]. lia.
      + change A_K36 with WIRE_RO_FCH. change (Z_to_bv 64 K36) with (wa WIRE_RO_FCH_VAL).
        apply (wcc_leafb_z8 B lyc (w_H W) m1 WIRE_RO_FCH WIRE_RO_FCH_VAL (w_Hoff W) HKc);
          [wcc_leafb_row HCELLS lyc | vm_compute; reflexivity | unfold WIRE_RO_FCH; lia].
      + rewrite ESP. eapply (wcc_leafb_stk_journal B); [exact J1 | lia | unfold CW_STK, CW_FRAME, ESTACK; lia].
      + rewrite ESP. unfold RP_FRAME_CHANNELS_FRAME, CW_STK, CW_FRAME, ESTACK. lia.
      + unfold AKA.off_stk, RP_FRAME_CHANNELS_FRAME. rewrite ESP. left. unfold A_M. lia.
      + unfold AKA.off_stk, RP_FRAME_CHANNELS_FRAME. rewrite ESP. left. unfold A_T. lia.
      + unfold AKA.off_stk, RP_FRAME_CHANNELS_FRAME. rewrite ESP. left. unfold A_K36. lia.
      + rewrite ESP. unfold RP_FRAME_CHANNELS_FRAME.
        eapply (wcc_leafb_rng_journal B); [exact J1 | unfold CW_STK, CW_FRAME, ESTACK; lia | lia].
      + apply (wcc_leafb_rng W); [unfold A_M; lia | unfold A_M; lia |].
        apply (VIS A_M 8); [vm_compute; reflexivity | unfold A_M; lia].
      + apply (wcc_leafb_rng W); [unfold A_T; lia | unfold A_T; lia |].
        apply (VIS A_T 8); [vm_compute; reflexivity | unfold A_T; lia].
      + apply (wcc_leafb_rng W); [unfold A_K36; lia | unfold A_K36; lia |].
        apply (VIS A_K36 8); [vm_compute; reflexivity | unfold A_K36; lia]. }
  cbv beta. intros W' c' _ (-> & regs' & m' & md' & -> & J' & HP & HRES & HEFF & HGR & _).
  assert (G1' : YK11.getr regsC 1 = Z_to_bv 64 rl) by exact G1.
  rewrite G1'.
  change (mkCfg (YK11.mkst regs' (Z_to_bv 64 rl) m' (YK11.seg_rom segs)) md') with (@cfg_at fx segs rl regs' m' md').
  apply KONT.
  - exact J'.
  - apply (cw_frame_kept m1 m' HF (cw_win _ _ J1) (cw_win _ _ J')).
    intros a Ha. apply HEFF; [lia | rewrite SPC; lia | intros Hc; inversion Hc].
  - exact (cw_kept_pres _ _ HK HP).
  - exact (HRES _ eq_refl).
Qed.

(* At CW_RET1 (a0 = rp_frame_channels_model n): cw_seg2_F, then the second call and cw_at_ret2. *)
Lemma cw_at_ret1 : forall regs1 m1 md1,
  JI m1 md1 -> cw_frame m1 -> cw_kept regs1 -> GR regs1 10 = w64 (rp_frame_channels_model n) ->
  SRr segs W (@cfg_at fx segs CW_RET1 regs1 m1 md1) POST.
Proof.
  intros regs1 m1 md1 J1 HF HK G10.
  pose proof HK as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof Hn as Hn'. unfold CW_N_MAX in Hn'.
  eapply (@cw_run fx W regs1 m1 md1 CW_RET1).
  { unfold LCK.ms_of_regs. rewrite G10, K8. unfold w64.
    eapply cw_seg2_F with (n := n); [exact Hn' | apply cw_u64; lia]. }
  intros ms' md' (ms0 & (a0' & a1' & a2' & a5' & -> & Ha0') & EQV) SBM.
  destruct (cw_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 &
    E24 & E25 & E26 & E27).
  rewrite (cw_ms_shape _ _ _ _ EQV).
  pose proof (cw_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 SBM) as J1'.
  apply (cw_leaf_call (ms_regs ms') m1 md' CW_RET2 J1' HF).
  - unfold cw_kept.
    split; [rewrite E2; exact K2|]. split; [rewrite E3; exact K3|]. split; [rewrite E4; exact K4|].
    split; [rewrite E8; first [reflexivity | exact K8]|]. split; [rewrite E9; exact K9|].
    split; [rewrite E18; exact K18|]. split; [rewrite E19; exact K19|]. split; [rewrite E20; exact K20|].
    split; [rewrite E21; exact K21|]. split; [rewrite E22; exact K22|]. split; [rewrite E23; exact K23|].
    split; [rewrite E24; exact K24|]. split; [rewrite E25; exact K25|]. split; [rewrite E26; exact K26|].
    rewrite E27; exact K27.
  - exact E1.
  - rewrite E1. apply YK0s.ret_ok_even. vm_compute. reflexivity.
  - intros regs3 m3 md3 J3 HF3 HK3 HR3.
    apply (cw_at_ret2 regs3 m3 md3 J3 HF3 HK3).
    rewrite HR3, E10, (cw_model_neg a0' Ha0'). reflexivity.
Qed.

(* At CW_ENTRY: the inner journal, cw_seg1_F (the frame), then the first call and cw_at_ret1. *)
Lemma cw_entry : SRr segs W (@cfg_at fx segs CW_ENTRY regs memc mdc) POST.
Proof.
  pose proof cw_sp_rng as [Hsp1 Hsp2].
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof cw_JI0 as JI0.
  pose proof (cw_win _ _ JI0) as Hpres0.
  pose proof Hn as Hn'. unfold CW_N_MAX in Hn'.
  assert (E10 : GR regs 10 = Z_to_bv 64 n) by exact H10.
  eapply (@cw_run fx W regs memc mdc CW_ENTRY).
  { unfold LCK.ms_of_regs. rewrite E10.
    eapply cw_seg1_F with (lo := spZ regs - CW_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - exact Hn'.
    - apply (wcc_leafb_stk W); [unfold CW_STK, CW_FRAME, ESTACK; lia | lia | exact Hpres0].
    - unfold CW_STK, CW_FRAME, ESTACK. lia.
    - apply (wcc_leafb_rng_vis W memc); [lia | lia |]. intros a Ha. apply Hpres0.
      unfold CW_STK, CW_FRAME, ESTACK. lia. }
  intros ms' md' (ms0 & (m1 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR.
  destruct (cw_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10' & _ & _ & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  rewrite (cw_ms_shape _ _ _ _ EQV).
  (* the inner journal after the frame write *)
  assert (HJ1 : JI m1 md').
  { apply (ajournal_exec segs B LAWS WirePImg.wire_segs_low CW_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc
             mdc 0 m1 md' (fun a => spZ regs - 16 <= a < spZ regs) JI0).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 16)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hxr : spZ regs - CW_STK <= bv_unsigned x < spZ regs) by (unfold CW_STK, CW_FRAME, ESTACK; lia).
      destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
      assert (Hw : wview rsegs m1 x <> None).
      { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
      unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (LeafCgGlue.find_segment_out rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
      intros sg Hin Hr. pose proof (WirePImg.wire_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
      unfold kLowMemEnd in Hlow. lia.
    - intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 16)) as [Hl|Hl];
        [apply (MU x); cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|apply (MU x); cbn [outside]; split; [lia | exact I]].
      exfalso.
      assert (Hxr : spZ regs - CW_STK <= bv_unsigned x < spZ regs) by (unfold CW_STK, CW_FRAME, ESTACK; lia).
      pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
    - exact SBM.
    - intros a Ha. cbv beta in Ha. left. unfold CW_STK, CW_FRAME, ESTACK. lia. }
  apply (cw_leaf_call (ms_regs ms') m1 md' CW_RET1 HJ1).
  - exact FR.
  - unfold cw_kept.
    split; [rewrite E2; reflexivity|]. split; [rewrite E3; reflexivity|]. split; [rewrite E4; reflexivity|].
    split; [rewrite E8; reflexivity|]. split; [rewrite E9; reflexivity|].
    split; [rewrite E18; reflexivity|]. split; [rewrite E19; reflexivity|]. split; [rewrite E20; reflexivity|].
    split; [rewrite E21; reflexivity|]. split; [rewrite E22; reflexivity|]. split; [rewrite E23; reflexivity|].
    split; [rewrite E24; reflexivity|]. split; [rewrite E25; reflexivity|]. split; [rewrite E26; reflexivity|].
    rewrite E27; reflexivity.
  - exact E1.
  - rewrite E1. apply YK0s.ret_ok_even. vm_compute. reflexivity.
  - intros regs3 m3 md3 J3 HF3 HK3 HR3.
    apply (cw_at_ret1 regs3 m3 md3 J3 HF3 HK3).
    rewrite HR3, E10', cw_signed_small by lia. reflexivity.
Qed.

End Entry.
End Walk.

(* The frozen statement. *)
Theorem wire_check_width_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (B : asyms) (MT : ameter_ops),
  @wire_check_width_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT HCELLS HOWN HERR LAWS MTL LEAF.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n.
  intros HJ Hra Hra4 Hgp Htp H10 Hal Hwlo Hwhi Hn Hrom Hnev.
  rewrite cw_entry_eq.
  eapply cw_entry; eassumption.
Qed.
