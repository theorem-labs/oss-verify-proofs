(* check_read_seg3: the proof of crd_seg_S3_stmt (lib/A/Prog/check_read_segs.v), segment S3 of the image-A walk of
   check_read (fuzz_wire.asan 0x8077c + 0x1a4 .. + 0x35c): the `got != want` test, the loop set-up and the comparison
   of the twelve samples.
   s3_loop0 is the loop on a declined read (got = 0): v still holds UNTOUCHED_SAMPLE and the loop stores nothing.
   s3_loop1 is the loop on a taken read (got = 1): each iteration reads the six braid bytes of its group, each behind
   the shadow byte of its address (the partial-granule arms return to the load), stores them to s1 + 0x12 .. s1 + 0x17,
   reads three of them back and compares the sign-extended 24-bit sample with v[s]. Every read of c, of its shadow and
   of v lies below s1 and comes from the entry memory through the munch fact of the six stores.
   crd_seg_S3_ok steps the `bne` and the set-up and applies one of the two loops at the first iteration.
   Text ported from this unit: s3_le4s_read is lib/Prog/check_read.v le4s_read over this image's rsegs; s3_chk is
   lib/A/Prog/check_read_walk_kit.v crk_chk with the generalized register given as a term and the arm as a tactic;
   s3_loop1 follows lib/Prog/check_read.v cr_loop; s3_word_eq follows lib/Prog/check_read.v wsamp_eq for this
   image's sign extension (slli 56 / srai 56 / and -0x1000000). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import check_read_segs check_read_walk_kit.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_read_c rp_slot_width_c check_read.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PCR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.check_read.

(* ---- helpers over this image's rsegs ---- *)

Lemma s3_wa : forall (w : word) a, bv_unsigned w = a -> w = wa a.
Proof. intros w a E. unfold wa. rewrite <- E. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma s3_rd_w : forall mm (w : word) a n bs, ov_read_bytes rsegs mm (wa a) n = Some bs -> bv_unsigned w = a ->
  ov_read_bytes rsegs mm w n = Some bs.
Proof. intros mm w a n bs H E. rewrite (s3_wa w a E). exact H. Qed.

Lemma s3_rd_wk : forall mm (w : word) k a n bs, ov_read_bytes rsegs mm (wa a) n = Some bs -> bv_unsigned w + k = a ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned w + k)) n = Some bs.
Proof. intros mm w k a n bs H E. rewrite E. exact H. Qed.

Lemma s3_tp : forall m mm (S a : Z) b, mrd rsegs m (wa a) = Some b -> S + 24 <= 2 ^ 64 ->
  munch [(S + 18, S + 24)] m mm -> 0 <= a < S + 18 -> mrd rsegs mm (wa a) = Some b.
Proof. intros m mm S a b H HS MU Ha. apply (mrd_tp m mm (S + 18) (S + 24) a b MU); [lia | lia | exact H]. Qed.

Lemma s3_le4s_read : forall m A f i, bytes_at rsegs m A (PCR.le4s f) -> 0 <= i < 12 ->
  ov_read_bytes rsegs m (wa (A + 4 * i)) 4 = Some (le4 (Z_to_bv 64 (f i))).
Proof.
  intros m A f i H Hi.
  assert (L : length (PCR.le4s f) = 48%nat)
    by (unfold PCR.le4s; cbn [seq flat_map]; rewrite !length_app, !length_le4; reflexivity).
  rewrite (bytes_at_read rsegs m A (PCR.le4s f) (4 * i) 4 H) by lia. f_equal.
  replace (Z.to_nat (4 * i)) with (4 * Z.to_nat i)%nat by lia.
  unfold PCR.le4s. rewrite (PCR.flat4_nth (fun s => le4 (Z_to_bv 64 (f (Z.of_nat s)))))
    by (first [intros; apply length_le4 | lia]).
  cbn [Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma s3_cell1 : forall mm A cs k b, rw_cells rsegs mm A cs -> cell_at cs k = Some (C1 b) ->
  ov_read_bytes rsegs mm (wa (A + Z.of_nat k)) 1 = Some [b].
Proof. intros mm A cs k b H E. exact (rw_cells_read rsegs mm A cs k (C1 b) H E). Qed.

Lemma s3_merge6 : forall mm A cs, rw_cells rsegs mm A cs -> cells_size cs = 6%nat ->
  exists J, rw_cells rsegs mm A [CB 6 J].
Proof.
  intros mm A cs H Hs.
  assert (H' : rw_cells rsegs mm A ([] ++ cs ++ [])) by (rewrite app_nil_r; exact H).
  apply rw_cells_merge in H'. rewrite Hs in H'. exists (cells_bytes cs). exact H'.
Qed.

Lemma s3_eqb0 : forall (w : word) z, bv_unsigned w = z -> bv_eqb w (Z_to_bv 64 0) = (z =? 0).
Proof. intros w z E. unfold bv_eqb. rewrite E. reflexivity. Qed.

Lemma s3_read01 : forall n bs sl, PSR.rp_slot_read_model n bs sl = 0 \/ PSR.rp_slot_read_model n bs sl = 1.
Proof. intros n bs sl. unfold PSR.rp_slot_read_model. destruct (_ <? 0); auto. Qed.

(* The 64-bit word image A's code builds from the three bytes be[at], be[at + 1], be[at + 2] (+0x2b4 .. +0x2d4:
   `slli s6, s4, 56`, `slli s4, s4, 16`, `slli a0, a0, 8`, `srai s6, s6, 56`, `or s4, s4, s5`, `or a0, s4, a0`,
   `and s4, s6, t4` with t4 = -0x1000000, `or a0, a0, s4`): the 24-bit sample, sign-extended. *)
Definition s3_word (hi mid lo : byte) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64
    (Z.shiftl (bv_unsigned (zxb hi)) 16))) (bv_unsigned (zxb lo))))) (bv_unsigned (Z_to_bv 64 (Z.shiftl
    (bv_unsigned (zxb mid)) 8)))))) (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed
    (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb hi)) 56))) 56))) 18446744073692774400)))).

Lemma s3_word_eq : forall hi mid lo : byte, s3_word hi mid lo = Z_to_bv 64 (PCR.samp24 hi mid lo).
Proof.
  intros hi mid lo. unfold s3_word, PCR.samp24, zxb. cbv zeta.
  pose proof (byte_range hi) as Rh. pose proof (byte_range mid) as Rm. pose proof (byte_range lo) as Rl.
  rewrite (unsigned_lit (bv_unsigned hi)), (unsigned_lit (bv_unsigned mid)), (unsigned_lit (bv_unsigned lo)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (bv_unsigned hi * 2 ^ 16)), (unsigned_lit (bv_unsigned mid * 2 ^ 8)) by lia.
  rewrite (Z.lor_comm (bv_unsigned hi * 2 ^ 16)), (PCR.lor_disj (bv_unsigned lo) (bv_unsigned hi) 16) by lia.
  rewrite (unsigned_lit (bv_unsigned lo + bv_unsigned hi * 2 ^ 16)) by lia.
  replace (Z.lor (bv_unsigned lo + bv_unsigned hi * 2 ^ 16) (bv_unsigned mid * 2 ^ 8))
    with (bv_unsigned lo + bv_unsigned mid * 2 ^ 8 + bv_unsigned hi * 2 ^ 16).
  2:{ rewrite <- (PCR.lor_disj (bv_unsigned lo) (bv_unsigned hi) 16) by lia.
      rewrite <- Z.lor_assoc, (Z.lor_comm (bv_unsigned hi * 2 ^ 16)), Z.lor_assoc.
      rewrite (PCR.lor_disj (bv_unsigned lo) (bv_unsigned mid) 8) by lia.
      rewrite (PCR.lor_disj (bv_unsigned lo + bv_unsigned mid * 2 ^ 8) (bv_unsigned hi) 16) by lia. reflexivity. }
  rewrite (unsigned_lit (bv_unsigned lo + bv_unsigned mid * 2 ^ 8 + bv_unsigned hi * 2 ^ 16)) by lia.
  replace 18446744073692774400 with (2 ^ 64 - 2 ^ 24) by reflexivity.
  destruct (Z.ltb_spec (bv_unsigned hi) 128) as [H|H].
  - rewrite (PCR.signed_lit (bv_unsigned hi * 2 ^ 56)) by lia.
    rewrite Z.shiftr_div_pow2, Z.div_mul by lia.
    rewrite (unsigned_lit (bv_unsigned hi)) by lia.
    rewrite PCR.land_hi by lia. rewrite (Z.div_small (bv_unsigned hi)) by lia. rewrite Z.mul_0_r.
    rewrite (unsigned_lit 0) by lia. rewrite Z.lor_0_r.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. f_equal. lia.
  - replace (Z_to_bv 64 (bv_unsigned hi * 2 ^ 56)) with (Z_to_bv 64 ((bv_unsigned hi - 256) * 2 ^ 56))
      by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
    rewrite (PCR.signed_lit ((bv_unsigned hi - 256) * 2 ^ 56)) by lia.
    rewrite Z.shiftr_div_pow2, Z.div_mul by lia.
    rewrite (unsigned_lit_wrap (bv_unsigned hi - 256)).
    replace ((bv_unsigned hi - 256) mod 2 ^ 64) with (bv_unsigned hi - 256 + 2 ^ 64)
      by (apply Z.mod_unique with (q := -1); lia).
    rewrite PCR.land_hi by lia.
    replace ((bv_unsigned hi - 256 + 2 ^ 64) / 2 ^ 24) with (2 ^ 40 - 1)
      by (apply Z.div_unique with (r := bv_unsigned hi - 256 + 2 ^ 24); lia).
    rewrite unsigned_lit by lia.
    replace (2 ^ 24 * (2 ^ 40 - 1)) with ((2 ^ 40 - 1) * 2 ^ 24) by ring.
    rewrite (PCR.lor_disj _ (2 ^ 40 - 1) 24) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. apply Z_to_bv_eqm. Z.div_mod_to_equations. lia.
Qed.

Lemma s3_eqb_refl : forall w : word, bv_eqb w w = true.
Proof. intros w. unfold bv_eqb. apply Z.eqb_refl. Qed.

(* A branch on a closed condition. *)
Ltac s3_if :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let c' := eval vm_compute in c in change c with c'; cbv iota
  end.

(* The shadow test of a byte (lib/A/Prog/check_read_walk_kit.v crk_chk, with the register the arm's `andi` writes given
   as a term): k = 0 falls through; otherwise the arm `andi`, then `bge` (not taken) and `j` back (arm = the `j`), or
   `blt` back (arm = idtac), returns to the load because the partial granule holds the byte. Both reach the load with
   only that register changed. *)
Ltac s3_chk SK U MB k reg arm :=
  lazymatch goal with
  | |- ExecF.evtF ?s ?RNG ?Q (MS ?R ?F (if _ then _ else ?pE) ?fc ?rv ?m ?ro) =>
      let Rf := eval pattern reg in R in
      lazymatch Rf with
      | ?g reg =>
        let K := fresh "K" in
        assert (K : forall x : word, ExecF.evtF s RNG Q (MS (g x) F pE fc rv m ro));
        [ let x := fresh "z" in intro x; cbv beta; clear SK MB
        | let C := fresh "C" in let Cu := fresh "Cu" in destruct SK as [C|[C Cu]];
          [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]; exact (K reg)
          | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
            rewrite land7, ?U, (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb]; arm; apply K ] ]
      end
  end.

Ltac s3_st := rewrite ?le1_zxb; mem_after_store_opt.

(* ---- the loop on a declined read (got = 0): v is still UNTOUCHED_SAMPLE; no store ---- *)
Section L0.
Variables (RNG : ExecF.footprint) (x1 x2 x3 x4 x8 x9 x18 x23 x25 x27 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (v : Z) (Q : machine_state -> Prop).
Hypothesis HV0 : 0 <= v.
Hypothesis HV1 : v + 48 < 2 ^ 64.
Hypothesis BV : bytes_at rsegs m v (repeat (Z_to_bv 8 90) 48).
Hypothesis RV : ExecF.rng RNG v 48.

Local Abbreviation L0ST pc x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31 :=
  (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 1515870810) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
           (Z_to_bv 64 ASAN_K) x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Hypothesis K0 : forall x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31 : word,
  ExecF.evtF rsegs RNG Q (L0ST 0x80ad8 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31).

Lemma s3_loop0 : forall k i (x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31 : word),
  Z.of_nat k = 12 - i -> 0 <= i < 12 -> bv_unsigned x17 = 12 - i -> bv_unsigned x19 = v + 4 * i ->
  ExecF.evtF rsegs RNG Q (L0ST 0x80978 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros i x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31 Hk Hi U17 U19;
    [lia|].
  pose proof BV as BV'. rewrite PCR.v0_le4s in BV'.
  pose proof (s3_rd_w m x19 (v + 4 * i) 4 _ (s3_le4s_read m v _ i BV' Hi) U19) as R.
  pose proof (rng_sub' _ _ _ (bv_unsigned x19) 4 RV ltac:(lia)) as R19.
  (* lw t6, 0(s3); beqz s10 (taken); bne t6, t1 (not taken) *)
  step. clear R BV'.
  step. s3_if.
  step. s3_if.
  (* s3 += 4, a1 .. a6 / t5 += t0, a7 -= 1 *)
  step. gen_addi x19 y19 V19.
  do 2 step.
  step. gen_addi x17 y17 V17.
  do 5 step.
  (* beqz a7 *)
  step. rewrite (s3_eqb0 y17 (12 - i + -1)) by lia.
  destruct k as [|k].
  - rewrite (proj2 (Z.eqb_eq _ 0)) by lia. cbv iota. apply K0.
  - rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbv iota. step.
    apply (IH (i + 1)); lia.
Qed.
End L0.

(* ---- the loop on a taken read (got = 1): the six braid bytes of each group, behind their shadow bytes ---- *)
Section L1.
Variables (RNG : ExecF.footprint) (x1 x2 x3 x4 x6 x8 x9 x18 x23 x25 wt0 wt2 w28 : word) (F : bvmap 5 word)
  (fc : bv 32) (m : word -> option byte) (wc wn : word) (v W sl : Z) (bs : list byte) (Q : machine_state -> Prop).
Hypothesis HX9 : bv_unsigned x9 + 24 <= 2 ^ 64.
Hypothesis HV0 : 4096 <= v.
Hypothesis HV1 : v + 48 <= bv_unsigned x9.
Hypothesis HL : Z.of_nat (length bs) = bv_unsigned wn.
Hypothesis HW : 2 <= W <= 40.
Hypothesis HWe : W mod 2 = 0.
Hypothesis HWn : 52 + 36 * W <= bv_unsigned wn.
Hypothesis Hsl : 0 <= sl < W.
Hypothesis BV : bytes_at rsegs m v (PSR.rp_slot_bytes bs W sl).
Hypothesis BC : bytes_at rsegs m (bv_unsigned wc) bs.
Hypothesis ADR : addressable m (bv_unsigned wc) (bv_unsigned wn).
Hypothesis HC1 : bv_unsigned wc + bv_unsigned wn <= bv_unsigned x9.
Hypothesis HC2 : shadow_addr (bv_unsigned wc + bv_unsigned wn) <= bv_unsigned x9.
Hypothesis RC : ExecF.rng RNG (bv_unsigned wc) (bv_unsigned wn).
Hypothesis RSH : ExecF.rng RNG (shadow_addr (bv_unsigned wc))
  (shadow_addr (bv_unsigned wc + bv_unsigned wn - 1) - shadow_addr (bv_unsigned wc) + 1).
Hypothesis RV : ExecF.rng RNG v 48.
Hypothesis RJ : ExecF.rng RNG (bv_unsigned x9 + 18) 6.
Hypothesis Ut0 : bv_unsigned wt0 = 3 * W.
Hypothesis Ut2 : bv_unsigned wt2 = 3 * (sl - sl mod 2).
Hypothesis U28 : bv_unsigned w28 = bv_unsigned x9 + 18 + 3 * (sl mod 2).

Local Abbreviation L1ST pc x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x30 x31 mk :=
  (MS (mkR x1 x2 x3 x4 wt0 x6 wt2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
           (Z_to_bv 64 ASAN_K) x25 (Z_to_bv 64 1) (Z_to_bv 64 W) w28 (Z_to_bv 64 (-16777216)) x30 x31)
      F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

Hypothesis K1 : forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y28 y29 y30 y31 : word) mk,
  munch [(bv_unsigned x9 + 18, bv_unsigned x9 + 24)] m mk -> wmono rsegs m mk ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 y19 y20 y21 y22 x23
             (Z_to_bv 64 ASAN_K) x25 (Z_to_bv 64 1) (Z_to_bv 64 W) y28 y29 y30 y31)
        F (Z_to_bv 64 0x80ad8) fc None mk (seg_rom rsegs)).

Lemma s3_loop1 : forall k i (x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x30 x31 : word) mk J,
  Z.of_nat k = 12 - i -> 0 <= i < 12 ->
  bv_unsigned x14 = bv_unsigned wc + 50 + 3 * W * i -> bv_unsigned x30 = bv_unsigned wc + 50 + 3 * W * i ->
  bv_unsigned x16 = bv_unsigned wc + 51 + 3 * W * i -> bv_unsigned x13 = bv_unsigned wc + 52 + 3 * W * i ->
  bv_unsigned x15 = bv_unsigned wc + 53 + 3 * W * i -> bv_unsigned x11 = bv_unsigned wc + 54 + 3 * W * i ->
  bv_unsigned x12 = bv_unsigned wc + 55 + 3 * W * i ->
  bv_unsigned x17 = 12 - i -> bv_unsigned x19 = v + 4 * i ->
  munch [(bv_unsigned x9 + 18, bv_unsigned x9 + 24)] m mk -> wmono rsegs m mk ->
  rw_cells rsegs mk (bv_unsigned x9 + 18) [CB 6 J] ->
  ExecF.evtF rsegs RNG Q (L1ST 0x80978 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x30 x31 mk).
Proof.
  induction k as [|k IH]; intros i x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x30 x31 mk J
    Hk Hi U14 U30 U16 U13 U15 U11 U12 U17 U19 MU WM FR; [lia|].
  pose proof (zr_word wc) as Rwc. pose proof (zr_word wn) as Rwn. pose proof (zr_word x9) as Rx9.
  unfold inr64 in Rwc, Rwn, Rx9.
  assert (QB : 0 <= 3 * W * i <= 33 * W).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    replace (33 * W) with (3 * W * 11) by ring. apply Z.mul_le_mono_nonneg_l; lia. }
  assert (SLB : 0 <= 3 * (sl - sl mod 2) <= 3 * W - 6) by (Z.div_mod_to_equations; lia).
  (* +0x2e8: s3 += 4, a1 .. a6 / t5 += t0, a7 -= 1, `beqz a7` to +0x35c, else back to +0x1fc *)
  assert (KX : forall (z10 z20 z21 z22 z31 : word) mm,
    munch [(bv_unsigned x9 + 18, bv_unsigned x9 + 24)] m mm -> wmono rsegs m mm ->
    (exists J', rw_cells rsegs mm (bv_unsigned x9 + 18) [CB 6 J']) ->
    ExecF.evtF rsegs RNG Q (L1ST 0x80a64 z10 x11 x12 x13 x14 x15 x16 x17 x19 z20 z21 z22 x30 z31 mm)).
  { intros z10 z20 z21 z22 z31 mm MU' WM' [J' FR'].
    step. gen_addi x19 y19 V19.
    step. gen_add x11 wt0 y11 V11.
    step. gen_add x12 wt0 y12 V12.
    step. gen_addi x17 y17 V17.
    step. gen_add x13 wt0 y13 V13.
    step. gen_add x30 wt0 y30 V30.
    step. gen_add x15 wt0 y15 V15.
    step. gen_add x14 wt0 y14 V14.
    step. gen_add x16 wt0 y16 V16.
    step. rewrite (s3_eqb0 y17 (12 - i + -1)) by lia.
    destruct k as [|k].
    - rewrite (proj2 (Z.eqb_eq _ 0)) by lia. cbv iota. apply K1; assumption.
    - rewrite (proj2 (Z.eqb_neq _ 0)) by lia. cbv iota. step.
      apply (IH (i + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm J'); try assumption; lia. }
  remember (50 + 3 * W * i + 3 * (sl - sl mod 2)) as Q0 eqn:EQ0.
  assert (QR : 50 <= Q0 /\ Q0 + 6 <= bv_unsigned wn) by lia.
  pose proof HC2 as HC2'. unfold shadow_addr, ASAN_K in HC2'.
  unfold ASAN_K.
  (* v[i], read through the run's memory *)
  pose proof (bytes_tp m mk (bv_unsigned x9 + 18) (bv_unsigned x9 + 24) v _ MU
    ltac:(rewrite PCR.rp_slot_bytes_length; lia) BV) as BVk.
  change (PSR.rp_slot_bytes bs W sl) with (PCR.le4s (fun s => PSR.rp_sample bs W sl s)) in BVk.
  pose proof (s3_rd_w mk x19 (v + 4 * i) 4 _ (s3_le4s_read mk v _ i BVk Hi) U19) as R.
  pose proof (rng_sub' _ _ _ (bv_unsigned x19) 4 RV ltac:(lia)) as R19.
  destruct ADR as (P0 & N0 & PE & AB).
  (* +0x1fc `lw t6, 0(s3)`; `beqz s10` not taken *)
  step. clear R BVk.
  step. if_false_by (crk_beqz 1 ltac:(lia)).
  (* g[1]: its address a0 = t2 + x16, the shadow byte, the test *)
  destruct (AB (Q0 + 1) ltac:(lia)) as (_ & k1 & MK1 & SK1).
  pose proof (crk_shadow_byte_rng RNG (bv_unsigned wc) (bv_unsigned wn) (Q0 + 1) ltac:(lia) RSH) as RS1.
  pose proof (Z.mod_pos_bound (bv_unsigned wc + (Q0 + 1)) 8 ltac:(lia)) as MB1.
  unfold shadow_addr, shadow_ok, ASAN_K in MK1, SK1, RS1.
  step. gen_add wt2 x16 e1 E1.
  assert (E1' : bv_unsigned e1 = bv_unsigned wc + (Q0 + 1)) by lia. clear E1.
  step. gen_shr e1 g1 G1. rewrite E1' in G1.
  step. gen_addi g1 h1 H1.
  pose proof (rng_sub' _ _ _ (bv_unsigned h1) 1 RS1 ltac:(lia)) as RH1.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ MK1 HX9 MU ltac:(lia)) as M).
  pose proof (rdw0 _ h1 _ _ M ltac:(lia)) as R. step. clear R M MK1 RS1.
  step.
  s3_chk SK1 E1' MB1 k1 x21 ltac:(cbv iota; step).
  clear E1' G1 H1 RH1.
  (* g = t5 + t2 *)
  step. gen_add x30 wt2 gw UG.
  assert (UG' : bv_unsigned gw = bv_unsigned wc + Q0) by lia. clear UG.
  pose proof (rng_sub' _ _ _ (bv_unsigned gw) 6 RC ltac:(lia)) as RG.
  (* `add a0, t2, a4`, then `lbu s6, 1(s4)` before g[0]'s shadow byte *)
  destruct (AB (Q0 + 0) ltac:(lia)) as (_ & k0 & MK0 & SK0).
  pose proof (crk_shadow_byte_rng RNG (bv_unsigned wc) (bv_unsigned wn) (Q0 + 0) ltac:(lia) RSH) as RS0.
  pose proof (Z.mod_pos_bound (bv_unsigned wc + (Q0 + 0)) 8 ltac:(lia)) as MB0.
  unfold shadow_addr, shadow_ok, ASAN_K in MK0, SK0, RS0.
  step. gen_add wt2 x14 e0 E0.
  assert (E0' : bv_unsigned e0 = bv_unsigned wc + (Q0 + 0)) by lia. clear E0.
  pose proof (bytes_nth m _ bs (Z.to_nat (Q0 + 1)) BC ltac:(lia)) as FB. rewrite Z2Nat.id in FB by lia.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ FB HX9 MU ltac:(lia)) as M).
  pose proof (rdw _ gw 1 _ _ M ltac:(lia)) as R. step. clear R M FB.
  step. gen_shr e0 g0 G0. rewrite E0' in G0.
  step. gen_addi g0 h0 H0.
  pose proof (rng_sub' _ _ _ (bv_unsigned h0) 1 RS0 ltac:(lia)) as RH0.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ MK0 HX9 MU ltac:(lia)) as M).
  pose proof (rdw0 _ h0 _ _ M ltac:(lia)) as R. step. clear R M MK0 RS0.
  (* `sb s6, 18(s1)`; the test *)
  step. s3_st.
  step.
  let r := reg_val 22 in s3_chk SK0 E0' MB0 k0 r ltac:(cbv iota; step).
  clear E0' G0 H0 RH0.
  (* `lbu s6, 0(s4)` *)
  pose proof (bytes_nth m _ bs (Z.to_nat (Q0 + 0)) BC ltac:(lia)) as FB. rewrite Z2Nat.id in FB by lia.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ FB HX9 MU ltac:(lia)) as M).
  pose proof (rdw0 _ gw _ _ M ltac:(lia)) as R. step. clear R M FB.
  (* g[3]: its address a0 = t2 + x15, the shadow byte, the test *)
  destruct (AB (Q0 + 3) ltac:(lia)) as (_ & k3 & MK3 & SK3).
  pose proof (crk_shadow_byte_rng RNG (bv_unsigned wc) (bv_unsigned wn) (Q0 + 3) ltac:(lia) RSH) as RS3.
  pose proof (Z.mod_pos_bound (bv_unsigned wc + (Q0 + 3)) 8 ltac:(lia)) as MB3.
  unfold shadow_addr, shadow_ok, ASAN_K in MK3, SK3, RS3.
  step. gen_add wt2 x15 e3 E3.
  assert (E3' : bv_unsigned e3 = bv_unsigned wc + (Q0 + 3)) by lia. clear E3.
  step. gen_shr e3 g3 G3. rewrite E3' in G3.
  step. gen_addi g3 h3 H3.
  pose proof (rng_sub' _ _ _ (bv_unsigned h3) 1 RS3 ltac:(lia)) as RH3.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ MK3 HX9 MU ltac:(lia)) as M).
  pose proof (rdw0 _ h3 _ _ M ltac:(lia)) as R. step. clear R M MK3 RS3.
  step. s3_st.
  step.
  let r := reg_val 22 in s3_chk SK3 E3' MB3 k3 r ltac:(cbv iota; step).
  clear E3' G3 H3 RH3.
  pose proof (bytes_nth m _ bs (Z.to_nat (Q0 + 3)) BC ltac:(lia)) as FB. rewrite Z2Nat.id in FB by lia.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ FB HX9 MU ltac:(lia)) as M).
  pose proof (rdw _ gw 3 _ _ M ltac:(lia)) as R. step. clear R M FB.
  (* g[2]: its address a0 = t2 + x13, the shadow byte, the test *)
  destruct (AB (Q0 + 2) ltac:(lia)) as (_ & k2 & MK2 & SK2).
  pose proof (crk_shadow_byte_rng RNG (bv_unsigned wc) (bv_unsigned wn) (Q0 + 2) ltac:(lia) RSH) as RS2.
  pose proof (Z.mod_pos_bound (bv_unsigned wc + (Q0 + 2)) 8 ltac:(lia)) as MB2.
  unfold shadow_addr, shadow_ok, ASAN_K in MK2, SK2, RS2.
  step. gen_add wt2 x13 e2 E2.
  assert (E2' : bv_unsigned e2 = bv_unsigned wc + (Q0 + 2)) by lia. clear E2.
  step. gen_shr e2 g2 G2. rewrite E2' in G2.
  step. gen_addi g2 h2 H2.
  pose proof (rng_sub' _ _ _ (bv_unsigned h2) 1 RS2 ltac:(lia)) as RH2.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ MK2 HX9 MU ltac:(lia)) as M).
  pose proof (rdw0 _ h2 _ _ M ltac:(lia)) as R. step. clear R M MK2 RS2.
  step. s3_st.
  step.
  let r := reg_val 22 in s3_chk SK2 E2' MB2 k2 r ltac:(cbv iota; step).
  clear E2' G2 H2 RH2.
  pose proof (bytes_nth m _ bs (Z.to_nat (Q0 + 2)) BC ltac:(lia)) as FB. rewrite Z2Nat.id in FB by lia.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ FB HX9 MU ltac:(lia)) as M).
  pose proof (rdw _ gw 2 _ _ M ltac:(lia)) as R. step. clear R M FB.
  (* g[5]: its address a0 = t2 + x12, the shadow byte, the test *)
  destruct (AB (Q0 + 5) ltac:(lia)) as (_ & k5 & MK5 & SK5).
  pose proof (crk_shadow_byte_rng RNG (bv_unsigned wc) (bv_unsigned wn) (Q0 + 5) ltac:(lia) RSH) as RS5.
  pose proof (Z.mod_pos_bound (bv_unsigned wc + (Q0 + 5)) 8 ltac:(lia)) as MB5.
  unfold shadow_addr, shadow_ok, ASAN_K in MK5, SK5, RS5.
  step. gen_add wt2 x12 e5 E5.
  assert (E5' : bv_unsigned e5 = bv_unsigned wc + (Q0 + 5)) by lia. clear E5.
  step. gen_shr e5 g5 G5. rewrite E5' in G5.
  step. gen_addi g5 h5 H5.
  pose proof (rng_sub' _ _ _ (bv_unsigned h5) 1 RS5 ltac:(lia)) as RH5.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ MK5 HX9 MU ltac:(lia)) as M).
  pose proof (rdw0 _ h5 _ _ M ltac:(lia)) as R. step. clear R M MK5 RS5.
  step. s3_st.
  step.
  let r := reg_val 22 in s3_chk SK5 E5' MB5 k5 r ltac:(cbv iota; step).
  clear E5' G5 H5 RH5.
  pose proof (bytes_nth m _ bs (Z.to_nat (Q0 + 5)) BC ltac:(lia)) as FB. rewrite Z2Nat.id in FB by lia.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ FB HX9 MU ltac:(lia)) as M).
  pose proof (rdw _ gw 5 _ _ M ltac:(lia)) as R. step. clear R M FB.
  (* g[4]: its address a0 = t2 + x11, the shadow byte, the test *)
  destruct (AB (Q0 + 4) ltac:(lia)) as (_ & k4 & MK4 & SK4).
  pose proof (crk_shadow_byte_rng RNG (bv_unsigned wc) (bv_unsigned wn) (Q0 + 4) ltac:(lia) RSH) as RS4.
  pose proof (Z.mod_pos_bound (bv_unsigned wc + (Q0 + 4)) 8 ltac:(lia)) as MB4.
  unfold shadow_addr, shadow_ok, ASAN_K in MK4, SK4, RS4.
  step. gen_add wt2 x11 e4 E4.
  assert (E4' : bv_unsigned e4 = bv_unsigned wc + (Q0 + 4)) by lia. clear E4.
  step. gen_shr e4 g4 G4. rewrite E4' in G4.
  step. gen_addi g4 h4 H4.
  pose proof (rng_sub' _ _ _ (bv_unsigned h4) 1 RS4 ltac:(lia)) as RH4.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ MK4 HX9 MU ltac:(lia)) as M).
  pose proof (rdw0 _ h4 _ _ M ltac:(lia)) as R. step. clear R M MK4 RS4.
  step. s3_st.
  step.
  let r := reg_val 22 in s3_chk SK4 E4' MB4 k4 r ltac:(idtac).
  clear E4' G4 H4 RH4.
  (* +0x2a8 `lbu a0, 4(s4)` *)
  pose proof (bytes_nth m _ bs (Z.to_nat (Q0 + 4)) BC ltac:(lia)) as FB. rewrite Z2Nat.id in FB by lia.
  crk_memF ltac:(fun mm => pose proof (s3_tp m mm (bv_unsigned x9) _ _ FB HX9 MU ltac:(lia)) as M).
  pose proof (rdw _ gw 4 _ _ M ltac:(lia)) as R. step. clear R M FB.
  pose proof (rng_sub' _ _ _ (bv_unsigned w28) 3 RJ ltac:(lia)) as RT.
  assert (P2 : sl mod 2 = 0 \/ sl mod 2 = 1) by lia.
  destruct P2 as [P2|P2].
  - (* even slot: the sample is be[0..2] = g[1], g[0], g[3] *)
    pose proof (s3_cell1 _ _ _ 0 _ FR ltac:(reflexivity)) as B.
    pose proof (s3_rd_w _ w28 _ 1 _ B ltac:(lia)) as R. step. clear R B.
    step. s3_st.
    pose proof (s3_cell1 _ _ _ 1 _ FR ltac:(reflexivity)) as B.
    pose proof (s3_rd_wk _ w28 1 _ 1 _ B ltac:(lia)) as R. step. clear R B.
    pose proof (s3_cell1 _ _ _ 2 _ FR ltac:(reflexivity)) as B.
    pose proof (s3_rd_wk _ w28 2 _ 1 _ B ltac:(lia)) as R. step. clear R B.
    do 8 step.
    (* +0x2b4 .. +0x2d4: the sample; `bne t6, a0` not taken; `j` to +0x2e8 *)
    rewrite (PCR.rps bs W sl i (Z.to_nat (Q0 + 3)) (Z.to_nat (Q0 + 0)) (Z.to_nat (Q0 + 1)))
      by (unfold PSR.braid_pos; cbv zeta; rewrite P2; cbn [Z.eqb Pos.eqb]; f_equal; lia).
    rewrite PCR.sx32_lit
      by (match goal with |- context [PCR.samp24 ?a ?b ?c] => pose proof (PCR.samp24_range a b c) end; lia).
    let E := fresh "E" in pose proof s3_word_eq as E; unfold s3_word in E; rewrite E; clear E.
    step. rewrite s3_eqb_refl. cbn [negb]; cbv iota.
    step.
    apply KX; [assumption | assumption | eapply s3_merge6; [exact FR | reflexivity]].
  - (* odd slot: the sample is be[3..5] = g[2], g[5], g[4] *)
    pose proof (s3_cell1 _ _ _ 3 _ FR ltac:(reflexivity)) as B.
    pose proof (s3_rd_w _ w28 _ 1 _ B ltac:(lia)) as R. step. clear R B.
    step. s3_st.
    pose proof (s3_cell1 _ _ _ 4 _ FR ltac:(reflexivity)) as B.
    pose proof (s3_rd_wk _ w28 1 _ 1 _ B ltac:(lia)) as R. step. clear R B.
    pose proof (s3_cell1 _ _ _ 5 _ FR ltac:(reflexivity)) as B.
    pose proof (s3_rd_wk _ w28 2 _ 1 _ B ltac:(lia)) as R. step. clear R B.
    do 8 step.
    (* +0x2b4 .. +0x2d4: the sample; `bne t6, a0` not taken; `j` to +0x2e8 *)
    rewrite (PCR.rps bs W sl i (Z.to_nat (Q0 + 4)) (Z.to_nat (Q0 + 5)) (Z.to_nat (Q0 + 2)))
      by (unfold PSR.braid_pos; cbv zeta; rewrite P2; cbn [Z.eqb Pos.eqb]; f_equal; lia).
    rewrite PCR.sx32_lit
      by (match goal with |- context [PCR.samp24 ?a ?b ?c] => pose proof (PCR.samp24_range a b c) end; lia).
    let E := fresh "E" in pose proof s3_word_eq as E; unfold s3_word in E; rewrite E; clear E.
    step. rewrite s3_eqb_refl. cbn [negb]; cbv iota.
    step.
    apply KX; [assumption | assumption | eapply s3_merge6; [exact FR | reflexivity]].
Qed.
End L1.

Lemma crd_seg_S3_ok : crd_seg_S3_stmt.
Proof.
  unfold crd_seg_S3_stmt.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 wc wn ws v F fc m
    bs j6 HN HL HV0 HV1 HX9 H1 H0 FR RV RJ.
  lazymatch goal with |- ExecF.evtF _ _ ?P _ => set (QQ := P) end.
  pose proof (zr_word wc) as Rwc. pose proof (zr_word wn) as Rwn. pose proof (zr_word ws) as Rws.
  pose proof (zr_word x9) as Rx9. unfold inr64 in Rwc, Rwn, Rws, Rx9.
  (* +0x1a4 `bne a0, s10`: a0 = s10 = got *)
  step. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb]; cbv iota.
  (* +0x1a8 .. +0x1f8 the loop set-up *)
  do 21 step.
  destruct (s3_read01 (bv_unsigned wn) bs (bv_signed ws)) as [G|G].
  - (* declined: v is untouched *)
    specialize (H0 G). rewrite G.
    eapply s3_loop0 with (k := 12%nat) (i := 0).
    all: try exact H0. all: try exact RV. all: try lia.
    all: try (rewrite unsigned_lit by lia; lia).
    intros. apply evtF_done. unfold QQ. cbv beta. exists m. do 19 eexists.
    split; [rewrite G; reflexivity | split; [apply munch_refl | apply wmono_refl]].
  - (* read: v holds the slot's samples *)
    destruct (H1 G) as (E27 & BV & BC & ADR & HC1 & HC2 & RC & RSH). subst x27.
    rewrite G.
    assert (W0 : 0 <= PSW.rp_slot_width_model (bv_unsigned wn) bs (bv_signed ws)).
    { revert G. unfold PSR.rp_slot_read_model.
      destruct (Z.ltb_spec (PSW.rp_slot_width_model (bv_unsigned wn) bs (bv_signed ws)) 0);
        [intros E; discriminate E | intros _; lia]. }
    destruct (PCR.width_facts (bv_unsigned wn) bs (bv_signed ws) ltac:(lia) W0) as (HW & HWe & Hsl & HWn & _).
    pose proof (PCR.signed_nonneg ws ltac:(lia)) as Usl.
    let t := reg_val 5 in
    assert (Ut0 : bv_unsigned t = 3 * PSW.rp_slot_width_model (bv_unsigned wn) bs (bv_signed ws))
      by (rewrite (unsigned_lit (PSW.rp_slot_width_model (bv_unsigned wn) bs (bv_signed ws))) by lia;
          rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2; rewrite unsigned_lit by lia; lia).
    let t := reg_val 7 in
    assert (Ut2 : bv_unsigned t = 3 * (bv_signed ws - bv_signed ws mod 2))
      by (rewrite (PCR.land_m2 (bv_unsigned ws)) by lia;
          rewrite (unsigned_lit (2 * (bv_unsigned ws / 2))) by (Z.div_mod_to_equations; lia);
          rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2;
          rewrite unsigned_lit by (Z.div_mod_to_equations; lia); rewrite Usl; Z.div_mod_to_equations; lia).
    let t := reg_val 28 in
    assert (U28 : bv_unsigned t = bv_unsigned x9 + 18 + 3 * (bv_signed ws mod 2))
      by (rewrite PCR.at_bits; rewrite unsigned_lit by (Z.div_mod_to_equations; lia); reflexivity).
    eapply s3_loop1 with (k := 12%nat) (i := 0) (mk := m) (J := j6).
    all: try eassumption.
    all: try lia.
    all: try (rewrite unsigned_lit by lia; lia).
    all: try apply munch_refl. all: try apply wmono_refl.
    intros. apply evtF_done. unfold QQ. cbv beta. exists mk. do 19 eexists.
    split; [rewrite G; reflexivity | split; assumption].
Qed.
