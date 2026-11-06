(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/reac-repacer/fuzz_uci/lib/Prog/check_value.v (the plain
   image's Section Ev: loop_dg, loop_tb, seg_trail, ev_tail, ev_ee8, ev_dgt and their model helpers) and from
   proofs/libreac/fuzz_decode/lib/A/Prog/crtA_loop.v at origin/ossv/recipes 88154566652a (crt_sh1F, the shadow-check
   site lemma cl1_F, takeF, crt_lits); the walk runs on image A's code (fuzz_uci.asan, the check_value addresses
   CV_AT 0x128 .. CV_AT 0x21c of lib/A/Prog/UciCvIface.v, its registers, and the ASan load check before each reply
   byte) as footprint runs (lib/Lib/ExecF.v evtF, stepped by lib/Lib/StepF.v). *)
(* UciCvEvB: the second half of the inlined expected_value of check_value in image A, from the digit loop's set-up
   (+0x128) to +0x21c: it proves UciCvIface.v's cv_dgt_stmt_F as cv_dgt_holds.

   The code (offsets from CV_ENTRY):
     +0x128 a3 := 0 (the value v), a6 := 9, a7 := 10, t0 := 10^10, a5 := a4 (= d0)
     +0x144 the digit loop, index a5: the shadow check of a0 := s3 + a5 (slow path +0x180, report +0x188), lbu a0;
            t1 := a0 - 0x30; `bltu a6, t1` to +0x190 (not a digit); `bge a3, t0` to +0x174 (v stops growing at
            10^10); a3 := a3 * a7 + (a0 & 0xf); +0x174 a5 += 1; `bne a1, a5` back; `j` +0x18c, a5 := a1
     +0x190 `beq a5, a4` to +0x21c (no digit read); +0x194 `bgeu a5, a1` to +0x200
     +0x198 a4 := -a5, a6 := -a1, a5 := a5 + s3, a7 := 0x20, t0 := 0x100002200 (the {9, 13, 32} mask), a0 := a5
     +0x1b8 the trailing-blank loop, a0 = a5 = r + p, a4 = -p: the shadow check of a0 (slow path +0x1f0, report
            +0x1f8), lbu t1 of a5; `bltu a7, t1` to +0x1fc; `beqz` of bit t1 of t0 to +0x1fc; a4 -= 1, a0 += 1,
            a5 += 1; `bne a6, a4` back; `j` +0x204
     +0x1fc a5 := -a4; +0x200 `bne a5, a1` to +0x21c (trailing junk)
     +0x204 `bne a2, '-'` over the `neg a3`; +0x210 `sext.w a0, a3`; `bne a0, a3` to +0x21c (out of int range);
            s0 := a3; +0x21c. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import AsanKA AsanKAProof UciPSyms UciPAddr
  UciCvIface.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---------------- model and bit-level helpers (lib/Prog/check_value.v:44-186) ---------------- *)

Lemma u8lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma zxb_lit : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zxb. rewrite u8lit by exact Hc. reflexivity. Qed.

(* the {9, 13, 32} bit mask of the trailing-blank loop *)
Lemma mask_bit : forall c, 0 <= c <= 32 ->
  Z.land (Z.shiftr 4294976000 c) 1 = (if is_trail_blank c then 1 else 0).
Proof.
  intros c Hc.
  assert (E : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/
              c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/
              c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/
              c = 31 \/ c = 32) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; reflexivity|]). subst c. vm_compute. reflexivity.
Qed.

Lemma shr_rng : forall c, 0 <= c -> 0 <= Z.shiftr 4294976000 c < 2 ^ 64.
Proof.
  intros c Hc. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) Hc) as Hp.
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with 4294976000; [|lia].
  apply Z.div_le_upper_bound; [lia | nia].
Qed.

Lemma mask_u : forall c, 0 <= c <= 32 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294976000 c))) 1 = (if is_trail_blank c then 1 else 0).
Proof.
  intros c Hc. rewrite (unsigned_lit _ (shr_rng c ltac:(lia))). apply mask_bit. exact Hc.
Qed.

(* the 32-bit sign extension the `sext.w` of the int-range test leaves behind *)
Lemma swrap32 : forall x, bv_swrap 32 x = (x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31). reflexivity.
Qed.

Lemma digit_land : forall c, is_digit c = true -> Z.land c 15 = c - 48.
Proof.
  intros c D. unfold is_digit in D. apply andb_true_iff in D as [D1 D2].
  apply Z.leb_le in D1. apply Z.leb_le in D2.
  change 15 with (2 ^ 4 - 1). rewrite zb_land_mask by lia. change (2 ^ 4) with 16. mlia.
Qed.

Lemma digits_ev_stop : forall v c t, is_digit c = false -> digits_ev v (c :: t) = (v, c :: t).
Proof. intros v c t D. cbn [digits_ev]. rewrite D. reflexivity. Qed.

Lemma digits_ev_step : forall v c t, is_digit c = true ->
  digits_ev v (c :: t) = digits_ev (if v <? 10 ^ 10 then v * 10 + (c - 48) else v) t.
Proof. intros v c t D. cbn [digits_ev]. rewrite D. reflexivity. Qed.

Lemma skip_t : forall f c t, f c = true -> skip f (c :: t) = skip f t.
Proof. intros f c t H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma skip_f : forall f c t, f c = false -> skip f (c :: t) = c :: t.
Proof. intros f c t H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma finish_nil : forall neg v rest cur0, skip is_trail_blank rest = [] ->
  finish neg v rest cur0 = (if ((if neg then - v else v) <? INT_MIN) || (INT_MAX <? (if neg then - v else v))
                            then cur0 else (if neg then - v else v)).
Proof. intros neg v rest cur0 H. unfold finish. rewrite H. reflexivity. Qed.

Lemma finish_rest : forall neg v rest cur0, skip is_trail_blank rest <> [] -> finish neg v rest cur0 = cur0.
Proof.
  intros neg v rest cur0 H. unfold finish.
  destruct (skip is_trail_blank rest); [contradiction | reflexivity].
Qed.

Lemma skipn_inj : forall (l : list Z) i j, (i <= length l)%nat -> (j <= length l)%nat ->
  skipn i l = skipn j l -> i = j.
Proof.
  intros l i j Hi Hj H.
  assert (E : length (skipn i l) = length (skipn j l)) by (rewrite H; reflexivity).
  rewrite !length_skipn in E. lia.
Qed.

(* ---------------- the ASan shadow cover (crtA_loop.v align8_cover, crt_sh1F) ---------------- *)

(* [a, c] inside the 8-aligned cover of [a, c] *)
Lemma align8_cover : forall a b c, a <= b -> b <= c -> a / 8 * 8 <= b /\ b + 1 <= c / 8 * 8 + 8.
Proof. intros a b c H1 H2. split; Z.div_mod_to_equations; lia. Qed.

(* The shadow byte of X + i, for i in [0, n), lies in the 8-aligned cover of the shadow bytes of [X, X + n). *)
Lemma cv_sh1F : forall RNG X n i,
  ExecF.rng RNG (shadow_addr X / 8 * 8)
    (shadow_addr (X + n - 1) / 8 * 8 + 8 - shadow_addr X / 8 * 8) ->
  0 <= i < n ->
  ExecF.rng RNG ((X + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG X n i H Hi. unfold shadow_addr in H.
  assert (L1 : X / 8 <= (X + i) / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : (X + i) / 8 <= (X + n - 1) / 8) by (apply Z.div_le_mono; lia).
  destruct (align8_cover (X / 8 + ASAN_K) ((X + i) / 8 + ASAN_K) ((X + n - 1) / 8 + ASAN_K)
             ltac:(lia) ltac:(lia)) as (A1 & A2).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* ---------------- tactics ---------------- *)

Local Ltac wsub :=
  repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
(* a conditional branch whose condition a Z fact decides (lib/Prog/check_value.v solve_c, with the U walk's
   repeated decide_tests for the nested tests of a signed compare) *)
Local Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; try unfold sx32; rewrite ?zb_signed; zsimp; wsub;
  zsimp; rewrite ?swrap32; do 3 (decide_tests; cbv beta iota); reflexivity.
(* crtA_loop.v takeF *)
Local Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv beta iota | symmetry; solve_c]
  end.
Local Ltac fact := cbv delta [zxb]; wsub; rewrite ?unsigned_lit_wrap; mlia.
(* the same, for a register whose value the walk built from literal shifts (the two constants) *)
Local Ltac factw := zsimp; wsub; zsimp; mlia.

(* As crtA_loop.v crt_lits: the statements name every pc as CV_AT off; inside the proofs each step first replaces
   every CV_AT o of the goal and of the hypotheses by its value, so that StepF's step runs on numeral pcs. *)
Local Ltac cv_lits :=
  repeat match goal with
  | |- context [CV_AT ?o] => let v := eval vm_compute in (CV_AT o) in change (CV_AT o) with v
  | H : context [CV_AT ?o] |- _ => let v := eval vm_compute in (CV_AT o) in change (CV_AT o) with v in H
  end.
Local Ltac step ::= cv_lits; stepF_k ltac:(idtac).

(* =========================================================================
   The two shadow-check sites (as crtA_loop.v cl1_F / cls4_F): each takes the 1-byte range of the shadow byte
   and of the data byte it loads, and the shadow byte's ASan verdict.
   ========================================================================= *)

(* +0x144 -> +0x15c : a0 := s3 + a5 ; shadow of a0 (lb t1) ; slow path andi t2 at +0x180 ; data b := [a0] (lbu a0) *)
Lemma dg_ck_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A : Z),
  bv_unsigned x19 + bv_unsigned x15 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG A 1 ->
  (forall y6 y7 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 y6 y7 x8 x9 (zxb b) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0x15c)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0x144)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK MD RK RD CONT.
  pose proof (u64_range x19) as R19. pose proof (u64_range x15) as R15. unfold ASAN_K in *.
  step. gen_add x19 x15 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0x1b8 -> +0x1cc : shadow of a0 (lb t1) ; slow path andi t2 at +0x1f0 ; data b := [a5] (lbu t1) *)
Lemma tb_ck_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A : Z),
  bv_unsigned x10 = A -> bv_unsigned x15 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG A 1 ->
  (forall y7 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 (zxb b) y7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0x1cc)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0x1b8)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros E10 E15 RA M SK MD RK RD CONT.
  pose proof (u64_range x10) as R10. unfold ASAN_K in *.
  step. gen_shr x10 g G. rewrite E10 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm x15 _ _ MD E15) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, E10, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* =========================================================================
   The walk from +0x128 to +0x21c. The section carries cv_dgt_stmt_F's premises, with e the length of the
   reply's first line and KFIN the statement's continuation at +0x21c.
   ========================================================================= *)

Section EvB.
Variables (ra sp gp tp s0 s1 g s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (r n cur e : Z) (zs : list Z) (Q : machine_state -> Prop) (RNG : ExecF.footprint).
Hypothesis HR0 : 4096 <= r.
Hypothesis HN : 0 < n <= 255.
Hypothesis HL : Z.of_nat (length zs) = n.
Hypothesis BR : forall i, 0 <= nthz zs i < 256.
Hypothesis RD : forall i, 0 <= i < n -> mrd rsegs m (wa (r + i)) = Some (Z_to_bv 8 (nthz zs i)).
Hypothesis AD : addressable m r n.
Hypothesis RR : ExecF.rng RNG r n.
Hypothesis RS : ExecF.rng RNG (shadow_addr r / 8 * 8)
  (shadow_addr (r + n - 1) / 8 * 8 + 8 - shadow_addr r / 8 * 8).
Hypothesis CUR : INT_MIN <= cur <= INT_MAX.
Hypothesis S0 : bv_unsigned s0 = cur mod 2 ^ 64.
Hypothesis HE : Z.of_nat (length (first_line zs)) = e.
Hypothesis KFIN : forall (s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
  bv_unsigned s0' = expected_value_m zs cur mod 2 ^ 64 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' g (Z_to_bv 64 r) (Z_to_bv 64 n)
             (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (CV_AT 0x21c)) fc None m (seg_rom rsegs)).

Local Abbreviation ST pc a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 g (Z_to_bv 64 r) (Z_to_bv 64 n)
           (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Local Abbreviation SKL := (skip is_lead_blank (first_line zs)).

Lemma eloc : 0 <= e <= n.
Proof. pose proof (cv_first_line_le zs) as H. lia. Qed.

Lemma rn_lt : 0 <= r /\ r + n <= 2 ^ 47.
Proof. pose proof AD as (A0 & _ & A2 & _). unfold APPMEM_END in A2. lia. Qed.

(* the reply byte r + i, for i in [0, n): its shadow byte and verdict, and the two 1-byte ranges *)
Lemma cv_byte : forall i, 0 <= i < n ->
  exists k, mrd rsegs m (wa ((r + i) / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ (r + i) mod 8 < bv_signed k) /\
    ExecF.rng RNG ((r + i) / 8 + ASAN_K) 1 /\ ExecF.rng RNG (r + i) 1.
Proof.
  intros i Hi. pose proof AD as (_ & _ & _ & A3).
  destruct (A3 i Hi) as (_ & k & Mk & Sk).
  exists k. unfold shadow_addr in Mk. unfold shadow_ok in Sk.
  split; [exact Mk|]. split; [destruct Sk as [C|[C _]]; [left|right]; exact C|].
  split; [apply (cv_sh1F RNG r n i RS Hi)|].
  eapply ExecF.rng_sub; [exact RR | lia | lia].
Qed.

(* the digit loop's check site at index i *)
Lemma dg_ck : forall i (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), 0 <= i < n -> bv_unsigned a5 = i ->
  (forall t1' t2' : word,
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x15c) (Z_to_bv 64 (nthz zs i)) a1 a2 a3 a4 a5 a6 a7 t0 t1' t2')) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x144) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros i a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 Hi Ha5 K.
  pose proof rn_lt as Hrn.
  destruct (cv_byte i Hi) as (k & Mk & Sk & Rk & Rd).
  apply (dg_ck_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 g (Z_to_bv 64 r) (Z_to_bv 64 n)
           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q k (Z_to_bv 8 (nthz zs i)) (r + i));
    [ rewrite unsigned_lit by lia; lia | lia | exact Mk | exact Sk | apply RD; exact Hi | exact Rk | exact Rd |].
  intros y6 y7. rewrite (zxb_lit _ (BR i)). apply K.
Qed.

(* the trailing-blank loop's check site at index p *)
Lemma tb_ck : forall p (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), 0 <= p < n ->
  bv_unsigned a0 = r + p -> bv_unsigned a5 = r + p ->
  (forall t2' : word,
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x1cc) a0 a1 a2 a3 a4 a5 a6 a7 t0 (Z_to_bv 64 (nthz zs p)) t2')) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x1b8) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros p a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 Hp Ha0 Ha5 K.
  pose proof rn_lt as Hrn.
  destruct (cv_byte p Hp) as (k & Mk & Sk & Rk & Rd).
  apply (tb_ck_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 g (Z_to_bv 64 r) (Z_to_bv 64 n)
           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q k (Z_to_bv 8 (nthz zs p)) (r + p));
    [ exact Ha0 | exact Ha5 | lia | exact Mk | exact Sk | apply RD; exact Hp | exact Rk | exact Rd |].
  intros y7. rewrite (zxb_lit _ (BR p)). apply K.
Qed.

(* the digit loop: +0x144, a5 the index, a3 the value *)
Lemma loop_dg : forall d0 (a1 a2 a4 a6 a7 t0 : word),
  bv_unsigned a1 = e -> bv_unsigned a4 = d0 -> bv_unsigned a6 = 9 -> bv_unsigned a7 = 10 ->
  bv_unsigned t0 = 10 ^ 10 ->
  (forall (a0 a3 a5 t1 t2 : word) i vf,
     bv_unsigned a5 = i -> bv_unsigned a3 = vf -> 0 <= vf < 10 ^ 11 -> d0 <= i <= e ->
     digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = (vf, skipn (Z.to_nat i) (first_line zs)) ->
     (i = d0 /\ is_digit (nthz zs d0) = false) \/ d0 < i ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x190) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  forall k i v (a0 a3 a5 t1 t2 : word),
  0 <= d0 <= i -> i + Z.of_nat (S k) = e -> 0 <= v < 10 ^ 11 ->
  digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = digits_ev v (skipn (Z.to_nat i) (first_line zs)) ->
  bv_unsigned a5 = i -> bv_unsigned a3 = v ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x144) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros d0 a1 a2 a4 a6 a7 t0 Ha1 Ha4 Ha6 Ha7 Ht0 K k. induction k as [|k IH];
    intros i v a0 a3 a5 t1 t2 Hd0 Hk Hv Hinv Ha5 Ha3.
  all: pose proof eloc as Hel.
  all: assert (Hie : 0 <= i < e) by lia.
  all: assert (Hin : 0 <= i < n) by lia.
  all: pose proof (BR i) as Hb.
  all: rewrite (cv_flsfx_cons zs i ltac:(lia)) in Hinv.
  all: apply (dg_ck i a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 Hin Ha5); intros t1' t2'.
  all: step.
  all: step.
  all: destruct (is_digit (nthz zs i)) eqn:Dg;
       [ assert (Dgr : 48 <= nthz zs i <= 57) by (pose proof Dg as D; unfold is_digit in D;
           apply andb_true_iff in D as [D1 D2]; apply Z.leb_le in D1; apply Z.leb_le in D2; lia)
       | assert (Dgr : nthz zs i < 48 \/ 57 < nthz zs i) by (pose proof Dg as D; unfold is_digit in D;
           apply andb_false_iff in D as [D1|D1]; apply Z.leb_gt in D1; [left | right]; lia) ].
  (* k = 0, digit *)
  - rewrite (digits_ev_step _ _ _ Dg) in Hinv.
    takeF false. step.
    destruct (Z.lt_ge_cases v (10 ^ 10)) as [Hlt|Hlt].
    + rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hinv.
      takeF false. step. step.
      rewrite ?(unsigned_lit (nthz zs i)) by lia. rewrite (digit_land _ Dg).
      step. step. step. takeF false. step. step.
      apply (K _ _ _ _ _ e (v * 10 + (nthz zs i - 48))); [fact | fact | lia | lia | | lia].
      rewrite Hinv, !skipn_all2 by lia. reflexivity.
    + rewrite (proj2 (Z.ltb_ge _ _) Hlt) in Hinv.
      takeF true. step. step. takeF false. step. step.
      apply (K _ _ _ _ _ e v); [fact | fact | lia | lia | | lia].
      rewrite Hinv, !skipn_all2 by lia. reflexivity.
  (* k = 0, not a digit *)
  - rewrite (digits_ev_stop _ _ _ Dg) in Hinv.
    takeF true.
    apply (K _ _ _ _ _ i v); [exact Ha5 | exact Ha3 | lia | lia | |].
    + rewrite Hinv. symmetry. f_equal. apply cv_flsfx_cons. lia.
    + destruct (Z.eq_dec i d0) as [->|Hne]; [left; split; [reflexivity | exact Dg] | right; lia].
  (* k = S k, digit *)
  - rewrite (digits_ev_step _ _ _ Dg) in Hinv.
    takeF false. step.
    destruct (Z.lt_ge_cases v (10 ^ 10)) as [Hlt|Hlt].
    + rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hinv.
      takeF false. step. step.
      rewrite ?(unsigned_lit (nthz zs i)) by lia. rewrite (digit_land _ Dg).
      step. step. step. takeF true.
      apply (IH (i + 1) (v * 10 + (nthz zs i - 48))); [lia | lia | lia | exact Hinv | fact | fact].
    + rewrite (proj2 (Z.ltb_ge _ _) Hlt) in Hinv.
      takeF true. step. step. takeF true.
      apply (IH (i + 1) v); [lia | lia | lia | exact Hinv | fact | exact Ha3].
  (* k = S k, not a digit *)
  - rewrite (digits_ev_stop _ _ _ Dg) in Hinv.
    takeF true.
    apply (K _ _ _ _ _ i v); [exact Ha5 | exact Ha3 | lia | lia | |].
    + rewrite Hinv. symmetry. f_equal. apply cv_flsfx_cons. lia.
    + destruct (Z.eq_dec i d0) as [->|Hne]; [left; split; [reflexivity | exact Dg] | right; lia].
Qed.

(* the trailing-blank loop: +0x1b8, a0 = a5 = r + p, a4 = -p, a6 = -e *)
Lemma loop_tb : forall i_f (a1 a2 a3 a6 a7 t0 : word),
  bv_unsigned a1 = e -> bv_unsigned a6 = (0 - e) mod 2 ^ 64 -> bv_unsigned a7 = 32 ->
  bv_unsigned t0 = 4294976000 ->
  (forall (a0 a4 a5 t1 t2 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) = [] ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x204) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  (forall (a0 a4 a5 t1 t2 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) <> [] ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x21c) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  forall k p (a0 a4 a5 t1 t2 : word),
  0 <= p -> p + Z.of_nat (S k) = e ->
  skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) =
    skip is_trail_blank (skipn (Z.to_nat p) (first_line zs)) ->
  bv_unsigned a0 = r + p -> bv_unsigned a5 = r + p -> bv_unsigned a4 = (0 - p) mod 2 ^ 64 ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x1b8) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros i_f a1 a2 a3 a6 a7 t0 Ha1 Ha6 Ha7 Ht0 KE KN k. induction k as [|k IH];
    intros p a0 a4 a5 t1 t2 Hp0 Hk Hinv Ha0 Ha5 Ha4.
  all: pose proof eloc as Hel.
  all: pose proof rn_lt as Hrn.
  all: assert (Hpe : 0 <= p < e) by lia.
  all: assert (Hpn : 0 <= p < n) by lia.
  all: pose proof (BR p) as Hb.
  all: rewrite (cv_flsfx_cons zs p ltac:(lia)) in Hinv.
  all: apply (tb_ck p a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 Hpn Ha0 Ha5); intros t2'.
  all: step.
  all: destruct (Z_le_gt_dec (nthz zs p) 32) as [H32|H32];
       [ takeF false; step; rewrite ?Ht0;
         rewrite ?(unsigned_lit (nthz zs p)) by lia; rewrite ?(Z.mod_small (nthz zs p) 64) by lia;
         step; rewrite (mask_u (nthz zs p) ltac:(lia));
         destruct (is_trail_blank (nthz zs p)) eqn:Tb; cbv beta iota; step
       | takeF true ].
  (* k = 0: blank, end reached *)
  - rewrite (skip_t _ _ _ Tb) in Hinv.
    takeF false. step. step. step. step. takeF false. step.
    apply KE. rewrite Hinv, skipn_all2 by lia. reflexivity.
  (* k = 0: not blank (bit clear) *)
  - rewrite (skip_f _ _ _ Tb) in Hinv.
    takeF true. step. step. takeF true.
    apply KN. rewrite Hinv. discriminate.
  (* k = 0: not blank (> 32) *)
  - assert (Tb : is_trail_blank (nthz zs p) = false).
    { unfold is_trail_blank.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 32)) by lia.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 9)) by lia.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 13)) by lia. reflexivity. }
    rewrite (skip_f _ _ _ Tb) in Hinv.
    step. step. takeF true.
    apply KN. rewrite Hinv. discriminate.
  (* k = S k: blank, loop *)
  - rewrite (skip_t _ _ _ Tb) in Hinv.
    takeF false. step. step. step. step. takeF true.
    apply (IH (p + 1)); [lia | lia | exact Hinv | fact | fact | fact].
  (* k = S k: not blank (bit clear) *)
  - rewrite (skip_f _ _ _ Tb) in Hinv.
    takeF true. step. step. takeF true.
    apply KN. rewrite Hinv. discriminate.
  (* k = S k: not blank (> 32) *)
  - assert (Tb : is_trail_blank (nthz zs p) = false).
    { unfold is_trail_blank.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 32)) by lia.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 9)) by lia.
      rewrite (proj2 (Z.eqb_neq (nthz zs p) 13)) by lia. reflexivity. }
    rewrite (skip_f _ _ _ Tb) in Hinv.
    step. step. takeF true.
    apply KN. rewrite Hinv. discriminate.
Qed.

(* the entry of the trailing scan: +0x194 *)
Lemma seg_trail : forall i_f (a1 a2 a3 : word),
  bv_unsigned a1 = e -> 0 <= i_f <= e ->
  (forall (a0 a4 a5 a6 a7 t0 t1 t2 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) = [] ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x204) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  (forall (a0 a4 a5 a6 a7 t0 t1 t2 : word), skip is_trail_blank (skipn (Z.to_nat i_f) (first_line zs)) <> [] ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x21c) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2)) ->
  forall (a0 a4 a5 a6 a7 t0 t1 t2 : word), bv_unsigned a5 = i_f ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x194) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros i_f a1 a2 a3 Ha1 Hif KE KN a0 a4 a5 a6 a7 t0 t1 t2 Ha5.
  pose proof eloc as Hel. pose proof rn_lt as Hrn.
  step. destruct (Z.eq_dec i_f e) as [Ee|Ee].
  - takeF true. step. takeF false. apply KE. rewrite Ee, skipn_all2 by lia. reflexivity.
  - takeF false. do 8 step.
    eapply (loop_tb i_f a1 a2 a3) with (k := Z.to_nat (e - i_f - 1)) (p := i_f).
    all: first [ lia | reflexivity | factw
               | intros A0 A4 A5 T1 T2 HH;
                 first [ apply (KE A0 A4 A5 _ _ _ T1 T2 HH) | apply (KN A0 A4 A5 _ _ _ T1 T2 HH) ] ].
Qed.

(* ---- the model, read through the projections the walk produces (lib/Prog/check_value.v ev_val ..) ---- *)

Lemma ev_val : expected_value_m zs cur =
  match snd (sign_split SKL) with
  | c :: _ => if is_digit c
              then finish (fst (sign_split SKL)) (fst (digits_ev 0 (snd (sign_split SKL))))
                     (snd (digits_ev 0 (snd (sign_split SKL)))) cur
              else cur
  | [] => cur
  end.
Proof.
  unfold expected_value_m. destruct (sign_split SKL) as [neg l]. cbn [fst snd].
  destruct l as [|c t]; [reflexivity|]. destruct (is_digit c); [|reflexivity].
  destruct (digits_ev 0 (c :: t)) as [v rest]. cbn [fst snd]. reflexivity.
Qed.

Lemma ev_cur_nodigit : forall c l, snd (sign_split SKL) = c :: l -> is_digit c = false ->
  expected_value_m zs cur = cur.
Proof. intros c l H D. rewrite ev_val, H, D. reflexivity. Qed.

Lemma ev_fin : forall c l vf rest, snd (sign_split SKL) = c :: l -> is_digit c = true ->
  digits_ev 0 (c :: l) = (vf, rest) ->
  expected_value_m zs cur = finish (fst (sign_split SKL)) vf rest cur.
Proof.
  intros c l vf rest H D E. rewrite ev_val, H, D, E. cbn [fst snd]. reflexivity.
Qed.

Lemma ev_cur : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word), expected_value_m zs cur = cur ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x21c) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof. intros. apply KFIN. rewrite H. exact S0. Qed.

(* the sign and the int-range test: +0x204 .. +0x21c *)
Lemma ev_tail : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word) c0 v rest,
  0 <= c0 < 256 -> 0 <= v < 10 ^ 11 -> skip is_trail_blank rest = [] ->
  bv_unsigned a2 = c0 -> bv_unsigned a3 = v ->
  finish (c0 =? 45) v rest cur = expected_value_m zs cur ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x204) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 c0 v rest Hc0 Hv Ht Ha2 Ha3 HM.
  rewrite (finish_nil _ _ _ _ Ht) in HM.
  step. step. destruct (Z.eq_dec c0 45) as [E45|E45].
  - rewrite E45, Z.eqb_refl in HM.
    takeF false. step. step. step.
    destruct (Z.ltb_spec (- v) INT_MIN) as [Hlo|Hlo];
      [ idtac | destruct (Z.ltb_spec INT_MAX (- v)) as [Hhi|Hhi] ];
      cbv beta iota delta [orb] in HM; unfold INT_MIN, INT_MAX in *.
    + takeF true. apply KFIN. rewrite <- HM. exact S0.
    + exfalso. lia.
    + takeF false. step. apply KFIN. rewrite <- HM. fact.
  - rewrite (proj2 (Z.eqb_neq c0 45) E45) in HM.
    takeF true. step. step.
    destruct (Z.ltb_spec v INT_MIN) as [Hlo|Hlo];
      [ idtac | destruct (Z.ltb_spec INT_MAX v) as [Hhi|Hhi] ];
      cbv beta iota delta [orb] in HM; unfold INT_MIN, INT_MAX in *.
    + exfalso. lia.
    + takeF true. apply KFIN. rewrite <- HM. exact S0.
    + takeF false. step. apply KFIN. rewrite <- HM. fact.
Qed.

(* +0x190: `i == d0` is the harness's `no digit read` test (lib/Prog/check_value.v ev_ee8) *)
Lemma ev_190 : forall (a1 a2 a4 : word) d0 c0,
  bv_unsigned a1 = e -> bv_unsigned a2 = c0 -> bv_unsigned a4 = d0 ->
  0 <= c0 < 256 -> 0 <= d0 < e ->
  snd (sign_split SKL) = skipn (Z.to_nat d0) (first_line zs) ->
  fst (sign_split SKL) = (c0 =? 45) ->
  forall (a0 a3 a5 a6 a7 t0 t1 t2 : word) i vf,
  bv_unsigned a5 = i -> bv_unsigned a3 = vf -> 0 <= vf < 10 ^ 11 -> d0 <= i <= e ->
  digits_ev 0 (skipn (Z.to_nat d0) (first_line zs)) = (vf, skipn (Z.to_nat i) (first_line zs)) ->
  (i = d0 /\ is_digit (nthz zs d0) = false) \/ d0 < i ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x190) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros a1 a2 a4 d0 c0 Ha1 Ha2 Ha4 Hc0 Hd0 HL2 HF a0 a3 a5 a6 a7 t0 t1 t2 i vf Ha5 Ha3 Hvf Hie Hdg Hdisj.
  pose proof eloc as Hel.
  assert (HD : skipn (Z.to_nat d0) (first_line zs) = nthz zs d0 :: skipn (Z.to_nat (d0 + 1)) (first_line zs))
    by (apply cv_flsfx_cons; lia).
  step. destruct (Z.eq_dec i d0) as [Ei|Ei].
  - takeF true. apply ev_cur.
    assert (Dg : is_digit (nthz zs d0) = false) by (destruct Hdisj as [[_ H]|H]; [exact H | lia]).
    apply (ev_cur_nodigit (nthz zs d0) (skipn (Z.to_nat (d0 + 1)) (first_line zs)));
      [rewrite HL2, HD; reflexivity | exact Dg].
  - takeF false.
    assert (Dg : is_digit (nthz zs d0) = true).
    { destruct (is_digit (nthz zs d0)) eqn:D; [reflexivity|]. exfalso.
      rewrite HD, (digits_ev_stop _ _ _ D) in Hdg. injection Hdg as _ Hl. rewrite <- HD in Hl.
      pose proof (skipn_inj (first_line zs) (Z.to_nat d0) (Z.to_nat i) ltac:(lia) ltac:(lia) Hl). lia. }
    assert (HE2 : expected_value_m zs cur = finish (c0 =? 45) vf (skipn (Z.to_nat i) (first_line zs)) cur).
    { rewrite <- HF.
      apply (ev_fin (nthz zs d0) (skipn (Z.to_nat (d0 + 1)) (first_line zs)) vf);
        [rewrite HL2, HD; reflexivity | exact Dg | rewrite <- HD; exact Hdg]. }
    apply (seg_trail i a1 a2 a3 Ha1 ltac:(lia)); [| | exact Ha5].
    + intros a0' a4' a5' a6' a7' t0' t1' t2' Hnil.
      apply (ev_tail a0' a1 a2 a3 a4' a5' a6' a7' t0' t1' t2' c0 vf (skipn (Z.to_nat i) (first_line zs)));
        [exact Hc0 | exact Hvf | exact Hnil | exact Ha2 | exact Ha3 | symmetry; exact HE2].
    + intros a0' a4' a5' a6' a7' t0' t1' t2' Hne.
      apply ev_cur. rewrite HE2. apply finish_rest. exact Hne.
Qed.

(* +0x128: the digit loop's set-up, then the loop *)
Lemma ev_dgt_F : forall (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : word) d0 c0,
  bv_unsigned a1 = e -> bv_unsigned a2 = c0 -> bv_unsigned a4 = d0 ->
  0 <= c0 < 256 -> 0 <= d0 < e ->
  snd (sign_split SKL) = skipn (Z.to_nat d0) (first_line zs) ->
  fst (sign_split SKL) = (c0 =? 45) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x128) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 d0 c0 Ha1 Ha2 Ha4 Hc0 Hd0 HL2 HF.
  pose proof eloc as Hel.
  do 7 step.
  eapply (loop_dg d0 a1 a2 a4) with (k := Z.to_nat (e - d0 - 1)) (i := d0) (v := 0).
  all: first [ lia | reflexivity | factw
             | intros A0 A3 A5 T1 T2 I VF H1 H2 H3 H4 H5 H6;
               apply (ev_190 a1 a2 a4 d0 c0 Ha1 Ha2 Ha4 Hc0 Hd0 HL2 HF A0 A3 A5 _ _ _ T1 T2 I VF
                        H1 H2 H3 H4 H5 H6) ].
Qed.

End EvB.

(* The second half of the inlined expected_value, as UciCvIface.v states it. *)
Theorem cv_dgt_holds : cv_dgt_stmt_F.
Proof.
  unfold cv_dgt_stmt_F, CV_TEST.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 g a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r n cur
    zs Q d0 c0 HR0 HN HL BR RD AD RR RS CUR S0 Ha1 Ha2 Ha4 Hc0 Hd0 HL2 HF KF.
  eapply ev_dgt_F with (zs := zs) (cur := cur) (e := Z.of_nat (length (first_line zs))) (d0 := d0) (c0 := c0).
  all: first [ eassumption | reflexivity ].
Qed.
