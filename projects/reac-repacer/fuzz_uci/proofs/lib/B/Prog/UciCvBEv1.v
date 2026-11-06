(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: the first half of lib/Prog/check_value.v's Section Ev (loop_nl, loop_lb,
   seg_sign, ev_val, ev_cur, ev_sign, ev_lb_nil, ev_60, ev_5c, ev_block and their list and sign helpers) moved to
   image A (fuzz_uci.asan): footprint runs (lib/Lib/ExecF.v evtF, lib/Lib/StepF.v step) instead of evt, this image's
   addresses (UciCvIface.v CV_AT offsets +0x06c .. +0x128) and registers, and the two ASan load checks of each loop
   in the form of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_loop.v at origin/ossv/recipes 88154566652a (cl1_F;
   crt_sh1F, takeF and crt_lits copied as cv_sh1F, takeF and cv_lits, module paths changed to reac_repacer.fuzz_uci). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCvEvA.v, with its module paths, module names and addresses changed; 142 of its 432 lines of code are new or changed and 112 lines of the source are left out. *)
(* UciCvBEv1: cv_ev_of_dgt proves lib/B/Prog/UciCvBIface.v cv_ev_stmt_F from cv_dgt_stmt_F, i.e. the walk of
   check_value's inlined expected_value in image B (fuzz_uci.asan-ubsan) from the return of rp_uci_int (+0x06c) to
   the digit loop's set-up (+0x15c), whose rest cv_dgt_stmt_F states. The image-B twin of lib/A/Prog/UciCvEvA.v (the
   first half of lib/Prog/check_value.v's Section Ev as footprint runs, with the ASan load checks in the form of
   proofs/libreac/fuzz_decode/lib/A/Prog/crtA_loop.v at recipes commit 88154566652a), on image B's code: its
   registers, its loop shapes and the UBSan checks of each reply index. Offsets from the entry (UciCvBIface.v CV_AT),
   read from the pinned image's code:
     +0x06c `mv s2, a0`; a1 := 0; a2 := -n; a3 := (r != 0); a4 := 10; a5 := r; a0 := r
     +0x088 .. +0x0d0  the scan for the first '\n' (a0 = a5 = r + i, a1 = -i): the UBSan checks of r + i (`bltu a0,
            s4` wrap, the null-ness test of a0 against a3, `beqz s4`), the ASan load check of a0 (report at +0x0d0 via
            the slow path +0x0c8), `lbu a6` of a5; `beq a6, a4` to +0x0e8; a1 -= 1, a0 += 1, a5 += 1; `bne a2, a1`
            back; else `j` +0x0f0 (no '\n': s3 = n)
     +0x0e8 `beqz a1` to +0x25c (empty first line: the value is cur); s3 := -a1 = i
     +0x0f0 a3 := 0, a2 := 32, a4 := 9
     +0x0fc .. +0x134  the leading-blank skip (index a3): a0 := r + a3, the UBSan wrap check, the ASan load check of
            a0 (report at +0x134 via +0x12c), `lbu a1`; `beq a1, a2` to +0x120; `bne a1, a4` to +0x138; +0x120
            a3 += 1; `bne s3, a3` back; else `j` +0x25c (all blank: cur)
     +0x138 .. +0x158  `beqz a0` and a4 := ~r, `bltu a4, a3` (the UBSan checks of r + a3); the optional sign: '+' or
            '-' steps a3 once; `bgeu a3, s3` to +0x25c (nothing after the sign: cur), else +0x15c, the hand-off
            (s3 = e, a3 = d0, a1 = c0, a4 = ~r). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import AsanKA AsanKAProof UciPSyms UciPAddr
  UciCvBIface.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---------------- model helpers (lib/Prog/check_value.v) ---------------- *)

Lemma u8lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma zxb_lit : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zxb. rewrite u8lit by exact Hc. reflexivity. Qed.

Lemma fl_nl : forall c t, c = 10 -> first_line (c :: t) = [].
Proof. intros c t ->. reflexivity. Qed.

Lemma fl_other : forall c t, c <> 10 -> first_line (c :: t) = c :: first_line t.
Proof. intros c t H. cbn [first_line]. rewrite (proj2 (Z.eqb_neq c 10) H). reflexivity. Qed.

Lemma skip_t : forall f c t, f c = true -> skip f (c :: t) = skip f t.
Proof. intros f c t H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma skip_f : forall f c t, f c = false -> skip f (c :: t) = c :: t.
Proof. intros f c t H. cbn [skip]. rewrite H. reflexivity. Qed.

Lemma lb_32 : forall c, c = 32 -> is_lead_blank c = true.
Proof. intros c ->. reflexivity. Qed.

Lemma lb_9 : forall c, c = 9 -> is_lead_blank c = true.
Proof. intros c ->. reflexivity. Qed.

Lemma ss_fst : forall c t, fst (sign_split (c :: t)) = (c =? 45).
Proof.
  intros c t. cbn [sign_split]. destruct ((c =? 43) || (c =? 45))%bool eqn:E; cbn [fst]; [reflexivity|].
  apply orb_false_iff in E as [_ E2]. symmetry. exact E2.
Qed.

Lemma ss_plus : forall c t, c = 43 -> sign_split (c :: t) = (false, t).
Proof. intros c t ->. reflexivity. Qed.

Lemma ss_minus : forall c t, c = 45 -> sign_split (c :: t) = (true, t).
Proof. intros c t ->. reflexivity. Qed.

Lemma ss_none : forall c t, c <> 43 -> c <> 45 -> sign_split (c :: t) = (false, c :: t).
Proof.
  intros c t H1 H2. cbn [sign_split].
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

(* `sltiu rd, rs, 1` of a nonzero word is 0 (the null-ness test of the scan). *)
Lemma sltiu1_nz : forall (w : word), 0 < bv_unsigned w -> v_sltiu w 1 = Z_to_bv 64 0.
Proof.
  intros w Hw. unfold v_sltiu. replace (bv_wrap 64 1) with 1 by reflexivity.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

(* ---------------- the shadow footprint (crtA_loop.v) ---------------- *)

(* [a, c] inside the 8-aligned cover of [a, c]. *)
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

(* lib/Prog/check_value.v's branch-test and register-fact tactics. *)
Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?zb_signed; zsimp; wsub; zsimp;
  do 3 (decide_tests; cbv beta iota); reflexivity.
Ltac fact := cbv delta [zxb]; wsub; rewrite ?unsigned_lit_wrap; mlia.

(* crtA_loop.v's branch choice, for the footprint run. *)
Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* As crtA_loop.v crt_lits: the statements name every pc by UciCvBIface.v's names; inside the proofs each step first
   replaces each of them, in the goal and in the hypotheses, by its value (vm_compute of a closed address), so that
   lib/Lib/StepF.v's step runs on numeral pcs. *)
Local Ltac cv_lits :=
  repeat match goal with
  | |- context [CV_AT ?o] => let v := eval vm_compute in (CV_AT o) in change (CV_AT o) with v
  | H : context [CV_AT ?o] |- _ => let v := eval vm_compute in (CV_AT o) in change (CV_AT o) with v in H
  | |- context [CV_TEST] => let v := eval vm_compute in CV_TEST in change CV_TEST with v
  | H : context [CV_TEST] |- _ => let v := eval vm_compute in CV_TEST in change CV_TEST with v in H
  | |- context [CV_RET_RUI] => let v := eval vm_compute in CV_RET_RUI in change CV_RET_RUI with v
  end.
Local Ltac step ::= cv_lits; stepF_k ltac:(idtac).
(* a4 := ~r (`xori a4, s4, -1`): its value, from bv_unsigned (Z_to_bv 64 r) = r and the complement's value. *)
Local Ltac fact4 := lazymatch goal with
  | Ur : bv_unsigned (Z_to_bv 64 ?r) = ?r, NOT : Z.lxor ?r _ = _ |- _ =>
      rewrite Ur, NOT; apply unsigned_lit; lia end.

(* =========================================================================
   The two check sites of this half (crtA_loop.v cl1_F's form, with the UBSan checks before each).  Each loads the
   shadow byte k of A = r + i (1 byte, inside the 8-aligned cover of the reply's shadow) and, since k allows the
   load, the reply byte b at A (1 byte inside the reply); the report call is not reached.  s5 (x21) holds the shadow
   offset, s4 (x20) the reply's start R.
   ========================================================================= *)

(* +0x088 -> +0x0b0: `bltu a0, s4`; a6 := (a0 == 0) xor a3, `beqz a6`; `beqz s4`; shadow of a0 into a6 (`lb`);
   handler `andi a7`; `lbu a6` of a5 *)
Lemma cv_ck1_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A R : Z),
  bv_unsigned x10 = A -> bv_unsigned x15 = A -> bv_unsigned x20 = R -> bv_unsigned x13 = 1 ->
  0 < R <= A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG A 1 ->
  (forall y17 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (zxb b) y17 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0xb0)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0x88)) fc None mm (seg_rom rsegs)).
Proof.
  intros until R. intros E10 E15 E20 E13 HR RA M SK MD RK RD CONT.
  pose proof (u64_range x10) as R10. unfold ASAN_K in M, RK.
  step. takeF false.
  step. rewrite (sltiu1_nz x10) by lia.
  step. step. takeF false.
  step. takeF false.
  step. gen_shr x10 g G. rewrite E10 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
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

(* +0x0fc -> +0x118: a0 := s4 + a3; `bltu a0, s4`; shadow of a0 into a1 (`lb`); handler `andi a5`; `lbu a1` *)
Lemma cv_ck2_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A R J : Z),
  bv_unsigned x20 = R -> bv_unsigned x13 = J -> R + J = A -> 0 <= J -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG A 1 ->
  (forall y10 y15 : word, bv_unsigned y10 = A ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 (zxb b) x12 x13 x14 y15 x16 x17 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0x118)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0xfc)) fc None mm (seg_rom rsegs)).
Proof.
  intros until J. intros E20 E13 EA HJ RA M SK MD RK RD CONT.
  pose proof (u64_range x20) as R20. pose proof (u64_range x13) as R13. unfold ASAN_K in M, RK.
  step. gen_add x20 x13 w U. rewrite E20, E13, EA in U.
  step. takeF false.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* =========================================================================
   The walk +0x06c .. +0x15c / +0x25c (lib/Prog/check_value.v Section Ev, first half).  The section carries
   cv_ev_stmt_F's premises, e the length of the first line, the continuation KFIN at +0x25c and the hand-off KD at
   +0x15c (cv_dgt_stmt_F at these premises).
   ========================================================================= *)

Section EvA.
Variables (ra sp gp tp t0 t1 t2 s0 s1 g s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (r n cur e : Z) (zs : list Z) (Q : machine_state -> Prop) (RNG : ExecF.footprint).
Hypothesis HR0 : 4096 <= r.
Hypothesis HN : 0 < n <= 255.
Hypothesis HL : Z.of_nat (length zs) = n.
Hypothesis BR : forall i, 0 <= nthz zs i < 256.
Hypothesis RD : forall i, 0 <= i < n -> mrd rsegs m (wa (r + i)) = Some (Z_to_bv 8 (nthz zs i)).
Hypothesis ADR : addressable m r n.
Hypothesis RR : ExecF.rng RNG r n.
Hypothesis RS : ExecF.rng RNG (shadow_addr r / 8 * 8)
  (shadow_addr (r + n - 1) / 8 * 8 + 8 - shadow_addr r / 8 * 8).
Hypothesis HE : Z.of_nat (length (first_line zs)) = e.
Hypothesis S0 : bv_unsigned s0 = cur mod 2 ^ 64.

Local Abbreviation ST pc a0 a1 a2 a3 a4 a5 a6 a7 s3 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 g s3 (Z_to_bv 64 r)
           (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Local Abbreviation SKL := (skip is_lead_blank (first_line zs)).

Hypothesis KFIN : forall (s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' : word),
  bv_unsigned s0' = expected_value_m zs cur mod 2 ^ 64 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' g s3' (Z_to_bv 64 r)
             (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CV_TEST) fc None m (seg_rom rsegs)).

Hypothesis KD : forall (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word) d0 c0,
  bv_unsigned s3 = e -> bv_unsigned a1 = c0 -> bv_unsigned a3 = d0 -> bv_unsigned a4 = 2 ^ 64 - 1 - r ->
  0 <= c0 < 256 -> 0 <= d0 < e ->
  snd (sign_split SKL) = skipn (Z.to_nat d0) (first_line zs) ->
  fst (sign_split SKL) = (c0 =? 45) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x15c) a0 a1 a2 a3 a4 a5 a6 a7 s3).

Lemma eloc : 0 <= e <= n.
Proof. pose proof (cv_first_line_le zs) as H. lia. Qed.

Lemma rn_lt : 0 <= r /\ r + n <= 2 ^ 47.
Proof. destruct ADR as (H0 & _ & H & _). unfold APPMEM_END in H. lia. Qed.

Lemma ur : bv_unsigned (Z_to_bv 64 r) = r.
Proof. pose proof rn_lt. apply unsigned_lit. lia. Qed.

(* a3 := (0 <u r) (`snez a3, s4`, the null-ness flag of the reply) *)
Lemma sltu_r : bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 r)) = 1.
Proof.
  unfold v_sltu, c_ltu, bv_ltu. rewrite ur. replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity.
  rewrite (proj2 (Z.ltb_lt 0 r)) by lia. reflexivity.
Qed.

Lemma sfx_cons : forall i, 0 <= i < n -> skipn (Z.to_nat i) zs = nthz zs i :: skipn (Z.to_nat (i + 1)) zs.
Proof.
  intros i Hi. unfold nthz. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply cv_skipn_nth_cons. lia.
Qed.

Lemma flsfx : forall j, 0 <= j < e ->
  skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs).
Proof. intros j Hj. apply cv_flsfx_cons. lia. Qed.

(* the shadow byte of r + i allows the 1-byte load (addressable) *)
Lemma sh_at : forall i, 0 <= i < n -> exists k : byte,
  mrd rsegs m (wa ((r + i) / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ (r + i) mod 8 < bv_signed k).
Proof.
  intros i Hi. destruct ADR as (_ & _ & _ & HA). destruct (HA i Hi) as (_ & k & Hk & Hok).
  exists k. split; [exact Hk|]. destruct Hok as [E|[E _]]; [left; exact E | right; exact E].
Qed.

(* the two check sites at reply index i *)
Lemma ck1 : forall i (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word), 0 <= i < n ->
  bv_unsigned a0 = r + i -> bv_unsigned a5 = r + i -> bv_unsigned a3 = 1 ->
  (forall y17 : word,
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0xb0) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (nthz zs i)) y17 s3)) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x88) a0 a1 a2 a3 a4 a5 a6 a7 s3).
Proof.
  intros i a0 a1 a2 a3 a4 a5 a6 a7 s3 Hi Ha0 Ha5 Ha3 K.
  pose proof rn_lt as Hrn.
  destruct (sh_at i Hi) as (k & M & SK).
  eapply (cv_ck1_F RNG) with (A := r + i) (R := r) (k := k) (b := Z_to_bv 8 (nthz zs i)).
  - exact Ha0.
  - exact Ha5.
  - exact ur.
  - exact Ha3.
  - lia.
  - lia.
  - exact M.
  - exact SK.
  - apply RD. exact Hi.
  - exact (cv_sh1F RNG r n i RS Hi).
  - apply (ExecF.rng_sub RNG r n); [exact RR | lia | lia].
  - intros y17. rewrite (zxb_lit _ (BR i)). apply K.
Qed.

Lemma ck2 : forall j (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word), 0 <= j < n -> bv_unsigned a3 = j ->
  (forall y10 y15 : word, bv_unsigned y10 = r + j ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x118) y10 (Z_to_bv 64 (nthz zs j)) a2 a3 a4 y15 a6 a7 s3)) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0xfc) a0 a1 a2 a3 a4 a5 a6 a7 s3).
Proof.
  intros j a0 a1 a2 a3 a4 a5 a6 a7 s3 Hj Ha3 K.
  pose proof rn_lt as Hrn.
  destruct (sh_at j Hj) as (k & M & SK).
  eapply (cv_ck2_F RNG) with (A := r + j) (R := r) (J := j) (k := k) (b := Z_to_bv 8 (nthz zs j)).
  - exact ur.
  - exact Ha3.
  - reflexivity.
  - lia.
  - lia.
  - exact M.
  - exact SK.
  - apply RD. exact Hj.
  - exact (cv_sh1F RNG r n j RS Hj).
  - apply (ExecF.rng_sub RNG r n); [exact RR | lia | lia].
  - intros y10 y15 Hy. rewrite (zxb_lit _ (BR j)). apply K. exact Hy.
Qed.

(* ---- the model, read through the projections the walk produces ---- *)

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

Lemma ev_cur_nil : snd (sign_split SKL) = [] -> expected_value_m zs cur = cur.
Proof. intros H. rewrite ev_val, H. reflexivity. Qed.

(* +0x25c with s0 = cur, when the value is cur *)
Lemma ev_cur : forall (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word), expected_value_m zs cur = cur ->
  ExecF.evtF rsegs RNG Q (ST CV_TEST a0 a1 a2 a3 a4 a5 a6 a7 s3).
Proof. intros a0 a1 a2 a3 a4 a5 a6 a7 s3 H. apply KFIN. rewrite H. exact S0. Qed.

Lemma ev_lb_nil : forall (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word), SKL = [] ->
  ExecF.evtF rsegs RNG Q (ST CV_TEST a0 a1 a2 a3 a4 a5 a6 a7 s3).
Proof. intros a0 a1 a2 a3 a4 a5 a6 a7 s3 H. apply ev_cur. apply ev_cur_nil. rewrite H. reflexivity. Qed.

(* ---- the loops ---- *)

(* the scan for the first '\n': +0x088, a0 = a5 = r + i, a1 = -i, a2 = -n, a3 = 1, a4 = 10; the '\n' test at
   +0x0e8 included *)
Lemma loop_nl :
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word), bv_unsigned s3 = e -> 0 < e ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0xf0) a0 a1 a2 a3 a4 a5 a6 a7 s3)) ->
  forall k i (a0 a1 a2 a3 a4 a5 a6 a7 : word),
  0 <= i -> i + Z.of_nat (S k) = n ->
  e = i + Z.of_nat (length (first_line (skipn (Z.to_nat i) zs))) ->
  bv_unsigned a0 = r + i -> bv_unsigned a5 = r + i -> bv_unsigned a1 = (0 - i) mod 2 ^ 64 ->
  bv_unsigned a2 = (0 - n) mod 2 ^ 64 -> bv_unsigned a3 = 1 -> bv_unsigned a4 = 10 ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x88) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n)).
Proof.
  intros K6 k. induction k as [|k IH]; intros i a0 a1 a2 a3 a4 a5 a6 a7 Hi0 Hk Hinv Ha0 Ha5 Ha1 Ha2 Ha3 Ha4.
  all: pose proof rn_lt as Hrn.
  all: assert (Hin : 0 <= i < n) by lia.
  all: pose proof (BR i) as Hb.
  all: rewrite (sfx_cons i Hin) in Hinv.
  all: apply (ck1 i a0 a1 a2 a3 a4 a5 a6 a7 _ Hin Ha0 Ha5 Ha3); intros y17.
  all: destruct (Z.eq_dec (nthz zs i) 10) as [Ec|Ec].
  (* the '\n' at i: e = i *)
  1, 3: rewrite (fl_nl _ _ Ec) in Hinv; cbn [length] in Hinv;
        assert (Ei : e = i) by lia;
        step; takeF true;
        step; destruct (Z.eq_dec i 0) as [E0|E0];
        [ takeF true; apply ev_lb_nil;
          assert (Hnil : first_line zs = []) by (apply length_zero_iff_nil; lia);
          rewrite Hnil; reflexivity
        | takeF false; step; apply K6; [fact | lia] ].
  (* k = 0, not '\n': the end, e = n *)
  - rewrite (fl_other _ _ Ec) in Hinv. cbn [length] in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [first_line length] in Hinv.
    step. takeF false. step. step. step. step. takeF false.
    step. apply K6; [rewrite unsigned_lit by lia; lia | lia].
  (* k = S k, not '\n' *)
  - rewrite (fl_other _ _ Ec) in Hinv. cbn [length] in Hinv.
    step. takeF false. step. step. step. step. takeF true.
    apply (IH (i + 1)); [lia | lia | lia | fact | fact | fact | exact Ha2 | exact Ha3 | exact Ha4].
Qed.

(* the leading-blank skip: +0x0fc, a3 the index, s3 = e, a2 = 32, a4 = 9 *)
Lemma loop_lb :
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word) j,
     bv_unsigned s3 = e -> bv_unsigned a0 = r + j -> bv_unsigned a1 = nthz zs j -> bv_unsigned a3 = j ->
     0 <= j < e -> SKL = skipn (Z.to_nat j) (first_line zs) ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x138) a0 a1 a2 a3 a4 a5 a6 a7 s3)) ->
  forall k j (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word),
  0 <= j -> j + Z.of_nat (S k) = e ->
  SKL = skip is_lead_blank (skipn (Z.to_nat j) (first_line zs)) ->
  bv_unsigned s3 = e -> bv_unsigned a2 = 32 -> bv_unsigned a4 = 9 -> bv_unsigned a3 = j ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0xfc) a0 a1 a2 a3 a4 a5 a6 a7 s3).
Proof.
  intros KN k. induction k as [|k IH]; intros j a0 a1 a2 a3 a4 a5 a6 a7 s3 Hj0 Hk Hinv Hs3 Ha2 Ha4 Ha3.
  all: pose proof eloc as Hel.
  all: pose proof (cv_first_line_le zs) as Hfl.
  all: assert (Hje : 0 <= j < e) by lia.
  all: assert (Hin : 0 <= j < n) by lia.
  all: pose proof (BR j) as Hb.
  all: rewrite (flsfx j Hje) in Hinv.
  all: apply (ck2 j a0 a1 a2 a3 a4 a5 a6 a7 s3 Hin Ha3); intros y10 y15 Hy10.
  all: destruct (Z.eq_dec (nthz zs j) 32) as [E32|E32];
       [ | destruct (Z.eq_dec (nthz zs j) 9) as [E9|E9] ].
  (* k = 0 *)
  - rewrite (skip_t _ _ _ (lb_32 _ E32)) in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [skip] in Hinv.
    step. takeF true. step. step. takeF false. step. apply ev_lb_nil. exact Hinv.
  - rewrite (skip_t _ _ _ (lb_9 _ E9)) in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [skip] in Hinv.
    step. takeF false. step. takeF false. step. step. takeF false. step. apply ev_lb_nil. exact Hinv.
  - assert (Hnb : is_lead_blank (nthz zs j) = false) by (unfold is_lead_blank;
      rewrite (proj2 (Z.eqb_neq _ _) E32), (proj2 (Z.eqb_neq _ _) E9); reflexivity).
    rewrite (skip_f _ _ _ Hnb) in Hinv.
    step. takeF false. step. takeF true.
    apply (KN _ _ _ _ _ _ _ _ _ j); [exact Hs3 | exact Hy10 | fact | exact Ha3 | lia | ].
    rewrite Hinv. symmetry. apply flsfx. lia.
  (* k = S k *)
  - rewrite (skip_t _ _ _ (lb_32 _ E32)) in Hinv.
    step. takeF true. step. step. takeF true.
    apply (IH (j + 1)); [lia | lia | exact Hinv | exact Hs3 | exact Ha2 | exact Ha4 | fact].
  - rewrite (skip_t _ _ _ (lb_9 _ E9)) in Hinv.
    step. takeF false. step. takeF false. step. step. takeF true.
    apply (IH (j + 1)); [lia | lia | exact Hinv | exact Hs3 | exact Ha2 | exact Ha4 | fact].
  - assert (Hnb : is_lead_blank (nthz zs j) = false) by (unfold is_lead_blank;
      rewrite (proj2 (Z.eqb_neq _ _) E32), (proj2 (Z.eqb_neq _ _) E9); reflexivity).
    rewrite (skip_f _ _ _ Hnb) in Hinv.
    step. takeF false. step. takeF true.
    apply (KN _ _ _ _ _ _ _ _ _ j); [exact Hs3 | exact Hy10 | fact | exact Ha3 | lia | ].
    rewrite Hinv. symmetry. apply flsfx. lia.
Qed.

(* the UBSan checks of r + j and the optional sign: +0x138 .. +0x158.  d0 = j + (sign ? 1 : 0), and the model's list
   after the sign is skipn d0 (first_line zs) in both cases *)
Lemma seg_sign : forall (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word) j,
  bv_unsigned s3 = e -> bv_unsigned a0 = r + j -> bv_unsigned a1 = nthz zs j -> bv_unsigned a3 = j -> 0 <= j < e ->
  (forall (a0' a1' a2' a3' a4' a5' a6' a7' : word) d0,
     bv_unsigned a1' = nthz zs j -> bv_unsigned a3' = d0 -> bv_unsigned a4' = 2 ^ 64 - 1 - r -> j <= d0 < e ->
     snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat d0) (first_line zs) ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x15c) a0' a1' a2' a3' a4' a5' a6' a7' s3)) ->
  (forall (a0' a1' a2' a3' a4' a5' a6' a7' : word),
     snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = [] ->
     ExecF.evtF rsegs RNG Q (ST CV_TEST a0' a1' a2' a3' a4' a5' a6' a7' s3)) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x138) a0 a1 a2 a3 a4 a5 a6 a7 s3).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 s3 j Hs3 Ha0 Ha1 Ha3 Hje KS KZ.
  pose proof (BR j) as Hb. pose proof eloc as Hel. pose proof (cv_first_line_le zs) as Hfl.
  pose proof rn_lt as Hrn. pose proof ur as Ur.
  assert (SP : skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs))
    by (apply flsfx; lia).
  assert (NOT : Z.lxor r 18446744073709551615 = 2 ^ 64 - 1 - r) by (rewrite zb_lxor_ones by lia; lia).
  step. takeF false.
  step. step. takeF false.
  destruct (Z.eq_dec (nthz zs j) 43) as [E43|E43].
  { (* '+' *)
    assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat (j + 1)) (first_line zs))
      by (rewrite SP, (ss_plus _ _ E43); reflexivity).
    step. step. takeF true. step. step.
    destruct (Z.eq_dec (j + 1) e) as [Ee|Ee].
    - takeF true. apply KZ. rewrite SG, Ee. apply skipn_all2. lia.
    - takeF false. apply (KS _ _ _ _ _ _ _ _ (j + 1)); [exact Ha1 | fact | fact4 | lia | exact SG]. }
  destruct (Z.eq_dec (nthz zs j) 45) as [E45|E45].
  { (* '-' *)
    assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat (j + 1)) (first_line zs))
      by (rewrite SP, (ss_minus _ _ E45); reflexivity).
    step. step. takeF false. step. step. takeF false. step. step.
    destruct (Z.eq_dec (j + 1) e) as [Ee|Ee].
    - takeF true. apply KZ. rewrite SG, Ee. apply skipn_all2. lia.
    - takeF false. apply (KS _ _ _ _ _ _ _ _ (j + 1)); [exact Ha1 | fact | fact4 | lia | exact SG]. }
  (* no sign *)
  assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat j) (first_line zs))
    by (rewrite SP at 1; rewrite (ss_none _ _ E43 E45); rewrite <- SP; reflexivity).
  step. step. takeF false. step. step. takeF true. step. takeF false.
  apply (KS _ _ _ _ _ _ _ _ j); [exact Ha1 | exact Ha3 | fact4 | lia | exact SG].
Qed.

(* +0x138: the sign, then the hand-off KD or +0x25c *)
Lemma ev_sign : forall (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word) j,
  bv_unsigned s3 = e -> bv_unsigned a0 = r + j -> bv_unsigned a1 = nthz zs j -> bv_unsigned a3 = j -> 0 <= j < e ->
  SKL = skipn (Z.to_nat j) (first_line zs) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x138) a0 a1 a2 a3 a4 a5 a6 a7 s3).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 s3 j Hs3 Ha0 Ha1 Ha3 Hje HS.
  pose proof eloc as Hel.
  assert (HJ : skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs))
    by (apply flsfx; lia).
  assert (HF : fst (sign_split SKL) = (nthz zs j =? 45)) by (rewrite HS, HJ; apply ss_fst).
  apply (seg_sign a0 a1 a2 a3 a4 a5 a6 a7 s3 j Hs3 Ha0 Ha1 Ha3 Hje).
  - intros a0' a1' a2' a3' a4' a5' a6' a7' d0 Ha1' Ha3' Ha4' Hd0 Hsnd.
    apply (KD a0' a1' a2' a3' a4' a5' a6' a7' s3 d0 (nthz zs j));
      [exact Hs3 | exact Ha1' | exact Ha3' | exact Ha4' | apply BR | lia | rewrite HS; exact Hsnd | exact HF].
  - intros a0' a1' a2' a3' a4' a5' a6' a7' Hnil.
    apply ev_cur. apply ev_cur_nil. rewrite HS. exact Hnil.
Qed.

(* +0x0f0: the leading-blank loop's set-up, then the loop *)
Lemma ev_f0 : forall (a0 a1 a2 a3 a4 a5 a6 a7 s3 : word), bv_unsigned s3 = e -> 0 < e ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0xf0) a0 a1 a2 a3 a4 a5 a6 a7 s3).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 s3 Hs3 He0.
  pose proof eloc as Hel.
  do 3 step.
  apply (loop_lb ev_sign (Z.to_nat (e - 1)) 0);
    [lia | lia | reflexivity | exact Hs3 | fact | fact | fact].
Qed.

(* +0x06c: s2 := g, the scan's set-up, then the whole first half *)
Lemma ev_block : forall (s2 a1 a2 a3 a4 a5 a6 a7 : word),
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 g a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 r)
             (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CV_RET_RUI) fc None m (seg_rom rsegs)).
Proof.
  intros s2 a1 a2 a3 a4 a5 a6 a7.
  pose proof eloc as Hel. pose proof rn_lt as Hrn. pose proof ur as Ur.
  do 7 step.
  apply (loop_nl ev_f0 (Z.to_nat (n - 1)) 0);
    [lia | lia | change (skipn (Z.to_nat 0) zs) with zs; lia | fact | fact | fact | fact | exact sltu_r | fact].
Qed.

End EvA.

(* The first half of the inlined expected_value: cv_ev_stmt_F, given the walk from the digit loop's set-up on. *)
Theorem cv_ev_of_dgt : cv_dgt_stmt_F -> cv_ev_stmt_F.
Proof.
  intros HD RNG ra sp gp tp t0 t1 t2 s0 s1 g a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m r n cur zs Q HR0 HN HL BR RD ADR RR RS CUR S0 KF.
  eapply ev_block with (e := Z.of_nat (length (first_line zs))) (zs := zs) (cur := cur).
  all: try first [ exact KF | assumption | reflexivity ].
  intros a0' a1' a2' a3' a4' a5' a6' a7' s3' d0 c0 Hs3 Ha1 Ha3 Ha4 Hc0 Hd0 Hs Hf.
  exact (HD RNG ra sp gp tp t0 t1 t2 s0 s1 g a0' a1' a2' a3' a4' a5' a6' a7' s3' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m r n cur zs Q d0 c0 HR0 HN HL BR RD ADR RR RS CUR S0 Hs3 Ha1 Ha3 Ha4 Hc0 Hd0 Hs Hf KF).
Qed.
