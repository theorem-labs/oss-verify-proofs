(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: the first half of lib/Prog/check_value.v's Section Ev (loop_nl, loop_lb,
   seg_sign, ev_val, ev_cur, ev_sign, ev_lb_nil, ev_60, ev_5c, ev_block and their list and sign helpers) moved to
   image A (fuzz_uci.asan): footprint runs (lib/Lib/ExecF.v evtF, lib/Lib/StepF.v step) instead of evt, this image's
   addresses (UciCvIface.v CV_AT offsets +0x06c .. +0x128) and registers, and the two ASan load checks of each loop
   in the form of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_loop.v at origin/ossv/recipes 88154566652a (cl1_F;
   crt_sh1F, takeF and crt_lits copied as cv_sh1F, takeF and cv_lits, module paths changed to reac_repacer.fuzz_uci). *)
(* UciCvEvA: cv_ev_of_dgt proves lib/A/Prog/UciCvIface.v cv_ev_stmt_F from cv_dgt_stmt_F, i.e. the walk of
   check_value's inlined expected_value from the return of rp_uci_int (+0x06c) to the digit loop's set-up (+0x128),
   whose rest cv_dgt_stmt_F states.  Offsets from the entry (UciCvIface.v CV_AT), read from the pinned image's code:
     +0x06c `mv s2, a0`; a1 := 0; a2 := 10
     +0x078 .. +0x0a8  the scan for the first '\n' (index a1): the ASan load check of r + a1 (report at +0x0a8 via the
            slow path +0x0a0), `lbu a0`; `beq a0, a2` to +0x0c0; a1 += 1; `bne s4, a1` back; else `j` +0x0c8
     +0x0c0 `bnez a1` to +0x0cc, else `j` +0x21c (empty first line: the value is cur); +0x0c8 a1 := n (no '\n')
     +0x0cc a4 := 0, a3 := 32, a5 := 9
     +0x0d8 .. +0x10c  the leading-blank skip (index a4): the ASan load check of r + a4 (report at +0x10c via +0x104),
            `lbu a2`; `beq a2, a3` to +0x0f8; `bne a2, a5` to +0x110; +0x0f8 a4 += 1; `bne a1, a4` back; else `j`
            +0x21c (all blank: cur)
     +0x110 .. +0x124  the optional sign: '+' or '-' steps a4 once; `bgeu a4, a1` to +0x21c (nothing after the sign:
            cur), else +0x128, the hand-off (a1 = e, a4 = d0, a2 = c0). *)
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

(* lib/Prog/check_value.v's branch-test and register-fact tactics (this half has no `sext.w`, so solve_c needs
   no 32-bit wrap). *)
Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?zb_signed; zsimp; wsub; zsimp;
  decide_tests; reflexivity.
Ltac fact := cbv delta [zxb]; wsub; rewrite ?unsigned_lit_wrap; mlia.

(* crtA_loop.v's branch choice, for the footprint run. *)
Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* As crtA_loop.v crt_lits: the statements name every pc by UciCvIface.v's names; inside the proofs each step first
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

(* =========================================================================
   The two ASan load checks (crtA_loop.v cl1_F's form).  Each loads the shadow byte k of A = r + i (1 byte, inside
   the 8-aligned cover of the reply's shadow) and, since k allows the load, the reply byte b at A (1 byte inside the
   reply); the report call is not reached.  s5 (x21) holds the shadow offset.
   ========================================================================= *)

(* +0x078 -> +0x090: a0 := s3 + a1; shadow of a0 into a3 (`lb`); handler `andi a4`; `lbu a0` *)
Lemma cv_ck1_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A : Z),
  bv_unsigned x19 + bv_unsigned x11 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG A 1 ->
  (forall y13 y14 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) x11 x12 y13 y14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0x90)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0x78)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK MD RK RD CONT.
  pose proof (u64_range x19) as R19. pose proof (u64_range x11) as R11. unfold ASAN_K in M, RK.
  step. gen_add x19 x11 w U. rewrite EA in U.
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

(* +0x0d8 -> +0x0f0: a0 := s3 + a4; shadow of a0 into a2 (`lb`); handler `andi a6`; `lbu a2` *)
Lemma cv_ck2_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A : Z),
  bv_unsigned x19 + bv_unsigned x14 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG A 1 ->
  (forall y10 y16 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 x11 (zxb b) x13 x14 x15 y16 x17 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0xf0)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CV_AT 0xd8)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK MD RK RD CONT.
  pose proof (u64_range x19) as R19. pose proof (u64_range x14) as R14. unfold ASAN_K in M, RK.
  step. gen_add x19 x14 w U. rewrite EA in U.
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

(* =========================================================================
   The walk +0x06c .. +0x128 / +0x21c (lib/Prog/check_value.v Section Ev, first half).  The section carries
   cv_ev_stmt_F's premises, e the length of the first line, the continuation KFIN at +0x21c and the hand-off KD at
   +0x128 (cv_dgt_stmt_F at these premises).
   ========================================================================= *)

Section EvA.
Variables (ra sp gp tp t0 t1 t2 s0 s1 g s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (r n cur e : Z) (zs : list Z) (Q : machine_state -> Prop) (RNG : ExecF.footprint).
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

Local Abbreviation ST pc a0 a1 a2 a3 a4 a5 a6 a7 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 g (Z_to_bv 64 r) (Z_to_bv 64 n)
           (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Local Abbreviation SKL := (skip is_lead_blank (first_line zs)).

Hypothesis KFIN : forall (s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word),
  bv_unsigned s0' = expected_value_m zs cur mod 2 ^ 64 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' g (Z_to_bv 64 r) (Z_to_bv 64 n)
             (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CV_TEST) fc None m (seg_rom rsegs)).

Hypothesis KD : forall (a0 a1 a2 a3 a4 a5 a6 a7 : word) d0 c0,
  bv_unsigned a1 = e -> bv_unsigned a2 = c0 -> bv_unsigned a4 = d0 ->
  0 <= c0 < 256 -> 0 <= d0 < e ->
  snd (sign_split SKL) = skipn (Z.to_nat d0) (first_line zs) ->
  fst (sign_split SKL) = (c0 =? 45) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x128) a0 a1 a2 a3 a4 a5 a6 a7).

Lemma eloc : 0 <= e <= n.
Proof. pose proof (cv_first_line_le zs) as H. lia. Qed.

Lemma rn_lt : 0 <= r /\ r + n < 2 ^ 64.
Proof. destruct ADR as (H0 & _ & H & _). unfold APPMEM_END in H. lia. Qed.

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
Lemma ck1 : forall i (a0 a1 a2 a3 a4 a5 a6 a7 : word), 0 <= i < n -> bv_unsigned a1 = i ->
  (forall y13 y14 : word,
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x90) (Z_to_bv 64 (nthz zs i)) a1 a2 y13 y14 a5 a6 a7)) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x78) a0 a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros i a0 a1 a2 a3 a4 a5 a6 a7 Hi Ha1 K.
  pose proof rn_lt as Hrn.
  destruct (sh_at i Hi) as (k & M & SK).
  eapply (cv_ck1_F RNG) with (A := r + i) (k := k) (b := Z_to_bv 8 (nthz zs i)).
  - rewrite Ha1, unsigned_lit by lia. reflexivity.
  - lia.
  - exact M.
  - exact SK.
  - apply RD. exact Hi.
  - exact (cv_sh1F RNG r n i RS Hi).
  - apply (ExecF.rng_sub RNG r n); [exact RR | lia | lia].
  - intros y13 y14. rewrite (zxb_lit _ (BR i)). apply K.
Qed.

Lemma ck2 : forall j (a0 a1 a2 a3 a4 a5 a6 a7 : word), 0 <= j < n -> bv_unsigned a4 = j ->
  (forall y10 y16 : word,
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0xf0) y10 a1 (Z_to_bv 64 (nthz zs j)) a3 a4 a5 y16 a7)) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0xd8) a0 a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros j a0 a1 a2 a3 a4 a5 a6 a7 Hj Ha4 K.
  pose proof rn_lt as Hrn.
  destruct (sh_at j Hj) as (k & M & SK).
  eapply (cv_ck2_F RNG) with (A := r + j) (k := k) (b := Z_to_bv 8 (nthz zs j)).
  - rewrite Ha4, unsigned_lit by lia. reflexivity.
  - lia.
  - exact M.
  - exact SK.
  - apply RD. exact Hj.
  - exact (cv_sh1F RNG r n j RS Hj).
  - apply (ExecF.rng_sub RNG r n); [exact RR | lia | lia].
  - intros y10 y16. rewrite (zxb_lit _ (BR j)). apply K.
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

(* +0x21c with s0 = cur, when the value is cur *)
Lemma ev_cur : forall (a0 a1 a2 a3 a4 a5 a6 a7 : word), expected_value_m zs cur = cur ->
  ExecF.evtF rsegs RNG Q (ST CV_TEST a0 a1 a2 a3 a4 a5 a6 a7).
Proof. intros a0 a1 a2 a3 a4 a5 a6 a7 H. apply KFIN. rewrite H. exact S0. Qed.

Lemma ev_lb_nil : forall (a0 a1 a2 a3 a4 a5 a6 a7 : word), SKL = [] ->
  ExecF.evtF rsegs RNG Q (ST CV_TEST a0 a1 a2 a3 a4 a5 a6 a7).
Proof. intros a0 a1 a2 a3 a4 a5 a6 a7 H. apply ev_cur. apply ev_cur_nil. rewrite H. reflexivity. Qed.

(* ---- the loops ---- *)

(* the scan for the first '\n': +0x078, a1 the index, a2 = 10; the '\n' test at +0x0c0 included *)
Lemma loop_nl :
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 : word), bv_unsigned a1 = e -> 0 < e ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0xcc) a0 a1 a2 a3 a4 a5 a6 a7)) ->
  forall k i (a0 a1 a2 a3 a4 a5 a6 a7 : word),
  0 <= i -> i + Z.of_nat (S k) = n ->
  e = i + Z.of_nat (length (first_line (skipn (Z.to_nat i) zs))) ->
  bv_unsigned a1 = i -> bv_unsigned a2 = 10 ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x78) a0 a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros K6 k. induction k as [|k IH]; intros i a0 a1 a2 a3 a4 a5 a6 a7 Hi0 Hk Hinv Ha1 Ha2.
  all: assert (Hin : 0 <= i < n) by lia.
  all: pose proof (BR i) as Hb.
  all: rewrite (sfx_cons i Hin) in Hinv.
  all: apply (ck1 i a0 a1 a2 a3 a4 a5 a6 a7 Hin Ha1); intros y13 y14.
  all: destruct (Z.eq_dec (nthz zs i) 10) as [Ec|Ec].
  (* the '\n' at i: e = i *)
  1, 3: rewrite (fl_nl _ _ Ec) in Hinv; cbn [length] in Hinv;
        assert (Ei : e = i) by lia;
        step; takeF true;
        step; destruct (Z.eq_dec i 0) as [E0|E0];
        [ takeF false; step; apply ev_lb_nil;
          assert (Hnil : first_line zs = []) by (apply length_zero_iff_nil; lia);
          rewrite Hnil; reflexivity
        | takeF true; apply K6; [rewrite Ei; exact Ha1 | lia] ].
  (* k = 0, not '\n': the end, e = n *)
  - rewrite (fl_other _ _ Ec) in Hinv. cbn [length] in Hinv.
    rewrite skipn_all2 in Hinv by lia. cbn [first_line length] in Hinv.
    step. takeF false. step. step. takeF false.
    step. step. apply K6; [fact | lia].
  (* k = S k, not '\n' *)
  - rewrite (fl_other _ _ Ec) in Hinv. cbn [length] in Hinv.
    step. takeF false. step. step. takeF true.
    apply (IH (i + 1)); [lia | lia | lia | fact | exact Ha2].
Qed.

(* the leading-blank skip: +0x0d8, a4 the index, a1 = e, a3 = 32, a5 = 9 *)
Lemma loop_lb :
  (forall (a0 a1 a2 a3 a4 a5 a6 a7 : word) j,
     bv_unsigned a1 = e -> bv_unsigned a2 = nthz zs j -> bv_unsigned a4 = j -> 0 <= j < e ->
     SKL = skipn (Z.to_nat j) (first_line zs) ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x110) a0 a1 a2 a3 a4 a5 a6 a7)) ->
  forall k j (a0 a1 a2 a3 a4 a5 a6 a7 : word),
  0 <= j -> j + Z.of_nat (S k) = e ->
  SKL = skip is_lead_blank (skipn (Z.to_nat j) (first_line zs)) ->
  bv_unsigned a1 = e -> bv_unsigned a3 = 32 -> bv_unsigned a5 = 9 -> bv_unsigned a4 = j ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0xd8) a0 a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros KN k. induction k as [|k IH]; intros j a0 a1 a2 a3 a4 a5 a6 a7 Hj0 Hk Hinv Ha1 Ha3 Ha5 Ha4.
  all: pose proof eloc as Hel.
  all: pose proof (cv_first_line_le zs) as Hfl.
  all: assert (Hje : 0 <= j < e) by lia.
  all: assert (Hin : 0 <= j < n) by lia.
  all: pose proof (BR j) as Hb.
  all: rewrite (flsfx j Hje) in Hinv.
  all: apply (ck2 j a0 a1 a2 a3 a4 a5 a6 a7 Hin Ha4); intros y10 y16.
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
    apply (KN _ _ _ _ _ _ _ _ j); [exact Ha1 | fact | exact Ha4 | lia | ].
    rewrite Hinv. symmetry. apply flsfx. lia.
  (* k = S k *)
  - rewrite (skip_t _ _ _ (lb_32 _ E32)) in Hinv.
    step. takeF true. step. step. takeF true.
    apply (IH (j + 1)); [lia | lia | exact Hinv | exact Ha1 | exact Ha3 | exact Ha5 | fact].
  - rewrite (skip_t _ _ _ (lb_9 _ E9)) in Hinv.
    step. takeF false. step. takeF false. step. step. takeF true.
    apply (IH (j + 1)); [lia | lia | exact Hinv | exact Ha1 | exact Ha3 | exact Ha5 | fact].
  - assert (Hnb : is_lead_blank (nthz zs j) = false) by (unfold is_lead_blank;
      rewrite (proj2 (Z.eqb_neq _ _) E32), (proj2 (Z.eqb_neq _ _) E9); reflexivity).
    rewrite (skip_f _ _ _ Hnb) in Hinv.
    step. takeF false. step. takeF true.
    apply (KN _ _ _ _ _ _ _ _ j); [exact Ha1 | fact | exact Ha4 | lia | ].
    rewrite Hinv. symmetry. apply flsfx. lia.
Qed.

(* the optional sign: +0x110 .. +0x124.  d0 = j + (sign ? 1 : 0), and the model's list after the sign is
   skipn d0 (first_line zs) in both cases *)
Lemma seg_sign : forall (a0 a1 a2 a3 a4 a5 a6 a7 : word) j,
  bv_unsigned a1 = e -> bv_unsigned a2 = nthz zs j -> bv_unsigned a4 = j -> 0 <= j < e ->
  (forall (a0' a1' a2' a3' a4' a5' a6' a7' : word) d0,
     bv_unsigned a1' = e -> bv_unsigned a2' = nthz zs j -> bv_unsigned a4' = d0 -> j <= d0 < e ->
     snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat d0) (first_line zs) ->
     ExecF.evtF rsegs RNG Q (ST (CV_AT 0x128) a0' a1' a2' a3' a4' a5' a6' a7')) ->
  (forall (a0' a1' a2' a3' a4' a5' a6' a7' : word),
     snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = [] ->
     ExecF.evtF rsegs RNG Q (ST CV_TEST a0' a1' a2' a3' a4' a5' a6' a7')) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x110) a0 a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 j Ha1 Ha2 Ha4 Hje KS KZ.
  pose proof (BR j) as Hb. pose proof eloc as Hel. pose proof (cv_first_line_le zs) as Hfl.
  assert (SP : skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs))
    by (apply flsfx; lia).
  destruct (Z.eq_dec (nthz zs j) 43) as [E43|E43].
  { (* '+' *)
    assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat (j + 1)) (first_line zs))
      by (rewrite SP, (ss_plus _ _ E43); reflexivity).
    step. step. takeF true. step. step.
    destruct (Z.eq_dec (j + 1) e) as [Ee|Ee].
    - takeF true. apply KZ. rewrite SG, Ee. apply skipn_all2. lia.
    - takeF false. apply (KS _ _ _ _ _ _ _ _ (j + 1)); [exact Ha1 | exact Ha2 | fact | lia | exact SG]. }
  destruct (Z.eq_dec (nthz zs j) 45) as [E45|E45].
  { (* '-' *)
    assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat (j + 1)) (first_line zs))
      by (rewrite SP, (ss_minus _ _ E45); reflexivity).
    step. step. takeF false. step. step. takeF false. step. step.
    destruct (Z.eq_dec (j + 1) e) as [Ee|Ee].
    - takeF true. apply KZ. rewrite SG, Ee. apply skipn_all2. lia.
    - takeF false. apply (KS _ _ _ _ _ _ _ _ (j + 1)); [exact Ha1 | exact Ha2 | fact | lia | exact SG]. }
  (* no sign *)
  assert (SG : snd (sign_split (skipn (Z.to_nat j) (first_line zs))) = skipn (Z.to_nat j) (first_line zs))
    by (rewrite SP at 1; rewrite (ss_none _ _ E43 E45); rewrite <- SP; reflexivity).
  step. step. takeF false. step. step. takeF true. step. takeF false.
  apply (KS _ _ _ _ _ _ _ _ j); [exact Ha1 | exact Ha2 | exact Ha4 | lia | exact SG].
Qed.

(* +0x110: the sign, then the hand-off KD or +0x21c *)
Lemma ev_sign : forall (a0 a1 a2 a3 a4 a5 a6 a7 : word) j,
  bv_unsigned a1 = e -> bv_unsigned a2 = nthz zs j -> bv_unsigned a4 = j -> 0 <= j < e ->
  SKL = skipn (Z.to_nat j) (first_line zs) ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0x110) a0 a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 j Ha1 Ha2 Ha4 Hje HS.
  pose proof eloc as Hel.
  assert (HJ : skipn (Z.to_nat j) (first_line zs) = nthz zs j :: skipn (Z.to_nat (j + 1)) (first_line zs))
    by (apply flsfx; lia).
  assert (HF : fst (sign_split SKL) = (nthz zs j =? 45)) by (rewrite HS, HJ; apply ss_fst).
  apply (seg_sign a0 a1 a2 a3 a4 a5 a6 a7 j Ha1 Ha2 Ha4 Hje).
  - intros a0' a1' a2' a3' a4' a5' a6' a7' d0 Ha1' Ha2' Ha4' Hd0 Hsnd.
    apply (KD a0' a1' a2' a3' a4' a5' a6' a7' d0 (nthz zs j));
      [exact Ha1' | exact Ha2' | exact Ha4' | apply BR | lia | rewrite HS; exact Hsnd | exact HF].
  - intros a0' a1' a2' a3' a4' a5' a6' a7' Hnil.
    apply ev_cur. apply ev_cur_nil. rewrite HS. exact Hnil.
Qed.

(* +0x0cc: the leading-blank loop's set-up, then the loop *)
Lemma ev_cc : forall (a0 a1 a2 a3 a4 a5 a6 a7 : word), bv_unsigned a1 = e -> 0 < e ->
  ExecF.evtF rsegs RNG Q (ST (CV_AT 0xcc) a0 a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 Ha1 He0.
  pose proof eloc as Hel.
  do 3 step.
  apply (loop_lb ev_sign (Z.to_nat (e - 1)) 0);
    [lia | lia | reflexivity | exact Ha1 | fact | fact | fact].
Qed.

(* +0x06c: s2 := g, the scan's set-up, then the whole first half *)
Lemma ev_block : forall (s2 a1 a2 a3 a4 a5 a6 a7 : word),
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 g a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 r) (Z_to_bv 64 n)
             (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CV_RET_RUI) fc None m (seg_rom rsegs)).
Proof.
  intros s2 a1 a2 a3 a4 a5 a6 a7.
  pose proof eloc as Hel.
  step. step. step.
  apply (loop_nl ev_cc (Z.to_nat (n - 1)) 0);
    [lia | lia | change (skipn (Z.to_nat 0) zs) with zs; lia | fact | fact].
Qed.

End EvA.

(* The first half of the inlined expected_value: cv_ev_stmt_F, given the walk from the digit loop's set-up on. *)
Theorem cv_ev_of_dgt : cv_dgt_stmt_F -> cv_ev_stmt_F.
Proof.
  intros HD RNG ra sp gp tp t0 t1 t2 s0 s1 g a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m r n cur zs Q HR0 HN HL BR RD ADR RR RS CUR S0 KF.
  eapply ev_block with (e := Z.of_nat (length (first_line zs))) (zs := zs) (cur := cur).
  all: try first [ exact KF | assumption | reflexivity ].
  intros a0' a1' a2' a3' a4' a5' a6' a7' d0 c0 Ha1 Ha2 Ha4 Hc0 Hd0 Hs Hf.
  exact (HD RNG ra sp gp tp t0 t1 t2 s0 s1 g a0' a1' a2' a3' a4' a5' a6' a7' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m r n cur zs Q d0 c0 HR0 HN HL BR RD ADR RR RS CUR S0 Ha1 Ha2 Ha4 Hc0 Hd0 Hs Hf KF).
Qed.
