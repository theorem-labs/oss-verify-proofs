(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: the first half of lib/Prog/check_value.v's Section Ev (loop_nl, loop_lb,
   seg_sign, ev_val, ev_cur, ev_sign, ev_lb_nil, ev_60, ev_5c, ev_block and their list and sign helpers) moved to
   image A (fuzz_uci.asan): footprint runs (lib/Lib/ExecF.v evtF, lib/Lib/StepF.v step) instead of evt, this image's
   addresses (UciCvIface.v CV_AT offsets +0x06c .. +0x128) and registers, and the two ASan load checks of each loop
   in the form of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_loop.v at origin/ossv/recipes 88154566652a (cl1_F;
   crt_sh1F, takeF and crt_lits copied as cv_sh1F, takeF and cv_lits, module paths changed to reac_repacer.fuzz_uci). *)
(* Modified by Theorem Labs, 2026-10: the straight-line segments of reac-repacer/fuzz_uci's check_value in image A, in the form
   and with the helpers of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_segs.v (origin/ossv/recipes 88154566652a:
   crt_seg1_F .. crt_seg9_F, Z_to_le_bytes_to_Z, crt_le8_of_bytes, crt_c8s, crt_rw_c8s, crt_frame_words, crt_regs,
   crt_usub, crt_shift, crt_w, crt_finF, crt_memF, crt_pc) and of its lib/A/Prog/ReacDecodeLib.v rd_all. *)
(* Modified by Theorem Labs, 2026-10: the helpers and tactics of reac-repacer/fuzz_uci's lib/A/Prog/UciCvSegs.v
   (cv_le_bytes_to_Z, cv_le8_of_bytes, cv_c8s, cv_c8s_spec, cv_rw_c8s, cv_frame_words, cv_rd_all, cv_regs, cv_usub,
   cv_shift, cv_w, cv_finF, cv_memF, cv_lits, whose own notice names their source crtA_segs.v of
   proofs/libreac/fuzz_decode/lib/A/Prog) and of its lib/A/Prog/UciCvEvA.v (u8lit, zxb_lit, align8_cover, cv_sh1F,
   sh_at, and the steps of the ASan load check cv_ck1_F), renamed cc_* and moved to fuzz_wire's check_copy (image A,
   module paths reac_repacer.fuzz_wire). *)
(* check_copy_cgW_segs: proofs of the footprint-run statements of lib/A/Prog/check_copy_cgW_iface.v, the
   straight-line segments of check_copy (fuzz_wire.asan 0x80c38) between its cut points, stepped by lib/Lib/StepF.v.
   Offsets are from the entry (check_copy_cgW_iface.v CC_AT).
     cc_seg_entry_ok    +0x000 -> rp_copy_untag: the 0x40-byte frame, s3 := n, s4 := f, s5 := the shadow base
                        (GOT_CELL_K -> CELL_K), s1 := c, a1 := n;
     cc_seg_m_ok        +0x040 -> malloc: s0 := a0, a0 := n + (n == 0);
     cc_seg_z_ok        +0x050, n = 0, got = 0 -> free(u);
     cc_seg_cp1_ok      +0x050, n > 0 -> __asan_memcpy(u, f, n);
     cc_seg_short_ok    +0x06c, n < 18, got = 0 -> free(u);
     cc_seg_tag_yes_ok  +0x06c, n >= 18, f[12, 13, 16, 17] = 81 00 88 19 -> __asan_memcpy(u + 12, f + 16, n - 16);
     cc_seg_tag_no_ok   +0x06c, n >= 18, not all four match -> +0x110 with a2 = n;
     cc_seg_cp2ret_ok   +0x10c -> +0x110: a2 := n - 4;
     cc_seg_want_lo_ok  +0x110, n < 50, got = 0 -> free(u);
     cc_seg_want_hi_ok  +0x110, n >= 50: the want test on u[12, 13, 16, 17], `beq s0, a0` taken, then free(u) or
                        bcmp(c, u, got);
     cc_seg_bcmpret_ok  +0x18c, a0 = 0 -> free(u);
     cc_seg_end_ok      +0x198 -> the return: a0 := s0, the frame reloaded, sp += 0x40, `ret`.
   Each instrumented 1-byte load (the tag test at +0x074, +0x098, +0x0b8, +0x0dc and the want test at +0x118,
   +0x138, +0x158, +0x1c0) is a lemma cc_ck_* in continuation form, the instrumented check: the load of the shadow
   byte k at (A >> 3) + 0x7fff8000 (1 byte inside the 8-aligned cover of the buffer's shadow bytes), `bnez` on k,
   and for k <> 0 the second compare (`andi` of A's low 3 bits, `blt` against k) back to the load; the range is
   addressable, so k = 0 or (A mod 8) < k, the check passes and the error path is not reached; then the load of the
   byte at A (1 byte inside the buffer). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr
  check_copy_cgW_iface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- helpers (UciCvSegs.v) ---- *)

Lemma cc_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
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

Lemma cc_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply cc_le_bytes_to_Z.
Qed.

Fixpoint cc_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: cc_c8s n' (skipn 8 bs)
  end.

Lemma cc_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (cc_c8s n bs) /\ cells_bytes (cc_c8s n bs) = bs /\ cells_size (cc_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [cc_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite cc_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma cc_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (cc_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (cc_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 64 bytes, read as 8 words. *)
Lemma cc_frame_words : forall m A bs, rw_cells rsegs m A [CB 64 bs] ->
  exists v0 v8 v16 v24 v32 v40 v48 v56 : word,
    rw_cells rsegs m A [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56].
Proof.
  intros m A bs H. apply (cc_rw_c8s rsegs m A 8 bs) in H. cbn [cc_c8s] in H. do 8 eexists. exact H.
Qed.

Lemma cc_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* A word is the literal of its value. *)
Lemma cc_word_of : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros w z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma cc_u8lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cc_zxb_lit : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zxb. rewrite cc_u8lit by exact Hc. reflexivity. Qed.

Ltac cc_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cc_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cc_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac cc_w := cc_shift; cc_usub; cc_shift; cc_usub;
  first [ reflexivity | rewrite ?Z_to_bv_plus0, ?Z_to_bv_bv_unsigned; reflexivity | f_equal; lia
        | apply Z_to_bv_eqm; f_equal; lia | f_equal; Z.div_mod_to_equations; nia ].
Ltac cc_finF := apply evtF_done; f_equal; cc_regs; cc_w.
Ltac cc_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* StepF's step reads the start pc; every pc here is a check_copy_cgW_iface name, so each proof first computes every
   such closed name, in the goal and in the hypotheses, to its value (as UciCvSegs.v cv_lits). *)
Ltac cc_lit X := let v := eval vm_compute in X in change X with v.
Ltac cc_lit_in X H := let v := eval vm_compute in X in change X with v in H.
Ltac cc_lits :=
  repeat match goal with
  | |- context [CC_RET_RCU] => cc_lit CC_RET_RCU
  | |- context [CC_RET_MALLOC] => cc_lit CC_RET_MALLOC
  | |- context [CC_RET_CP1] => cc_lit CC_RET_CP1
  | |- context [CC_RET_CP2] => cc_lit CC_RET_CP2
  | |- context [CC_WANT] => cc_lit CC_WANT
  | |- context [CC_RET_BCMP] => cc_lit CC_RET_BCMP
  | |- context [CC_RET_FREE] => cc_lit CC_RET_FREE
  | |- context [CC_RCU] => cc_lit CC_RCU
  | |- context [CC_MALLOC] => cc_lit CC_MALLOC
  | |- context [CC_FREE] => cc_lit CC_FREE
  | |- context [CC_MEMCPY] => cc_lit CC_MEMCPY
  | |- context [CC_BCMP] => cc_lit CC_BCMP
  | |- context [CC_AT ?o] => cc_lit (CC_AT o)
  | |- context [CC_ENTRY] => cc_lit CC_ENTRY
  | H : context [CC_AT ?o] |- _ => cc_lit_in (CC_AT o) H
  end.

(* ---- the shadow footprint (UciCvEvA.v) ---- *)

(* [a, c] inside the 8-aligned cover of [a, c]. *)
Lemma cc_align8_cover : forall a b c, a <= b -> b <= c -> a / 8 * 8 <= b /\ b + 1 <= c / 8 * 8 + 8.
Proof. intros a b c H1 H2. split; Z.div_mod_to_equations; lia. Qed.

(* The shadow byte of X + i, for i in [0, n), lies in the 8-aligned cover of the shadow bytes of [X, X + n). *)
Lemma cc_sh1F : forall RNG X n i,
  ExecF.rng RNG (cc_hull_lo X) (cc_hull_len X n) ->
  0 <= i < n ->
  ExecF.rng RNG ((X + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG X n i H Hi. unfold cc_hull_lo, cc_hull_len, shadow_addr in H.
  assert (L1 : X / 8 <= (X + i) / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : (X + i) / 8 <= (X + n - 1) / 8) by (apply Z.div_le_mono; lia).
  destruct (cc_align8_cover (X / 8 + ASAN_K) ((X + i) / 8 + ASAN_K) ((X + n - 1) / 8 + ASAN_K)
             ltac:(lia) ltac:(lia)) as (A1 & A2).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* The shadow byte of p + i passes the check of a 1-byte load (addressable). *)
Lemma cc_sh_at : forall m p n i, addressable m p n -> 0 <= i < n -> exists k : byte,
  mrd rsegs m (wa ((p + i) / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ (p + i) mod 8 < bv_signed k).
Proof.
  intros m p n i ADR Hi. destruct ADR as (_ & _ & _ & HA). destruct (HA i Hi) as (_ & k & Hk & Hok).
  exists k. split; [exact Hk|]. destruct Hok as [E|[E _]]; [left; exact E | right; exact E].
Qed.

(* ---- the instrumented 1-byte loads ---- *)

(* One check (UciCvEvA.v cv_ck1_F), at the buffer p (in the base register xb) and its byte off: the shadow byte k
   of p + off and the fact that it passes the check (cc_sh_at), the two footprint ranges, the bound of p + off; then
   the steps: the address xb + off, its shadow address through s5, the `lb` of k, `bnez`; for k <> 0 the `andi` of
   the low 3 bits and the `blt` back; then the `lbu` of the byte, and the continuation. *)
Ltac cc_ck_proof xb p off n :=
  let HX := fresh "HX" in let ADR := fresh "ADR" in let HN := fresh "HN" in let RF := fresh "RF" in
  let RS := fresh "RS" in let MD := fresh "MD" in let HB := fresh "HB" in let CONT := fresh "CONT" in
  let k := fresh "k" in let M := fresh "M" in let SK := fresh "SK" in let RK := fresh "RK" in
  let RD := fresh "RD" in let RA := fresh "RA" in let EA := fresh "EA" in let E := fresh "E" in
  let Rb := fresh "Rb" in let w := fresh "w" in let U := fresh "U" in let g := fresh "g" in
  let G := fresh "G" in let h := fresh "h" in let H := fresh "H" in let R := fresh "R" in
  let MB := fresh "MB" in let R2 := fresh "R2" in let C := fresh "C" in
  intros HX ADR HN RF RS MD HB CONT;
  destruct (cc_sh_at _ p n off ADR ltac:(lia)) as (k & M & SK);
  pose proof (cc_sh1F _ p n off RS ltac:(lia)) as RK;
  pose proof (ExecF.rng_sub _ p n (p + off) 1 RF ltac:(lia) ltac:(lia)) as RD;
  assert (RA : p + off < 2 ^ 64) by (destruct ADR as (_ & _ & E & _); unfold APPMEM_END in E; lia);
  assert (EA : bv_unsigned xb + off = p + off) by lia;
  pose proof (u64_range xb) as Rb;
  unfold ASAN_K in *; cc_lits;
  step; gen_addi xb w U; rewrite EA in U;
  step; gen_shr w g G; rewrite U in G;
  step; gen_addi g h H;
  pose proof (rdw0 _ h _ _ M ltac:(lia)) as R; step; clear R;
  step;
  pose proof (Z.mod_pos_bound (p + off) 8 ltac:(lia)) as MB;
  pose proof (rdw0 _ w _ _ MD U) as R2;
  destruct SK as [C|C];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb];
    step; rewrite (cc_zxb_lit _ HB); apply CONT; try exact U
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
    step; step; rewrite land7, U, (lts_low ((p + off) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb];
    step; rewrite (cc_zxb_lit _ HB); apply CONT; try exact U ].

(* +0x074: a0 := s4 + 12; shadow byte into a1; second compare (`andi a2`) at +0x1f0; `lbu a0` at +0x088. *)
Lemma cc_ck_t12 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (p n b : Z),
  bv_unsigned x20 = p -> addressable mm p n -> 18 <= n -> ExecF.rng RNG p n ->
  ExecF.rng RNG (cc_hull_lo p) (cc_hull_len p n) ->
  mrd rsegs mm (wa (p + 12)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) y11 y12 x13 x14 x15 x16 x17 x18 x19 x20
              (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 (CC_AT 0x8c)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (CC_AT 0x74)) fc None mm (seg_rom rsegs)).
Proof. intros until b. cc_ck_proof x20 p 12 n. Qed.

(* +0x098: a0 := s4 + 13; shadow byte into a1; second compare (`andi a2`) at +0x1fc; `lbu a0` at +0x0ac. *)
Lemma cc_ck_t13 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (p n b : Z),
  bv_unsigned x20 = p -> addressable mm p n -> 18 <= n -> ExecF.rng RNG p n ->
  ExecF.rng RNG (cc_hull_lo p) (cc_hull_len p n) ->
  mrd rsegs mm (wa (p + 13)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) y11 y12 x13 x14 x15 x16 x17 x18 x19 x20
              (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 (CC_AT 0xb0)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (CC_AT 0x98)) fc None mm (seg_rom rsegs)).
Proof. intros until b. cc_ck_proof x20 p 13 n. Qed.

(* +0x0b8: a1 := s4 + 16 (kept); shadow byte into a0; second compare (`andi a2`) at +0x220; `lbu a0` at +0x0cc. *)
Lemma cc_ck_t16 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (p n b : Z),
  bv_unsigned x20 = p -> addressable mm p n -> 18 <= n -> ExecF.rng RNG p n ->
  ExecF.rng RNG (cc_hull_lo p) (cc_hull_len p n) ->
  mrd rsegs mm (wa (p + 16)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
  (forall y11 : word, bv_unsigned y11 = p + 16 -> forall y12 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) y11 y12 x13 x14 x15 x16 x17 x18 x19 x20
              (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 (CC_AT 0xd0)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (CC_AT 0xb8)) fc None mm (seg_rom rsegs)).
Proof. intros until b. cc_ck_proof x20 p 16 n. Qed.

(* +0x0dc: a0 := s4 + 17; shadow byte into a2; second compare (`andi a3`) at +0x23c; `lbu a0` at +0x0f0. *)
Lemma cc_ck_t17 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (p n b : Z),
  bv_unsigned x20 = p -> addressable mm p n -> 18 <= n -> ExecF.rng RNG p n ->
  ExecF.rng RNG (cc_hull_lo p) (cc_hull_len p n) ->
  mrd rsegs mm (wa (p + 17)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
  (forall y12 y13 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) x11 y12 y13 x14 x15 x16 x17 x18 x19 x20
              (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 (CC_AT 0xf4)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (CC_AT 0xdc)) fc None mm (seg_rom rsegs)).
Proof. intros until b. cc_ck_proof x20 p 17 n. Qed.

(* The want test's four checks, of u = s2: a0 := s2 + off; shadow byte into a1; second compare `andi a3`. *)
(* +0x118 (second compare at +0x208, `lbu` at +0x12c) *)
Lemma cc_ck_w12 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (p n b : Z),
  bv_unsigned x18 = p -> addressable mm p n -> 18 <= n -> ExecF.rng RNG p n ->
  ExecF.rng RNG (cc_hull_lo p) (cc_hull_len p n) ->
  mrd rsegs mm (wa (p + 12)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
  (forall y11 y13 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) y11 x12 y13 x14 x15 x16 x17 x18 x19 x20
              (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 (CC_AT 0x130)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (CC_AT 0x118)) fc None mm (seg_rom rsegs)).
Proof. intros until b. cc_ck_proof x18 p 12 n. Qed.

(* +0x138 (second compare at +0x214, `lbu` at +0x14c) *)
Lemma cc_ck_w13 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (p n b : Z),
  bv_unsigned x18 = p -> addressable mm p n -> 18 <= n -> ExecF.rng RNG p n ->
  ExecF.rng RNG (cc_hull_lo p) (cc_hull_len p n) ->
  mrd rsegs mm (wa (p + 13)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
  (forall y11 y13 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) y11 x12 y13 x14 x15 x16 x17 x18 x19 x20
              (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 (CC_AT 0x150)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (CC_AT 0x138)) fc None mm (seg_rom rsegs)).
Proof. intros until b. cc_ck_proof x18 p 13 n. Qed.

(* +0x158 (second compare at +0x230, `lbu` at +0x16c) *)
Lemma cc_ck_w16 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (p n b : Z),
  bv_unsigned x18 = p -> addressable mm p n -> 18 <= n -> ExecF.rng RNG p n ->
  ExecF.rng RNG (cc_hull_lo p) (cc_hull_len p n) ->
  mrd rsegs mm (wa (p + 16)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
  (forall y11 y13 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) y11 x12 y13 x14 x15 x16 x17 x18 x19 x20
              (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 (CC_AT 0x170)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (CC_AT 0x158)) fc None mm (seg_rom rsegs)).
Proof. intros until b. cc_ck_proof x18 p 16 n. Qed.

(* +0x1c0 (second compare at +0x248, `lbu` at +0x1d4) *)
Lemma cc_ck_w17 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (p n b : Z),
  bv_unsigned x18 = p -> addressable mm p n -> 18 <= n -> ExecF.rng RNG p n ->
  ExecF.rng RNG (cc_hull_lo p) (cc_hull_len p n) ->
  mrd rsegs mm (wa (p + 17)) = Some (Z_to_bv 8 b) -> 0 <= b < 256 ->
  (forall y11 y13 : word, ExecF.evtF rsegs RNG Q
     (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 b) y11 x12 y13 x14 x15 x16 x17 x18 x19 x20
              (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 (CC_AT 0x1d8)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (CC_AT 0x1c0)) fc None mm (seg_rom rsegs)).
Proof. intros until b. cc_ck_proof x18 p 17 n. Qed.

(* ---- the segments ---- *)

(* +0x000 -> rp_copy_untag *)
Lemma cc_seg_entry_ok : cc_seg_entry_F.
Proof.
  unfold cc_seg_entry_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c f n lo
    ST LO GCK CK HLOW RFR RGC RCK.
  cc_lits.
  unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  destruct (cc_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & FR'). clear FR.
  rename FR' into FR.
  do 11 step.
  (* the stores moved the two cell facts to the new memory (StepF's store transport) *)
  unfold ASAN_K in CK.
  pose proof (cc_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (cc_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 5 step.
  cc_memF ltac:(fun mm => apply evtF_done; exists mm, v0).
  replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; cc_regs; try cc_w.
Qed.

(* +0x040 -> malloc: s0 := a0; `seqz` / `add` a0 := n + (n == 0) *)
Lemma cc_seg_m_ok : cc_seg_m_F.
Proof.
  unfold cc_seg_m_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n HN.
  cc_lits.
  do 4 step.
  apply evtF_done. f_equal; cc_regs; try cc_w.
  all: f_equal; unfold v_sltiu; rewrite (unsigned_lit n) by lia;
       replace (bv_wrap 64 1) with 1 by reflexivity;
       destruct (Z.ltb_spec n 1); rewrite unsigned_lit by lia; lia.
Qed.

(* +0x050, u > 0, n = 0, got = 0 -> free(u) *)
Lemma cc_seg_z_ok : cc_seg_z_F.
Proof.
  unfold cc_seg_z_F.
  intros RNG ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P HP.
  cc_lits.
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  step. if_false.
  step. step. if_true.
  step. if_false.
  step. if_true.
  do 2 step.
  cc_finF.
Qed.

(* +0x050, u > 0, n > 0 -> __asan_memcpy(u, f, n) *)
Lemma cc_seg_cp1_ok : cc_seg_cp1_F.
Proof.
  unfold cc_seg_cp1_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n HP HN.
  cc_lits.
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  step. if_false.
  step. step. if_false.
  do 4 step.
  cc_finF.
Qed.

(* +0x06c, n < 18, got = 0 -> free(u) *)
Lemma cc_seg_short_ok : cc_seg_short_F.
Proof.
  unfold cc_seg_short_F.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n HP HN.
  cc_lits.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  step. step. if_true.
  step. if_false.
  step. if_true.
  do 2 step.
  cc_finF.
Qed.

(* +0x06c, n >= 18, the four tag bytes match -> __asan_memcpy(u + 12, f + 16, n - 16) *)
Lemma cc_seg_tag_yes_ok : cc_seg_tag_yes_F.
Proof.
  unfold cc_seg_tag_yes_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P f n
    HP HPN HN ADR RF RS M12 M13 M16 M17.
  pose proof ADR as ADR'. destruct ADR' as (Hf0 & _ & HfE & _). unfold APPMEM_END in HfE.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  pose proof cc_ck_t12 as K12. pose proof cc_ck_t13 as K13. pose proof cc_ck_t16 as K16. pose proof cc_ck_t17 as K17.
  cc_lits.
  step. step. if_false.
  eapply K12; [exact UF | exact ADR | lia | exact RF | exact RS | exact M12 | lia |]. intros y11 y12.
  step. step. step. if_false.
  eapply K13; [exact UF | exact ADR | lia | exact RF | exact RS | exact M13 | lia |]. intros y11' y12'.
  step. step. if_false.
  eapply K16; [exact UF | exact ADR | lia | exact RF | exact RS | exact M16 | lia |]. intros y11'' Hy y12''.
  apply cc_word_of in Hy. subst y11''.
  step. step. step. if_false.
  eapply K17; [exact UF | exact ADR | lia | exact RF | exact RS | exact M17 | lia |]. intros y12''' y13.
  step. step. step. if_false.
  do 3 step.
  apply evtF_done. eexists. f_equal; cc_regs; try cc_w.
Qed.

(* +0x06c, n >= 18, not all four tag bytes match -> +0x110 with a2 = n *)
Ltac cc_fin_no := apply evtF_done; do 3 eexists; f_equal; cc_regs; try cc_w.

Lemma cc_seg_tag_no_ok : cc_seg_tag_no_F.
Proof.
  unfold cc_seg_tag_no_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P f n
    b12 b13 b16 b17 HP HPN HN ADR RF RS B12 B13 B16 B17 M12 M13 M16 M17 NOT.
  pose proof ADR as ADR'. destruct ADR' as (Hf0 & _ & HfE & _). unfold APPMEM_END in HfE.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U12 : bv_unsigned (Z_to_bv 64 b12) = b12) by (apply unsigned_lit; lia).
  assert (U13 : bv_unsigned (Z_to_bv 64 b13) = b13) by (apply unsigned_lit; lia).
  assert (U16 : bv_unsigned (Z_to_bv 64 b16) = b16) by (apply unsigned_lit; lia).
  assert (U17 : bv_unsigned (Z_to_bv 64 b17) = b17) by (apply unsigned_lit; lia).
  pose proof cc_ck_t12 as K12. pose proof cc_ck_t13 as K13. pose proof cc_ck_t16 as K16. pose proof cc_ck_t17 as K17.
  cc_lits.
  step. step. if_false.
  eapply K12; [exact UF | exact ADR | lia | exact RF | exact RS | exact M12 | lia |]. intros y11 y12.
  step. step. step.
  destruct (Z.eq_dec b12 0x81) as [E12|E12]; [|if_true; cc_fin_no].
  if_false.
  eapply K13; [exact UF | exact ADR | lia | exact RF | exact RS | exact M13 | lia |]. intros y11' y12'.
  step. step.
  destruct (Z.eq_dec b13 0) as [E13|E13]; [|if_true; cc_fin_no].
  if_false.
  eapply K16; [exact UF | exact ADR | lia | exact RF | exact RS | exact M16 | lia |]. intros y11'' Hy y12''.
  step. step. step.
  destruct (Z.eq_dec b16 0x88) as [E16|E16]; [|if_true; cc_fin_no].
  if_false.
  eapply K17; [exact UF | exact ADR | lia | exact RF | exact RS | exact M17 | lia |]. intros y12''' y13.
  step. step. step.
  destruct (Z.eq_dec b17 0x19) as [E17|E17]; [exfalso; apply NOT; repeat split; assumption|].
  if_true. cc_fin_no.
Qed.

(* +0x10c -> +0x110: a2 := n - 4 *)
Lemma cc_seg_cp2ret_ok : cc_seg_cp2ret_F.
Proof.
  unfold cc_seg_cp2ret_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n HN.
  cc_lits.
  step.
  cc_finF.
Qed.

(* +0x110, n < 50, got = 0 -> free(u) *)
Lemma cc_seg_want_lo_ok : cc_seg_want_lo_F.
Proof.
  unfold cc_seg_want_lo_F.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n HP HN.
  cc_lits.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  step. step. if_true.
  step. if_false.
  step. if_true.
  do 2 step.
  cc_finF.
Qed.

(* +0x18c, a0 = 0 -> free(u) *)
Lemma cc_seg_bcmpret_ok : cc_seg_bcmpret_F.
Proof.
  unfold cc_seg_bcmpret_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  cc_lits.
  step. if_false.
  do 2 step.
  cc_finF.
Qed.

(* +0x198 -> the return *)
Lemma cc_seg_end_ok : cc_seg_end_F.
Proof.
  unfold cc_seg_end_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 c5 c4 c3 c2 c1 c0 cra FR HSP RFR.
  cc_lits.
  unfold cc_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 10 step.
  apply evtF_done. f_equal.
Qed.

(* The mask of +0x1d8 .. +0x1e0 (`snez a0, a0`, `addi a0, a0, -1`, `and a0, a0, a2`): L when u[17] = 0, else 0. *)
Lemma cc_mask0 : forall L, 0 <= L < 2 ^ 63 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) + -1)))
                     (bv_unsigned (Z_to_bv 64 L))) = Z_to_bv 64 L.
Proof.
  intros L HL.
  replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) + -1))) with (Z.ones 64)
    by (vm_compute; reflexivity).
  rewrite (unsigned_lit L) by lia. rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma cc_mask1 : forall u L, 0 <= u < 256 -> u <> 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 u)) + -1)))
                     (bv_unsigned (Z_to_bv 64 L))) = Z_to_bv 64 0.
Proof.
  intros u L Hu Hn. rewrite v_sltu_b2z, (unsigned_lit 0), (unsigned_lit u) by lia.
  rewrite (proj2 (Z.ltb_lt 0 u)) by lia. cbn [Z.b2z].
  replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) + -1))) with 0 by (vm_compute; reflexivity).
  rewrite Z.land_0_l. reflexivity.
Qed.

(* The ends of the want test: free(u) with got = 0, or bcmp(c, u, got) with got > 0 (whose post leaves a1', a2'
   unused). *)
Ltac cc_fin_free := apply evtF_done; do 3 eexists; left; split; [reflexivity | f_equal; cc_regs; cc_w].
Ltac cc_fin_bcmp := apply evtF_done; exists (Z_to_bv 64 0), (Z_to_bv 64 0); eexists; right;
  split; [lia | f_equal; cc_regs; cc_w].
(* From +0x174 with s0 = 0: `bnez s0` not taken, `beqz s0` taken, a0 := u, call free. *)
Ltac cc_free_dac := step; if_false; step; if_true; do 2 step; cc_fin_free.

(* +0x110, n >= 50: the want test on u[12], u[13], u[16], u[17]; `beq s0, a0` taken; free(u) or bcmp(c, u, got) *)
Lemma cc_seg_want_hi_ok : cc_seg_want_hi_F.
Proof.
  unfold cc_seg_want_hi_F.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n L
    u12 u13 u16 u17 HP HN HL ADR RP RS B12 B13 B16 B17 M12 M13 M16 M17.
  pose proof ADR as ADR'. destruct ADR' as (HP0 & _ & HPE & _). unfold APPMEM_END in HPE.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (U12 : bv_unsigned (Z_to_bv 64 u12) = u12) by (apply unsigned_lit; lia).
  assert (U13 : bv_unsigned (Z_to_bv 64 u13) = u13) by (apply unsigned_lit; lia).
  assert (U16 : bv_unsigned (Z_to_bv 64 u16) = u16) by (apply unsigned_lit; lia).
  pose proof cc_ck_w12 as K12. pose proof cc_ck_w13 as K13. pose proof cc_ck_w16 as K16. pose proof cc_ck_w17 as K17.
  cc_lits.
  (* `li a0, 50`; `bltu s3, a0` not taken *)
  step. step. if_false.
  (* u[12]: `li a1, 0x88`; `bne a0, a1` *)
  eapply K12; [exact UP | exact ADR | lia | exact RP | exact RS | exact M12 | lia |]. intros y11 y13.
  step. step.
  destruct (Z.eq_dec u12 0x88) as [E12|E12].
  2: { assert (W0 : cc_want u12 u13 u16 u17 L = 0)
         by (unfold cc_want; rewrite (proj2 (Z.eqb_neq u12 0x88) E12); reflexivity).
       rewrite W0. if_true. cc_free_dac. }
  subst u12. if_false.
  (* u[13]: `li a1, 0x19`; `bne a0, a1` *)
  eapply K13; [exact UP | exact ADR | lia | exact RP | exact RS | exact M13 | lia |]. intros y11' y13'.
  step. step.
  destruct (Z.eq_dec u13 0x19) as [E13|E13].
  2: { assert (W0 : cc_want 0x88 u13 u16 u17 L = 0)
         by (unfold cc_want; rewrite (proj2 (Z.eqb_neq u13 0x19) E13); reflexivity).
       rewrite W0. if_true. cc_free_dac. }
  subst u13. if_false.
  (* u[16]: `beqz a0` *)
  eapply K16; [exact UP | exact ADR | lia | exact RP | exact RS | exact M16 | lia |]. intros y11'' y13''.
  step.
  destruct (Z.eq_dec u16 0) as [E16|E16].
  2: { assert (W0 : cc_want 0x88 0x19 u16 u17 L = 0)
         by (unfold cc_want; rewrite (proj2 (Z.eqb_neq u16 0) E16); reflexivity).
       rewrite W0. if_false. cc_free_dac. }
  subst u16. if_true.
  (* u[17]: the mask, `beq s0, a0` taken to +0x178, `beqz s0` *)
  eapply K17; [exact UP | exact ADR | lia | exact RP | exact RS | exact M17 | lia |]. intros y11''' y13'''.
  do 3 step.
  destruct (Z.eq_dec u17 0) as [E17|E17].
  - subst u17. rewrite (cc_mask0 L HL). change (cc_want 0x88 0x19 0 0 L) with L.
    step. if_true.
    destruct (Z.eq_dec L 0) as [EL|EL].
    + subst L. step. if_true. do 2 step. cc_fin_free.
    + step. if_false. do 4 step. cc_fin_bcmp.
  - assert (W0 : cc_want 0x88 0x19 0 u17 L = 0)
      by (unfold cc_want; rewrite (proj2 (Z.eqb_neq u17 0) E17); reflexivity).
    rewrite W0, (cc_mask1 u17 L B17 E17).
    step. if_true. step. if_true. do 2 step. cc_fin_free.
Qed.
