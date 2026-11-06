(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 601 of its 666 lines of code are new or changed and 399 lines of the source are left out. *)
(* check_copy_cgW_segs: proofs of the twelve footprint-run statements of lib/B/Prog/check_copy_cgW_iface.v, the
   straight-line segments of check_copy in image B (fuzz_wire.asan-ubsan 0x80abc), each stepped by lib/Lib/StepF.v
   from its cut point to the next call (or to CC_WANT):
     cc_seg_entry_ok     entry -> rp_copy_untag: the 0x40-byte frame, s3 := n, s4 := f, s5 := the shadow base
                         through GOT_CELL_K -> CELL_K, s1 := c, a1 := n;
     cc_seg_m_ok         CC_RET_RCU -> malloc: s0 := a0, a0 := n + (n == 0) (`seqz`, `add`);
     cc_seg_z_ok         CC_RET_MALLOC, n = 0 -> free: `beqz a0` not taken, `beqz s3` taken, the join at +0x1bc;
     cc_seg_cp1_ok       CC_RET_MALLOC, n > 0 -> __asan_memcpy(u, f, n);
     cc_seg_short_ok     CC_RET_CP1, n < 18 -> free: `bltu s3, 18` taken, the join at +0x1bc;
     cc_seg_tag_yes_ok   CC_RET_CP1, the four bytes of f match -> __asan_memcpy(u + 12, f + 16, n - 16);
     cc_seg_tag_no_ok    CC_RET_CP1, one byte of f differs -> CC_WANT with a2 = n;
     cc_seg_cp2ret_ok    CC_RET_CP2 -> CC_WANT: a2 := n - 4;
     cc_seg_want_lo_ok   CC_WANT, n < 50 -> free: `bltu s3, 50` taken, the join at +0x1bc;
     cc_seg_want_hi_ok   CC_WANT, n >= 50: the want test on u's bytes 12, 13, 16, 17, then free(u) (want 0) or
                         bcmp(c, u, want);
     cc_seg_bcmpret_ok   CC_RET_BCMP, a0 = 0 -> free: `bnez a0` not taken, a0 := u;
     cc_seg_end_ok       CC_RET_FREE -> the return: a0 := s0, the frame reloaded, sp += 0x40, `ret`.
   Each instrumented 1-byte load (of f + 12, 13, 16, 17 and u + 12, 13, 16, 17) is one check-site lemma below
   (ccsg_ckt12 .. ccsg_ckw17): the code loads the shadow byte k at (a >> 3) + 0x7fff8000 and continues to the load
   when k = 0 or (a mod 8) < k; the range is addressable, so the error path is not reached. Before each such load the
   code compares the base with -K (a wrap check that branches to `unimp` at +0x240); f and u lie in application memory
   (addressable: base + n <= 2 ^ 47), so the branch is not taken. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr
  check_copy_cgW_iface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- helpers (UciCvBSegs.v cv_le_bytes_to_Z .. cv_rd_all) ---- *)

Lemma ccsg_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
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

Lemma ccsg_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply ccsg_le_bytes_to_Z.
Qed.

Fixpoint ccsg_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: ccsg_c8s n' (skipn 8 bs)
  end.

Lemma ccsg_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (ccsg_c8s n bs) /\ cells_bytes (ccsg_c8s n bs) = bs /\ cells_size (ccsg_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [ccsg_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite ccsg_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma ccsg_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (ccsg_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (ccsg_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 64 bytes, read as 8 words. *)
Lemma ccsg_frame_words : forall m A bs, rw_cells rsegs m A [CB 64 bs] ->
  exists v0 v8 v16 v24 v32 v40 v48 v56 : word,
    rw_cells rsegs m A [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56].
Proof.
  intros m A bs H. apply (ccsg_rw_c8s rsegs m A 8 bs) in H. cbn [ccsg_c8s] in H. do 8 eexists. exact H.
Qed.

Lemma ccsg_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* ---- facts of the addressable ranges f and u (UciCvBEv1.v u8lit, zxb_lit, cv_sh1F, sh_at, rn_lt) ---- *)

Lemma ccsg_u8lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma ccsg_zxb_lit : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zxb. rewrite ccsg_u8lit by exact Hc. reflexivity. Qed.

(* An addressable range lies in application memory, below 2 ^ 47. *)
Lemma ccsg_adr_bound : forall m X n, addressable m X n -> 0 <= X /\ X + n <= 2 ^ 47.
Proof. intros m X n (H0 & _ & H & _). unfold APPMEM_END in H. lia. Qed.

(* The shadow byte of X + i, for i in [0, n), allows the 1-byte load (addressable). *)
Lemma ccsg_sh : forall m X n i, addressable m X n -> 0 <= i < n -> exists k : byte,
  mrd rsegs m (wa ((X + i) / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ (X + i) mod 8 < bv_signed k).
Proof.
  intros m X n i ADR Hi. destruct ADR as (_ & _ & _ & HA). destruct (HA i Hi) as (_ & k & Hk & Hok).
  exists k. split; [exact Hk|]. destruct Hok as [E|[E _]]; [left; exact E | right; exact E].
Qed.

(* [a, c] inside the 8-aligned cover of [a, c]. *)
Lemma ccsg_align8_cover : forall a b c, a <= b -> b <= c -> a / 8 * 8 <= b /\ b + 1 <= c / 8 * 8 + 8.
Proof. intros a b c H1 H2. split; Z.div_mod_to_equations; lia. Qed.

(* The shadow byte of X + i, for i in [0, n), lies in the 8-aligned cover of the shadow bytes of [X, X + n). *)
Lemma ccsg_sh1F : forall RNG X n i,
  ExecF.rng RNG (cc_hull_lo X) (cc_hull_len X n) -> 0 <= i < n -> ExecF.rng RNG ((X + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG X n i H Hi. unfold cc_hull_lo, cc_hull_len, shadow_addr in H.
  assert (L1 : X / 8 <= (X + i) / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : (X + i) / 8 <= (X + n - 1) / 8) by (apply Z.div_le_mono; lia).
  destruct (ccsg_align8_cover (X / 8 + ASAN_K) ((X + i) / 8 + ASAN_K) ((X + n - 1) / 8 + ASAN_K)
             ltac:(lia) ltac:(lia)) as (A1 & A2).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

Lemma ccsg_rng1 : forall RNG X n i, ExecF.rng RNG X n -> 0 <= i < n -> ExecF.rng RNG (X + i) 1.
Proof. intros RNG X n i H Hi. apply (ExecF.rng_sub RNG X n); [exact H | lia | lia]. Qed.

(* `snez a0, a0`, `addi a0, a0, -1`, `and a0, a0, a2` on a0 = u, a2 = L: L when u = 0, else 0. *)
Lemma ccsg_sel : forall u L, 0 <= u < 256 -> 0 <= L < 2 ^ 63 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 u)) + -1)))
                     (bv_unsigned (Z_to_bv 64 L))) = Z_to_bv 64 (if u =? 0 then L else 0).
Proof.
  intros u L Hu HL. f_equal. rewrite v_sltu_b2z. rewrite (unsigned_lit u), (unsigned_lit L) by lia.
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity.
  destruct (Z.eqb_spec u 0) as [E|E].
  - subst u. change (if true then L else 0) with L.
    replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.b2z (0 <? 0))) + -1))) with (Z.ones 64)
      by (vm_compute; reflexivity).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - change (if false then L else 0) with 0. rewrite (proj2 (Z.ltb_lt 0 u)) by lia.
    replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.b2z true)) + -1))) with 0
      by (vm_compute; reflexivity).
    apply Z.land_0_l.
Qed.

(* ---- tactics (UciCvBSegs.v cv_regs .. cv_memF, UciCvBEv1.v wsub, solve_c, takeF) ---- *)

Local Ltac ccsg_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Local Ltac ccsg_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Local Ltac ccsg_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Local Ltac ccsg_w := ccsg_shift; ccsg_usub; ccsg_shift; ccsg_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Local Ltac ccsg_finF := apply evtF_done; f_equal; ccsg_regs; ccsg_w.
Local Ltac ccsg_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Local Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Local Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?zb_signed; zsimp; wsub; zsimp;
  do 3 (decide_tests; cbv beta iota); reflexivity.
Local Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* StepF's step reads the start pc: every pc of the statements is a check_copy_cgW_iface.v name, so each step first
   computes every such closed name of the goal and of the hypotheses to its value (vm_compute of a closed address). *)
Local Ltac ccsg_lit X := let v := eval vm_compute in X in change X with v.
Local Ltac ccsg_lits :=
  repeat match goal with
  | |- context [CC_RET_RCU] => ccsg_lit CC_RET_RCU
  | |- context [CC_RET_MALLOC] => ccsg_lit CC_RET_MALLOC
  | |- context [CC_RET_CP1] => ccsg_lit CC_RET_CP1
  | |- context [CC_RET_CP2] => ccsg_lit CC_RET_CP2
  | |- context [CC_WANT] => ccsg_lit CC_WANT
  | |- context [CC_RET_BCMP] => ccsg_lit CC_RET_BCMP
  | |- context [CC_RET_FREE] => ccsg_lit CC_RET_FREE
  | |- context [CC_RCU] => ccsg_lit CC_RCU
  | |- context [CC_MALLOC] => ccsg_lit CC_MALLOC
  | |- context [CC_FREE] => ccsg_lit CC_FREE
  | |- context [CC_MEMCPY] => ccsg_lit CC_MEMCPY
  | |- context [CC_BCMP] => ccsg_lit CC_BCMP
  | |- context [CC_AT ?o] => ccsg_lit (CC_AT o)
  | |- context [CC_ENTRY] => ccsg_lit CC_ENTRY
  | H : context [CC_AT ?o] |- _ => let v := eval vm_compute in (CC_AT o) in change (CC_AT o) with v in H
  end.
Local Ltac step ::= ccsg_lits; stepF_k ltac:(idtac).
(* the pc of the goal, a closed address, named back as CC_AT o (checked by conversion), to meet a check-site lemma *)
Local Ltac ccsg_at o := lazymatch goal with
  | |- ExecF.evtF ?s ?R ?Q (MS ?r ?F (Z_to_bv 64 _) ?fc ?rv ?m ?ro) =>
      change (ExecF.evtF s R Q (MS r F (Z_to_bv 64 (CC_AT o)) fc rv m ro))
  end.
(* the join at +0x1bc with s0 = 0: `bnez s0` not taken, `beqz s0` taken to +0x1d8, a0 := s2, call free *)
Local Ltac ccsg_join0 := step; takeF false; step; takeF true; step; step.

(* =========================================================================
   The eight check sites: each takes the shadow byte of the address and its verdict, the byte at the address and
   the two 1-byte ranges, and runs to the instruction after the load.
   ========================================================================= *)

(* +0x074 .. +0x090: li a0, -12 and `bgeu s4, a0` (the wrap check of f + 12); a0 := s4 + 12; a1 := the shadow byte of a0
   (`srli`, `add s5`, `lb`); `bnez a1` to +0x244 (`andi a2, a0, 7`, `blt a2, a1` back to +0x090); `lbu a0` of s4 + 12 *)
Lemma ccsg_ckt12 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (X : Z),
  bv_unsigned x20 = X -> 0 <= X -> X + 18 < 2 ^ 64 ->
  mrd rsegs mm (wa ((X + 12) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (X + 12) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa (X + 12)) = Some b ->
  ExecF.rng RNG ((X + 12) / 8 + ASAN_K) 1 -> ExecF.rng RNG (X + 12) 1 ->
  (forall y11 y12 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                F (Z_to_bv 64 (CC_AT 0x94)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                             F (Z_to_bv 64 (CC_AT 0x74)) fc None mm (seg_rom rsegs)).
Proof.
  intros until X. intros EB HX0 HX M SK MD RK RD CONT.
  pose proof (u64_range x20) as RB. unfold ASAN_K in *.
  step. step. takeF false.
  step. gen_addi x20 w U. rewrite EB in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound (X + 12) 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low ((X + 12) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0x0a0 .. +0x0bc: li a0, -14 and `bltu a0, s4` (the wrap check of f + 13); a0 := s4 + 13; a1 := its shadow byte; `bnez a1`
   to +0x250 (`andi a2, a0, 7`, `blt a2, a1` back to +0x0bc); `lbu a0` of s4 + 13 *)
Lemma ccsg_ckt13 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (X : Z),
  bv_unsigned x20 = X -> 0 <= X -> X + 18 < 2 ^ 64 ->
  mrd rsegs mm (wa ((X + 13) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (X + 13) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa (X + 13)) = Some b ->
  ExecF.rng RNG ((X + 13) / 8 + ASAN_K) 1 -> ExecF.rng RNG (X + 13) 1 ->
  (forall y11 y12 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                F (Z_to_bv 64 (CC_AT 0xc0)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                             F (Z_to_bv 64 (CC_AT 0xa0)) fc None mm (seg_rom rsegs)).
Proof.
  intros until X. intros EB HX0 HX M SK MD RK RD CONT.
  pose proof (u64_range x20) as RB. unfold ASAN_K in *.
  step. step. takeF false.
  step. gen_addi x20 w U. rewrite EB in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound (X + 13) 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low ((X + 13) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0x0c8 .. +0x0e4: li a0, -16 and `bgeu s4, a0` (the wrap check of f + 16); a1 := s4 + 16; a0 := its shadow byte; `bnez a0`
   to +0x274 (`andi a2, a1, 7`, `blt a2, a0` back to +0x0e4); `lbu a0` of a1 = s4 + 16 *)
Lemma ccsg_ckt16 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (X : Z),
  bv_unsigned x20 = X -> 0 <= X -> X + 18 < 2 ^ 64 ->
  mrd rsegs mm (wa ((X + 16) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (X + 16) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa (X + 16)) = Some b ->
  ExecF.rng RNG ((X + 16) / 8 + ASAN_K) 1 -> ExecF.rng RNG (X + 16) 1 ->
  (forall y11 y12 : word, bv_unsigned y11 = X + 16 ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                F (Z_to_bv 64 (CC_AT 0xe8)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                             F (Z_to_bv 64 (CC_AT 0xc8)) fc None mm (seg_rom rsegs)).
Proof.
  intros until X. intros EB HX0 HX M SK MD RK RD CONT.
  pose proof (u64_range x20) as RB. unfold ASAN_K in *.
  step. step. takeF false.
  step. gen_addi x20 w U. rewrite EB in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound (X + 16) 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT; exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low ((X + 16) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT; exact U.
Qed.

(* +0x0f4 .. +0x110: li a0, -18 and `bltu a0, s4` (the wrap check of f + 17); a0 := s4 + 17; a2 := its shadow byte; `bnez a2`
   to +0x290 (`andi a3, a0, 7`, `blt a3, a2` back to +0x110); `lbu a0` of s4 + 17 *)
Lemma ccsg_ckt17 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (X : Z),
  bv_unsigned x20 = X -> 0 <= X -> X + 18 < 2 ^ 64 ->
  mrd rsegs mm (wa ((X + 17) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (X + 17) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa (X + 17)) = Some b ->
  ExecF.rng RNG ((X + 17) / 8 + ASAN_K) 1 -> ExecF.rng RNG (X + 17) 1 ->
  (forall y12 y13 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) x11 y12 y13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                F (Z_to_bv 64 (CC_AT 0x114)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                             F (Z_to_bv 64 (CC_AT 0xf4)) fc None mm (seg_rom rsegs)).
Proof.
  intros until X. intros EB HX0 HX M SK MD RK RD CONT.
  pose proof (u64_range x20) as RB. unfold ASAN_K in *.
  step. step. takeF false.
  step. gen_addi x20 w U. rewrite EB in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound (X + 17) 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low ((X + 17) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0x148 .. +0x164: li a0, -12 and `bgeu s2, a0` (the wrap check of u + 12); a0 := s2 + 12; a1 := its shadow byte; `bnez a1`
   to +0x25c (`andi a3, a0, 7`, `blt a3, a1` back to +0x164); `lbu a0` of s2 + 12 *)
Lemma ccsg_ckw12 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (X : Z),
  bv_unsigned x18 = X -> 0 <= X -> X + 18 < 2 ^ 64 ->
  mrd rsegs mm (wa ((X + 12) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (X + 12) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa (X + 12)) = Some b ->
  ExecF.rng RNG ((X + 12) / 8 + ASAN_K) 1 -> ExecF.rng RNG (X + 12) 1 ->
  (forall y11 y13 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 y13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                F (Z_to_bv 64 (CC_AT 0x168)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                             F (Z_to_bv 64 (CC_AT 0x148)) fc None mm (seg_rom rsegs)).
Proof.
  intros until X. intros EB HX0 HX M SK MD RK RD CONT.
  pose proof (u64_range x18) as RB. unfold ASAN_K in *.
  step. step. takeF false.
  step. gen_addi x18 w U. rewrite EB in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound (X + 12) 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low ((X + 12) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0x170 .. +0x18c: li a0, -14 and `bltu a0, s2` (the wrap check of u + 13); a0 := s2 + 13; a1 := its shadow byte; `bnez a1`
   to +0x268 (`andi a3, a0, 7`, `blt a3, a1` back to +0x18c); `lbu a0` of s2 + 13 *)
Lemma ccsg_ckw13 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (X : Z),
  bv_unsigned x18 = X -> 0 <= X -> X + 18 < 2 ^ 64 ->
  mrd rsegs mm (wa ((X + 13) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (X + 13) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa (X + 13)) = Some b ->
  ExecF.rng RNG ((X + 13) / 8 + ASAN_K) 1 -> ExecF.rng RNG (X + 13) 1 ->
  (forall y11 y13 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 y13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                F (Z_to_bv 64 (CC_AT 0x190)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                             F (Z_to_bv 64 (CC_AT 0x170)) fc None mm (seg_rom rsegs)).
Proof.
  intros until X. intros EB HX0 HX M SK MD RK RD CONT.
  pose proof (u64_range x18) as RB. unfold ASAN_K in *.
  step. step. takeF false.
  step. gen_addi x18 w U. rewrite EB in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound (X + 13) 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low ((X + 13) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0x198 .. +0x1b4: li a0, -16 and `bgeu s2, a0` (the wrap check of u + 16); a0 := s2 + 16; a1 := its shadow byte; `bnez a1`
   to +0x284 (`andi a3, a0, 7`, `blt a3, a1` back to +0x1b4); `lbu a0` of s2 + 16 *)
Lemma ccsg_ckw16 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (X : Z),
  bv_unsigned x18 = X -> 0 <= X -> X + 18 < 2 ^ 64 ->
  mrd rsegs mm (wa ((X + 16) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (X + 16) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa (X + 16)) = Some b ->
  ExecF.rng RNG ((X + 16) / 8 + ASAN_K) 1 -> ExecF.rng RNG (X + 16) 1 ->
  (forall y11 y13 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 y13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                F (Z_to_bv 64 (CC_AT 0x1b8)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                             F (Z_to_bv 64 (CC_AT 0x198)) fc None mm (seg_rom rsegs)).
Proof.
  intros until X. intros EB HX0 HX M SK MD RK RD CONT.
  pose proof (u64_range x18) as RB. unfold ASAN_K in *.
  step. step. takeF false.
  step. gen_addi x18 w U. rewrite EB in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound (X + 16) 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low ((X + 16) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* +0x208 .. +0x224: li a0, -18 and `bltu a0, s2` (the wrap check of u + 17); a0 := s2 + 17; a1 := its shadow byte; `bnez a1`
   to +0x29c (`andi a3, a0, 7`, `blt a3, a1` back to +0x224); `lbu a0` of s2 + 17 *)
Lemma ccsg_ckw17 : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (X : Z),
  bv_unsigned x18 = X -> 0 <= X -> X + 18 < 2 ^ 64 ->
  mrd rsegs mm (wa ((X + 17) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (X + 17) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa (X + 17)) = Some b ->
  ExecF.rng RNG ((X + 17) / 8 + ASAN_K) 1 -> ExecF.rng RNG (X + 17) 1 ->
  (forall y11 y13 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 y13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                F (Z_to_bv 64 (CC_AT 0x228)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ASAN_K) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                             F (Z_to_bv 64 (CC_AT 0x208)) fc None mm (seg_rom rsegs)).
Proof.
  intros until X. intros EB HX0 HX M SK MD RK RD CONT.
  pose proof (u64_range x18) as RB. unfold ASAN_K in *.
  step. step. takeF false.
  step. gen_addi x18 w U. rewrite EB in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as Rk. step. clear Rk.
  step.
  pose proof (Z.mod_pos_bound (X + 17) 8 ltac:(lia)) as MB.
  pose proof (rdw0 mm w _ _ MD U) as R2.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    step. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low ((X + 17) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* =========================================================================
   The twelve segments.
   ========================================================================= *)

Lemma cc_seg_entry_ok : cc_seg_entry_F.
Proof.
  unfold cc_seg_entry_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c f n lo
    ST LO GCK CK HLOW RFR RGC RCK.
  ccsg_lits.
  unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  destruct (ccsg_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & FR'). clear FR.
  rename FR' into FR.
  do 11 step.
  unfold ASAN_K in CK.
  pose proof (ccsg_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (ccsg_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 5 step.
  ccsg_memF ltac:(fun mm => apply evtF_done; exists mm, v0).
  replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; ccsg_regs; try ccsg_w.
Qed.

Lemma cc_seg_m_ok : cc_seg_m_F.
Proof.
  unfold cc_seg_m_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n HN.
  ccsg_lits.
  do 4 step.
  apply evtF_done. f_equal; ccsg_regs; try ccsg_w.
  (* a0 = n + (n <u 1), the `seqz` / `add` pair *)
  all: f_equal; unfold v_sltiu; rewrite (unsigned_lit n) by lia;
       replace (bv_wrap 64 1) with 1 by reflexivity;
       destruct (Z.ltb_spec n 1); rewrite unsigned_lit by lia; lia.
Qed.

Lemma cc_seg_z_ok : cc_seg_z_F.
Proof.
  unfold cc_seg_z_F.
  intros RNG ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P HP.
  ccsg_lits.
  step. takeF false.
  step. step. takeF true.
  ccsg_join0.
  ccsg_finF.
Qed.

Lemma cc_seg_cp1_ok : cc_seg_cp1_F.
Proof.
  unfold cc_seg_cp1_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n HP HN.
  ccsg_lits.
  step. takeF false.
  step. step. takeF false.
  do 4 step.
  ccsg_finF.
Qed.

Lemma cc_seg_short_ok : cc_seg_short_F.
Proof.
  unfold cc_seg_short_F.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n HP HN.
  ccsg_lits.
  step. step. takeF true.
  ccsg_join0.
  ccsg_finF.
Qed.

Lemma cc_seg_tag_yes_ok : cc_seg_tag_yes_F.
Proof.
  unfold cc_seg_tag_yes_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P f n
    HP HPN HN ADR RF RH M12 M13 M16 M17.
  destruct (ccsg_adr_bound m f n ADR) as [Hf0 Hfn].
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  ccsg_lits.
  (* `bltu s3, 18` not taken *)
  step. step. takeF false.
  (* f[12] = 0x81 *)
  destruct (ccsg_sh m f n 12 ADR ltac:(lia)) as (k & M & SK).
  ccsg_at 0x74.
  eapply (ccsg_ckt12 RNG) with (X := f) (k := k) (b := Z_to_bv 8 0x81);
    [exact UF | lia | lia | exact M | exact SK | exact M12 | apply (ccsg_sh1F RNG f n); [exact RH | lia]
    | apply (ccsg_rng1 RNG f n); [exact RF | lia] | ].
  intros y11 y12. rewrite (ccsg_zxb_lit 0x81) by lia.
  step. step. step. takeF false.
  (* f[13] = 0 *)
  destruct (ccsg_sh m f n 13 ADR ltac:(lia)) as (k1 & M1 & SK1).
  ccsg_at 0xa0.
  eapply (ccsg_ckt13 RNG) with (X := f) (k := k1) (b := Z_to_bv 8 0);
    [exact UF | lia | lia | exact M1 | exact SK1 | exact M13 | apply (ccsg_sh1F RNG f n); [exact RH | lia]
    | apply (ccsg_rng1 RNG f n); [exact RF | lia] | ].
  intros z11 z12. rewrite (ccsg_zxb_lit 0) by lia.
  step. step. takeF false.
  (* f[16] = 0x88 *)
  destruct (ccsg_sh m f n 16 ADR ltac:(lia)) as (k2 & M2 & SK2).
  ccsg_at 0xc8.
  eapply (ccsg_ckt16 RNG) with (X := f) (k := k2) (b := Z_to_bv 8 0x88);
    [exact UF | lia | lia | exact M2 | exact SK2 | exact M16 | apply (ccsg_sh1F RNG f n); [exact RH | lia]
    | apply (ccsg_rng1 RNG f n); [exact RF | lia] | ].
  intros w11 w12 Hy. rewrite (ccsg_zxb_lit 0x88) by lia.
  assert (EY : w11 = Z_to_bv 64 (f + 16)) by (apply bv_eq; rewrite Hy, unsigned_lit by lia; reflexivity).
  subst w11.
  step. step. step. takeF false.
  (* f[17] = 0x19 *)
  destruct (ccsg_sh m f n 17 ADR ltac:(lia)) as (k3 & M3 & SK3).
  ccsg_at 0xf4.
  eapply (ccsg_ckt17 RNG) with (X := f) (k := k3) (b := Z_to_bv 8 0x19);
    [exact UF | lia | lia | exact M3 | exact SK3 | exact M17 | apply (ccsg_sh1F RNG f n); [exact RH | lia]
    | apply (ccsg_rng1 RNG f n); [exact RF | lia] | ].
  intros v12 v13. rewrite (ccsg_zxb_lit 0x19) by lia.
  step. step. step. takeF false.
  (* the wrap checks of f + 16 and u + 12 not taken; a0 := u + 12, a2 := n - 16, call __asan_memcpy *)
  step. step. takeF false.
  step. step. takeF false.
  do 3 step.
  apply evtF_done. eexists. f_equal; ccsg_regs; ccsg_w.
Qed.

(* the end of a mismatch of the tag test: CC_WANT with a2 = n *)
Local Ltac ccsg_tagno_fin := apply evtF_done; do 3 eexists; f_equal; ccsg_regs; ccsg_w.

Lemma cc_seg_tag_no_ok : cc_seg_tag_no_F.
Proof.
  unfold cc_seg_tag_no_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P f n
    b12 b13 b16 b17 HP HPN HN ADR RF RH R12 R13 R16 R17 M12 M13 M16 M17 NOT.
  destruct (ccsg_adr_bound m f n ADR) as [Hf0 Hfn].
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  ccsg_lits.
  step. step. takeF false.
  (* f[12] *)
  destruct (ccsg_sh m f n 12 ADR ltac:(lia)) as (k & M & SK).
  ccsg_at 0x74.
  eapply (ccsg_ckt12 RNG) with (X := f) (k := k) (b := Z_to_bv 8 b12);
    [exact UF | lia | lia | exact M | exact SK | exact M12 | apply (ccsg_sh1F RNG f n); [exact RH | lia]
    | apply (ccsg_rng1 RNG f n); [exact RF | lia] | ].
  intros y11 y12. rewrite (ccsg_zxb_lit b12) by lia.
  step. step. step.
  destruct (Z.eq_dec b12 0x81) as [E12|E12]; [takeF false | takeF true; ccsg_tagno_fin].
  (* f[13] *)
  destruct (ccsg_sh m f n 13 ADR ltac:(lia)) as (k1 & M1 & SK1).
  ccsg_at 0xa0.
  eapply (ccsg_ckt13 RNG) with (X := f) (k := k1) (b := Z_to_bv 8 b13);
    [exact UF | lia | lia | exact M1 | exact SK1 | exact M13 | apply (ccsg_sh1F RNG f n); [exact RH | lia]
    | apply (ccsg_rng1 RNG f n); [exact RF | lia] | ].
  intros z11 z12. rewrite (ccsg_zxb_lit b13) by lia.
  step. step.
  destruct (Z.eq_dec b13 0) as [E13|E13]; [takeF false | takeF true; ccsg_tagno_fin].
  (* f[16] *)
  destruct (ccsg_sh m f n 16 ADR ltac:(lia)) as (k2 & M2 & SK2).
  ccsg_at 0xc8.
  eapply (ccsg_ckt16 RNG) with (X := f) (k := k2) (b := Z_to_bv 8 b16);
    [exact UF | lia | lia | exact M2 | exact SK2 | exact M16 | apply (ccsg_sh1F RNG f n); [exact RH | lia]
    | apply (ccsg_rng1 RNG f n); [exact RF | lia] | ].
  intros w11 w12 Hy. rewrite (ccsg_zxb_lit b16) by lia.
  step. step. step.
  destruct (Z.eq_dec b16 0x88) as [E16|E16]; [takeF false | takeF true; ccsg_tagno_fin].
  (* f[17] *)
  destruct (ccsg_sh m f n 17 ADR ltac:(lia)) as (k3 & M3 & SK3).
  ccsg_at 0xf4.
  eapply (ccsg_ckt17 RNG) with (X := f) (k := k3) (b := Z_to_bv 8 b17);
    [exact UF | lia | lia | exact M3 | exact SK3 | exact M17 | apply (ccsg_sh1F RNG f n); [exact RH | lia]
    | apply (ccsg_rng1 RNG f n); [exact RF | lia] | ].
  intros v12 v13. rewrite (ccsg_zxb_lit b17) by lia.
  assert (E17 : b17 <> 0x19) by (intros E; apply NOT; auto).
  step. step. step. takeF true. ccsg_tagno_fin.
Qed.

Lemma cc_seg_cp2ret_ok : cc_seg_cp2ret_F.
Proof.
  unfold cc_seg_cp2ret_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n HN.
  ccsg_lits.
  step.
  ccsg_finF.
Qed.

Lemma cc_seg_want_lo_ok : cc_seg_want_lo_F.
Proof.
  unfold cc_seg_want_lo_F.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n HP HN.
  ccsg_lits.
  step. step. takeF true.
  ccsg_join0.
  ccsg_finF.
Qed.

(* the free arm of the want test: cc_want = 0 (a1', a2', a3' the words the walk left) *)
Local Ltac ccsg_want_free := apply evtF_done; do 3 eexists; left; split; [lia|]; f_equal; ccsg_regs; ccsg_w.

Lemma cc_seg_want_hi_ok : cc_seg_want_hi_F.
Proof.
  unfold cc_seg_want_hi_F.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n L
    u12 u13 u16 u17 HP HN HL ADR RP RH R12 R13 R16 R17 M12 M13 M16 M17.
  destruct (ccsg_adr_bound m P n ADR) as [HP0 HPn].
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  ccsg_lits.
  (* `bltu s3, 50` not taken *)
  step. step. takeF false.
  (* u[12] *)
  destruct (ccsg_sh m P n 12 ADR ltac:(lia)) as (k & M & SK).
  ccsg_at 0x148.
  eapply (ccsg_ckw12 RNG) with (X := P) (k := k) (b := Z_to_bv 8 u12);
    [exact UP | lia | lia | exact M | exact SK | exact M12 | apply (ccsg_sh1F RNG P n); [exact RH | lia]
    | apply (ccsg_rng1 RNG P n); [exact RP | lia] | ].
  intros y11 y13. rewrite (ccsg_zxb_lit u12) by lia.
  step. step.
  destruct (Z.eq_dec u12 0x88) as [E12|E12].
  2: { takeF true.
       assert (W : cc_want u12 u13 u16 u17 L = 0)
         by (unfold cc_want; rewrite (proj2 (Z.eqb_neq _ _) E12); reflexivity).
       rewrite W. ccsg_join0. ccsg_want_free. }
  takeF false.
  (* u[13] *)
  destruct (ccsg_sh m P n 13 ADR ltac:(lia)) as (k1 & M1 & SK1).
  ccsg_at 0x170.
  eapply (ccsg_ckw13 RNG) with (X := P) (k := k1) (b := Z_to_bv 8 u13);
    [exact UP | lia | lia | exact M1 | exact SK1 | exact M13 | apply (ccsg_sh1F RNG P n); [exact RH | lia]
    | apply (ccsg_rng1 RNG P n); [exact RP | lia] | ].
  intros z11 z13. rewrite (ccsg_zxb_lit u13) by lia.
  step. step.
  destruct (Z.eq_dec u13 0x19) as [E13|E13].
  2: { takeF true.
       assert (W : cc_want u12 u13 u16 u17 L = 0)
         by (unfold cc_want; rewrite (proj2 (Z.eqb_eq _ _) E12), (proj2 (Z.eqb_neq _ _) E13); reflexivity).
       rewrite W. ccsg_join0. ccsg_want_free. }
  takeF false.
  (* u[16] *)
  destruct (ccsg_sh m P n 16 ADR ltac:(lia)) as (k2 & M2 & SK2).
  ccsg_at 0x198.
  eapply (ccsg_ckw16 RNG) with (X := P) (k := k2) (b := Z_to_bv 8 u16);
    [exact UP | lia | lia | exact M2 | exact SK2 | exact M16 | apply (ccsg_sh1F RNG P n); [exact RH | lia]
    | apply (ccsg_rng1 RNG P n); [exact RP | lia] | ].
  intros w11 w13. rewrite (ccsg_zxb_lit u16) by lia.
  step.
  destruct (Z.eq_dec u16 0) as [E16|E16].
  2: { takeF false.
       assert (W : cc_want u12 u13 u16 u17 L = 0)
         by (unfold cc_want; rewrite (proj2 (Z.eqb_eq _ _) E12), (proj2 (Z.eqb_eq _ _) E13),
               (proj2 (Z.eqb_neq _ _) E16); reflexivity).
       rewrite W. ccsg_join0. ccsg_want_free. }
  takeF true.
  (* u[17] *)
  destruct (ccsg_sh m P n 17 ADR ltac:(lia)) as (k3 & M3 & SK3).
  ccsg_at 0x208.
  eapply (ccsg_ckw17 RNG) with (X := P) (k := k3) (b := Z_to_bv 8 u17);
    [exact UP | lia | lia | exact M3 | exact SK3 | exact M17 | apply (ccsg_sh1F RNG P n); [exact RH | lia]
    | apply (ccsg_rng1 RNG P n); [exact RP | lia] | ].
  intros v11 v13. rewrite (ccsg_zxb_lit u17) by lia.
  (* a0 := ((u17 != 0) - 1) & L (`snez`, `addi -1`, `and a2`); `beq s0, a0` taken to +0x1c0 *)
  step. step. step.
  rewrite (ccsg_sel u17 L) by lia.
  step.
  destruct (Z.eq_dec u17 0) as [E17|E17].
  - assert (W : cc_want u12 u13 u16 u17 L = L)
      by (unfold cc_want; rewrite (proj2 (Z.eqb_eq _ _) E12), (proj2 (Z.eqb_eq _ _) E13),
            (proj2 (Z.eqb_eq _ _) E16), (proj2 (Z.eqb_eq _ _) E17); reflexivity).
    assert (W2 : (if u17 =? 0 then L else 0) = L) by (rewrite (proj2 (Z.eqb_eq _ _) E17); reflexivity).
    rewrite W, W2. takeF true.
    (* `beqz s0` at +0x1c0: L = 0 frees u, L > 0 calls bcmp(c, u, L) *)
    step. destruct (Z.eq_dec L 0) as [EL|EL].
    + takeF true. step. step. ccsg_want_free.
    + takeF false. do 4 step.
      apply evtF_done. exists s1, s1. eexists. right. split; [lia|]. f_equal; ccsg_regs; ccsg_w.
  - assert (W : cc_want u12 u13 u16 u17 L = 0)
      by (unfold cc_want; rewrite (proj2 (Z.eqb_eq _ _) E12), (proj2 (Z.eqb_eq _ _) E13),
            (proj2 (Z.eqb_eq _ _) E16), (proj2 (Z.eqb_neq _ _) E17); reflexivity).
    assert (W2 : (if u17 =? 0 then L else 0) = 0) by (rewrite (proj2 (Z.eqb_neq _ _) E17); reflexivity).
    rewrite W, W2. takeF true.
    step. takeF true. step. step. ccsg_want_free.
Qed.

Lemma cc_seg_bcmpret_ok : cc_seg_bcmpret_F.
Proof.
  unfold cc_seg_bcmpret_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  ccsg_lits.
  step. takeF false.
  do 2 step.
  ccsg_finF.
Qed.

Lemma cc_seg_end_ok : cc_seg_end_F.
Proof.
  unfold cc_seg_end_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 c5 c4 c3 c2 c1 c0 cra FR HSP RFR.
  ccsg_lits.
  unfold cc_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 10 step.
  apply evtF_done. f_equal.
Qed.
