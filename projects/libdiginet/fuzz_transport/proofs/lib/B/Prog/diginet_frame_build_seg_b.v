(* diginet_frame_build_seg_b: eight control-flow pieces of the image-B walk of diginet_frame_build
   (fuzz_frame.asan-ubsan 0x82670), each the Lemma of a statement of lib/B/Prog/diginet_frame_build_iface.v, as a
   footprint run (lib/Lib/ExecF.v evtF) stepped by lib/Lib/StepF.v step:
     fb_sumZ_F    0x8280c `beqz s5` not taken (mode <> 0): a0 := 0, a1 := 0, the jump to 0x8282c;
     fb_sumC_F    0x8280c `beqz s5` taken (mode = 0): a0 := s2, a1 := s1, the call of diginet_sum16 at 0x82824;
     fb_sumR_F    0x82828 `srli a1,a0,0x8` after the return of diginet_sum16;
     fb_seg4Z_F   0x82a7c `beqz s1` taken (body_len = 0): the body copy is skipped;
     fb_seg4_F    body_len <> 0: the wrap guard of out + 30 (0x82a80 `li a0,-31`, 0x82a84 `bltu a0,s0`), then the
                  third __asan_memcpy (out + 30, body, body_len) at 0x82a94;
     fb_seg5Z_F   0x82a98 `bgeu s9,s8` taken (30 + body_len >= len): the padding is skipped;
     fb_seg5_F    30 + body_len < len: the wrap guard of out + 30 + body_len (0x82a9c `not a0,s0`, 0x82aa0
                  `bltu a0,s9`), then the __asan_memset (out + 30 + body_len, 0, len - 30 - body_len) at 0x82ab0;
     fb_epi_F     0x82ab4 a0 := sext.w s8, ra and s0 .. s10 reloaded from the frame, sp += 96, `ret` at 0x82aec.
   The two wrap guards branch to the `unimp` word at 0x82af0 only when the unsigned compare holds; the premises
   out + 31 <= 2 ^ 64 and out + 60 < 2 ^ 64 make each compare false, so neither branch is taken.
   None of these pieces makes an instrumented access or a store into out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof diginet_frame_build_iface.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(** * Helpers *)

(* `sext.w` (addiw rd, rs, 0) of a word that holds a 32-bit signed value leaves that word. *)
Lemma fbb_sext_w : forall v, - 2 ^ 31 <= v < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0)) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite Z.add_0_r, unsigned_lit_wrap. apply Z_to_bv_eqm. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  Z.div_mod_to_equations. lia.
Qed.

(* `not` (xori rd, rs, -1) of a 64-bit value x is 2 ^ 64 - 1 - x: below bit 64 each bit of the xor is the negated
   bit of x, which is the low 64 bits of Z.lnot x = - x - 1. *)
Lemma fbb_lxor_ones : forall x k, 0 <= x < 2 ^ 64 -> k = Z.ones 64 -> Z.lxor x k = 2 ^ 64 - 1 - x.
Proof.
  intros x k Hx ->.
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.ltb_spec i 64) as [Hl | Hg].
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r. destruct (Z.testbit x i); reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite andb_false_r, xorb_false_r.
      rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot.
  symmetry. apply (Z.mod_unique_pos (Z.pred (- x)) (2 ^ 64) (-1)); lia.
Qed.

(* Every pc of these pieces is a closed iface name; compute each to its value, since step reads a literal pc. *)
Ltac fbb_lit X := let v := eval vm_compute in X in change X with v.
Ltac fbb_lits :=
  repeat match goal with
  | |- context [FB_SUM] => fbb_lit FB_SUM
  | |- context [FB_RET_S] => fbb_lit FB_RET_S
  | |- context [FB_H2] => fbb_lit FB_H2
  | |- context [FB_S16] => fbb_lit FB_S16
  | |- context [FB_TAIL] => fbb_lit FB_TAIL
  | |- context [FB_RET_C3] => fbb_lit FB_RET_C3
  | |- context [FB_EPI] => fbb_lit FB_EPI
  | |- context [FB_CPY] => fbb_lit FB_CPY
  | |- context [FB_SET] => fbb_lit FB_SET
  | |- context [FB_AT ?o] => fbb_lit (FB_AT o)
  | |- context [FB_ENTRY] => fbb_lit FB_ENTRY
  end.

(* bv_unsigned of a literal word whose value is in range. *)
Ltac fbb_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

(* bv_unsigned of a word built from closed literals (a negative `li` immediate such as -31), computed. *)
Ltac fbb_closed_ux :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => is_closed_lits z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in
      replace (bv_unsigned (Z_to_bv 64 z)) with v by (vm_compute; reflexivity)
  end.

(* A branch decided by the numeric premises. *)
Ltac fbb_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; rewrite ?w0_lit; fbb_closed_ux; fbb_usub;
  solve_cond_rec.
Ltac fbb_br b :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; fbb_cond]
  end.

(* The final register file, register by register. *)
Ltac fbb_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac fbb_w := fbb_usub; first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].
Ltac fbb_fin := apply evtF_done; f_equal; fbb_regs; fbb_w.

(** * fb_sumZ: FB_SUM with s5 = mode <> 0 -> FB_H2 with a0 = a1 = 0 *)

Lemma fb_sumZ_F : fb_sumZ_stmt.
Proof.
  unfold fb_sumZ_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HS5.
  fbb_lits.
  (* 0x8280c beqz s5 not taken; 0x82810 li a0,0; 0x82814 li a1,0; 0x82818 j 0x8282c *)
  step. fbb_br false.
  step. step. step.
  fbb_fin.
Qed.

(** * fb_sumC: FB_SUM with s5 = mode = 0 -> the call of diginet_sum16 *)

Lemma fb_sumC_F : fb_sumC_stmt.
Proof.
  unfold fb_sumC_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HS5.
  fbb_lits.
  (* 0x8280c beqz s5 taken; 0x8281c mv a0,s2; 0x82820 mv a1,s1; 0x82824 jal diginet_sum16 *)
  step. fbb_br true.
  step. step. step.
  rewrite ?Z.add_0_r, ?Z_to_bv_lit_self.
  fbb_fin.
Qed.

(** * fb_sumR: FB_RET_S -> FB_H2: `srli a1,a0,0x8` *)

Lemma fb_sumR_F : fb_sumR_stmt.
Proof.
  unfold fb_sumR_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    sm HSM.
  fbb_lits.
  (* 0x82828 srli a1,a0,0x8 *)
  step.
  rewrite (unsigned_lit sm) by lia. rewrite Z.shiftr_div_pow2 by lia.
  fbb_fin.
Qed.

(** * fb_seg4Z: FB_TAIL with s1 = 0 -> FB_RET_C3 *)

Lemma fb_seg4Z_F : fb_seg4Z_stmt.
Proof.
  unfold fb_seg4Z_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  fbb_lits.
  (* 0x82a7c beqz s1 taken, to 0x82a98 *)
  step. fbb_br true.
  fbb_fin.
Qed.

(** * fb_seg4: FB_TAIL with s1 = body_len <> 0 -> the third __asan_memcpy *)

Lemma fb_seg4_F : fb_seg4_stmt.
Proof.
  unfold fb_seg4_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out body blen HOUT HOUT31 HBODY HBLEN.
  fbb_lits.
  (* 0x82a7c beqz s1 not taken (body_len <> 0) *)
  step. fbb_br false.
  (* 0x82a80 li a0,-31; 0x82a84 bltu a0,s0 not taken: 2 ^ 64 - 31 < out is false for out + 31 <= 2 ^ 64 *)
  step. step. fbb_br false.
  (* 0x82a88 addi a0,s0,30; mv a1,s2; mv a2,s1; 0x82a94 jal __asan_memcpy *)
  do 4 step.
  fbb_fin.
Qed.

(** * fb_seg5Z: FB_RET_C3 with 30 + body_len >= len -> FB_EPI *)

Lemma fb_seg5Z_F : fb_seg5Z_stmt.
Proof.
  unfold fb_seg5Z_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m
    blen HBLEN.
  fbb_lits. unfold fb_len in *.
  (* 0x82a98 bgeu s9,s8 taken (s8 = 30 + body_len = s9), to 0x82ab4 *)
  step. fbb_br true.
  fbb_fin.
Qed.

(** * fb_seg5: FB_RET_C3 with 30 + body_len < len -> the __asan_memset *)

Lemma fb_seg5_F : fb_seg5_stmt.
Proof.
  unfold fb_seg5_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m
    out blen HOUT HOUT60 HBLEN.
  fbb_lits.
  (* 0x82a98 bgeu s9,s8 not taken (30 + body_len < 60) *)
  step. fbb_br false.
  (* 0x82a9c not a0,s0: a0 := 2 ^ 64 - 1 - out *)
  step.
  rewrite ?(unsigned_lit out) by lia.
  rewrite (fbb_lxor_ones out) by first [ lia | reflexivity ].
  (* 0x82aa0 bltu a0,s9 not taken: 2 ^ 64 - 1 - out < 30 + body_len is false for out + 60 < 2 ^ 64 *)
  step. fbb_br false.
  (* 0x82aa4 add a0,s0,s9; sub a2,s8,s9; li a1,0; 0x82ab0 jal __asan_memset *)
  do 4 step.
  fbb_fin.
Qed.

(** * fb_epi: FB_EPI -> the return *)

Lemma fb_epi_F : fb_epi_stmt.
Proof.
  unfold fb_epi_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m
    v c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra FR HSP RFR HV.
  fbb_lits.
  unfold fb_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  (* 0x82ab4 sext.w a0,s8 *)
  step. rewrite (fbb_sext_w v HV).
  (* 0x82ab8 .. 0x82ae4 the twelve reloads; 0x82ae8 addi sp,sp,96; 0x82aec ret *)
  do 14 step.
  apply evtF_done. f_equal.
Qed.
