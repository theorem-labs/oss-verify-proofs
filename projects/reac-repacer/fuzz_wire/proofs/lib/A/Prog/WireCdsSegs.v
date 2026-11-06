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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_copy_cgW_segs.v, with its module paths and numbers changed; 288 of its 360 lines of code are new or changed and 451 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/WireCdsBSegs.v, with its module paths, addresses and numbers changed; 392 of its 456 lines of code are new or changed and 296 lines of the source are left out. *)
(* WireCdsSegs: the straight-line runs of check_downstream (fuzz_wire.asan 0x801fc = wire_sigma WS_check_downstream,
   81 words), as footprint (ExecF.evtF) runs:
     cds_pro_F   the entry .. the call of rp_ds_accept (`jal` at +0xd4, return address +0xd8 = CDS_RET): the frame
                 (`addi sp, sp, -0x10` at +0x0, `sd ra, 8(sp)` at +0x4, `sd s0, 0(sp)` at +0x8), then
                 `bltu a1, a2, +0xd0` (a2 = 18 from +0xc). n < 18 takes +0xd0 `mv s0, zero` and reads no frame byte;
                 n >= 18 loads the shadow base (the GOT word at +0x14 / +0x18, the cell at +0x1c) and reads the frame
                 bytes f[12] (+0x34), f[13] (+0x5c on the f[12] = 0x88 path, +0x84 on the 0x81 path), f[16] (+0xa0)
                 and f[17] (+0xc0). Both paths reach +0xd4 with s0 = ds_accept_result n bs of the released
                 lib/Prog/rp_ds_accept_c.v and a0 = f, a1 = n unchanged;
     cds_epi_F   CDS_RET .. the return: `bne a0, s0, +0xec` (+0xd8) is not taken when a0 = s0, so the abort path
                 (+0xec `jal __asan_handle_no_return`, +0xf0 `jal abort`) is unreachable; then +0xdc `ld ra, 8(sp)`,
                 +0xe0 `ld s0, 0(sp)`, +0xe4 `addi sp, sp, 0x10`, +0xe8 `ret`.
   Each frame-byte read is one block (cds_b12_F, cds_b13a_F, cds_b13b_F, cds_b16_F, cds_b17_F): the byte's shadow
   byte (`lb` at +0x2c, +0x54, +0x7c, +0x98, +0xb8) and, when it is non-zero, the partial-granule test (+0xf4,
   +0x104, +0x114, +0x124, +0x134) back to the load; the report call (`jal __asan_report_load1` at +0x100, +0x110,
   +0x120, +0x130, +0x140) is refuted by `addressable m (f + 12) 6`, as in the leaf's own walk.
   Every address and offset is measured on the objdump of record of fuzz_wire.asan (sha256 2f8f8697cd4f). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_ds_accept_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ds_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ds_accept_c.
Module RDF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ds_accept_F_c.

(* ---- the cut points (offsets from the entry, read from the pinned image's code) ---- *)
Definition CDS_ENTRY : Z := wire_sigma WS_check_downstream.
Definition CDS_AT (off : Z) : Z := CDS_ENTRY + off.
(* the return address of the call of rp_ds_accept (`jal` at +0xd4) *)
Definition CDS_RET : Z := CDS_AT 0xd8.
Definition CDS_LEAF : Z := wire_sigma WS_rp_ds_accept.
(* the frame of check_downstream (`addi sp, sp, -0x10` at the entry) *)
Definition CDS_FR : Z := 16.

Lemma cds_leaf_pc : CDS_LEAF = RDF.RP_DS_ACCEPT.
Proof. reflexivity. Qed.

(* ---- tactics ---- *)

Ltac cds_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cds_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cds_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac cds_w := cds_shift; cds_usub; cds_shift; cds_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac cds_ms := first [ reflexivity | f_equal; cds_regs; try cds_w ].
(* StepF's step reads the start pc: compute every closed name of the goal to its value first. *)
Ltac cds_lit X := let v := eval vm_compute in X in change X with v.
Ltac cds_lits :=
  repeat match goal with
  | |- context [CDS_RET] => cds_lit CDS_RET
  | |- context [CDS_LEAF] => cds_lit CDS_LEAF
  | |- context [RDF.RP_DS_ACCEPT] => cds_lit RDF.RP_DS_ACCEPT
  | |- context [CDS_AT ?o] => cds_lit (CDS_AT o)
  | |- context [CDS_ENTRY] => cds_lit CDS_ENTRY
  end.

(* ---- helpers ---- *)

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of [a, a + n)
   (this unit's reac_frame_is_reac_F.v is_reac_shadow_byte_rng). *)
Lemma cds_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* A whole byte string read at once. *)
Lemma cds_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* `addi r, b, -0x19; seqz s, r` on a loaded byte b: s = (b == 0x19) (released lib/Prog/rp_ds_accept.v seqz_byte). *)
Lemma cds_seqz_byte : forall b : byte,
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -25)) 1 = Z_to_bv 64 (if bv_unsigned b =? 25 then 1 else 0).
Proof.
  intros b. unfold v_sltiu, zxb. rewrite zxb_u. pose proof (byte_range b) as X.
  destruct (Z.eq_dec (bv_unsigned b) 25) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) E).
    rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    replace ((bv_unsigned b + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

(* Each byte test of the model whose answer the path fixed (released lib/Prog/rp_ds_accept.v bfacts). *)
Local Ltac bfacts :=
  repeat match goal with
  | H : ?x = ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_eq x c) H)
  | H : ?x <> ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  | H : ?x < ?c |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_lt x c) H)
  | H : ?c <= ?x |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_ge x c) H)
  end.

(* The model's value on the path just walked is the want the code left in s0 (rp_ds_accept.v `fin`). *)
Local Ltac ds_val :=
  symmetry; unfold PDA.ds_accept_result, PDA.ds_byte;
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end;
  bfacts;
  repeat match goal with |- context [Z.eqb ?x ?c] => destruct (Z.eqb_spec x c); try (exfalso; lia) end;
  cbn [andb orb]; reflexivity.

Section Segs.
(* The register slots of the state the runs start from (lib/Lib/MState.v mkR). *)
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variable RNG : ExecF.footprint.

(* ---- cds_b12_F: +0x14 (the shadow base) .. +0x38, with a2 = f[12] ---- *)
Lemma cds_b12_F : forall (b k : byte),
  bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
  bv_unsigned a0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned a0 + 12))) = Some k ->
  shadow_ok (bv_unsigned a0 + 12) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned a0 + 12)) = Some b ->
  ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
  ExecF.rng RNG (bv_unsigned a0 + 12) 1 -> ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12)) 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (zxb b) (Z_to_bv 64 ASAN_K) a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (CDS_AT 0x38)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (CDS_AT 0x14)) fc None m (seg_rom rsegs)).
Proof.
  intros b k GCK CK HT MK SK F12 RGC RCK RBUF RSH.
  cds_lits.
  unfold GOT_CELL_K in RGC, GCK. unfold CELL_K in RCK, GCK, CK. unfold ASAN_K in CK.
  unfold shadow_addr, ASAN_K, shadow_ok in MK, SK, RSH.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 12) 8 ltac:(lia)) as MB.
  pose proof (cds_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (cds_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  (* auipc a2; ld a2 (the GOT word); ld a3 (the shadow base) *)
  do 3 step.
  (* addi a2, a0, 0xc; srli a4, a2, 3; add a4, a4, a3; lb a4, 0(a4); bnez a4 *)
  step. gen_addi a0 w U.
  pose proof (rng_sub' _ _ _ (bv_unsigned w) 1 RBUF ltac:(lia)) as RW.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  try rewrite (unsigned_lit 2147450880) in H by lia.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RSH ltac:(lia)) as RH.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned a0 + 12) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ F12 ltac:(lia)) as R; step; clear R.
  all: apply evtF_done; do 2 eexists; cds_ms.
Qed.

(* ---- cds_b13a_F: +0x48 .. +0x60, with a2 = f[13] (the f[12] = 0x88 path; the shadow base is clobbered) ---- *)
Lemma cds_b13a_F : forall (b k : byte),
  bv_unsigned a0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned a0 + 13))) = Some k ->
  shadow_ok (bv_unsigned a0 + 13) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned a0 + 13)) = Some b ->
  ExecF.rng RNG (bv_unsigned a0 + 13) 1 -> ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 13)) 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists a3' a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (zxb b) a3' a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (CDS_AT 0x60)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 ASAN_K) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (CDS_AT 0x48)) fc None m (seg_rom rsegs)).
Proof.
  intros b k HT MK SK F13 RBUF RSH.
  cds_lits. unfold ASAN_K. unfold shadow_addr, ASAN_K, shadow_ok in MK, SK, RSH.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 13) 8 ltac:(lia)) as MB.
  step. gen_addi a0 w U.
  pose proof (rng_sub' _ _ _ (bv_unsigned w) 1 RBUF ltac:(lia)) as RW.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  try rewrite (unsigned_lit 2147450880) in H by lia.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RSH ltac:(lia)) as RH.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned a0 + 13) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ F13 ltac:(lia)) as R; step; clear R.
  all: apply evtF_done; do 3 eexists; cds_ms.
Qed.

(* ---- cds_b13b_F: +0x70 .. +0x88, with a2 = f[13] (the f[12] = 0x81 path; the shadow base is kept) ---- *)
Lemma cds_b13b_F : forall (b k : byte),
  bv_unsigned a0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned a0 + 13))) = Some k ->
  shadow_ok (bv_unsigned a0 + 13) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned a0 + 13)) = Some b ->
  ExecF.rng RNG (bv_unsigned a0 + 13) 1 -> ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 13)) 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (zxb b) (Z_to_bv 64 ASAN_K) a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (CDS_AT 0x88)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 ASAN_K) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (CDS_AT 0x70)) fc None m (seg_rom rsegs)).
Proof.
  intros b k HT MK SK F13 RBUF RSH.
  cds_lits. unfold ASAN_K. unfold shadow_addr, ASAN_K, shadow_ok in MK, SK, RSH.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 13) 8 ltac:(lia)) as MB.
  step. gen_addi a0 w U.
  pose proof (rng_sub' _ _ _ (bv_unsigned w) 1 RBUF ltac:(lia)) as RW.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  try rewrite (unsigned_lit 2147450880) in H by lia.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RSH ltac:(lia)) as RH.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned a0 + 13) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ F13 ltac:(lia)) as R; step; clear R.
  all: apply evtF_done; do 2 eexists; cds_ms.
Qed.

(* ---- cds_b16_F: +0x8c .. +0xa4, with a2 = f[16] (the shadow base is kept) ---- *)
Lemma cds_b16_F : forall (b k : byte),
  bv_unsigned a0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned a0 + 16))) = Some k ->
  shadow_ok (bv_unsigned a0 + 16) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned a0 + 16)) = Some b ->
  ExecF.rng RNG (bv_unsigned a0 + 16) 1 -> ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 16)) 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (zxb b) (Z_to_bv 64 ASAN_K) a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (CDS_AT 0xa4)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 ASAN_K) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (CDS_AT 0x8c)) fc None m (seg_rom rsegs)).
Proof.
  intros b k HT MK SK F16 RBUF RSH.
  cds_lits. unfold ASAN_K. unfold shadow_addr, ASAN_K, shadow_ok in MK, SK, RSH.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 16) 8 ltac:(lia)) as MB.
  step. gen_addi a0 w U.
  pose proof (rng_sub' _ _ _ (bv_unsigned w) 1 RBUF ltac:(lia)) as RW.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  try rewrite (unsigned_lit 2147450880) in H by lia.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RSH ltac:(lia)) as RH.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned a0 + 16) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ F16 ltac:(lia)) as R; step; clear R.
  all: apply evtF_done; do 2 eexists; cds_ms.
Qed.

(* ---- cds_b17_F: +0xac .. +0xc4, with a2 = f[17] (the shadow base is clobbered) ---- *)
Lemma cds_b17_F : forall (b k : byte),
  bv_unsigned a0 + 18 <= 2 ^ 64 ->
  mrd rsegs m (wa (shadow_addr (bv_unsigned a0 + 17))) = Some k ->
  shadow_ok (bv_unsigned a0 + 17) (bv_signed k) ->
  mrd rsegs m (wa (bv_unsigned a0 + 17)) = Some b ->
  ExecF.rng RNG (bv_unsigned a0 + 17) 1 -> ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 17)) 1 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists a3' a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (zxb b) a3' a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (CDS_AT 0xc4)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 ASAN_K) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (CDS_AT 0xac)) fc None m (seg_rom rsegs)).
Proof.
  intros b k HT MK SK F17 RBUF RSH.
  cds_lits. unfold ASAN_K. unfold shadow_addr, ASAN_K, shadow_ok in MK, SK, RSH.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 17) 8 ltac:(lia)) as MB.
  step. gen_addi a0 w U.
  pose proof (rng_sub' _ _ _ (bv_unsigned w) 1 RBUF ltac:(lia)) as RW.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  try rewrite (unsigned_lit 2147450880) in H by lia.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RSH ltac:(lia)) as RH.
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U, (lts_low ((bv_unsigned a0 + 17) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m w _ _ F17 ltac:(lia)) as R; step; clear R.
  all: apply evtF_done; do 3 eexists; cds_ms.
Qed.

End Segs.

(* ---- cds_pro_F: the entry .. the call of rp_ds_accept ---- *)
Lemma cds_pro_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + CDS_FR <= bv_unsigned sp ->
    (18 <= bv_unsigned a1 ->
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp CDS_FR (bv_unsigned a0) 18 /\
       asan_cells m /\
       off_stk sp CDS_FR GOT_CELL_K 8 /\
       off_stk sp CDS_FR CELL_K 8 /\
       app_mem (bv_unsigned sp - CDS_FR) /\ app_mem (bv_unsigned sp - 1) /\
       addressable m (bv_unsigned a0 + 12) 6) ->
    ExecF.rng RNG (bv_unsigned sp - CDS_FR) CDS_FR ->
    (18 <= bv_unsigned a1 ->
       ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
       ExecF.rng RNG (bv_unsigned a0 + 12) 6 /\
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 6 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 CDS_RET) (Z_to_bv 64 (bv_unsigned sp - CDS_FR)) gp tp t0 t1 t2
                       (Z_to_bv 64 (PDA.ds_accept_result (bv_unsigned a1) bs)) s1 a0 a1 a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RDF.RP_DS_ACCEPT) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CDS_FR, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned sp - CDS_FR) [C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CDS_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    bs lo ST HLO HB RFR RX.
  cds_lits. unfold CDS_FR in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  (* addi sp, sp, -0x10; sd ra, 8(sp); sd s0, 0(sp) *)
  do 3 step.
  match goal with MU' : munch _ m ?mm |- _ => rename MU' into MU1; rename mm into m0 end.
  (* li a2, 18; bltu a1, a2 *)
  step. step. if_cases HL.
  - (* n < 18: +0xd0 `mv s0, zero`, then the call *)
    zc HL.
    do 2 step.
    apply evtF_done. do 5 eexists.
    split; [f_equal; cds_regs; try cds_w; try (f_equal; ds_val)|].
    split; [eassumption | split; [eassumption | eassumption]].
  - zc HL.
    destruct (HB HL) as (LEN & BA & DJ & CELLS & DG & DS & APS1 & APS2 & ADR).
    destruct (RX HL) as (RGOT & RCELL & RBUF & RSH).
    destruct CELLS as (CK & GCK & _).
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
    destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
    destruct (AB 4 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
    destruct (AB 5 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
    pose proof (cds_shadow_byte_rng RNG (bv_unsigned a0 + 12) 6 0 ltac:(lia) RSH) as RS12.
    pose proof (cds_shadow_byte_rng RNG (bv_unsigned a0 + 12) 6 1 ltac:(lia) RSH) as RS13.
    pose proof (cds_shadow_byte_rng RNG (bv_unsigned a0 + 12) 6 4 ltac:(lia) RSH) as RS16.
    pose proof (cds_shadow_byte_rng RNG (bv_unsigned a0 + 12) 6 5 ltac:(lia) RSH) as RS17.
    rewrite Z.add_0_r in RS12.
    replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in RS13 by lia.
    replace (bv_unsigned a0 + 12 + 4) with (bv_unsigned a0 + 16) in RS16 by lia.
    replace (bv_unsigned a0 + 12 + 5) with (bv_unsigned a0 + 17) in RS17 by lia.
    pose proof (rng_sub' _ _ _ (bv_unsigned a0 + 12) 1 RBUF ltac:(lia)) as RB12.
    pose proof (rng_sub' _ _ _ (bv_unsigned a0 + 13) 1 RBUF ltac:(lia)) as RB13.
    pose proof (rng_sub' _ _ _ (bv_unsigned a0 + 16) 1 RBUF ltac:(lia)) as RB16.
    pose proof (rng_sub' _ _ _ (bv_unsigned a0 + 17) 1 RBUF ltac:(lia)) as RB17.
    clear RSH RBUF.
    rewrite Z.add_0_r in MK12, SK12.
    replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in MK13, SK13 by lia.
    replace (bv_unsigned a0 + 12 + 4) with (bv_unsigned a0 + 16) in MK16, SK16 by lia.
    replace (bv_unsigned a0 + 12 + 5) with (bv_unsigned a0 + 17) in MK17, SK17 by lia.
    unfold off_stk, GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APP16, APP17, APS1, APS2, PE.
    pose proof BA as (BA0 & BA1 & _).
    (* the two frame stores moved every fact of the entry memory to m0 *)
    pose proof (bytes_tp m m0 _ _ 0x987e8 (le8 (wa 0xa0778)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
    pose proof (bytes_tp m m0 _ _ 0xa0778 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
    pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
    pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
    pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 16) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK16) as M16.
    pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 17) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK17) as M17.
    pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
    pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
    pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 16) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 16 BA ltac:(lia))) as F16.
    pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 17) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 17 BA ltac:(lia))) as F17.
    change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
    change (Z.of_nat 16) with 16 in F16. change (Z.of_nat 17) with 17 in F17.
    remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
    remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
    remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
    remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
    (* +0x14 .. +0x38: the shadow base and f[12] *)
    eapply evtF_cut;
      [ eapply (cds_b12_F _ _ gp tp t0 t1 t2 _ s1 a0 a1 _ _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m0 RNG b12 k12 GOT0 SV0 ltac:(lia) M12 SK12 F12 RGOT RCELL RB12 RS12) |].
    intros ms' (a4' & a5' & ->). cds_lits.
    (* li a4, 0x81; beq a2, a4 *)
    step. step. if_cases H81.
    + (* f[12] = 0x81: the tagged path at +0x70 *)
      zc H81.
      eapply evtF_cut;
        [ eapply (cds_b13b_F _ _ gp tp t0 t1 t2 _ s1 a0 a1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6 F fc m0 RNG b13 k13 ltac:(lia) M13 SK13 F13 RB13 RS13) |].
      intros ms' (a4'' & a5'' & ->). cds_lits.
      (* bnez a2 *)
      step. if_cases H13.
      * (* f[13] /= 0: +0xd0 *)
        zc H13. do 2 step.
        apply evtF_done. do 5 eexists.
        split; [f_equal; cds_regs; try cds_w; try (f_equal; ds_val)|].
        split; [eassumption | split; [eassumption | eassumption]].
      * zc H13.
        eapply evtF_cut;
          [ eapply (cds_b16_F _ _ gp tp t0 t1 t2 _ s1 a0 a1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      t3 t4 t5 t6 F fc m0 RNG b16 k16 ltac:(lia) M16 SK16 F16 RB16 RS16) |].
        intros ms' (a4''' & a5''' & ->). cds_lits.
        (* li a4, 0x88; bne a2, a4 *)
        step. step. if_cases H16.
        -- (* f[16] /= 0x88: +0xd0 *)
           zc H16. do 2 step.
           apply evtF_done. do 5 eexists.
           split; [f_equal; cds_regs; try cds_w; try (f_equal; ds_val)|].
           split; [eassumption | split; [eassumption | eassumption]].
        -- zc H16.
           eapply evtF_cut;
             [ eapply (cds_b17_F _ _ gp tp t0 t1 t2 _ s1 a0 a1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                         t3 t4 t5 t6 F fc m0 RNG b17 k17 ltac:(lia) M17 SK17 F17 RB17 RS17) |].
           intros ms' (a3'''' & a4'''' & a5'''' & ->). cds_lits.
           (* addi a2, a2, -0x19; seqz s0, a2; j +0xd4; jal *)
           do 4 step.
           apply evtF_done. do 5 eexists.
           split; [rewrite cds_seqz_byte; f_equal; cds_regs; try cds_w; try (f_equal; ds_val)|].
           split; [eassumption | split; [eassumption | eassumption]].
    + zc H81.
      (* li a4, 0x88; bne a2, a4 *)
      step. step. if_cases H88.
      * (* f[12] is neither 0x81 nor 0x88: +0xd0 *)
        zc H88. do 2 step.
        apply evtF_done. do 5 eexists.
        split; [f_equal; cds_regs; try cds_w; try (f_equal; ds_val)|].
        split; [eassumption | split; [eassumption | eassumption]].
      * zc H88.
        eapply evtF_cut;
          [ eapply (cds_b13a_F _ _ gp tp t0 t1 t2 _ s1 a0 a1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      t3 t4 t5 t6 F fc m0 RNG b13 k13 ltac:(lia) M13 SK13 F13 RB13 RS13) |].
        intros ms' (a3'' & a4'' & a5'' & ->). cds_lits.
        (* li a3, 0x19; bne a2, a3 *)
        step. step. if_cases H13.
        -- (* f[13] /= 0x19: +0xd0 *)
           zc H13. do 2 step.
           apply evtF_done. do 5 eexists.
           split; [f_equal; cds_regs; try cds_w; try (f_equal; ds_val)|].
           split; [eassumption | split; [eassumption | eassumption]].
        -- (* f[12] = 0x88, f[13] = 0x19: li s0, 1; j +0xd4; jal *)
           zc H13. do 3 step.
           apply evtF_done. do 5 eexists.
           split; [f_equal; cds_regs; try cds_w; try (f_equal; ds_val)|].
           split; [eassumption | split; [eassumption | eassumption]].
Qed.

(* ---- cds_epi_F: CDS_RET .. the return ---- *)
Lemma cds_epi_F :
  forall (RNG : ExecF.footprint) (v : Z)
         (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 c0; C8 cra] ->
    bv_unsigned sp + CDS_FR < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) CDS_FR ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + CDS_FR)) gp tp t0 t1 t2 c0 s1
                       (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CDS_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG v ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c0 cra FR HSP RFR.
  cds_lits. unfold CDS_FR in *.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  (* bne a0, s0 (not taken: both hold the result of rp_ds_accept) *)
  step. if_false.
  (* ld ra, 8(sp); ld s0, 0(sp); addi sp, sp, 0x10; ret *)
  do 4 step.
  apply evtF_done. cds_ms.
Qed.
