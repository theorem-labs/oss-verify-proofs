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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_copy_cgW_segs.v, with its numbers changed; 398 of its 490 lines of code are new or changed and 431 lines of the source are left out. *)
(* check_read_walk_kit: the footprint segments of the image-A walk of check_read (fuzz_wire.asan 0x8077c) that run
   between its calls, each an ExecF.evtF run over image A's segments:
     cr_seg0_F  +0x000 .. `jal __asan_stack_malloc_1`: the 0x80-byte frame and its thirteen saves, the realign, the
                UAR flag (1, so the fake stack is asked) and the shadow base;
     cr_seg1_F  +0x78 .. `jal __asan_memset`: the fake frame's header and its sixteen shadow bytes;
     cr_seg2_F  +0x134 .. `jal rp_slot_read`: the inlined w_width loop (cr_ww_loop), c[16] and c[17] behind their
                shadow bytes (cr_b16_F), the harness's want;
     cr_seg4_F  +0x35c .. `ret`: v's shadow, the retire magic, the frame's shadow 0xf5, the flag byte, the reloads.
   The model facts come from the walk of check_read in lib/Prog/check_read.v (w_width_model, ww_facts, srm_zero,
   srm_one). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_slot_read_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_read_c rp_slot_width_c rp_frame_channels_c check_read.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PCR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.check_read.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_frame_channels_c.

(* ---- helpers ---- *)

Lemma crk_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
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

Lemma crk_ble : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + 256 * bytes_le_to_Z bs.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia. reflexivity.
Qed.

Lemma crk_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply crk_le_bytes_to_Z.
Qed.

Fixpoint crk_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: crk_c8s n' (skipn 8 bs)
  end.

Lemma crk_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (crk_c8s n bs) /\ cells_bytes (crk_c8s n bs) = bs /\ cells_size (crk_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [crk_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite crk_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma crk_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (crk_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (crk_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 128 bytes of the frame, read as 16 words. *)
Lemma crk_frame_words : forall m A bs, rw_cells rsegs m A [CB 128 bs] ->
  exists v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 : word,
    rw_cells rsegs m A [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72;
                        C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120].
Proof.
  intros m A bs H. apply (crk_rw_c8s rsegs m A 16 bs) in H. cbn [crk_c8s] in H. do 16 eexists. exact H.
Qed.

Lemma crk_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* `andi sp, sp, -0x20`. *)
Lemma crk_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof. intros x Hx. exact (PCR.land_hi x 5 Hx ltac:(lia)). Qed.

Ltac crk_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac crk_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac crk_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac crk_w := crk_shift; crk_usub; crk_shift; crk_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac crk_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* ---- cr_seg0_F: the entry -> __asan_stack_malloc_1 (0x3c6b8), ra = +0x78 ---- *)

(* The words the prologue saves, at sp - 0x68 .. sp: s11, s10, .., s0, ra. *)
Definition crk_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition crk_sp1 (sp : word) : Z := 32 * ((bv_unsigned sp - 128) / 32).

Lemma crk_sp1_eq : forall sp : word, 128 <= bv_unsigned sp ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128))) 18446744073709551584) = Z_to_bv 64 (crk_sp1 sp).
Proof.
  intros sp H. pose proof (zr_word sp) as R. unfold inr64 in R.
  rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia.
  change 18446744073709551584 with (2 ^ 64 - 32). rewrite crk_land_m32 by lia.
  unfold crk_sp1. replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) by lia. reflexivity.
Qed.

Lemma crk_sp1_range : forall sp : word, 128 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
  bv_unsigned sp - 144 <= crk_sp1 sp <= bv_unsigned sp - 128 /\ crk_sp1 sp mod 32 = 0.
Proof.
  intros sp H H16. unfold crk_sp1. pose proof (Z.div_mod (bv_unsigned sp - 128) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (bv_unsigned sp - 128) 32 ltac:(lia)).
  assert (M : (bv_unsigned sp - 128) mod 32 = 0 \/ (bv_unsigned sp - 128) mod 32 = 16) by (Z.div_mod_to_equations; lia).
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma cr_seg0_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> 0xa2000 <= bv_unsigned sp - 128 ->
    bytes_at rsegs m GOT_UAR (le8 (wa UAR)) -> bytes_at rsegs m UAR (le4 (wa 1)) ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    ExecF.rng RNG (bv_unsigned sp - 128) 128 ->
    ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG UAR 4 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 v0 v8 v16,
         ms' = MS (mkR (Z_to_bv 64 0x807f4) (Z_to_bv 64 (crk_sp1 sp)) gp tp t0 t1 t2
                    (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 (crk_sp1 sp)) (Z_to_bv 64 0x80) (Z_to_bv 64 CELL_K)
                    (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 a0 a2 a1 s7 (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x3c6b8) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 128)
           (C8 v0 :: C8 v8 :: C8 v16 :: crk_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8077c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO HLOW GU U GCK CK RFR RGU RU RGC RCK.
  unfold GOT_UAR in RGU, GU. unfold UAR in RU, U, GU. unfold GOT_CELL_K in RGC, GCK. unfold CELL_K in RCK, GCK, CK.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 128%nat ST.
  destruct (crk_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & v96
    & v104 & v112 & v120 & FR'). clear FR. rename FR' into FR.
  do 16 step.
  pose proof (crk_rd_all _ _ _ GU) as RDGU. rewrite length_le8 in RDGU.
  pose proof (crk_rd_all _ _ _ GCK) as RDGC. rewrite length_le8 in RDGC.
  pose proof (crk_rd_all _ _ _ U) as RDU. rewrite length_le4 in RDU.
  pose proof (crk_rd_all _ _ _ CK) as RDC. rewrite length_le8 in RDC.
  unfold ASAN_K in RDC.
  do 11 step.
  step. if_false.
  do 2 step.
  crk_memF ltac:(fun mm => apply evtF_done; exists mm, (Z_to_bv 64 0), v8, v16).
  replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; crk_regs; try crk_w.
  all: apply crk_sp1_eq; lia.
Qed.

(* A store at offset 0 of a word base w writes `write_to_mem m w`, which the store transport of lib/Lib/StepF.v
   reads in the form `wa (A + Z.of_nat k)`. *)
Lemma crk_wa0 : forall w : word, wa (bv_unsigned w + Z.of_nat 0) = w.
Proof. intros w. unfold wa. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Ltac crk_fix0 :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m ?w ?bs) _) =>
      is_var w; rewrite <- (crk_wa0 w); mem_after_store_opt
  end.

(* ---- cr_seg1_F: +0x78 (the return of the stack malloc, a0 = F) -> __asan_memset (0x510d0), ra = +0x134 ---- *)

(* The frame's sixteen shadow bytes as +0xe0 .. +0x120 write them: 0xf1 over the left redzone, 0 over v, 0xf3 over the
   right redzone. *)
Definition crk_sh_entry : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13));
   C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].

Lemma crk_bnez : forall x, 0 < x < 2 ^ 64 -> negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) = true.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x 0)) by lia. reflexivity.
Qed.

Lemma cr_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (fF : Z) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j24 h24 sh16 : list byte),
    4096 <= fF -> fF + 128 <= bv_unsigned s1 ->
    fF / 8 + ASAN_K + 16 <= fF \/ fF + 128 <= fF / 8 + ASAN_K ->
    fF / 8 + ASAN_K + 16 <= bv_unsigned s1 ->
    bv_unsigned s1 + 24 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned s1) [CB 24 j24] ->
    rw_cells rsegs m fF [CB 24 h24] ->
    rw_cells rsegs m (fF / 8 + ASAN_K) [CB 16 sh16] ->
    ExecF.rng RNG (bv_unsigned s1) 24 -> ExecF.rng RNG fF 24 ->
    ExecF.rng RNG (fF / 8 + ASAN_K) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 x0 x16,
         ms' = MS (mkR (Z_to_bv 64 0x808b0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fF + 32))
                    (Z_to_bv 64 0x5a) (Z_to_bv 64 0x30) a3 a4 a5 a6 a7 (Z_to_bv 64 fF) (Z_to_bv 64 (fF + 32)) s4 s5 s6
                    (Z_to_bv 64 (fF / 8 + ASAN_K)) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 fF) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x510d0) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s1, bv_unsigned s1 + 24); (fF, fF + 24); (fF / 8 + ASAN_K, fF / 8 + ASAN_K + 16)] m m1 /\
         wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned s1) [CB 8 x0; C8 (Z_to_bv 64 fF); CB 8 x16] /\
         rw_cells rsegs m1 fF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x16e29); C8 (Z_to_bv 64 0x8077c)] /\
         rw_cells rsegs m1 (fF / 8 + ASAN_K) crk_sh_entry)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fF) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 ASAN_K)
               s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x807f4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 fF F fc m
    j24 h24 sh16 HF0 HFs HSHF HSHs Hs1 SC HD SH RSC RHD RSH.
  pose proof (zr_word s1) as Rs1. unfold inr64 in Rs1.
  pose proof (munch_refl [(bv_unsigned s1, bv_unsigned s1 + 24); (fF, fF + 24);
                (fF / 8 + ASAN_K, fF / 8 + ASAN_K + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold ASAN_K in *.
  assert (HF8 : 0 <= fF / 8) by (apply Z.div_pos; lia).
  assert (HFr : 0 <= fF < 2 ^ 64) by lia.
  do 3 step. step. if_true_by (crk_bnez fF ltac:(lia)).
  do 14 step.
  setreg 23 (Z_to_bv 64 (fF / 8 + 2147450880)) ltac:(crk_w).
  do 21 step.
  crk_memF ltac:(fun mm => apply evtF_done; exists mm).
  exists (firstn 8 j24), (skipn 16 j24).
  split; [f_equal; crk_regs; try crk_w|].
  split; [replace (fF / 8 + 2147450896) with (fF / 8 + 2147450880 + 16) by lia; exact MU|].
  split; [exact WM|]. split; [exact SC|]. split; [exact HD|].
  unfold crk_sh_entry. exact SH.
Qed.

(* ---- cr_seg2_F: +0x134 (the return of __asan_memset) -> rp_slot_read (0x8160c), ra = +0x1a4 ---- *)

(* w_width (fuzz.h:55-63), inlined at +0x14c .. +0x160: a3 = 126 + 72 k - len, a0 = 2 k, s11 = 2 + 2 k at the loop
   head; the loop leaves to +0x170 with s11 = nch when len is 52 + 36 nch or that + 2, else to +0x164. *)
Section WW.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
  (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (len : Z)
  (Q : machine_state -> Prop).
Hypothesis Hlen : 0 <= len <= 1600.

Local Abbreviation WST pc x10 x13 x27 :=
  (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 2) (Z_to_bv 64 38) x13 x14 x15 x16 x17 x18 x19 x20
           x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Lemma cr_ww_loop : forall j k, Z.of_nat j + k = 19 -> 0 <= k ->
  (forall x10 x13 n, PCR.ww_go (S j) (2 + 2 * k) len = n -> 2 <= n <= 40 ->
     ExecF.evtF rsegs RNG Q (WST 0x808ec x10 x13 (Z_to_bv 64 n))) ->
  (forall x10 x13 x27, PCR.ww_go (S j) (2 + 2 * k) len = -1 -> ExecF.evtF rsegs RNG Q (WST 0x808e0 x10 x13 x27)) ->
  ExecF.evtF rsegs RNG Q (WST 0x808c8 (Z_to_bv 64 (2 * k)) (Z_to_bv 64 (126 + 72 * k - len)) (Z_to_bv 64 (2 + 2 * k))).
Proof.
  induction j as [|j IH]; intros k Hk H0 KF KN.
  all: step; rewrite PCR.bveqb_lit by lia.
  all: destruct (Z.eqb_spec (126 + 72 * k - len) 2) as [E1|E1]; cbv iota.
  1,3: eapply KF; [cbn [PCR.ww_go]; rewrite (proj2 (Z.eqb_eq len (52 + (2 + 2 * k) * 36))) by lia; reflexivity | lia].
  all: step; rewrite PCR.bveqb_lit by lia.
  all: destruct (Z.eqb_spec (126 + 72 * k - len) 0) as [E2|E2]; cbv iota.
  1,3: eapply KF; [cbn [PCR.ww_go]; rewrite (proj2 (Z.eqb_neq len (52 + (2 + 2 * k) * 36))) by lia;
                   rewrite (proj2 (Z.eqb_eq len (52 + (2 + 2 * k) * 36 + 2))) by lia; reflexivity | lia].
  all: do 4 step; rewrite PCR.bvltu_lit by lia.
  all: rewrite (unsigned_lit (2 + 2 * k)), PCR.sw32 by lia.
  - rewrite (proj2 (Z.ltb_lt 38 (2 * k + 2))) by lia. cbv iota.
    apply KN. cbn [PCR.ww_go]. rewrite (proj2 (Z.eqb_neq len _)), (proj2 (Z.eqb_neq len _)) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge 38 (2 * k + 2))) by lia. cbv iota.
    replace (2 * k + 2) with (2 * (k + 1)) by lia.
    replace (126 + 72 * k - len + 72) with (126 + 72 * (k + 1) - len) by lia.
    replace (2 + 2 * k + 2) with (2 + 2 * (k + 1)) by lia.
    apply (IH (k + 1)); [lia | lia | |].
    + intros x10 x13 n E R. apply KF; [|exact R]. rewrite <- E. cbn [PCR.ww_go].
      rewrite (proj2 (Z.eqb_neq len _)), (proj2 (Z.eqb_neq len _)) by lia. cbn [orb].
      replace (2 + 2 * k + 2) with (2 + 2 * (k + 1)) by lia. reflexivity.
    + intros x10 x13 x27 E. apply KN. rewrite <- E. cbn [PCR.ww_go].
      rewrite (proj2 (Z.eqb_neq len _)), (proj2 (Z.eqb_neq len _)) by lia. cbn [orb].
      replace (2 + 2 * k + 2) with (2 + 2 * (k + 1)) by lia. reflexivity.
Qed.
End WW.

(* A shadow byte k that allows its byte, at the `bnez` on it: k = 0 falls
   through; otherwise the `andi` into reg / `blt` of the partial granule return to the load. Both arms reach the load
   with only reg changed, so the walk goes on from one goal, K, with reg generalized. *)
Ltac crk_chk SK U MB k reg :=
  lazymatch goal with
  | |- ExecF.evtF ?s ?RNG ?Q (MS ?R ?F (if _ then _ else ?pE) ?fc ?rv ?m ?ro) =>
      let Rf := eval pattern reg in R in
      lazymatch Rf with
      | ?g reg =>
        let K := fresh "K" in
        assert (K : forall x : word, ExecF.evtF s RNG Q (MS (g x) F pE fc rv m ro));
        [ clear reg; let x := fresh "a2" in intro x; cbv beta
        | let C := fresh "C" in let Cu := fresh "Cu" in destruct SK as [C|[C Cu]];
          [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]; exact (K reg)
          | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
            rewrite land7, ?U, (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb]; apply K ] ]
      end
  end.
Ltac crk_byte_cond H := zify_cond H; rewrite ?zxb_u in H.

Lemma crk_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Section S2.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s7 s9 t3 t4 t5 t6 wv wc ws wn : word)
  (RNG : ExecF.footprint) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
Hypothesis HN : bv_unsigned wn <= 1600.
Hypothesis HL : Z.of_nat (length bs) = bv_unsigned wn.
Hypothesis HB : 50 <= bv_unsigned wn ->
  bytes_at rsegs m (bv_unsigned wc) bs /\ addressable m (bv_unsigned wc) 18 /\
  ExecF.rng RNG (bv_unsigned wc) 18 /\
  ExecF.rng RNG (shadow_addr (bv_unsigned wc)) (shadow_addr (bv_unsigned wc + 18 - 1) - shadow_addr (bv_unsigned wc) + 1).

Local Abbreviation GOT := (PSR.rp_slot_read_model (bv_unsigned wn) bs (bv_signed ws)).
Local Abbreviation WID := (PSW.rp_slot_width_model (bv_unsigned wn) bs (bv_signed ws)).

(* The state at the call of rp_slot_read (+0x1a0): a0 .. a3 = c, len, slot, v; s10 = the harness's want, which is
   rp_slot_read's answer; s11 = the width when the read is taken. *)
Definition cr_p2 : machine_state -> Prop := fun ms' => exists s11',
  ms' = MS (mkR (Z_to_bv 64 0x80920) sp gp tp t0 t1 t2 s0 s1 wc wn ws wv a4 a5 a6 a7 s2 wv wc ws wn s7
              (Z_to_bv 64 ASAN_K) s9 (Z_to_bv 64 GOT) s11' t3 t4 t5 t6)
           F (Z_to_bv 64 0x8160c) fc None m (seg_rom rsegs) /\
  (GOT = 1 -> s11' = Z_to_bv 64 WID).

Local Abbreviation ST2 pc x10 x11 x12 x13 x26 x27 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 wv wc ws wn s7 (Z_to_bv 64 ASAN_K) s9 x26 x27
           t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* +0x190: the four argument moves and `jal rp_slot_read`. *)
Lemma cr_call2 : forall x10 x11 x12 x13 x26 x27,
  x26 = Z_to_bv 64 GOT -> (GOT = 1 -> x27 = Z_to_bv 64 WID) ->
  ExecF.evtF rsegs RNG cr_p2 (ST2 0x8090c x10 x11 x12 x13 x26 x27).
Proof.
  intros x10 x11 x12 x13 x26 x27 E26 E27. subst x26.
  do 5 step. apply evtF_done. exists x27. split; [reflexivity | exact E27].
Qed.

(* +0x18c: `mv s10, zero` on a declined read. *)
Lemma cr_zero2 : forall x10 x11 x12 x13 x26 x27, GOT = 0 ->
  ExecF.evtF rsegs RNG cr_p2 (ST2 0x80908 x10 x11 x12 x13 x26 x27).
Proof.
  intros x10 x11 x12 x13 x26 x27 G. step. apply cr_call2.
  - rewrite G. reflexivity.
  - intros E. rewrite G in E. discriminate E.
Qed.

(* +0x170: c[16] and c[17] behind their shadow bytes (the report arms at +0x490 / +0x49c are not taken: the bytes are
   addressable), the slot's sign and the width's, and the want into s10 (fuzz_wire.c:218). *)
Lemma cr_b16_F : forall x10 x11 x12 x13 x26 W,
  50 <= bv_unsigned wn -> W = PCR.w_width_model (bv_unsigned wn) -> (W = -1 \/ 2 <= W <= 40) ->
  ExecF.evtF rsegs RNG cr_p2 (ST2 0x808ec x10 x11 x12 x13 x26 (Z_to_bv 64 W)).
Proof.
  intros x10 x11 x12 x13 x26 W H50 EW RW.
  destruct (HB H50) as (BA & ADR & RBUF & RSH).
  pose proof (zr_word wc) as Rwc. unfold inr64 in Rwc.
  pose proof (zr_word wn) as Rwn. unfold inr64 in Rwn.
  pose proof (zr_word ws) as Rws. unfold inr64 in Rws.
  pose proof (crk_shadow_byte_rng RNG (bv_unsigned wc) 18 16 ltac:(lia) RSH) as RS16.
  pose proof (crk_shadow_byte_rng RNG (bv_unsigned wc) 18 17 ltac:(lia) RSH) as RS17.
  clear RSH.
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 16 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
  destruct (AB 17 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
  clear AB.
  unfold shadow_addr, shadow_ok, ASAN_K in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP16, APP17, PE.
  assert (LB : (18 <= length bs)%nat) by lia.
  pose proof (bytes_nth m _ bs 16 BA ltac:(lia)) as F16.
  pose proof (bytes_nth m _ bs 17 BA ltac:(lia)) as F17.
  change (Z.of_nat 16) with 16 in F16. change (Z.of_nat 17) with 17 in F17.
  pose proof (Z.mod_pos_bound (bv_unsigned wc + 16) 8 ltac:(lia)) as MB16.
  pose proof (Z.mod_pos_bound (bv_unsigned wc + 17) 8 ltac:(lia)) as MB17.
  destruct (PCR.ww_facts (bv_unsigned wn) ltac:(lia)) as [WF _]. rewrite <- EW in WF.
  assert (SW : bv_swrap 64 (bv_unsigned wn) = bv_unsigned wn)
    by (apply bv_swrap_small; change (bv_half_modulus 64) with (2^63); lia).
  (* c[16] *)
  step. gen_addi wc w16 U16.
  pose proof (rng_sub' _ _ _ (bv_unsigned w16) 1 RBUF ltac:(lia)) as RW16.
  step. gen_shr w16 g16 G16. rewrite U16 in G16.
  step. gen_addi g16 h16 H16.
  pose proof (rng_sub' _ _ _ (bv_unsigned h16) 1 RS16 ltac:(lia)) as RH16.
  pose proof (rdw0 m h16 _ _ MK16 ltac:(lia)) as R. step. clear R.
  step.
  crk_chk SK16 U16 MB16 k16 x12.
  pose proof (rdw0 m w16 _ _ F16 ltac:(lia)) as R. step. clear R.
  step. if_cases HC16.
  2: { (* c[16] <> 0: declined *)
    crk_byte_cond HC16. apply cr_zero2. apply PCR.srm_zero. right; left. unfold PSW.slot_byte. lia. }
  crk_byte_cond HC16.
  (* c[17] *)
  step. gen_addi wc w17 U17.
  pose proof (rng_sub' _ _ _ (bv_unsigned w17) 1 RBUF ltac:(lia)) as RW17.
  step. gen_shr w17 g17 G17. rewrite U17 in G17.
  step. gen_addi g17 h17 H17.
  pose proof (rng_sub' _ _ _ (bv_unsigned h17) 1 RS17 ltac:(lia)) as RH17.
  pose proof (rdw0 m h17 _ _ MK17 ltac:(lia)) as R. step. clear R.
  step.
  crk_chk SK17 U17 MB17 k17 a2.
  step. step.
  assert (FC : PFC.rp_frame_channels_model (bv_swrap 64 (bv_unsigned wn)) = W) by (rewrite SW; congruence).
  if_cases HS5.
  { (* slot < 0: declined *)
    unfold bv_lts in HS5. rewrite (PCR.signed_lit 0) in HS5 by lia. apply Z.ltb_lt in HS5.
    apply cr_call2.
    - f_equal. symmetry. apply PCR.srm_zero. right; right; right; left. exact HS5.
    - intros E. rewrite PCR.srm_zero in E by (right; right; right; left; exact HS5). discriminate E. }
  unfold bv_lts in HS5. rewrite (PCR.signed_lit 0) in HS5 by lia. apply Z.ltb_ge in HS5.
  pose proof (rdw0 m w17 _ _ F17 ltac:(lia)) as R. step. clear R.
  step. if_cases HC17.
  { (* c[17] <> 0: declined *)
    crk_byte_cond HC17. apply cr_call2.
    - f_equal. symmetry. apply PCR.srm_zero. right; right; left. unfold PSW.slot_byte. lia.
    - intros E. rewrite PCR.srm_zero in E by (right; right; left; unfold PSW.slot_byte; lia). discriminate E. }
  crk_byte_cond HC17.
  step. if_cases HW0.
  { (* the width is -1: declined *)
    unfold bv_lts in HW0. rewrite (PCR.signed_lit 0), (PCR.signed_lit W) in HW0 by lia. cbn [negb] in HW0.
    apply cr_call2.
    - f_equal. symmetry. apply PCR.srm_zero. right; right; right; right; left. rewrite FC.
      destruct RW as [RW|RW]; [lia|]. destruct (Z.ltb_spec 0 W); cbn in HW0; [discriminate HW0 | lia].
    - intros E. rewrite PCR.srm_zero in E; [discriminate E|]. right; right; right; right; left. rewrite FC.
      destruct RW as [RW|RW]; [lia|]. destruct (Z.ltb_spec 0 W); cbn in HW0; [discriminate HW0 | lia]. }
  unfold bv_lts in HW0. rewrite (PCR.signed_lit 0), (PCR.signed_lit W) in HW0 by lia. cbn [negb] in HW0.
  assert (WP : 2 <= W <= 40) by (destruct RW as [RW|RW]; [rewrite RW in HW0; vm_compute in HW0; discriminate HW0 | exact RW]).
  step. step.
  pose proof (PCR.signed_nonneg ws HS5) as SU.
  destruct (Z.ltb_spec (bv_signed ws) W) as [LT|GE].
  - destruct (PCR.srm_one (bv_unsigned wn) bs (bv_signed ws) H50 ltac:(unfold PSW.slot_byte; lia)
      ltac:(unfold PSW.slot_byte; lia) ltac:(lia)) as [M1 M2].
    apply cr_call2.
    + rewrite M1, v_sltu_b2z, SU, unsigned_lit by lia. rewrite (proj2 (Z.ltb_lt _ _) LT). reflexivity.
    + intros _. rewrite M2, FC. reflexivity.
  - apply cr_call2.
    + rewrite PCR.srm_zero by (right; right; right; right; right; lia).
      rewrite v_sltu_b2z, SU, unsigned_lit by lia. rewrite (proj2 (Z.ltb_ge _ _) GE). reflexivity.
    + intros E. rewrite PCR.srm_zero in E by (right; right; right; right; right; lia). discriminate E.
Qed.


(* +0x134 .. the call: the width loop (cr_ww_loop), then `bltu len, 50` when it found no width, then cr_b16_F. *)
Lemma cr_seg2_F : forall x10 x11 x12 x13 x26 x27,
  ExecF.evtF rsegs RNG cr_p2 (ST2 0x808b0 x10 x11 x12 x13 x26 x27).
Proof.
  intros x10 x11 x12 x13 x26 x27.
  pose proof (zr_word wn) as Rwn. unfold inr64 in Rwn.
  do 6 step.
  setreg 10 (Z_to_bv 64 (2 * 0)) ltac:(reflexivity).
  setreg 13 (Z_to_bv 64 (126 + 72 * 0 - bv_unsigned wn)) ltac:(crk_w).
  setreg 27 (Z_to_bv 64 (2 + 2 * 0)) ltac:(reflexivity).
  apply (cr_ww_loop ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 wv wc ws wn s7 (Z_to_bv 64 ASAN_K) s9 x26 t3 t4 t5 t6
           RNG F fc m (bv_unsigned wn) cr_p2 ltac:(lia) 19 0 ltac:(lia) ltac:(lia)).
  - intros y10 y13 n E R.
    change (PCR.ww_go 20 (2 + 2 * 0) (bv_unsigned wn)) with (PCR.w_width_model (bv_unsigned wn)) in E.
    destruct (PCR.ww_facts (bv_unsigned wn) ltac:(lia)) as [_ WF2]. rewrite E in WF2.
    apply (cr_b16_F y10 (Z_to_bv 64 2) (Z_to_bv 64 38) y13 x26 n); [lia | symmetry; exact E | right; exact R].
  - intros y10 y13 y27 E.
    change (PCR.ww_go 20 (2 + 2 * 0) (bv_unsigned wn)) with (PCR.w_width_model (bv_unsigned wn)) in E.
    do 3 step. unfold bv_ltu. rewrite (unsigned_lit 50) by lia.
    destruct (Z.ltb_spec (bv_unsigned wn) 50); cbv iota.
    + apply cr_zero2. apply PCR.srm_zero. left. lia.
    + apply (cr_b16_F (Z_to_bv 64 50) (Z_to_bv 64 2) (Z_to_bv 64 38) y13 x26 (-1)); [lia | symmetry; exact E | left; reflexivity].
Qed.
End S2.

(* ---- cr_seg4_F: +0x35c (the loop done) -> the return ---- *)

Lemma crk_beqz : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.

Definition crk_sh_exit : list cell :=
  [C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11));
   C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11));
   C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11));
   C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11))].

Lemma cr_seg4_F :
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31 w0 : word)
         (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (fF FL : Z) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sh16 hd8 fl1 j24 : list byte),
    4096 <= fF -> fF + 128 <= bv_unsigned w0 - 128 ->
    fF / 8 + ASAN_K + 16 <= fF \/ fF + 128 <= fF / 8 + ASAN_K ->
    fF / 8 + ASAN_K + 16 <= bv_unsigned w0 - 128 ->
    (FL + 1 <= fF \/ fF + 128 <= FL) -> (FL + 1 <= fF / 8 + ASAN_K \/ fF / 8 + ASAN_K + 16 <= FL) ->
    0 <= FL -> FL + 1 <= bv_unsigned w0 - 128 -> 128 <= bv_unsigned w0 ->
    rw_cells rsegs m (fF / 8 + ASAN_K) [CB 16 sh16] ->
    rw_cells rsegs m fF [CB 8 hd8] ->
    bytes_at rsegs m (fF + 120) (le8 (wa FL)) ->
    rw_cells rsegs m FL [CB 1 fl1] ->
    rw_cells rsegs m (bv_unsigned w0 + -128) (CB 24 j24 :: crk_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    ExecF.rng RNG (fF / 8 + ASAN_K) 16 -> ExecF.rng RNG fF 8 -> ExecF.rng RNG (fF + 120) 8 ->
    ExecF.rng RNG FL 1 -> ExecF.rng RNG (bv_unsigned w0 - 128) 128 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 y10,
         ms' = MS (mkR ra w0 x3 x4 x5 x6 x7 s0 s1 y10 x11 x12 x13 x14 x15 x16 x17
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                  F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
         munch [(fF / 8 + ASAN_K, fF / 8 + ASAN_K + 16); (fF, fF + 8); (FL, FL + 1)] m m1 /\
         wmono rsegs m m1 /\
         rw_cells rsegs m1 FL [C1 (Z_to_bv 8 0)] /\
         rw_cells rsegs m1 (fF / 8 + ASAN_K) crk_sh_exit /\
         rw_cells rsegs m1 fF [C8 (Z_to_bv 64 0x45e0360e)])
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 w0 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fF) x19 x20 x21 x22
               (Z_to_bv 64 (fF / 8 + ASAN_K)) x24 (Z_to_bv 64 fF) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x80ad8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31 w0
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fF FL F fc m sh16 hd8 fl1 j24
    HF0 HFs HSHF HSHs HFL1 HFL2 HFL3 HFL4 Hw0 SH HD FLW FLB FR RSH RHD RFW RFL RFR.
  pose proof (zr_word w0) as Rw0. unfold inr64 in Rw0.
  unfold crk_saved in FR.
  pose proof (munch_refl [(fF / 8 + ASAN_K, fF / 8 + ASAN_K + 16); (fF, fF + 8); (FL, FL + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold ASAN_K in *.
  assert (HF8 : 0 <= fF / 8) by (apply Z.div_pos; lia).
  assert (HFr : 0 <= fF < 2 ^ 64) by lia.
  do 7 step.
  do 2 step. step.
  step. if_false_by (crk_beqz fF ltac:(lia)).
  do 17 step.
  pose proof (crk_rd_all _ _ _ FLW) as RDF. rewrite length_le8 in RDF.
  step. clear RDF.
  step. step.
  do 16 step.
  crk_memF ltac:(fun mm => apply evtF_done; exists mm, (Z_to_bv 64 FL)).
  split; [reflexivity|].
  split; [replace (fF / 8 + 2147450896) with (fF / 8 + 2147450880 + 16) by lia; exact MU|].
  split; [exact WM|]. split; [exact FLB|]. split; [unfold crk_sh_exit; exact SH | exact HD].
Qed.
