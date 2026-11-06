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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_copy_cgW_segs.v, with its module paths and numbers changed; 123 of its 189 lines of code are new or changed and 457 lines of the source are left out. *)
(* WireCmSeg1: the first footprint run of the image-B walk of reac-repacer/fuzz_wire's check_meter
   (fuzz_wire.asan-ubsan 0x8016c = wire_sigma WS_check_meter), lib/B/Prog/WireCmIface.v cm_seg1_stmt: the entry ->
   the `jal __asan_stack_malloc_0` at 0x801d8 (ra = CM_RET_SM = 0x801dc), stepped by lib/Lib/StepF.v:
     0x8016c `addi sp, sp, -128`, 0x80170 `sd zero, 0(sp)`, 0x80174 .. 0x801a0 ra, s0 .. s10 at 120(sp) .. 32(sp);
     0x801a4 `addi s0, sp, 128`, 0x801a8 `andi sp, sp, -32`, 0x801ac `mv s1, sp`, 0x801b0 `mv s4, a1`;
     0x801b4 / 0x801b8 `auipc`, 0x801bc `ld a2` (the GOT word GOT_UAR), 0x801c0 `ld a1` (the GOT word GOT_CELL_K),
     0x801c4 `lw a2, 0(a2)` (UAR, 1 sign-extended), 0x801c8 `ld s8, 0(a1)` (the shadow offset in CELL_K);
     0x801cc `mv s3, a0`, 0x801d0 `beqz a2` (not taken: a2 = 1), 0x801d4 `li a0, 64`, 0x801d8 `jal`.
   The form and the frame-word helpers are reac-repacer/fuzz_uci's lib/B/Prog/UciCvBSegs.v cv_seg1_F (recipes commit
   0295462466b2): carve_frame, the 128 carved bytes read as 16 words, the GOT and cell bytes read through cv_rd_all.
   The realign `andi sp, sp, -32` is reac-repacer/fuzz_uci's lib/B/Prog/UciCcKit.v ucc_land_m32 (recipes commit
   0295462466b2); the cell split is reac-repacer/fuzz_wire's lib/Prog/check_read.v rw_cells_app (recipes commit
   4029ae11bb5e). The slot word at cm_sp1 sp + 24 is the frame's word at offset 24 when sp mod 32 = 0 and at offset 8
   when sp mod 32 = 16; the twelve saves are the frame's last twelve words, at sp - 96. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr WireCmIface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- helpers (UciCvBSegs.v cv_le_bytes_to_Z .. cv_rd_all, copied; check_read.v rw_cells_app, copied) ---- *)

Lemma cm_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
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

Lemma cm_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply cm_le_bytes_to_Z.
Qed.

Fixpoint cm_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: cm_c8s n' (skipn 8 bs)
  end.

Lemma cm_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (cm_c8s n bs) /\ cells_bytes (cm_c8s n bs) = bs /\ cells_size (cm_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [cm_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite cm_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma cm_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (cm_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (cm_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 128 bytes, read as 16 words. *)
Lemma cm_frame_words : forall m A bs, rw_cells rsegs m A [CB 128 bs] ->
  exists v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 : word,
    rw_cells rsegs m A [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56;
                        C8 v64; C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120].
Proof.
  intros m A bs H. apply (cm_rw_c8s rsegs m A 16 bs) in H. cbn [cm_c8s] in H. do 16 eexists. exact H.
Qed.

Lemma cm_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma cm_rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (H1 & H2 & H3)].
    rewrite (cells_bytes_length cs1 W1) in B2.
    split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]).
    + intros i Hi. apply H3. lia.
    + intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply H3. lia.
  - intros [[[W1 B1] (H1 & H2 & H3)] [[W2 B2] (K1 & K2 & K3)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))) as [L|L]; [apply H3; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply K3. lia.
Qed.

Lemma cm_rw_cells_cons : forall m A c cs,
  rw_cells rsegs m A (c :: cs) -> rw_cells rsegs m A [c] /\ rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs H. change (c :: cs) with ([c] ++ cs) in H.
  apply (proj1 (cm_rw_cells_app m A [c] cs)) in H. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

(* The frame after the prologue's stores: its words at offsets 8 and 24 (the two candidates for the slot at
   cm_sp1 sp + 24) and its last twelve words (the saves). *)
Lemma cm_frame_parts : forall m A (w0 w8 w16 w24 : word) cs,
  rw_cells rsegs m A (C8 w0 :: C8 w8 :: C8 w16 :: C8 w24 :: cs) ->
  rw_cells rsegs m (A + 8) [C8 w8] /\ rw_cells rsegs m (A + 24) [C8 w24] /\ rw_cells rsegs m (A + 32) cs.
Proof.
  intros m A w0 w8 w16 w24 cs H.
  apply cm_rw_cells_cons in H as [_ H]. apply cm_rw_cells_cons in H as [H8 H].
  apply cm_rw_cells_cons in H as [_ H]. apply cm_rw_cells_cons in H as [H24 H].
  cbn [csize] in H8, H24, H. change (Z.of_nat 8) with 8 in H8, H24, H.
  replace (A + 8 + 8 + 8) with (A + 24) in H24 by lia.
  replace (A + 8 + 8 + 8 + 8) with (A + 32) in H by lia.
  split; [exact H8 | split; [exact H24 | exact H]].
Qed.

(* `andi sp, sp, -32` on a symbolic sp (UciCcKit.v ucc_land_m32, copied). *)
Lemma cm_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
  intros x Hx.
  assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
  rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
  rewrite Z.land_ones, Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

Lemma cm_land_w : forall x : word, Z.land (bv_unsigned x) 18446744073709551584 = 32 * (bv_unsigned x / 32).
Proof.
  intros x. pose proof (zr_word x) as R. unfold inr64 in R.
  change 18446744073709551584 with (2 ^ 64 - 32). apply cm_land_m32. lia.
Qed.

Ltac cm_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cm_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cm_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac cm_w := cm_shift; cm_usub; cm_shift; cm_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
(* sp and s1 after the realign: 32 * ((sp0 - 128) / 32) *)
Ltac cm_sp_w :=
  lazymatch goal with |- context [cm_sp1 _] => idtac end;
  unfold cm_sp1;
  try change (bv_wrap 64 (-32)) with 18446744073709551584;
  rewrite ?cm_land_w;
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
    rewrite (unsigned_lit z) by (Z.div_mod_to_equations; lia) end;
  f_equal; Z.div_mod_to_equations; lia.
Ltac cm_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* StepF's step reads the start pc: each proof first computes every closed name of its goal to its value. *)
Ltac cm_lit X := let v := eval vm_compute in X in change X with v.
Ltac cm_lits :=
  repeat match goal with
  | |- context [CM_RET_SM] => cm_lit CM_RET_SM
  | |- context [CM_SMALLOC] => cm_lit CM_SMALLOC
  | |- context [CM_AT ?o] => cm_lit (CM_AT o)
  | |- context [CM_ENTRY] => cm_lit CM_ENTRY
  end.

(* ---- cm_seg1: CM_ENTRY -> __asan_stack_malloc_0 (ra = CM_RET_SM) ---- *)
Lemma cm_seg1 : cm_seg1_stmt.
Proof.
  unfold cm_seg1_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO A16 GCK CK GUA UA HLOW RFR RGC RCK RGU RU.
  cm_lits.
  unfold GOT_CELL_K, CELL_K, GOT_UAR, UAR, ASAN_K in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 128%nat ST.
  destruct (cm_frame_words _ _ _ FR)
    as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & v96 & v104 & v112 & v120 & FR').
  clear FR. rename FR' into FR.
  (* addi sp; sd zero; the twelve saves; addi s0; andi sp; mv s1; mv s4 *)
  do 18 step.
  (* the stores moved the four GOT / cell facts to the new memory (StepF's store transport) *)
  pose proof (cm_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (cm_rd_all _ _ _ CK) as RDK. rewrite length_le8 in RDK.
  pose proof (cm_rd_all _ _ _ GUA) as RDGU. rewrite length_le8 in RDGU.
  pose proof (cm_rd_all _ _ _ UA) as RDU. rewrite length_le4 in RDU.
  (* auipc a1; auipc a2; ld a2; ld a1; lw a2; ld s8; mv s3 *)
  do 7 step.
  (* beqz a2 (a2 = 1: not taken); li a0, 64; jal *)
  step. if_false.
  do 2 step.
  destruct (cm_frame_parts _ _ _ _ _ _ _ FR) as (F8 & F24 & FS).
  destruct (Z.eq_dec (bv_unsigned sp mod 32) 0) as [M0|M16].
  - cm_memF ltac:(fun mm => apply evtF_done; exists mm, v24).
    split; [|split; [|split; [exact WM|split]]].
    + f_equal; cm_regs; try cm_sp_w; try cm_w.
    + try replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) by lia. exact MU.
    + replace (cm_sp1 (bv_unsigned sp) + 24) with (bv_unsigned sp + -128 + 24)
        by (unfold cm_sp1; Z.div_mod_to_equations; lia).
      exact F24.
    + replace (bv_unsigned sp - 96) with (bv_unsigned sp + -128 + 32) by lia. exact FS.
  - cm_memF ltac:(fun mm => apply evtF_done; exists mm, v8).
    split; [|split; [|split; [exact WM|split]]].
    + f_equal; cm_regs; try cm_sp_w; try cm_w.
    + try replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) by lia. exact MU.
    + replace (cm_sp1 (bv_unsigned sp) + 24) with (bv_unsigned sp + -128 + 8)
        by (unfold cm_sp1; Z.div_mod_to_equations; lia).
      exact F8.
    + replace (bv_unsigned sp - 96) with (bv_unsigned sp + -128 + 32) by lia. exact FS.
Qed.
