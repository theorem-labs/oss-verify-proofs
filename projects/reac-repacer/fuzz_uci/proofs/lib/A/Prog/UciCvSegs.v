(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 245 of its 281 lines of code are new or changed and 428 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the straight-line segments of reac-repacer/fuzz_uci's check_value in image A, in the form
   and with the helpers of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_segs.v (origin/ossv/recipes 88154566652a:
   crt_seg1_F .. crt_seg9_F, Z_to_le_bytes_to_Z, crt_le8_of_bytes, crt_c8s, crt_rw_c8s, crt_frame_words, crt_regs,
   crt_usub, crt_shift, crt_w, crt_finF, crt_memF, crt_pc) and of its lib/A/Prog/ReacDecodeLib.v rd_all. *)
(* UciCvSegs: the footprint (ExecF.evtF) runs of the straight-line segments of check_value (fuzz_uci.asan 0x7f62c),
   each from a cut point of lib/A/Prog/UciCvIface.v to the next call, stepped by lib/Lib/StepF.v:
     cv_seg1_F   entry -> malloc(n + (n == 0)): the 0x40-byte frame (s5 .. s0, ra at 8(sp) .. 0x38(sp)), the shadow
                 offset through GOT_CELL_K -> CELL_K, s0 := cur, s3 := r, s4 := n;
     cv_seg2p_F  CV_RET_MALLOC, n > 0 -> __asan_memcpy(P, r, n) (the `beqz a0` and `beqz s4` not taken);
     cv_seg2z_F  CV_RET_MALLOC, n = 0 -> rp_uci_int(P, 0, cur);
     cv_seg3_F   CV_RET_MEMCPY -> rp_uci_int(P, n, cur);
     cv_segz_F   CV_RET_RUI0 (n = 0) -> CV_TEST: s2 := a0;
     cv_test_F   CV_TEST -> free(P): `sext.w s0, s0` and the property test `bne s2, s0` (not taken: s2 = s0);
     cv_end_F    CV_RET_FREE -> the return: a0 := s2, ra and s0 .. s5 reloaded from the frame, sp += 0x40, `ret`.
   The inlined expected_value between CV_RET_RUI and CV_TEST is lib/A/Prog/UciCvIface.v cv_ev_stmt_F. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import AsanKA AsanKAProof UciCvIface.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- helpers (crtA_segs.v:29-122, ReacDecodeLib.v:42-47) ---- *)

Lemma cv_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
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

Lemma cv_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply cv_le_bytes_to_Z.
Qed.

Fixpoint cv_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: cv_c8s n' (skipn 8 bs)
  end.

Lemma cv_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (cv_c8s n bs) /\ cells_bytes (cv_c8s n bs) = bs /\ cells_size (cv_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [cv_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite cv_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma cv_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (cv_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (cv_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 64 bytes, read as 8 words. *)
Lemma cv_frame_words : forall m A bs, rw_cells rsegs m A [CB 64 bs] ->
  exists v0 v8 v16 v24 v32 v40 v48 v56 : word,
    rw_cells rsegs m A [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56].
Proof.
  intros m A bs H. apply (cv_rw_c8s rsegs m A 8 bs) in H. cbn [cv_c8s] in H. do 8 eexists. exact H.
Qed.

Lemma cv_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Ltac cv_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cv_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cv_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac cv_w := cv_shift; cv_usub; cv_shift; cv_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac cv_finF := apply evtF_done; f_equal; cv_regs; cv_w.
Ltac cv_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* StepF's step reads the start pc; every pc here is a UciCvIface name, so each proof first computes every such
   closed name of its goal to its value (as crtA_loop.v crt_lits does for CRT_AT). *)
Ltac cv_lit X := let v := eval vm_compute in X in change X with v.
Ltac cv_lits :=
  repeat match goal with
  | |- context [CV_RET_MALLOC] => cv_lit CV_RET_MALLOC
  | |- context [CV_RET_MEMCPY] => cv_lit CV_RET_MEMCPY
  | |- context [CV_RET_RUI0] => cv_lit CV_RET_RUI0
  | |- context [CV_RET_RUI] => cv_lit CV_RET_RUI
  | |- context [CV_RET_FREE] => cv_lit CV_RET_FREE
  | |- context [CV_TEST] => cv_lit CV_TEST
  | |- context [CV_MALLOC] => cv_lit CV_MALLOC
  | |- context [CV_FREE] => cv_lit CV_FREE
  | |- context [CV_MEMCPY] => cv_lit CV_MEMCPY
  | |- context [CV_RUI] => cv_lit CV_RUI
  | |- context [CV_AT ?o] => cv_lit (CV_AT o)
  | |- context [CV_ENTRY] => cv_lit CV_ENTRY
  end.

(* ---- cv_seg1_F: CV_ENTRY -> malloc (ra = CV_RET_MALLOC) ---- *)
Lemma cv_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n cur lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    CELL_K + 8 <= bv_unsigned sp - 64 ->
    0 <= n <= 255 ->
    ExecF.rng RNG (bv_unsigned sp - 64) 64 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 v0,
         ms' = MS (mkR (Z_to_bv 64 CV_RET_MALLOC) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2
                    (Z_to_bv 64 cur) s1 (Z_to_bv 64 (Z.max n 1)) (Z_to_bv 64 n) (Z_to_bv 64 cur) a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 r) (Z_to_bv 64 n) (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CV_MALLOC) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 64) (C8 v0 :: cv_fr s5 s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 n) (Z_to_bv 64 cur) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CV_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r n cur lo
    ST LO GCK CK HLOW HN RFR RGC RCK.
  cv_lits.
  unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  destruct (cv_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & FR'). clear FR.
  rename FR' into FR.
  do 11 step.
  (* the stores moved the two cell facts to the new memory (StepF's store transport) *)
  unfold ASAN_K in CK.
  pose proof (cv_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (cv_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 6 step.
  cv_memF ltac:(fun mm => apply evtF_done; exists mm, v0).
  replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; cv_regs; try cv_w.
  (* a0 = n + (n <u 1), the `seqz` / `add` pair *)
  all: f_equal; unfold v_sltiu; rewrite (unsigned_lit n) by lia;
       replace (bv_wrap 64 1) with 1 by reflexivity;
       destruct (Z.ltb_spec n 1); rewrite unsigned_lit by lia; lia.
Qed.

(* ---- cv_seg2p_F: CV_RET_MALLOC with a0 = P > 0 and s4 = n > 0 -> __asan_memcpy(P, r, n) ---- *)
Lemma cv_seg2p_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n : Z),
    0 < P < 2 ^ 64 -> 0 < n < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CV_RET_MEMCPY) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 P) s3
                    (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 n) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CV_MEMCPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 n) s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CV_RET_MALLOC) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n HP HN.
  cv_lits.
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  step. if_false.
  step. step. if_false.
  do 3 step.
  cv_finF.
Qed.

(* ---- cv_seg2z_F: CV_RET_MALLOC with a0 = P > 0 and s4 = 0 -> rp_uci_int(P, 0, cur) ---- *)
Lemma cv_seg2z_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
    0 < P < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CV_RET_RUI0) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 0)
                    s0 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CV_RUI) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CV_RET_MALLOC) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P HP.
  cv_lits.
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  step. if_false.
  step. step. if_true.
  do 3 step.
  cv_finF.
Qed.

(* ---- cv_seg3_F: CV_RET_MEMCPY -> rp_uci_int(s1, s4, s0) (ra = CV_RET_RUI) ---- *)
Lemma cv_seg3_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CV_RET_RUI) sp gp tp t0 t1 t2 s0 s1 s1 s4 s0 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CV_RUI) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CV_RET_MEMCPY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  cv_lits.
  do 4 step.
  cv_finF.
Qed.

(* ---- cv_segz_F: CV_RET_RUI0 (n = 0) -> CV_TEST: s2 := a0 ---- *)
Lemma cv_segz_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CV_TEST) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CV_RET_RUI0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  cv_lits.
  do 2 step.
  cv_finF.
Qed.

(* `sext.w` (addiw rd, rs, 0) of a word holding an int is that word. *)
Lemma cv_swrap_int : forall v, INT_MIN <= v <= INT_MAX ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0)) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold INT_MIN, INT_MAX in Hv. rewrite Z.add_0_r, unsigned_lit_wrap.
  f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  Z.div_mod_to_equations. lia.
Qed.

Lemma cv_word_int : forall (w : word) v, bv_unsigned w = v mod 2 ^ 64 -> w = Z_to_bv 64 v.
Proof.
  intros w v Hw. apply bv_eq. rewrite Hw, Z_to_bv_unsigned. reflexivity.
Qed.

(* ---- cv_test_F: CV_TEST -> free(s1) (ra = CV_RET_FREE); the property test not taken ---- *)
Lemma cv_test_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
    INT_MIN <= v <= INT_MAX -> bv_unsigned s0 = v mod 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CV_RET_FREE) sp gp tp t0 t1 t2 (Z_to_bv 64 v) s1 s1 a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 v) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CV_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v) s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 CV_TEST) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v
    HV HS0.
  cv_lits.
  rewrite (cv_word_int s0 v HS0).
  step.
  rewrite (cv_swrap_int v HV).
  step.
  if_false.
  do 2 step.
  cv_finF.
Qed.

(* ---- cv_end_F: CV_RET_FREE -> the return: a0 := s2, the frame reloaded, sp += 0x40, `ret` ---- *)
Lemma cv_end_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 c5 c4 c3 c2 c1 c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) (C8 v0 :: cv_fr c5 c4 c3 c2 c1 c0 cra) ->
    bv_unsigned sp + 64 < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 c0 c1 s2 a1 a2 a3 a4 a5 a6 a7
                    c2 c3 c4 c5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CV_RET_FREE) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 c5 c4 c3 c2 c1 c0 cra FR HSP RFR.
  cv_lits.
  unfold cv_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 10 step.
  apply evtF_done. f_equal.
Qed.
