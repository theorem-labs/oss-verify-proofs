(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 263 of its 300 lines of code are new or changed and 427 lines of the source are left out. *)
(* crtA_segs: port of a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs_F.v:1-252
   (crt_seg1_F .. crt_seg9_F), the footprint (ExecF.evtF) runs of the straight-line segments of check_round_trip in
   image A (fuzz_decode.asan).
   The addresses are re-based on the listing: every pc in a statement is a name of lib/A/Prog/crtA_iface.v
   (CRT_ENTRY, CRT_AT off with off = pc - entry, CRT_MALLOC / CRT_CALLOC / CRT_FREE / CRT_ENCODE / CRT_BCMP,
   CRT_LOOP_IN, CRT_LOOP_OUT); the frame list crt_fr and the constant CRT_A5 are crtA_iface's.
   The record imports lib/A/AsanRT.v, which is lib/A/AsanCells.v here (same names and bodies).  The record's
   proofs/libreac/fuzz_decode/lib/A/Spec/StrFun.v (on a working branch at dc455613c81) does not exist here: its
   lemma Z_to_le_bytes_to_Z is copied below, and byte_range (same statement) comes from lib/A/Prog/AsanKAProof.v.
   The helpers crt_segs_F.v takes from
   a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v are copied below, each
   with the lines it came from. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof ReacDecodeLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_iface.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- helpers ---- *)

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Spec/StrFun.v:420-433
   (that file does not exist on this branch). *)
Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
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

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:17-22
   (needed by crt_frame_words). *)
Lemma crt_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply Z_to_le_bytes_to_Z.
Qed.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:24-28
   (needed by crt_frame_words). *)
Fixpoint crt_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: crt_c8s n' (skipn 8 bs)
  end.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:30-41
   (needed by crt_frame_words). *)
Lemma crt_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (crt_c8s n bs) /\ cells_bytes (crt_c8s n bs) = bs /\ cells_size (crt_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [crt_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite crt_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:43-51
   (needed by crt_frame_words). *)
Lemma crt_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (crt_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (crt_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:53-59. *)
(* The carved 96 bytes, read as 12 words. *)
Lemma crt_frame_words : forall m A bs, rw_cells rsegs m A [CB 96 bs] ->
  exists v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 : word,
    rw_cells rsegs m A (crt_fr v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88).
Proof.
  intros m A bs H. apply (crt_rw_c8s rsegs m A 12 bs) in H. cbn [crt_c8s] in H. do 12 eexists. exact H.
Qed.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:61-65. *)
(* bv_signed of a small non-negative literal word. *)
Lemma crt_signed_lit : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec0 z (2^63)); lia.
Qed.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:67-71. *)
Ltac crt_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:73
   (used by crt_w). *)
Ltac crt_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:75
   (used by crt_w). *)
Ltac crt_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs.v:77-79. *)
Ltac crt_w := crt_shift; crt_usub; crt_shift; crt_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].

(* ---- the segments: a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_segs_F.v ---- *)

(* crt_segs_F.v:13-19: *)

(* Footprint twins of the straight-line segments of check_round_trip (A image, entry 0x80bc8, frame 96 bytes).
   crt_segK_F states crt_segK_stmt of crt_iface.v with a footprint RNG: the run is an ExecF.evtF run, each step's
   data accesses lie in RNG, and RNG holds the ranges the segment reads or writes:
     - seg1 stores the 12 saved registers into [sp-96, sp) and loads 8 bytes at GOT_CELL_K and 8 bytes at CELL_K;
     - seg2 .. seg8 read and write no memory;
     - seg9 loads the 12 saved registers from [sp, sp+96).
   The proofs follow crt_segs.v step for step, with StepF's step. *)

Ltac crt_finF := apply evtF_done; f_equal; crt_regs; crt_w.

Ltac crt_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* Not in the record (its start pcs were numerals): StepF's step reads the start pc, and the start pc of each
   statement here is a crtA_iface name, so compute that one pc term to its value inside the proof. *)
Ltac crt_pc := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let v := eval vm_compute in pc in change pc with v
  end.

(* ---- seg1: 0x80bc8 (entry) -> call of malloc(4*nch*ns) at 0x80c28 ---- *)
(*      listing: CRT_ENTRY -> call at CRT_AT 0x60, ra = CRT_AT 0x64.  Port of crt_segs_F.v:25-71. *)
Lemma crt_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (audio pcm nch ns lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp ->
    asan_cells m -> off_stk sp 96 GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    2 <= nch <= 127 -> 1 <= ns <= 12 -> 0 <= audio < 2^64 -> 0 <= pcm < 2^64 ->
    ExecF.rng RNG (bv_unsigned sp - 96) 96 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x64)) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
                    s0 (Z_to_bv 64 audio) (Z_to_bv 64 (4 * (nch * ns))) (Z_to_bv 64 pcm) (Z_to_bv 64 nch)
                    (Z_to_bv 64 ns) a4 a5 a6 a7 (Z_to_bv 64 ns) (Z_to_bv 64 nch) (Z_to_bv 64 (3 * (nch * ns)))
                    s5 (Z_to_bv 64 pcm) (Z_to_bv 64 (nch * ns)) (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_MALLOC) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp - 96) /\
         rw_cells rsegs m1 (bv_unsigned sp - 96) (crt_fr s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 audio) (Z_to_bv 64 pcm) (Z_to_bv 64 nch) (Z_to_bv 64 ns)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CRT_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m audio pcm nch
    ns lo ST LO CELLS DC HN HS HA HP RFR RGC RCK.
  crt_pc.
  unfold GOT_CELL_K in RGC. unfold CELL_K in RCK.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold off_stk, GOT_CELL_K, MIDEND in DC.
  carve_frame 96%nat ST.
  destruct (crt_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & FR').
  clear FR. unfold crt_fr in FR'. rename FR' into FR.
  do 17 step.
  match goal with H : munch _ m ?m1 |- _ => assert (CELLS1 : asan_cells m1)
    by (eapply asan_cells_munch; [exact CELLS | exact H | unfold MIDEND, GOT_CELL_K; lia]) end.
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 8 step.
  crt_memF ltac:(fun mm => apply evtF_done; exists mm).
  replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia.
  split; [|split; [exact MU|split; [exact WM|split; [exact ST|exact FR]]]].
  f_equal; crt_regs; crt_w.
Qed.

(* ---- seg2: 0x80c2c (a0 = P) -> call of malloc(8*nch) at 0x80c34 ---- *)
(*      listing: CRT_AT 0x64 -> call at CRT_AT 0x6c, ra = CRT_AT 0x70.  Port of crt_segs_F.v:73-92. *)
Lemma crt_seg2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nch : Z),
    s3 = Z_to_bv 64 nch -> 0 <= nch <= 127 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x70)) sp gp tp t0 t1 t2 a0 s1 (Z_to_bv 64 (8 * nch)) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_MALLOC) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x64)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nch
    E3 HN.
  crt_pc.
  subst s3.
  do 3 step.
  crt_finF.
Qed.

(* ---- seg3: 0x80c38 (a0 = Q) -> call of calloc(3*nn, 1) at 0x80c4c; the bnez s7 at 0x80c40 is taken ---- *)
(*      listing: CRT_AT 0x70 -> call at CRT_AT 0x84, ra = CRT_AT 0x88; the bnez at CRT_AT 0x78.
        Port of crt_segs_F.v:94-115. *)
Lemma crt_seg3_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nn : Z),
    s4 = Z_to_bv 64 (3 * nn) -> s7 = Z_to_bv 64 nn -> 1 <= nn <= 1524 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x88)) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (3 * nn)) (Z_to_bv 64 1) a2 a3
                    a4 a5 a6 a7 s2 s3 s4 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_CALLOC) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x70)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nn
    E4 E7 HN.
  crt_pc.
  assert (U7 : bv_unsigned s7 = nn) by (subst s7; apply unsigned_lit; lia).
  subst s4.
  do 3 step. if_true.
  do 2 step.
  crt_finF.
Qed.

(* ---- seg4: 0x80c50 (a0 = R) -> the convert loop's top 0x80c9c ---- *)
(*      listing: CRT_AT 0x88 -> CRT_LOOP_IN (= CRT_AT 0xd4).  Port of crt_segs_F.v:117-151. *)
Lemma crt_seg4_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P Q R nch ns : Z),
    s0 = Z_to_bv 64 P -> s5 = Z_to_bv 64 Q -> a0 = Z_to_bv 64 R ->
    s3 = Z_to_bv 64 nch -> s2 = Z_to_bv 64 ns ->
    0 < P < 2^64 -> 0 < Q < 2^64 -> 0 < R < 2^64 -> 2 <= nch <= 127 -> 1 <= ns <= 12 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' : word) (F' : bvmap 5 word),
         ms' = MS (mkR ra sp gp tp s6 s0 s0 s0 s1 a0' a1' a2 (Z_to_bv 64 0) (Z_to_bv 64 (4 * ns))
                    (Z_to_bv 64 CRT_A5) (Z_to_bv 64 (3 * ns)) (Z_to_bv 64 (3 * ns))
                    s2 s3 s4 s5 s6 (Z_to_bv 64 R) s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (Z_to_bv 64 CRT_LOOP_IN) fc None m (seg_rom rsegs) /\
         unbox_s (reg_get F' (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 /\
         (forall k : bv 5, bv_unsigned k <> 15 -> reg_get F' k = reg_get F k))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x88)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    P Q R nch ns E0 E5 EA E3 E2 HP HQ HR HN HS.
  crt_pc.
  assert (U0 : bv_unsigned s0 = P) by (subst s0; apply unsigned_lit; lia).
  assert (U5 : bv_unsigned s5 = Q) by (subst s5; apply unsigned_lit; lia).
  assert (UA : bv_unsigned a0 = R) by (subst a0; apply unsigned_lit; lia).
  assert (S3 : bv_signed s3 = nch) by (subst s3; apply crt_signed_lit; lia).
  step. if_false.
  step. if_false.
  do 2 step. if_false.
  step. if_false.
  do 14 step.
  apply evtF_done. do 3 eexists. split; [|split].
  - subst s2 a0. f_equal; crt_regs; crt_w.
  - rewrite freg_get_same by reflexivity. apply bv_eq. vm_compute. reflexivity.
  - intros k Hk. apply reg_get_set_other. intros E. subst k. apply Hk. reflexivity.
Qed.

(* ---- seg5: 0x80db8 (loop exit) -> call of reac_braid_encode(s7, s3, s5, s3, s2) at 0x80dcc ---- *)
(*      listing: CRT_LOOP_OUT (= CRT_AT 0x1f0) -> call at CRT_AT 0x204, ra = CRT_AT 0x208.
        Port of crt_segs_F.v:153-170. *)
Lemma crt_seg5_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x208)) sp gp tp t0 t1 t2 s0 s1 s7 s3 s5 s3 s2 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_ENCODE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CRT_LOOP_OUT) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  crt_pc.
  do 6 step.
  crt_finF.
Qed.

(* ---- seg6: 0x80dd0 -> call of bcmp(s7, s1, s4) at 0x80ddc ---- *)
(*      listing: CRT_AT 0x208 -> call at CRT_AT 0x214, ra = CRT_AT 0x218.  Port of crt_segs_F.v:172-188. *)
Lemma crt_seg6_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x218)) sp gp tp t0 t1 t2 s0 s1 s7 s1 s4 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_BCMP) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x208)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  crt_pc.
  do 4 step.
  crt_finF.
Qed.

(* ---- seg7: 0x80de0 with a0 = 0 (the bnez to 0x80e30 not taken) -> call of free(s7) at 0x80de8 ---- *)
(*      listing: CRT_AT 0x218 (the bnez to CRT_AT 0x268 not taken) -> call at CRT_AT 0x220, ra = CRT_AT 0x224.
        Port of crt_segs_F.v:190-209. *)
Lemma crt_seg7_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x224)) sp gp tp t0 t1 t2 s0 s1 s7 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x218)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m E0.
  crt_pc.
  subst a0.
  step. if_false.
  do 2 step.
  crt_finF.
Qed.

(* ---- seg8: 0x80dec -> call of free(s5) at 0x80df0 ---- *)
(*      listing: CRT_AT 0x224 -> call at CRT_AT 0x228, ra = CRT_AT 0x22c.  Port of crt_segs_F.v:211-227. *)
Lemma crt_seg8_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x22c)) sp gp tp t0 t1 t2 s0 s1 s5 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x224)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  crt_pc.
  do 2 step.
  crt_finF.
Qed.

(* ---- seg9: 0x80df4 -> tail jump to free(s0) at 0x80e2c: ra, s0-s10 loaded back, sp = sp + 96 ---- *)
(*      listing: CRT_AT 0x22c -> tail jump at CRT_AT 0x264.  Port of crt_segs_F.v:229-252. *)
Lemma crt_seg9_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) (crt_fr c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    bv_unsigned sp + 96 < 2^64 ->
    ExecF.rng RNG (bv_unsigned sp) 96 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 96)) gp tp t0 t1 t2 c0 c1 s0 a1 a2 a3 a4 a5 a6 a7
                    c2 c3 c4 c5 c6 c7 c8 c9 c10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x22c)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra FR HSP RFR.
  crt_pc.
  unfold crt_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 15 step.
  crt_finF.
Qed.
