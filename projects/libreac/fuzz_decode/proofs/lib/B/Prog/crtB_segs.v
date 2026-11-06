(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 322 of its 359 lines of code are new or changed and 427 lines of the source are left out. *)
(* crtB_segs: port of a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/B/Prog/crt_segs_F.v
   (crt_seg1_F .. crt_seg8_F there) and of the first 24 steps of
   a working branch b04a1406048:proofs/libreac/fuzz_decode/lib/B/Prog/crt_loopF.v crt_loop_holds_F
   (+0xac .. +0x10c), the footprint (ExecF.evtF) runs of the straight-line segments of check_round_trip in image B
   (fuzz_decode.asan-ubsan, original pin: entry 0x80d54, frame 160; the donor's addresses are the original image's).
   Twin of lib/A/Prog/crtA_segs.v (a working branch ae1529ccb00): the same numbering
   crt_seg1_F .. crt_seg9_F; image B's seg4 joins the donor's crt_seg3c_regs_F and the loop constants, so that it
   ends at CRT_LOOP_IN (+0x10c), where the donor's crt_outer_F starts.
   The addresses are re-based on the listing: every pc in a statement is a name of lib/B/Prog/crtB_iface.v.
   The donor imports lib/B/AsanRT.v, which is lib/B/AsanCells.v here (same names and bodies).  The donor's
   lib/B/Spec/StrFun.v does not exist here: its lemma Z_to_le_bytes_to_Z is copied below (as crtA_segs.v does), and
   byte_range (same statement) comes from lib/B/Prog/AsanKAProof.v.  The helpers crt_segs_F.v takes from the
   donor's lib/B/Prog/crt_segs.v are copied below, each with the lines it came from. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof ReacDecodeLib check_braid.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_iface.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- helpers ---- *)

(* Copied from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/B/Spec/StrFun.v (via
   lib/A/Prog/crtA_segs.v; that file does not exist on this branch). *)
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

(* Copied from the donor crt_segs.v:26-31 (needed by crt_frame_words). *)
Lemma crt_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply Z_to_le_bytes_to_Z.
Qed.

(* Copied from the donor crt_segs.v:33-37. *)
Fixpoint crt_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: crt_c8s n' (skipn 8 bs)
  end.

(* Copied from the donor crt_segs.v:39-50. *)
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

(* Copied from the donor crt_segs.v:52-60. *)
Lemma crt_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (crt_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (crt_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* Copied from the donor crt_segs.v:62-68: the carved 160 bytes, read as 20 words. *)
Lemma crt_frame_words : forall m A bs, rw_cells rsegs m A [CB 160 bs] ->
  exists v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 : word,
    rw_cells rsegs m A (crt_fr v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152).
Proof.
  intros m A bs H. apply (crt_rw_c8s rsegs m A 20 bs) in H. cbn [crt_c8s] in H. do 20 eexists. exact H.
Qed.

(* As lib/A/Prog/crtA_segs.v:99-103 (the A donor's crt_segs.v:61-65): bv_signed of a small non-negative literal. *)
Lemma crt_signed_lit : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec0 z (2^63)); lia.
Qed.

(* Copied from the donor crt_convert.v:164-165 (image B's andi masks of the loop constants). *)
Lemma crt_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. exact (Z.land_ones x 2 ltac:(lia)). Qed.
Lemma crt_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. exact (Z.land_ones x 3 ltac:(lia)). Qed.

(* Copied from the donor crt_segs.v:70-74. *)
Ltac crt_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

(* Copied from the donor crt_segs.v:76 (used by crt_w). *)
Ltac crt_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.

(* As lib/A/Prog/crtA_segs.v (used by crt_w). *)
Ltac crt_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.

(* The donor crt_segs.v:78-79, in crtA_segs.v's form (with the shift and division cases). *)
Ltac crt_w := crt_shift; crt_usub; crt_shift; crt_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].

(* Donor crt_segs_F.v:30-32. *)
Ltac crt_finF := apply evtF_done; f_equal; crt_regs; crt_w.

Ltac crt_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* As crtA_segs.v (not in the donor, whose start pcs were numerals): StepF's step reads the start pc, and the start
   pc of each statement here is a crtB_iface name, so compute that one pc term to its value inside the proof. *)
Ltac crt_pc := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let v := eval vm_compute in pc in change pc with v
  end.

(* `norm` / `fact` / `solve_c` are lib/B/Prog/check_braid.v:311-324; the donor crt_convert.v:172-177 builds wfct on
   them, for the bv_unsigned value of a register the steps left as a `bv_and` / `bv_not` / shift term. *)
Ltac crt_fct := try unfold wa; norm;
  first [ reflexivity | lia | (rewrite ?unsigned_lit_wrap; zb_fold_lits; Z.div_mod_to_equations; lia) ].
Ltac crt_wfct := rewrite ?crt_land3, ?crt_land7; first [ crt_fct | fact ].

(* Donor check_braid_F.v:26-28, at ExecF (the signed `blez` test, which solve_cond does not take). *)
Ltac crt_takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* ---- the segments ---- *)

(* ---- seg1: CRT_ENTRY -> call of malloc(4 nch ns) at CRT_AT 0x64, ra = CRT_AT 0x68.  Donor crt_segs_F.v:34-73
        (crt_seg1_F, its post crt_s1_post of crt_segs.v:86-97 written out). ---- *)
Lemma crt_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (audio pcm nch ns lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp ->
    asan_cells m -> off_stk sp 160 GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    2 <= nch <= 127 -> 1 <= ns <= 12 -> 0 <= audio < 2^64 -> 0 <= pcm < 2^64 ->
    ExecF.rng RNG (bv_unsigned sp - 160) 160 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 (v0 v8 v16 v32 v40 v48 : word),
         ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x68)) (Z_to_bv 64 (bv_unsigned sp - 160)) gp tp t0 t1 t2
                    (Z_to_bv 64 (nch * ns)) (Z_to_bv 64 nch) (Z_to_bv 64 (4 * (nch * ns))) (Z_to_bv 64 pcm)
                    (Z_to_bv 64 nch) (Z_to_bv 64 ns) a4 a5 a6 a7 (Z_to_bv 64 ns) (Z_to_bv 64 (3 * (nch * ns)))
                    (Z_to_bv 64 pcm) s5 s6 s7 (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CRT_MALLOC) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp - 160) /\
         rw_cells rsegs m1 (bv_unsigned sp - 160)
           (crt_fr v0 v8 v16 (Z_to_bv 64 audio) v32 v40 v48 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 audio) (Z_to_bv 64 pcm) (Z_to_bv 64 nch) (Z_to_bv 64 ns)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CRT_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m audio pcm nch
    ns lo ST LO CELLS DC HN HS HA HP RFR RGC RCK.
  crt_pc.
  unfold GOT_CELL_K in RGC. unfold CELL_K in RCK.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold off_stk, GOT_CELL_K, MIDEND in DC.
  carve_frame 160%nat ST.
  destruct (crt_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & v96 &
    v104 & v112 & v120 & v128 & v136 & v144 & v152 & FR'). clear FR. unfold crt_fr in FR'. rename FR' into FR.
  do 18 step.
  match goal with H : munch _ m ?m1 |- _ => assert (CELLS1 : asan_cells m1)
    by (eapply asan_cells_munch; [exact CELLS | exact H | unfold MIDEND, GOT_CELL_K; lia]) end.
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 8 step.
  crt_memF ltac:(fun mm => apply evtF_done; exists mm, v0, v8, v16, v32, v40, v48).
  replace (bv_unsigned sp - 160) with (bv_unsigned sp + -160) by lia.
  split; [|split; [exact MU|split; [exact WM|split; [exact ST|exact FR]]]].
  f_equal; crt_regs; crt_w.
Qed.

(* ---- seg2: CRT_AT 0x68 (a0 = P) -> call of malloc(8 nch) at CRT_AT 0x74, ra = CRT_AT 0x78; P to 48(sp), nch to
        40(sp).  Donor crt_segs_F.v:75-104. ---- *)
Lemma crt_seg2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nch : Z)
         (v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word),
    0 <= nch <= 127 ->
    rw_cells rsegs m (bv_unsigned sp) (crt_fr v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    ExecF.rng RNG (bv_unsigned sp) 160 ->
    ExecF.evtF rsegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x78)) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 nch) (Z_to_bv 64 (8 * nch)) a1 a2 a3
                   a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 CRT_MALLOC) fc None m' (seg_rom rsegs) /\
        munch [(bv_unsigned sp, bv_unsigned sp + 160)] m m' /\ wmono rsegs m m' /\
        rw_cells rsegs m' (bv_unsigned sp)
          (crt_fr v0 v8 v16 v24 v32 (Z_to_bv 64 nch) a0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 nch) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x68)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nch
    v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra HN FR RFR.
  crt_pc.
  unfold crt_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  crt_memF ltac:(fun mm => apply evtF_done; exists mm).
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; crt_regs; crt_w.
Qed.

(* ---- seg3: CRT_AT 0x78 (a0 = Q) -> call of calloc(3 nch ns, 1) at CRT_AT 0x90, ra = CRT_AT 0x94; Q to s5, s3 to
        16(sp); the `bnez s0` at CRT_AT 0x84 is taken (s0 = nch ns).  Donor crt_segs_F.v:106-134. ---- *)
Lemma crt_seg3_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word),
    bv_unsigned s0 <> 0 ->
    rw_cells rsegs m (bv_unsigned sp) (crt_fr v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    ExecF.rng RNG (bv_unsigned sp) 160 ->
    ExecF.evtF rsegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x94)) sp gp tp t0 t1 t2 s0 s1 s3 (Z_to_bv 64 1) a2 a3 a4
                   a5 a6 a7 s2 s3 s4 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 CRT_CALLOC) fc None m' (seg_rom rsegs) /\
        munch [(bv_unsigned sp, bv_unsigned sp + 160)] m m' /\ wmono rsegs m m' /\
        rw_cells rsegs m' (bv_unsigned sp)
          (crt_fr v0 v8 s3 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x78)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra H0 FR RFR.
  crt_pc.
  unfold crt_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step. if_true.
  do 2 step.
  crt_memF ltac:(fun mm => apply evtF_done; exists mm).
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; crt_regs; crt_w.
Qed.

(* ---- seg4: CRT_AT 0x94 (a0 = R) -> CRT_LOOP_IN: the three NULL checks (P, Q, R non-zero, so none of the `beqz`
        to the abort block at CRT_AT 0x2f0 is taken), R to 8(sp), `blez nch` not taken, the loop constants and
        `fmv.w.x fa5,a1`.  Donor crt_segs_F.v:166-197 (crt_seg3c_regs_F, +0x94 .. +0xac) followed by the first 24
        steps of the donor crt_loopF.v crt_loop_holds_F (+0xac .. +0x10c). ---- *)
Lemma crt_seg4_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v0 v8 v16 v24 v32 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (P Q R pcm nch ns : Z),
    a0 = Z_to_bv 64 R -> s5 = Z_to_bv 64 Q -> s4 = Z_to_bv 64 pcm -> s2 = Z_to_bv 64 ns ->
    0 < P < 2^64 -> 0 < Q < 2^64 -> 0 < R < 2^64 -> 0 <= pcm < 2^64 -> P mod 4 = 0 -> Q mod 8 = 0 ->
    2 <= nch <= 127 -> 1 <= ns <= 12 ->
    rw_cells rsegs m (bv_unsigned sp)
      (crt_fr v0 v8 v16 v24 v32 (Z_to_bv 64 nch) (Z_to_bv 64 P) c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    ExecF.rng RNG (bv_unsigned sp) 160 ->
    ExecF.evtF rsegs RNG (fun ms' => exists (F' : bvmap 5 word) m'
        (wt0 wt1 wt2 ws0 wa0 wa1 wa3 wa4 wa6 wa7 ws9 ws11 wt3 wt4 wt5 wt6 w32 : word),
        ms' = MS (mkR ra sp gp tp wt0 wt1 wt2 ws0 s1 wa0 wa1 a2 wa3 wa4 a5 wa6 wa7 s2 s3 s4 s5 s6 s7 s8 ws9 s10 ws11
                   wt3 wt4 wt5 wt6)
                 F' (Z_to_bv 64 CRT_LOOP_IN) fc None m' (seg_rom rsegs) /\
        rw_cells rsegs m' (bv_unsigned sp)
          (crt_fr v0 (Z_to_bv 64 R) v16 v24 w32 (Z_to_bv 64 nch) (Z_to_bv 64 P)
             c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) /\
        munch [(bv_unsigned sp, bv_unsigned sp + 160)] m m' /\ wmono rsegs m m' /\
        unbox_s (reg_get F' (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 /\
        (forall k : bv 5, bv_unsigned k <> 15 -> reg_get F' k = reg_get F k) /\
        bv_unsigned wt0 = 0 /\ bv_unsigned wt1 = 4 * ns /\ bv_unsigned wt2 = 1 /\
        bv_unsigned ws0 = P /\ bv_unsigned wa3 = 0 /\ bv_unsigned wa4 = 0 /\
        bv_unsigned wa6 = 2 ^ 64 - 1 - pcm /\ bv_unsigned wa7 = 0 /\
        bv_unsigned ws9 = pcm /\ bv_unsigned ws11 = P /\
        bv_unsigned wt3 = CRT_T3 /\ bv_unsigned wt4 = 3 * ns /\ bv_unsigned wt5 = CRT_T5 /\
        bv_unsigned wt6 = 3 * ns /\ bv_unsigned w32 = 2 ^ 64 - 1 - P)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x94)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v8 v16 v24 v32 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra P Q R pcm nch ns EA E5 E4 E2 HP HQ HR HC HP4 HQ8 HN HS
    FR RFR.
  crt_pc.
  unfold crt_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UQ : bv_unsigned (Z_to_bv 64 Q) = Q) by (apply unsigned_lit; lia).
  assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (UPc : bv_unsigned (Z_to_bv 64 pcm) = pcm) by (apply unsigned_lit; lia).
  assert (UNs : bv_unsigned (Z_to_bv 64 ns) = ns) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (NP : bv_unsigned (Z_to_bv 64 P) <> 0) by lia.
  assert (NQ : bv_unsigned (Z_to_bv 64 Q) <> 0) by lia.
  assert (NR : bv_unsigned (Z_to_bv 64 R) <> 0) by lia.
  assert (SN : bv_signed (Z_to_bv 64 nch) = nch) by (apply crt_signed_lit; lia).
  subst a0 s5 s4 s2.
  do 3 step. first [ if_false | crt_takeF false ].
  step. first [ if_false | crt_takeF false ].
  step. first [ if_false | crt_takeF false ].
  step.
  do 2 step. first [ if_false | crt_takeF false ].
  do 22 step.
  crt_memF ltac:(fun mm => apply evtF_done; eexists; exists mm; do 17 eexists).
  split; [reflexivity|].
  split; [exact FR|]. split; [exact MU|]. split; [exact WM|].
  split; [rewrite freg_get_same by reflexivity; apply bv_eq; vm_compute; reflexivity|].
  split; [intros k Hk; apply reg_get_set_other; intros E; subst k; apply Hk; reflexivity|].
  unfold CRT_T3, CRT_T5. repeat (split; [crt_wfct|]). crt_wfct.
Qed.

(* ---- seg5: CRT_LOOP_OUT -> call of reac_braid_encode(R, nch, Q, nch, ns) at CRT_AT 0x284, ra = CRT_AT 0x288;
        R from 8(sp) to s0, nch from 40(sp).  Donor crt_segs_F.v:237-256 (crt_seg4a_regs_F). ---- *)
Lemma crt_seg5_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) (crt_fr v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    ExecF.rng RNG (bv_unsigned sp) 160 ->
    ExecF.evtF rsegs RNG (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x288)) sp gp tp t0 t1 t2 v8 s1 v8 v40 s5 v40 s2 a5 a6 a7 s2 s3 s4 s5 s6 s7
                   s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 CRT_ENCODE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CRT_LOOP_OUT) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra FR RFR.
  crt_pc.
  unfold crt_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  do 7 step.
  crt_finF.
Qed.

(* ---- seg6: CRT_AT 0x288 -> call of bcmp(R, audio, 3 nch ns) at CRT_AT 0x294, ra = CRT_AT 0x298; audio from
        24(sp), the size from 16(sp).  Donor crt_segs_F.v:284-304 (crt_seg5_F). ---- *)
Lemma crt_seg6_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) (crt_fr v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    ExecF.rng RNG (bv_unsigned sp) 160 ->
    ExecF.evtF rsegs RNG (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x298)) sp gp tp t0 t1 t2 s0 s1 s0 v24 v16 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                   s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 CRT_BCMP) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x288)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra FR RFR.
  crt_pc.
  unfold crt_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  do 4 step.
  crt_finF.
Qed.

(* ---- seg7: CRT_AT 0x298 with a0 = 0 (the `bnez a0` to the abort block at CRT_AT 0x2f0 not taken) -> call of
        free(R) at CRT_AT 0x2a0, ra = CRT_AT 0x2a4.  Donor crt_segs_F.v:306-323 (crt_seg6_F). ---- *)
Lemma crt_seg7_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x2a4)) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                   s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x298)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  crt_pc.
  step. if_false.
  do 2 step.
  crt_finF.
Qed.

(* ---- seg8: CRT_AT 0x2a4 -> call of free(Q) at CRT_AT 0x2a8, ra = CRT_AT 0x2ac.  Donor crt_segs_F.v:325-340
        (crt_seg7_F). ---- *)
Lemma crt_seg8_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 (CRT_AT 0x2ac)) sp gp tp t0 t1 t2 s0 s1 s5 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                   s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x2a4)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  crt_pc.
  do 2 step.
  crt_finF.
Qed.

(* ---- seg9: CRT_AT 0x2ac -> tail jump to free(P) at CRT_AT 0x2e8: ra, s0-s11 restored, sp back to the entry sp.
        Donor crt_segs_F.v:342-363 (crt_seg8_F). ---- *)
Lemma crt_seg9_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) (crt_fr v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    ExecF.rng RNG (bv_unsigned sp) 160 ->
    ExecF.evtF rsegs RNG (fun ms' =>
        ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 160)) gp tp t0 t1 t2 c0 c1 v48 a1 a2 a3 a4 a5 a6 a7
                   c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
                 F (Z_to_bv 64 CRT_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CRT_AT 0x2ac)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra FR RFR.
  crt_pc.
  unfold crt_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 16 step.
  crt_finF.
Qed.
