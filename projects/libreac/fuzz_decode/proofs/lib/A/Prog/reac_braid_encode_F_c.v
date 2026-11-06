From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crt_braid_need.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YImgTop.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of reac_braid_encode_exact_contract (crt_braid_need.v, entry REAC_BRAID_ENCODE, frame
   REAC_BRAID_ENCODE_FRAME), and reac_braid_encode_exact_contract_of_F, which gives the plain contract back at the
   footprint RNG_all. A relocation of the fuzz_ctrl A statement (proofs/libreac/fuzz_ctrl/lib/A/Prog/
   reac_braid_encode_exact_c.v of a working branch, commit 8359926e36b), in the form of image B's statement: RNG
   is the first binder, then the premises of the plain contract unchanged, then one rng premise per region the run
   reads or writes, then evtF in place of evt. The regions: the image span [YImgTop.IMG_LO, YImgTop.IMG_TOP), which holds the three
   words of the image that the run reads (the GOT cell GOT_CELL_K and the runtime cell CELL_K that hold the shadow
   offset, and the clamp constant FCLAMP_HI, 0x4afffffe, in the read-only data at 0x20dac, loaded PC-relative); the
   48-byte frame below sp; the 3 N ns bytes at a; the 8 N bytes at P; the 4 ns bytes at each Q ch; and the 8-aligned
   shadow word cover of each of those three ranges. From Definition reac_braid_encode_exact_contract_F to the end,
   this file is a Theorem Labs lane's alreloc.py output (--src libreac/fuzz_ctrl --build asan) byte for byte: the image premise,
   which cites lib/Reusable/YImgTop.v (computed from the images) in place of alreloc's two derived numerals. This file replaces the interim twin statement, which
   had no region for FCLAMP_HI. reac_braid_encode_exactF.v proves the twin. *)

Definition reac_braid_encode_exact_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (a N P ns : Z) (Q : Z -> Z) (V K : Z -> Z -> Z),
    a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 N -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 N -> a4 = Z_to_bv 64 ns ->
    2 <= N <= 127 -> N mod 2 = 0 -> 1 <= ns <= 12 ->
    frm0 fc -> mem_inv rsegs m ->
    stk rsegs m (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp) ->
    0 < a -> a + 3 * N * ns <= 2^64 -> wr_at rsegs m a (3 * N * ns) ->
    0 < P -> P mod 8 = 0 -> P + 8 * N <= 2^64 ->
    (forall ch, 0 <= ch < N -> bytes_at rsegs m (P + 8 * ch) (le8 (Z_to_bv 64 (Q ch)))) ->
    (forall ch, 0 <= ch < N -> 0 < Q ch /\ Q ch mod 4 = 0 /\ Q ch + 4 * ns <= 2^64) ->
    (forall s ch, 0 <= s < ns -> 0 <= ch < N ->
       bytes_at rsegs m (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch))) /\ rb_sample (V s ch) (K s ch)) ->
    (a + 3 * N * ns <= P \/ P + 8 * N <= a) ->
    (forall ch, 0 <= ch < N -> a + 3 * N * ns <= Q ch \/ Q ch + 4 * ns <= a) ->
    (a + 3 * N * ns <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= a) ->
    (P + 8 * N <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= P) ->
    (forall ch, 0 <= ch < N ->
       Q ch + 4 * ns <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= Q ch) ->
    asan_cells m -> shadow_rw m ->
    addressable m a (3 * N * ns) -> addressable m P (8 * N) ->
    (forall ch, 0 <= ch < N -> addressable m (Q ch) (4 * ns)) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp); (a, a + 3 * N * ns)] x) ->
    rng RNG YImgTop.IMG_LO (YImgTop.IMG_TOP - YImgTop.IMG_LO) ->
    rng RNG (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) REAC_BRAID_ENCODE_FRAME ->
    rng RNG a (3 * N * ns) ->
    rng RNG (shadow_addr a / 8 * 8)
        (shadow_addr (a + 3 * N * ns - 1) / 8 * 8 + 8 - shadow_addr a / 8 * 8) ->
    rng RNG P (8 * N) ->
    rng RNG (shadow_addr P / 8 * 8) (shadow_addr (P + 8 * N - 1) / 8 * 8 + 8 - shadow_addr P / 8 * 8) ->
    (forall ch, 0 <= ch < N -> rng RNG (Q ch) (4 * ns)) ->
    (forall ch, 0 <= ch < N ->
       rng RNG (shadow_addr (Q ch) / 8 * 8)
           (shadow_addr (Q ch + 4 * ns - 1) / 8 * 8 + 8 - shadow_addr (Q ch) / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
         (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get F' k = reg_get F k) /\
         munch [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp); (a, a + 3 * N * ns)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp) /\
         (forall x : word, outside [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp)] (bv_unsigned x) ->
            m' x = rb_enc m (rb_rows a N K (Z.to_nat ns)) x))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BRAID_ENCODE) fc None m (seg_rom rsegs)).

(* The old statement is the _F statement at the footprint that admits every access (every rng premise by rng_all):
   the _F statement asks for nothing the old one lacks. *)
Lemma reac_braid_encode_exact_contract_of_F :
  reac_braid_encode_exact_contract_F -> reac_braid_encode_exact_contract.
Proof.
  unfold reac_braid_encode_exact_contract_F, reac_braid_encode_exact_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    a N P ns Q V K E0 E1 E2 E3 E4 HN HNe Hns FRM HI ST Ha HaE HW HP0 HP8m HP8 HPb HQ HV HD1 HD2 HD3 HD4 HD5
    HCE HSW HAa HAP HAQ HWO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _). unfold REAC_BRAID_ENCODE_FRAME in ST0.
  pose proof YImgTop.IMG_LO_val as HIL. pose proof YImgTop.IMG_TOP_val as HIT.
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m a N P ns Q V K); try assumption;
    try (intros ch Hch; destruct (HQ ch Hch) as (HQ0 & HQ4 & HQE));
    apply rng_all; cbv [shadow_addr ASAN_K REAC_BRAID_ENCODE_FRAME];
    try Z.div_mod_to_equations; lia.
Qed.
