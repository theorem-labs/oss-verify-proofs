From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import memrchr_c.
Import ListNotations.
Open Scope Z_scope.

Lemma memrchr_firstn_S : forall (l : list byte) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IH k x H). reflexivity.
Qed.

Lemma memrchr_skipn_1 : forall (l : list byte) k x, nth_error l k = Some x -> firstn 1 (skipn k l) = [x].
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - exact (IH k x H).
Qed.

Lemma memrchr_loop :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte) (k : nat)
         (x10 cw p q x14 : word),
    bytes_at rsegs m (bv_unsigned a0) buf ->
    mem_inv rsegs m ->
    bv_unsigned a2 <= Z.of_nat (length buf) ->
    Z.of_nat k <= bv_unsigned a2 ->
    bv_unsigned cw = bv_unsigned a1 mod 256 ->
    bv_unsigned p = (bv_unsigned a0 + Z.of_nat k) mod 2^64 ->
    bv_unsigned q = (- Z.of_nat k) mod 2^64 ->
    rfind_byte (bv_unsigned a1 mod 256) (firstn k buf) =
      rfind_byte (bv_unsigned a1 mod 256) (firstn (Z.to_nat (bv_unsigned a2)) buf) ->
    evt rsegs (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 cw p q x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1efa8) fc None m (seg_rom rsegs)).
Proof.
  intros until k. induction k as [|k IH]; intros x10 cw p q x14 BA MI HN HK HC HP HQ HR.
  - pose proof (bytes_at_bound _ _ _ _ BA) as BB.
    pose proof (zr_word a2) as R2. unfold inr64 in R2.
    zstep.
    if_cases B; zify_cond B.
    2:{ exfalso. Z.div_mod_to_equations. lia. }
    zstep. zstep.
    apply evt_done. unfold memrchr_post, memrchr_res. rewrite <- HR. cbn [firstn rfind_byte].
    do 15 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; assumption.
  - pose proof (bytes_at_bound _ _ _ _ BA) as BB.
    pose proof (zr_word a2) as R2. unfold inr64 in R2.
    destruct (nth_error buf k) as [x|] eqn:HX.
    2:{ exfalso. apply nth_error_None in HX. lia. }
    assert (HXL : (k < length buf)%nat) by (apply nth_error_Some; rewrite HX; discriminate).
    assert (RD : ov_read_bytes rsegs m (wa (bv_unsigned a0 + Z.of_nat k)) 1 = Some [x]).
    { rewrite (bytes_at_read rsegs m (bv_unsigned a0) buf (Z.of_nat k) 1 BA) by lia.
      rewrite Nat2Z.id. rewrite (memrchr_skipn_1 buf k x HX). reflexivity. }
    zstep.
    if_cases B; zify_cond B.
    { exfalso. Z.div_mod_to_equations. lia. }
    zstep. zstep. zstep. zstep. zstep.
    rewrite (memrchr_firstn_S buf k x HX) in HR.
    if_cases B2; zify_cond B2.
    + apply IH; try assumption.
      * lia.
      * rewrite unsigned_lit_wrap. rewrite HP. Z.div_mod_to_equations. lia.
      * rewrite unsigned_lit_wrap. rewrite HQ. Z.div_mod_to_equations. lia.
      * rewrite <- HR. rewrite rfind_byte_snoc_miss; [reflexivity|]. lia.
    + zstep.
      apply evt_done. unfold memrchr_post.
      replace (memrchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf)
        with (bv_unsigned a0 + Z.of_nat k).
      2:{ unfold memrchr_res. rewrite <- HR. rewrite rfind_byte_snoc_hit by lia. cbv beta iota.
          rewrite length_firstn. lia. }
      replace (Z_to_bv 64 (bv_unsigned p + -1)) with (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat k)).
      2:{ apply Z_to_bv_eqm. rewrite HP. Z.div_mod_to_equations. lia. }
      do 15 eexists. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; assumption.
Qed.

Theorem memrchr_holds : memrchr_contract.
Proof.
  unfold memrchr_contract, MEMRCHR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
    BA HN MI.
  pose proof (bytes_at_bound _ _ _ _ BA) as BB.
  pose proof (zr_word a2) as R2. unfold inr64 in R2.
  zstep. zstep. zstep.
  eapply (memrchr_loop _ _ _ _ _ _ _ _ _ a0 a1 a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ buf (Z.to_nat (bv_unsigned a2)));
    try eassumption.
  - lia.
  - rewrite unsigned_lit_wrap. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    pose proof (zr_word a1) as R1. unfold inr64 in R1. Z.div_mod_to_equations. lia.
  - rewrite unsigned_lit_wrap. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite unsigned_lit_wrap. rewrite Z2Nat.id by lia. Z.div_mod_to_equations. lia.
  - reflexivity.
Qed.
