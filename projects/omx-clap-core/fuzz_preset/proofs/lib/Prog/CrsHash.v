From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ReaderRes check_reject_clean_starved_c.
Import ListNotations.
Open Scope Z_scope.

Lemma crs_djb2_cons : forall h (c : byte) r,
  djb2 h (zb (c :: r)) = djb2 ((33 * h + bv_unsigned c) mod 2 ^ 64) (zb r).
Proof. reflexivity. Qed.

Lemma crs_read1 : forall m p (c : byte) r,
  bytes_at rsegs m p (c :: r) -> ov_read_bytes rsegs m (wa p) 1 = Some [c].
Proof.
  intros m p c r HB. rewrite <- (Z.add_0_r p) at 1.
  rewrite (bytes_at_read rsegs m p _ 0 1 HB) by (cbn; lia). reflexivity.
Qed.

Lemma crs_tail : forall m p (c : byte) r,
  bytes_at rsegs m p (c :: r) -> bytes_at rsegs m (p + 1) r.
Proof.
  intros m p c r HB. apply (proj1 (bytes_at_app rsegs m p [c] r)) in HB. destruct HB as [_ HB]. exact HB.
Qed.

Lemma crs_hash_val : forall h (c : byte), 0 <= h < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 h)) 5 + h + bv_unsigned (zxb c)) =
  Z_to_bv 64 ((33 * h + bv_unsigned c) mod 2 ^ 64).
Proof.
  intros h c Hh.
  assert (Hc : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  unfold zxb. rewrite (unsigned_lit h) by lia. rewrite (unsigned_lit (bv_unsigned c)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  apply bv_eq. rewrite !unsigned_lit_wrap. rewrite Zmod_mod. f_equal. change (2 ^ 5) with 32. lia.
Qed.

Local Ltac crs_iter IH :=
  lazymatch goal with
  | HB : bytes_at rsegs ?m ?p (?c :: ?r), HE : _ + Z.of_nat (length (_ :: _)) = ?E, Hh : 0 <= ?h < 2 ^ 64 |- _ =>
      pose proof (crs_read1 m p c r HB) as RD;
      pose proof (bytes_at_bound rsegs m p (c :: r) HB) as BB;
      pose proof (crs_tail m p c r HB) as HB';
      cbn [length] in HE, BB;
      rewrite crs_djb2_cons;
      step; step; step; step; step; step;
      rewrite (crs_hash_val h c Hh);
      destruct r as [|c' r];
      [ assert (HE1 : E = p + 1) by (cbn in HE; lia); clear HE; subst E;
        assert (C : negb (bv_eqb (Z_to_bv 64 (p + 1)) (Z_to_bv 64 (p + 1))) = false) by (rewrite bv_eqb_refl; reflexivity);
        rewrite C; cbv iota;
        apply evt_done; cbv beta; eexists _, _; reflexivity
      | cbn [length] in HE, BB;
        assert (C : negb (bv_eqb (Z_to_bv 64 (p + 1)) (Z_to_bv 64 E)) = true)
          by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply negb_true_iff, Z.eqb_neq; lia);
        rewrite C; cbv iota;
        eapply IH; [exact HB' | congruence | cbn [length] in *; lia | assumption | apply Z.mod_pos_bound; lia] ]
  end.

Lemma crs_l1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (E : Z) (tl : list byte) (p h : Z) (a3 a4 : word),
  bytes_at rsegs m p tl -> tl <> [] -> p + Z.of_nat (length tl) = E -> E < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a3' a4' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (djb2 h (zb tl)))
                     (Z_to_bv 64 E) (Z_to_bv 64 E) a3' a4' a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13c70) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) (Z_to_bv 64 E) (Z_to_bv 64 p)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c58) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m E tl.
  induction tl as [|c r IH]; intros p h a3 a4 HB HNE HE HEb Hh; [congruence|].
  crs_iter IH.
Qed.

Lemma crs_loop1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p h : Z) (tl : list byte),
  bytes_at rsegs m p tl -> tl <> [] -> p + Z.of_nat (length tl) < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a3' a4' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (djb2 h (zb tl)))
                     (Z_to_bv 64 (p + Z.of_nat (length tl))) (Z_to_bv 64 (p + Z.of_nat (length tl))) a3' a4' a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13c70) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) (Z_to_bv 64 (p + Z.of_nat (length tl))) (Z_to_bv 64 p)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c58) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply crs_l1; eauto.
Qed.

Lemma crs_l2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (E : Z) (tl : list byte) (p h : Z) (a4 a5 : word),
  bytes_at rsegs m p tl -> tl <> [] -> p + Z.of_nat (length tl) = E -> E < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (djb2 h (zb tl)))
                     (Z_to_bv 64 E) (Z_to_bv 64 E) a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13d24) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 h) (Z_to_bv 64 E) (Z_to_bv 64 p)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d0c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m E tl.
  induction tl as [|c r IH]; intros p h a4 a5 HB HNE HE HEb Hh; [congruence|].
  crs_iter IH.
Qed.

Lemma crs_l3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (E : Z) (tl : list byte) (p h : Z) (a2 a3 : word),
  bytes_at rsegs m p tl -> tl <> [] -> p + Z.of_nat (length tl) = E -> E < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a2' a3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (djb2 h (zb tl))) a2' a3' a4 a5 a6 a7
                     (Z_to_bv 64 E) (Z_to_bv 64 E)
                     s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13e00) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 h) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 E) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13de8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m E tl.
  induction tl as [|c r IH]; intros p h a2 a3 HB HNE HE HEb Hh; [congruence|].
  crs_iter IH.
Qed.

Lemma crs_loop2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p h : Z) (tl : list byte),
  bytes_at rsegs m p tl -> tl <> [] -> p + Z.of_nat (length tl) < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (djb2 h (zb tl)))
                     (Z_to_bv 64 (p + Z.of_nat (length tl))) (Z_to_bv 64 (p + Z.of_nat (length tl))) a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13d24) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 h) (Z_to_bv 64 (p + Z.of_nat (length tl))) (Z_to_bv 64 p)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d0c) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply crs_l2; eauto.
Qed.

Lemma crs_loop3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p h : Z) (tl : list byte),
  bytes_at rsegs m p tl -> tl <> [] -> p + Z.of_nat (length tl) < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a2' a3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (djb2 h (zb tl))) a2' a3' a4 a5 a6 a7
                     (Z_to_bv 64 (p + Z.of_nat (length tl))) (Z_to_bv 64 (p + Z.of_nat (length tl)))
                     s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13e00) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 h) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 (p + Z.of_nat (length tl))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13de8) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply crs_l3; eauto.
Qed.
