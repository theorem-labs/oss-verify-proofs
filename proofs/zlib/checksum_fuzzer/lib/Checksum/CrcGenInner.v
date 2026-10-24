(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Functional multiplication loop adapted from the pinned Varnish proof to
    the actual zlib checksum_fuzzer instruction layout and register allocation. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Img0 CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.transport_chunks segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.footprint_after_store segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.transport_after_call segs m m' MU WM ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.addr_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.mlia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require StepFast.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.step_core segs R F pc fc rv m ro ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.zstep ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Destzna.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_exs PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_exs PO.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_ands PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require WeqGuard TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.WeqGuard.weq_guard; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Stor0fe.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Dieta54.
Local Ltac lia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section X2N.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv rsegs m.

  (* [comment removed for export] *)
  Notation AT pc x5 x10 x11 x12 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 x11 x12 (Z_to_bv 64 0x11954) (Z_to_bv 64 18446744073402876704) x15 x16 x17
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Section AnyPost.
  Variable Q : machine_state -> Prop.

  (* [comment removed for export] *)
  Lemma x2n_shift : forall (k : nat) (a b p : Z) x5 x10 x12,
    (0 < a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (0 <= p < 2^32)%Z -> (1 <= k <= 31)%nat ->
    (forall x5', evt rsegs Q (AT 0x14d38 x5' x10 x12 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) (Z_to_bv 64 (SX (2 ^ Z.of_nat (k - 1)))) (Z_to_bv 64 (SX (cstep b))))) ->
    evt rsegs Q (AT 0x14d20 x5 x10 x12 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) (Z_to_bv 64 (SX b))).
  Proof.
    intros k a b p x5 x10 x12 Ha Hb Hp Hk H.
    pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
    assert (Hm : (0 < 2 ^ Z.of_nat k <= 2^31)%Z). { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]. }
    pose proof (SX_range (2 ^ Z.of_nat k) ltac:(lia)) as Rm.
    pose proof (cstep_range b Hb) as Rc. pose proof (SX_range _ Rc) as Rc'.
    do 6 zstep.
    rewrite (srliw1_SX b Hb). rewrite (srliw1_SX (2 ^ Z.of_nat k)) by lia.
    rewrite (signmask_SX b Hb). rewrite (shr1_mod64 b Hb). rewrite (bstep_SX b Hb).
    rewrite (pow2k_half k) by lia.
    rewrite <- (SX_small (2 ^ Z.of_nat (k - 1))) by (pose proof (pow2k_range (k-1)%nat ltac:(lia)); split; [lia|]; apply Z.pow_lt_mono_r; lia).
    apply H.
  Qed.

  Lemma x2n_inner : forall (k : nat) (a b p : Z) x5 x10 x12,
    (0 < a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (0 <= p < 2^32)%Z -> (k <= 31)%nat ->
    lowbits_nz a (Z.of_nat k) ->
    (forall x5' x15' x17',
       evt rsegs Q (AT 0x14cec x5' x10 x12 (Z_to_bv 64 (SX (mm_loop (S k) (2 ^ Z.of_nat k) a b p))) (Z_to_bv 64 (SX a)) x17' x15')) ->
    evt rsegs Q (AT 0x14d38 x5 x10 x12 (Z_to_bv 64 (SX p)) (Z_to_bv 64 (SX a)) (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) (Z_to_bv 64 (SX b))).
  Proof.
    induction k as [|k IH]; intros a b p x5 x10 x12 Ha Hb Hp Hk LB CONT.
    - (* [comment removed for export] *)
      destruct (lowbits_0 a ltac:(lia) LB) as [T0 L0].
      pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
      change (2 ^ Z.of_nat 0)%Z with 1%Z in *. change (SX 1) with 1%Z.
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. rewrite land_small_SX in K by lia. change 1%Z with (2^0)%Z in K. apply land_pow2_zero in K; [|lia]. rewrite T0 in K. discriminate. }
      do 4 zstep.
      change (bv_swrap 32 (1 + -1)) with 0%Z. rewrite Z.land_0_l.
      if_cases K2; zify_cond K2. 1:{ exfalso. apply K2. reflexivity. }
      rewrite (lxor_SX p b) by lia.
      rewrite land_small_SX in K by lia.
      rewrite mm_loop_exit in CONT by (first [exact K | exact L0]).
      zstep. apply CONT.
    - pose proof (SX_range a ltac:(lia)) as Ra. pose proof (SX_range b Hb) as Rb. pose proof (SX_range p Hp) as Rp.
      pose proof (pow2k_range (S k) Hk) as Hm. pose proof (SX_range (2 ^ Z.of_nat (S k)) ltac:(lia)) as Rm.
      pose proof (lxor_bound 32 p b ltac:(lia) Hp Hb) as Rx. pose proof (SX_range _ Rx) as Rx'.
      zstep. zstep. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        rewrite land_SX in K by lia. apply (proj1 (SX_nz _ (land_bound_l 32 (2 ^ Z.of_nat (S k)) a ltac:(lia) ltac:(lia)))) in K.
        pose proof (land_pow2_zero a (Z.of_nat (S k)) ltac:(lia) K) as Tk.
        apply x2n_shift; try lia. intros x5'.
        rewrite mm_loop_skip in CONT by exact K. rewrite pow2k_half in CONT by lia.
        replace (S k - 1)%nat with k in * by lia.
        apply IH; try lia. 1:{ apply cstep_range; lia. } 2:{ exact CONT. }
        replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (left; exact Tk).
      + (* [comment removed for export] *)
        do 4 zstep.
        rewrite (addiw_m1_SX (2 ^ Z.of_nat (S k))) by lia.
        rewrite (Z.mod_small (2 ^ Z.of_nat (S k) - 1) 18446744073709551616) by lia.
        rewrite (land_small_SX (2 ^ Z.of_nat (S k) - 1) a) by lia.
        rewrite (lxor_SX p b) by lia.
        rewrite land_SX in K by lia.
        assert (K' : Z.land (2 ^ Z.of_nat (S k)) a <> 0%Z). { intros E. apply K. rewrite E. reflexivity. }
        if_cases K2; zify_cond K2.
        * apply x2n_shift; try lia. intros x5'.
          rewrite mm_loop_cont in CONT by (first [exact K' | exact K2]). rewrite pow2k_half in CONT by lia.
          replace (S k - 1)%nat with k in * by lia.
          apply IH; try lia. 1:{ apply cstep_range; lia. } 2:{ exact CONT. }
          replace (Z.of_nat k) with (Z.of_nat (S k) - 1)%Z by lia. apply lowbits_step; try lia; try exact LB; try (right; exact K2).
        * rewrite mm_loop_exit in CONT by (first [exact K' | exact K2]). zstep. apply CONT.
  Qed.

  End AnyPost.
End X2N.
