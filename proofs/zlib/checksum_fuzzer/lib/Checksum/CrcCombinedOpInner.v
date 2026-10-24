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

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcWord.


Lemma addiw0_word_SX : forall v, (0 <= v < 2^32)%Z ->
  Z_to_bv 64 (bv_swrap 32 (v + 0)) = Z_to_bv 64 (SX v).
Proof.
  intros v Hv. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  rewrite Z.add_0_r, swrap32_SX by exact Hv.
  rewrite Z.mod_small by (apply SX_range; exact Hv). reflexivity.
Qed.

Section Operator.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : Z).
  Hypothesis Ha : (0 < a < 2^32)%Z.
  Variable Q : machine_state -> Prop.
  Notation AT pc x10 x13 x14 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 a1 x13 x14 (Z_to_bv 64 18446744073402876704) (Z_to_bv 64 (SX a)) x16 a7
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma op_shift : forall (k : nat) (B b P : Z) x16,
    (0 <= B < 2^64)%Z -> (B mod 2^32 = b)%Z -> (0 <= b < 2^32)%Z -> (1 <= k <= 31)%nat ->
    (forall x16', evt rsegs Q (AT 0x14ca4 (Z_to_bv 64 (SX (cstep b))) (Z_to_bv 64 P)
      (Z_to_bv 64 (SX (2 ^ Z.of_nat (k-1)))) x16')) ->
    evt rsegs Q (AT 0x14c8c (Z_to_bv 64 B) (Z_to_bv 64 P)
      (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x16).
  Proof.
    intros k B b P x16 HB EB Hb Hk H.
    pose proof (pow2k_range k ltac:(lia)) as Hm.
    pose proof (SX_range (2^Z.of_nat k) ltac:(lia)) as Rm.
    pose proof (cstep_range b Hb) as Rc.
    pose proof (SX_range _ Rc) as Rc'.
    pose proof (signmask_low32 B b HB EB) as SIGN.
    change (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl B 63))) 63 mod 18446744073709551616) 18446744073402876704 = if Z.odd b then 18446744073402876704 else 0)%Z in SIGN.
    do 6 zstep.
    rewrite (srliw1_low32 B b EB Hb).
    rewrite (srliw1_SX (2 ^ Z.of_nat k)) by lia.
    rewrite SIGN. rewrite (shr1_mod64 b Hb). rewrite (bstep_SX b Hb).
    rewrite (pow2k_half k) by lia.
    rewrite <- (SX_small (2 ^ Z.of_nat (k - 1))) by (pose proof (pow2k_range (k-1)%nat ltac:(lia)); split; [lia|]; apply Z.pow_lt_mono_r; lia).
    apply H.
  Qed.

  Lemma op_inner : forall (k : nat) (B b P p : Z) x16,
    (0 <= B < 2^64)%Z -> (B mod 2^32 = b)%Z -> (0 <= b < 2^32)%Z ->
    (0 <= P < 2^64)%Z -> (P mod 2^32 = p)%Z -> (0 <= p < 2^32)%Z ->
    (k <= 31)%nat -> lowbits_nz a (Z.of_nat k) ->
    (forall B' P' x14' x16', (0 <= P' < 2^64)%Z ->
       (P' mod 2^32 = mm_loop (S k) (2 ^ Z.of_nat k) a b p)%Z ->
       evt rsegs Q (AT 0x14cbc (Z_to_bv 64 B') (Z_to_bv 64 P') x14' x16')) ->
    evt rsegs Q (AT 0x14ca4 (Z_to_bv 64 B) (Z_to_bv 64 P)
      (Z_to_bv 64 (SX (2 ^ Z.of_nat k))) x16).
  Proof.
    induction k as [|k IH]; intros B b P p x16 HB EB Hb HP EP Hp Hk LB CONT.
    - destruct (lowbits_0 a ltac:(lia) LB) as [T0 L0].
      change (2 ^ Z.of_nat 0)%Z with 1%Z in *. change (SX 1) with 1%Z.
      pose proof (land_bound_l 32 1 a ltac:(lia) ltac:(lia)) as RL.
      pose proof (SX_range a ltac:(lia)) as Ra.
      zstep. try rewrite (Z.mod_small (SX a) 18446744073709551616) by exact Ra. rewrite (land_small_SX 1 a) by lia.
      zstep. if_cases K; zify_cond K; try rewrite Z.mod_small in K by lia.
      { exfalso. change (Z.land (2^0) a = 0)%Z in K. apply land_pow2_zero in K; [|lia]. rewrite T0 in K. discriminate. }
      do 4 zstep.
      if_cases K2; zify_cond K2. 1:{ exfalso. apply K2. reflexivity. }
      apply CONT.
      + apply lxor_bound; lia.
      + rewrite low32_xor, EP, EB.
        assert (KNZ : (Z.land 1 a <> 0)%Z).
        { exact K. }
        rewrite (mm_loop_exit 0 1 a b p KNZ L0). reflexivity.
    - pose proof (pow2k_range (S k) Hk) as Hm.
      pose proof (SX_range (2^Z.of_nat (S k)) ltac:(lia)) as Rm.
      pose proof (land_bound_l 32 (2^Z.of_nat (S k)) a ltac:(lia) ltac:(lia)) as RL.
      pose proof (lxor_bound 32 p b ltac:(lia) Hp Hb) as RX.
      pose proof (lxor_bound 64 P B ltac:(lia) HP HB) as RXP.
      pose proof (cstep_range b Hb) as Rc.
      pose proof (SX_range _ Rc) as Rc'.
      pose proof (SX_mod32 _ Rc) as Ec'.
      pose proof (SX_range a ltac:(lia)) as Ra.
      zstep. try rewrite (Z.mod_small (SX a) 18446744073709551616) by exact Ra. rewrite land_SX by lia.
      zstep. if_cases K; zify_cond K; rewrite Z.mod_small in K by (apply SX_range; exact RL).
      + apply (proj1 (SX_nz _ RL)) in K.
        pose proof (land_pow2_zero a (Z.of_nat (S k)) ltac:(lia) K) as Tk.
        eapply op_shift; try eassumption; try lia. intros x16'.
        rewrite mm_loop_skip in CONT by exact K. rewrite pow2k_half in CONT by lia.
        replace (S k - 1)%nat with k in * by lia.
        eapply IH with (b:=cstep b) (p:=p); try eassumption; try lia.
        * replace (Z.of_nat k) with (Z.of_nat (S k)-1)%Z by lia. apply lowbits_step; try lia; try exact LB; left; exact Tk.
      + assert (K' : (Z.land (2^Z.of_nat (S k)) a <> 0)%Z).
        { intros E. apply K. rewrite E. reflexivity. }
        do 3 zstep.
        rewrite (addiw_m1_SX (2^Z.of_nat (S k))) by lia.
        rewrite (Z.mod_small (2^Z.of_nat (S k)-1) 18446744073709551616) by lia.
        try rewrite (Z.mod_small (SX a) 18446744073709551616) by exact Ra.
        rewrite land_small_SX by lia.
        pose proof (land_bound_l 31 (2^Z.of_nat (S k)-1) a ltac:(lia) ltac:(lia)) as RL2.
        zstep. if_cases K2; zify_cond K2; try rewrite Z.mod_small in K2 by lia.
        * assert (K2' : (Z.land (2^Z.of_nat (S k)-1) a <> 0)%Z).
          { intros E. apply K2. rewrite E. reflexivity. }
          eapply op_shift; try eassumption; try lia. intros x16'.
          rewrite mm_loop_cont in CONT by (first [exact K'|exact K2']). rewrite pow2k_half in CONT by lia.
          replace (S k - 1)%nat with k in * by lia.
          eapply IH with (b:=cstep b) (p:=Z.lxor p b); try eassumption; try lia.
          -- rewrite low32_xor, EP, EB. reflexivity.
          -- replace (Z.of_nat k) with (Z.of_nat (S k)-1)%Z by lia. apply lowbits_step; try lia; try exact LB; right; exact K2'.
        *
          apply CONT; [exact RXP|].
          rewrite low32_xor, EP, EB. rewrite mm_loop_exit by (first [exact K'|exact K2]). reflexivity.
  Qed.
End Operator.
