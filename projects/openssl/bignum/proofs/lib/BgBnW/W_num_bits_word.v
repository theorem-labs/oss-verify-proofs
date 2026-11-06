(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnArith BnNumBits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition BN_num_bits_word_entry := 0xf5674%Z.

Definition nbw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (l : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (num_bits_word l)) a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgpsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono bgpsegs m m' /\ mem_inv bgpsegs m'
    /\ stk bgpsegs m' lo (bv_unsigned sp).

Lemma BN_num_bits_word_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk bgpsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgpsegs m ->
  evt bgpsegs (nbw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xf5674) fc None m (seg_rom bgpsegs)).
Proof.
  intros until lo. intros ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgpsegs m) as WM.
  pose proof (zr_word a0) as RL. unfold inr64 in RL. change (2 ^ 64)%Z with 18446744073709551616%Z in RL.
  carve_frame 16%nat ST.
  do 33 zstep.

  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let v := reg_val 10%Z in
    lazymatch v with Z_to_bv 64 (bv_swrap 32 ?e) =>
      replace (Z_to_bv 64 (bv_swrap 32 e)) with (Z_to_bv 64 (num_bits_word (bv_unsigned a0)))
        by (f_equal; change e with (nbw_m (bv_unsigned a0)); rewrite (nbw_m_correct _ RL);
            pose proof (num_bits_word_range _ RL); symmetry; apply bn_swrap32_small; lia)
    end
  end.
  do 4 zstep.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.
