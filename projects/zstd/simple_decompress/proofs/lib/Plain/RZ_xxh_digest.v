(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_frame_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DIGEST.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (STA : Z) (st : list byte).
  Hypothesis STB : bytes_at psegs m STA st.
  Hypothesis STL : zlen st = 88.
  Hypothesis R0 : 4096 <= STA.
  Hypothesis R1 : STA + 88 <= 2^47.
  Hypothesis MI : mem_inv psegs m.

  Notation POST := (zd_xxh_digest_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m).
  (* [comment removed for export] *)
  Notation STpc pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma d_fin : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 : word),
    evt psegs POST (STpc 0x27580 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30).
  Proof.
    intros.
    kx_auto [] 40%nat [KZImg 0x10fc8 0x111c8; KZRange STA 4096 (2^47)] [(STA, 88)].
    zstep. apply evt_done. unfold zd_xxh_digest_post. do 14 eexists. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma d_l1 : forall (n : nat) p q (x5 x6 x7 x11 x12 x13 x14 x16 x17 x28 x29 x30 : word),
    q - p <= Z.of_nat n -> 0 <= p < q -> q <= 32 ->
    evt psegs POST (STpc 0x27558 x5 x6 x7 (Z_to_bv 64 (STA + 40 + p)) x11 x12 x13 x14 (Z_to_bv 64 (STA + 40 + q)) x16 x17 x28 x29 x30).
  Proof.
    induction n as [|n IH]; intros p q x5 x6 x7 x11 x12 x13 x14 x16 x17 x28 x29 x30 RN RP RQ; [exfalso; lia|].
    kx_auto [0x27558; 0x27580] 40%nat [KZRange STA 4096 (2^47); KZRange p 0 32; KZRange q 0 33] [(STA, 88)].
    - replace (STA + p + 41) with (STA + 40 + (p + 1)) by lia.
      rewrite ?Z.mod_small in KXBR by lia.
      eapply (IH (p + 1) q); lia.
    - apply d_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma d_l4 : forall p r (x5 x6 x7 x11 x12 x13 x14 x16 x17 x28 x29 x30 : word),
    0 <= p -> 0 <= r <= 7 -> p + r <= 31 ->
    evt psegs POST (STpc 0x274f4 x5 x6 x7 (Z_to_bv 64 (STA + 40 + p)) x11 x12 x13 x14 (Z_to_bv 64 r) x16 x17 x28 x29 x30).
  Proof.
    intros p r x5 x6 x7 x11 x12 x13 x14 x16 x17 x28 x29 x30 RP RR RPR.
    kx_auto [0x27558; 0x27580] 60%nat [KZImg 0x10fc8 0x111c8; KZRange STA 4096 (2^47); KZRange p 0 32; KZRange r 0 8] [(STA, 88)].
    - apply d_fin.
    - rewrite ?Z.mod_small in * by lia.
      replace (STA + (p + r) + 40) with (STA + 40 + (p + r)) by lia.
      eapply (d_l1 (Z.to_nat r) p (p + r)); lia.
    - apply d_fin.
    - rewrite ?Z.mod_small in * by lia.
      replace (STA + p + 44) with (STA + 40 + (p + 4)) by lia.
      replace (STA + (p + r) + 40) with (STA + 40 + (p + r)) by lia.
      eapply (d_l1 (Z.to_nat r) (p + 4) (p + r)); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma d_l8 : forall (n : nat) p r (x5 x6 x7 x11 x12 x13 x14 x16 x28 x29 x30 : word),
    r <= Z.of_nat n -> 0 <= p -> 8 <= r -> p + r <= 31 ->
    evt psegs POST (STpc 0x27464 x5 x6 x7 (Z_to_bv 64 (STA + 40 + p)) x11 x12 x13 x14 (Z_to_bv 64 r) x16 (Z_to_bv 64 7) x28 x29 x30).
  Proof.
    induction n as [|n IH]; intros p r x5 x6 x7 x11 x12 x13 x14 x16 x28 x29 x30 RN RP RR RPR; [exfalso; lia|].
    kx_auto [0x27464; 0x274f4] 60%nat [KZRange STA 4096 (2^47); KZRange p 0 32; KZRange r 8 32] [(STA, 88)].
    - rewrite ?Z.mod_small in * by lia.
      replace (STA + p + 48) with (STA + 40 + (p + 8)) by lia.
      eapply (IH (p + 8) (r + -8)); lia.
    - rewrite ?Z.mod_small in * by lia.
      replace (STA + p + 48) with (STA + 40 + (p + 8)) by lia.
      eapply (d_l4 (p + 8) (r + -8)); lia.
  Qed.

  Lemma digest_body : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 : word),
    evt psegs POST (STpc PZD_XXH_DIGEST t0 t1 t2 (Z_to_bv 64 STA) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5).
  Proof.
    intros. unfold PZD_XXH_DIGEST.
    kx_auto [0x27428; 0x27448] 80%nat [KZImg 0x10fc8 0x111c8; KZRange STA 4096 (2^47)] [(STA, 88)].
    all: kx_abs.
    all: lazymatch goal with |- context [Z_to_bv 64 STA] => idtac end.
    all: match goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
           let tot := fresh "tot" in set (tot := w) in *; clearbody tot end.
    all: zstep.
    all: match goal with |- context [Z.land (bv_unsigned ?w) 31] =>
           assert (RR : 0 <= Z.land (bv_unsigned w) 31 <= 31)
             by (replace (Z.land (bv_unsigned w) 31) with (bv_unsigned w mod 32)
                   by (symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
                 pose proof (Z.mod_pos_bound (bv_unsigned w) 32 ltac:(lia)); lia);
           set (r := Z.land (bv_unsigned w) 31) in * end.
    all: zstep; zstep; zstep.
    all: if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (STA + 40) with (STA + 40 + 0) by lia. eapply d_l4; lia.
    - zstep. zstep. zstep. replace (STA + 40) with (STA + 40 + 0) by lia. eapply (d_l8 (Z.to_nat r)); lia.
    - zstep. zstep. zstep. replace (STA + 40) with (STA + 40 + 0) by lia. eapply (d_l8 (Z.to_nat r)); lia.
    - zstep. replace (STA + 40) with (STA + 40 + 0) by lia. eapply d_l4; lia.
  Qed.
End DIGEST.

Theorem zd_xxh_digest_proof : zd_xxh_digest_stmt.
Proof.
  intros until st. intros STB STL R0 R1 MI ->.
  eapply digest_body; eassumption.
Qed.
Print Assumptions zd_xxh_digest_proof.
