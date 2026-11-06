(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs.
Import ListNotations.
Open Scope bv_scope.

Definition imemcpy_entry := 0x6991c%Z.

Definition imemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (n : Z) (src : list byte) (S : Z) (a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3' a4' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat n) src]
    /\ bytes_at asegs m' S src.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n < 2^64 /\ 0 <= D /\ D + n < 2^64 /\ 0 <= n < 2^63)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 n src S a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m).

  Notation ST pc mm x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at asegs m1 S src /\ u8arr asegs m1 D bs /\ copied src bs (Z.to_nat P) /\
    mem_inv asegs m1 /\ munch W m m1 /\ wmono asegs m m1.
  Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

  Ltac fin :=
    lazymatch goal with
    | DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
        let E := fresh "E" in
        pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
        apply rw_cells_of_u8arr in DST; rewrite LEN in DST
    end;
    finish2.

  Lemma imc_loop : forall (K : nat) m1 bs (P : Z) xa1 xa3 x14,
    Z.to_nat (n - P) = K ->
    INV m1 bs P -> (0 <= P < n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt asegs POST (ST 0x69928 m1 xa1 (Z_to_bv 64 (D + n)) xa3 x14).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind; intros m1 bs P xa1 xa3 x14 HK I HP -> ->; open_inv I.
    window P 1%nat HW.
    ld1 HW 0%nat. st1 HW 0%nat.
    zstep. zstep. zstep. if_cases KK; zify_cond KK.
    - replace (D + P + 1)%Z with (D + (P + 1))%Z by lia. replace (S + P + 1)%Z with (S + (P + 1))%Z by lia.
      eapply (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z); try reflexivity; try lia.
      split; [eassumption | split; [eassumption | split; [| repeat split; eassumption]]].
      replace (Z.to_nat (P + 1)) with (Z.to_nat (P + Z.of_nat 1)) by lia. assumption.
    - zstep.   fin.
  Qed.

  Lemma imemcpy_body : forall junk x13 x14,
    rw_cells asegs m D [CB (Z.to_nat n) junk] -> bytes_at asegs m S src -> mem_inv asegs m ->
    evt asegs POST (ST imemcpy_entry m a1 a2 x13 x14).
  Proof using AB LEN SEP.
    intros junk x13 x14 DST0 SRC MI. unfold imemcpy_entry.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST. pose proof (rw_cells_CB_length _ _ _ _ _ DST0) as LJ.
    pose proof (copied_0 src junk ltac:(rewrite LJ, LEN; reflexivity)) as CP. clear DST0.
    zstep. if_cases K0; zify_cond K0.
    -   change 0%nat with (Z.to_nat 0) in CP. zstep.   fin.
    - zstep. zstep.
      eapply (imc_loop (Z.to_nat (n - 0)) m junk 0); try reflexivity; try lia.
      + split; [exact SRC| split; [exact DST| split; [exact CP| repeat split; assumption]]].
      + rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.
End Proofs.

Theorem imemcpy_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte),
    rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
    bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
    (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
    (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z -> (bv_unsigned a1 + bv_unsigned a2 < 2^64)%Z -> (bv_unsigned a2 < 2^63)%Z ->
    mem_inv asegs m ->
    evt asegs (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 (bv_unsigned a2) src (bv_unsigned a1) a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 imemcpy_entry) fc None m (seg_rom asegs)).
Proof.
  intros. pose proof (bv_unsigned_in_range 64 a0). pose proof (bv_unsigned_in_range 64 a1). pose proof (bv_unsigned_in_range 64 a2).
  unfold bv_modulus in *.
  eapply imemcpy_body; eauto; cbn in *; lia.
Qed.
