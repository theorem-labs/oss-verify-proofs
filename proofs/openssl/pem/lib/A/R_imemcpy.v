(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import F_memcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.

Definition imemcpy_entry := 0x1d4e10%Z.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  Notation ST pc mm x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition INVi (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
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

  (* [comment removed for export] *)
  Lemma im_loop : forall (K : nat) m1 bs (P : Z) xa1 xa3 x14,
    Z.to_nat (n - P) = K -> INVi m1 bs P -> (0 <= P < n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt asegs POST (ST 0x1d4e1c m1 xa1 (Z_to_bv 64 (D + n)) xa3 x14).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind; intros m1 bs P xa1 xa3 x14 HK I HP -> ->; open_inv I.
    window P 1%nat HW.
    ld1 HW 0%nat. st1 HW 0%nat. zstep. zstep. zstep. if_cases K1; zify_cond K1.
    - eapply (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z); [reflexivity| | lia | f_equal; lia | f_equal; lia].
      split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]].
      lazymatch goal with CP : copied _ _ (Z.to_nat ?P') |- copied _ _ (Z.to_nat ?P'') =>
        first [ exact CP | replace (Z.to_nat P'') with (Z.to_nat P') by lia; exact CP ] end.
    - zstep. fin.
  Qed.

  Lemma imemcpy_body : forall junk,
    rw_cells asegs m D [CB (Z.to_nat n) junk] -> bytes_at asegs m S src -> mem_inv asegs m ->
    evt asegs POST (ST 0x1d4e10 m a1 a2 a3 a4).
  Proof using AB LEN SEP.
    intros junk DST0 SRC MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
    pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
    change 0%nat with (Z.to_nat 0) in CP. clear DST0.
    zstep. if_cases K0; zify_cond K0.
    - zstep. fin.
    - zstep. zstep.
      eapply (im_loop (Z.to_nat n) m junk 0%Z).
      1:{ f_equal; lia. }
      3:{ rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned. }
      3:{ rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned. }
      2:{ lia. }
      split; [eassumption | split; [eassumption | split; [ exact CP | repeat split; eassumption ]]].
  Qed.
End Proofs.

Lemma imemcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  length src = Z.to_nat (bv_unsigned a2) ->
  (bv_unsigned a1 + bv_unsigned a2 <= 2^64)%Z -> (bv_unsigned a0 + bv_unsigned a2 <= 2^64)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  bytes_at asegs m (bv_unsigned a1) src ->
  mem_inv asegs m ->
  evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d4e10) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros LEN B1 B2 SEP DST SRC MI.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R0, R1, R2. cbn in R0, R1, R2.
  eapply imemcpy_body; eauto. repeat split; lia.
Qed.
