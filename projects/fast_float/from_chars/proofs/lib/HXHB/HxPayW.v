(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Notation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Notation PAYMAX := 67108864%Z (only parsing).
(* [comment removed for export] *)
Notation PAYPMIN := 4096%Z (only parsing).

Lemma slit64 : forall z, (- 2 ^ 63 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land7 : forall x, (0 <= x)%Z -> Z.land x 7 = (x mod 8)%Z.
Proof. intros x Hx. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Section PAY.
  Variables (m : word -> option byte) (pbs : list byte) (P PS Q R : Z).
  #[local] Notation N := (Z.of_nat (length pbs)).
  Hypothesis PAYB : bytes_at ASEGS m P pbs.
  Hypothesis HN : (1 <= N <= PAYMAX)%Z.
  Hypothesis HP : (P mod 8 = 0 /\ PAYPMIN <= P <= 140737488355072)%Z.
  Hypothesis HPS : (8 * (PS - ASAN_B) = P)%Z.
  Hypothesis HQR : (N = 8 * Q + R /\ 0 <= R < 8 /\ 0 <= Q)%Z.
  Hypothesis SHA : shz ASEGS m PS Q.
  Hypothesis SHB : (R <> 0)%Z -> bytes_at ASEGS m (PS + Q) [Z_to_bv 8 R].

  (* [comment removed for export] *)
  #[using="HP HPS"] Lemma pay_gran : forall i, (0 <= i < N)%Z -> ((P + i) / 8 + ASAN_B = PS + i / 8)%Z.
  Proof. LiaFast.lf_pins (fun (HP HPS : LiaFast.U) => LiaFast.u0). intros i Hi. destruct HP as [HP1 HP2]. Z.div_mod_to_equations. lia. Qed.
  #[using="pbs HP HPS"] Lemma pay_full : forall i, (0 <= i < 8 * Q)%Z -> (PS <= (P + i) / 8 + ASAN_B /\ (P + i) / 8 + ASAN_B + 1 <= PS + Q)%Z.
  Proof. LiaFast.lf_pins (fun (pbs HP HPS : LiaFast.U) => LiaFast.u0). intros i Hi. destruct HP as [HP1 HP2]. Z.div_mod_to_equations. lia. Qed.
End PAY.

(* [comment removed for export] *)
Section C1B.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pbs : list byte) (P PS Q R i : Z).
  #[local] Notation N := (Z.of_nat (length pbs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis PAYB : bytes_at ASEGS m P pbs.
  Hypothesis HN : (1 <= N <= PAYMAX)%Z.
  Hypothesis HP : (P mod 8 = 0 /\ PAYPMIN <= P <= 140737488355072)%Z.
  Hypothesis HPS : (8 * (PS - ASAN_B) = P)%Z.
  Hypothesis HQR : (N = 8 * Q + R /\ 0 <= R < 8 /\ 0 <= Q)%Z.
  Hypothesis SHA : shz ASEGS m PS Q.
  Hypothesis SHB : (R <> 0)%Z -> bytes_at ASEGS m (PS + Q) [Z_to_bv 8 R].
  Hypothesis HI : (0 <= i < N)%Z.

  #[local] Notation C1ST pc x11 x12 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Zw (P + i)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Zw ASAN_B) x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition c1b_post : machine_state -> Prop := fun ms' =>
    exists y11 y12 : word, ms' = C1ST 0x908cc y11 y12.

  #[using="pbs PS Q R HN HP HPS HQR SHA SHB HI"] Lemma blockC1B : forall (x11 x12 : word), evt ASEGS c1b_post (C1ST 0x908bc x11 x12).
  Proof. LiaFast.lf_pins (fun (pbs PS Q R HN HP HPS HQR SHA SHB HI : LiaFast.U) => LiaFast.u0).
    intros x11 x12. pose proof (shz_bound _ _ _ _ SHA) as BT.
    destruct HP as [HP1 HP2]. destruct HQR as (HQ1 & HQ2 & HQ3).
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    destruct (Z_lt_ge_dec i (8 * Q)) as [Hfull|Hpart].
    - assert (G0 : (PS <= (P + i) / 8 + ASAN_B /\ (P + i) / 8 + ASAN_B + 1 <= PS + Q)%Z) by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply evt_done. do 2 eexists. reflexivity.
    - assert (HR0 : (R <> 0)%Z) by lia.
      pose proof (SHB HR0) as TB.
      pose proof (txt_read ASEGS m (PS + Q) [Z_to_bv 8 R] 0 TB ltac:(cbn [length]; lia)) as RDB.
      change (nth (Z.to_nat 0) [Z_to_bv 8 R] (Z_to_bv 8 0)) with (Z_to_bv 8 R) in RDB.
      replace (PS + Q + 0)%Z with ((P + i) / 8 + ASAN_B)%Z in RDB by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      clear RDB. rewrite (sxb_lit_pos R) by lia.
      step. (* [comment removed for export] *)
      if_cases Hz; [| cond_cleanup Hz; exfalso; rewrite ?unsigned_lit in Hz by lia; lia].
      cond_cleanup Hz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb.
      { cond_cleanup Hb. exfalso. rewrite (land7 (P + i)) in Hb by lia. rewrite !slit64 in Hb by (Z.div_mod_to_equations; lia).
        Z.div_mod_to_equations. lia. }
      cond_cleanup Hb.
      step. (* [comment removed for export] *)
      apply evt_done. do 2 eexists. reflexivity.
  Qed.
End C1B.

(* [comment removed for export] *)
Section L1B.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pbs : list byte) (P i : Z).
  #[local] Notation N := (Z.of_nat (length pbs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis PAYB : bytes_at ASEGS m P pbs.
  Hypothesis HN : (1 <= N <= PAYMAX)%Z.
  Hypothesis HP : (PAYPMIN <= P <= 140737488355072)%Z.
  Hypothesis HI : (0 <= i < N)%Z.

  #[local] Notation L1ST pc x11 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Zw (P + i)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition l1b_post : machine_state -> Prop := fun ms' => ms' = L1ST 0x908d8 (Zw (tx pbs i)).

  #[using="PAYB HI"] Lemma blockL1B : forall (x11 : word), evt ASEGS l1b_post (L1ST 0x908d4 x11).
  Proof. LiaFast.lf_pins (fun (PAYB HI : LiaFast.U) => LiaFast.u0).
    intros x11. pose proof (tx_range pbs i) as Ri.
    txt_rd PAYB i RD.
    step. (* [comment removed for export] *)
    clear RD. fold_tx pbs i.
    apply evt_done. reflexivity.
  Qed.
End L1B.

(* [comment removed for export] *)
Section AFB.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pbs : list byte) (P PS Q R i : Z).
  #[local] Notation N := (Z.of_nat (length pbs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis PAYB : bytes_at ASEGS m P pbs.
  Hypothesis HN : (1 <= N <= PAYMAX)%Z.
  Hypothesis HP : (P mod 8 = 0 /\ PAYPMIN <= P <= 140737488355072)%Z.
  Hypothesis HPS : (8 * (PS - ASAN_B) = P)%Z.
  Hypothesis HQR : (N = 8 * Q + R /\ 0 <= R < 8 /\ 0 <= Q)%Z.
  Hypothesis SHA : shz ASEGS m PS Q.
  Hypothesis SHB : (R <> 0)%Z -> bytes_at ASEGS m (PS + Q) [Z_to_bv 8 R].
  Hypothesis HI : (0 <= i < N)%Z.

  #[local] Notation AFST pc x13 x30 x31 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Zw ASAN_B) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition afb_post : machine_state -> Prop := fun ms' =>
    exists y30 y31 : word, ms' = AFST 0x90024 (Zw (tx pbs i)) y30 y31.

  #[using="PS Q R PAYB HN HP HPS HQR SHA SHB HI"] Lemma blockAFB : forall (x30 x31 : word), evt ASEGS afb_post (AFST 0x90010 (Zw (P + i)) x30 x31).
  Proof. LiaFast.lf_pins (fun (PS Q R PAYB HN HP HPS HQR SHA SHB HI : LiaFast.U) => LiaFast.u0).
    intros x30 x31. pose proof (shz_bound _ _ _ _ SHA) as BT.
    pose proof (tx_range pbs i) as Ri.
    destruct HP as [HP1 HP2]. destruct HQR as (HQ1 & HQ2 & HQ3).
    assert (GR : ((P + i) / 8 + ASAN_B = PS + i / 8)%Z) by (Z.div_mod_to_equations; lia).
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    destruct (Z_lt_ge_dec i (8 * Q)) as [Hfull|Hpart].
    - assert (G0 : (PS <= (P + i) / 8 + ASAN_B /\ (P + i) / 8 + ASAN_B + 1 <= PS + Q)%Z) by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      txt_rd PAYB i RD.
      step. (* [comment removed for export] *)
      clear RD. fold_tx pbs i.
      apply evt_done. do 2 eexists. reflexivity.
    - assert (HR0 : (R <> 0)%Z) by lia.
      pose proof (SHB HR0) as TB.
      pose proof (txt_read ASEGS m (PS + Q) [Z_to_bv 8 R] 0 TB ltac:(cbn [length]; lia)) as RDB.
      change (nth (Z.to_nat 0) [Z_to_bv 8 R] (Z_to_bv 8 0)) with (Z_to_bv 8 R) in RDB.
      replace (PS + Q + 0)%Z with ((P + i) / 8 + ASAN_B)%Z in RDB by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      clear RDB. rewrite (sxb_lit_pos R) by lia.
      step. (* [comment removed for export] *)
      if_cases Hz; [| cond_cleanup Hz; exfalso; rewrite ?unsigned_lit in Hz by lia; lia].
      cond_cleanup Hz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb.
      2: { cond_cleanup Hb. exfalso. rewrite (land7 (P + i)) in Hb by lia. rewrite !slit64 in Hb by (Z.div_mod_to_equations; lia).
           Z.div_mod_to_equations. lia. }
      cond_cleanup Hb.
      txt_rd PAYB i RD.
      step. (* [comment removed for export] *)
      clear RD. fold_tx pbs i.
      apply evt_done. do 2 eexists. reflexivity.
  Qed.
End AFB.

(* [comment removed for export] *)
Section C2B.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pbs : list byte) (P PS Q R i : Z).
  #[local] Notation N := (Z.of_nat (length pbs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis PAYB : bytes_at ASEGS m P pbs.
  Hypothesis HN : (1 <= N <= PAYMAX)%Z.
  Hypothesis HP : (P mod 8 = 0 /\ PAYPMIN <= P <= 140737488355072)%Z.
  Hypothesis HPS : (8 * (PS - ASAN_B) = P)%Z.
  Hypothesis HQR : (N = 8 * Q + R /\ 0 <= R < 8 /\ 0 <= Q)%Z.
  Hypothesis SHA : shz ASEGS m PS Q.
  Hypothesis SHB : (R <> 0)%Z -> bytes_at ASEGS m (PS + Q) [Z_to_bv 8 R].
  Hypothesis HI : (0 <= i < N)%Z.

  #[local] Notation C2ST pc x14 x15 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Zw (P + i)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Zw ASAN_B) x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition c2b_post : machine_state -> Prop := fun ms' =>
    exists y14 y15 : word, ms' = C2ST 0x9090c y14 y15.

  #[using="pbs PS Q R HN HP HPS HQR SHA SHB HI"] Lemma blockC2B : forall (x14 x15 : word), evt ASEGS c2b_post (C2ST 0x908fc x14 x15).
  Proof. LiaFast.lf_pins (fun (pbs PS Q R HN HP HPS HQR SHA SHB HI : LiaFast.U) => LiaFast.u0).
    intros x14 x15. pose proof (shz_bound _ _ _ _ SHA) as BT.
    destruct HP as [HP1 HP2]. destruct HQR as (HQ1 & HQ2 & HQ3).
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    destruct (Z_lt_ge_dec i (8 * Q)) as [Hfull|Hpart].
    - assert (G0 : (PS <= (P + i) / 8 + ASAN_B /\ (P + i) / 8 + ASAN_B + 1 <= PS + Q)%Z) by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply evt_done. do 2 eexists. reflexivity.
    - assert (HR0 : (R <> 0)%Z) by lia.
      pose proof (SHB HR0) as TB.
      pose proof (txt_read ASEGS m (PS + Q) [Z_to_bv 8 R] 0 TB ltac:(cbn [length]; lia)) as RDB.
      change (nth (Z.to_nat 0) [Z_to_bv 8 R] (Z_to_bv 8 0)) with (Z_to_bv 8 R) in RDB.
      replace (PS + Q + 0)%Z with ((P + i) / 8 + ASAN_B)%Z in RDB by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      clear RDB. rewrite (sxb_lit_pos R) by lia.
      step. (* [comment removed for export] *)
      if_cases Hz; [| cond_cleanup Hz; exfalso; rewrite ?unsigned_lit in Hz by lia; lia].
      cond_cleanup Hz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb.
      2: { cond_cleanup Hb. exfalso. rewrite (land7 (P + i)) in Hb by lia. rewrite !slit64 in Hb by (Z.div_mod_to_equations; lia).
           Z.div_mod_to_equations. lia. }
      cond_cleanup Hb.
      apply evt_done. do 2 eexists. reflexivity.
  Qed.
End C2B.

(* [comment removed for export] *)
Section LDB.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pbs : list byte) (P i : Z).
  #[local] Notation N := (Z.of_nat (length pbs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis PAYB : bytes_at ASEGS m P pbs.
  Hypothesis HN : (1 <= N <= PAYMAX)%Z.
  Hypothesis HP : (PAYPMIN <= P <= 140737488355072)%Z.
  Hypothesis HI : (1 <= i < N)%Z.

  #[local] Notation LDST pc x12 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Zw (P + i - 1)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition ldb_post : machine_state -> Prop := fun ms' => ms' = LDST 0x90918 (Zw (tx pbs i)).

  #[using="PAYB HI"] Lemma blockLDB : forall (x12 : word), evt ASEGS ldb_post (LDST 0x90914 x12).
  Proof. LiaFast.lf_pins (fun (PAYB HI : LiaFast.U) => LiaFast.u0).
    intros x12. pose proof (tx_range pbs i) as Ri.
    txt_rd PAYB i RD.
    step. (* [comment removed for export] *)
    clear RD. fold_tx pbs i.
    apply evt_done. reflexivity.
  Qed.
End LDB.
