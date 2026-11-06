(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.

Module HxPayW.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Notation ASEGS := Asan.M.loaded_segments.

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

Section C1.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
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
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Zw (P + i)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Zw ASAN_B) x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition c1_post : machine_state -> Prop := fun ms' =>
    exists y12 : word, ms' = C1ST 0x906b8 (Zw (tx pbs i)) y12.

  #[using="PS Q R PAYB HN HP HPS HQR SHA SHB HI"] Lemma blockC1 : forall (x11 x12 : word), evt ASEGS c1_post (C1ST 0x906a4 x11 x12).
  Proof. LiaFast.lf_pins (fun (PS Q R PAYB HN HP HPS HQR SHA SHB HI : LiaFast.U) => LiaFast.u0).
    intros x11 x12. pose proof (shz_bound _ _ _ _ SHA) as BT.
    pose proof (tx_range pbs i) as Ri.
    destruct HP as [HP1 HP2]. destruct HQR as (HQ1 & HQ2 & HQ3).
    assert (GR : ((P + i) / 8 + ASAN_B = PS + i / 8)%Z) by (Z.div_mod_to_equations; lia).
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    destruct (Z_lt_ge_dec i (8 * Q)) as [Hfull|Hpart].
    - (* [comment removed for export] *)
      assert (G0 : (PS <= (P + i) / 8 + ASAN_B /\ (P + i) / 8 + ASAN_B + 1 <= PS + Q)%Z) by (Z.div_mod_to_equations; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      txt_rd PAYB i RD.
      step. (* [comment removed for export] *)
      clear RD. fold_tx pbs i.
      apply evt_done. eexists. reflexivity.
    - (* [comment removed for export] *)
      assert (HR0 : (R <> 0)%Z) by lia.
      pose proof (SHB HR0) as TB.
      assert (Hq : (i / 8 = Q)%Z) by (Z.div_mod_to_equations; lia).
      pose proof (txt_read ASEGS m (PS + Q) [Z_to_bv 8 R] 0 TB ltac:(cbn [length]; lia)) as RDB.
      change (nth (Z.to_nat 0) [Z_to_bv 8 R] (Z_to_bv 8 0)) with (Z_to_bv 8 R) in RDB.
      replace (PS + Q + 0)%Z with ((P + i) / 8 + ASAN_B)%Z in RDB by lia.
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
      txt_rd PAYB i RD.
      step. (* [comment removed for export] *)
      clear RD. fold_tx pbs i.
      apply evt_done. eexists. reflexivity.
  Qed.
End C1.

(* [comment removed for export] *)
Section AF.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
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

  #[local] Notation AFST pc x10 x11 x13 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Zw ASAN_B) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition af_post : machine_state -> Prop := fun ms' =>
    exists y11 y13 : word, ms' = AFST 0x8ffd4 (Zw (tx pbs i)) y11 y13.

  #[using="PS Q R PAYB HN HP HPS HQR SHA SHB HI"] Lemma blockAF : forall (x11 x13 : word), evt ASEGS af_post (AFST 0x8ffc0 (Zw (P + i)) x11 x13).
  Proof. LiaFast.lf_pins (fun (PS Q R PAYB HN HP HPS HQR SHA SHB HI : LiaFast.U) => LiaFast.u0).
    intros x11 x13. pose proof (shz_bound _ _ _ _ SHA) as BT.
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
End AF.

(* [comment removed for export] *)
Section C2.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
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
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Zw (P + i)) x13 x14 x15 x16 x17 x18 x19 (Zw ASAN_B) x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition c2_post : machine_state -> Prop := fun ms' =>
    exists y14 y15 : word, ms' = C2ST 0x906e8 y14 y15.

  #[using="pbs PS Q R HN HP HPS HQR SHA SHB HI"] Lemma blockC2 : forall (x14 x15 : word), evt ASEGS c2_post (C2ST 0x906d8 x14 x15).
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
End C2.

(* [comment removed for export] *)
Section LD.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pbs : list byte) (P i : Z).
  #[local] Notation N := (Z.of_nat (length pbs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis PAYB : bytes_at ASEGS m P pbs.
  Hypothesis HN : (1 <= N <= PAYMAX)%Z.
  Hypothesis HP : (PAYPMIN <= P <= 140737488355072)%Z.
  Hypothesis HI : (1 <= i < N)%Z.

  #[local] Notation LDST pc x12 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Zw (P + i - 1)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition ld_post : machine_state -> Prop := fun ms' => ms' = LDST 0x906f4 (Zw (tx pbs i)).

  #[using="PAYB HI"] Lemma blockLD : forall (x12 : word), evt ASEGS ld_post (LDST 0x906f0 x12).
  Proof. LiaFast.lf_pins (fun (PAYB HI : LiaFast.U) => LiaFast.u0).
    intros x12. pose proof (tx_range pbs i) as Ri.
    txt_rd PAYB i RD.
    step. (* [comment removed for export] *)
    clear RD. fold_tx pbs i.
    apply evt_done. reflexivity.
  Qed.
End LD.
End HxPayW.

Import OSSVerify.Proofs.fast_float.from_chars.lib.HXH.HxPay.HxPayW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation PAYQMAX := 8388608%Z (only parsing).
(* [comment removed for export] *)
Notation PAYSMAX := 35184372088832%Z (only parsing).
Definition SHBz : Z := 2147450880.
Definition rgl (L : sst) (k : Z) : lin := rget (s_regs L) (rkz k).
Definition fv (n : positive) (i : nat) : positive := Pos.of_nat (Pos.to_nat n + i).
(* [comment removed for export] *)
Definition xok0 : nat -> list word -> (word -> option byte) -> Prop := fun _ _ _ => True.

(* [comment removed for export] *)
Inductive pgeo : Type :=
| PGeo (P N PS Q R : lin)
| PGeoU (P N PS QU TU SBU Z : lin).     (* [comment removed for export] *)
Definition pg_P (g : pgeo) : lin := match g with PGeo P _ _ _ _ => P | PGeoU P _ _ _ _ _ _ => P end.
Definition pg_N (g : pgeo) : lin := match g with PGeo _ N _ _ _ => N | PGeoU _ N _ _ _ _ _ => N end.
(* [comment removed for export] *)
Definition pg_Z (g : pgeo) : lin := match g with PGeo _ N _ _ _ => N | PGeoU _ _ _ _ _ _ Z => Z end.
Definition pg_PS (g : pgeo) : lin := match g with PGeo _ _ PS _ _ => PS | PGeoU _ _ PS _ _ _ _ => PS end.

(* [comment removed for export] *)
Definition is_rg (R : region) (b s : lin) (k : rkind) : bool :=
  (lin_eqb (rg_base R) b && lin_eqb (rg_size R) s && rkind_eqb (rg_kind R) k)%bool.
Definition is_rz0 (R : region) (b s : lin) : bool :=
  (is_rg R b s RZ && match rg_cont R with TEmpty => true | _ => false end)%bool.
(* [comment removed for export] *)
Definition is_pb (R : region) (b r : lin) : bool :=
  (lin_eqb (rg_base R) b && tracked_b (rg_cont R) 0 [BV r 0])%bool.
(* [comment removed for export] *)
Fixpoint tnone (t : tree bval) : bool :=
  match t with TEmpty => true | TNode l None r => (tnone l && tnone r)%bool | TNode _ (Some _) _ => false end.
Definition only0 (t : tree bval) : bool := match t with TEmpty => true | TNode l _ r => (tnone l && tnone r)%bool end.
Lemma tnone_get : forall t p, tnone t = true -> tget p t = None.
Proof.
  induction t as [|l IHl v r IHr]; intros p H; [destruct p; reflexivity|]. cbn [tnone] in H. destruct v as [b|]; [discriminate|].
  apply andb_prop in H as [Hl Hr]. destruct p as [p|p|]; cbn [tget]; [exact (IHr p Hr) | exact (IHl p Hl) | reflexivity].
Qed.
Lemma only0_get : forall t p, only0 t = true -> p <> 1%positive -> tget p t = None.
Proof.
  intros [|l v r] p H Hp; [destruct p; reflexivity|]. cbn [only0] in H. apply andb_prop in H as [Hl Hr].
  destruct p as [p|p|]; cbn [tget]; [exact (tnone_get r p Hr) | exact (tnone_get l p Hl) | congruence].
Qed.
Definition is_rzA (R : region) (b s : lin) : bool := (is_rg R b s RZ && only0 (rg_cont R))%bool.

Definition pay_facts (g : pgeo) : list fact :=
  match g with
  | PGeo P N PS Q R =>
      [FMod P 4 0; FRange P PAYPMIN 140737488355072; FRange (lsub (lscale 8 (laddc PS (- SHBz))) P) 0 0;
       FRange N 1 PAYMAX; FRange (lsub N (ladd (lscale 8 Q) R)) 0 0; FRange R 0 7; FRange Q 0 PAYQMAX;
       FRange (laddc PS (- SHBz)) 0 PAYSMAX]
  | PGeoU P N PS QU TU SBU Z =>
      [FMod P 3 0; FRange P PAYPMIN 140737488355072; FRange (lsub (lscale 8 (laddc PS (- SHBz))) P) 0 0;
       FRange N 1 PAYMAX; FRange (lsub N (laddc (ladd (lscale 8 QU) TU) 1)) 0 0; FRange TU 0 7; FRange QU 0 (PAYQMAX - 1);
       FRange (laddc PS (- SHBz)) 0 PAYSMAX;
       FRange SBU 0 7; FRange (lsub (laddc TU 1) SBU) 0 8; FMod (lsub (laddc TU 1) SBU) 3 0; FRange (lsub Z N) 0 65536; FRange Z 1 (2 * PAYMAX)]
  end.
(* [comment removed for export] *)
Definition pay_ok (g : pgeo) (L : sst) : bool :=
  (existsb (fun R => is_rg R (pg_P g) (pg_Z g) RW) (s_rgs L) && forallb (fact_implied (s_facts L)) (pay_facts g) &&
   match g with
   | PGeo P N PS Q R =>
       existsb (fun X => is_rz0 X PS Q) (s_rgs L)
       && (fact_implied (s_facts L) (FRange R 0 0) ||
           (fact_implied (s_facts L) (FRange R 1 7) && existsb (fun X => is_pb X (ladd PS Q) R) (s_rgs L)))
   | PGeoU P N PS QU TU SBU Z =>
       existsb (fun X => is_rzA X (laddc PS (-1)) (laddc QU 1)) (s_rgs L) && existsb (fun X => is_pb X (ladd PS QU) SBU) (s_rgs L)
   end)%bool.
(* [comment removed for export] *)
Definition acc_facts (g : pgeo) (a : lin) : list fact :=
  [FRange (lsub a (pg_P g)) 0 (PAYMAX - 1); FRange (lsub (laddc (pg_N g) (-1)) (lsub a (pg_P g))) 0 (PAYMAX - 1)].

(* [comment removed for export] *)
Definition pay_Qz (g : pgeo) (E : valu) : Z :=
  match g with
  | PGeo _ _ _ Q _ => bv_unsigned (lden E Q)
  | PGeoU _ _ _ QU _ SBU _ => if Z.eqb (bv_unsigned (lden E SBU)) 0 then bv_unsigned (lden E QU) + 1 else bv_unsigned (lden E QU)
  end.
Definition pay_Rz (g : pgeo) (E : valu) : Z :=
  match g with PGeo _ _ _ _ R => bv_unsigned (lden E R) | PGeoU _ _ _ _ _ SBU _ => bv_unsigned (lden E SBU) end.

Section Open.
Variable g : pgeo.
Variable E : valu.
Variable ms : machine_state.
Variable L : sst.
Hypothesis Hd : sden ASEGS E L ms.
Hypothesis Hok : pay_ok g L = true.

Local Abbreviation Pz := (bv_unsigned (lden E (pg_P g))).
Local Abbreviation Nz := (bv_unsigned (lden E (pg_N g))).
Local Abbreviation PSz := (bv_unsigned (lden E (pg_PS g))).
Local Abbreviation Qz := (pay_Qz g E).
Local Abbreviation Rz := (pay_Rz g E).

#[using="Type"] Lemma u_sub : forall a b, bv_unsigned (lden E (lsub a b)) = (bv_unsigned (lden E a) - bv_unsigned (lden E b)) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b. rewrite lden_lsub, bv_sub_unsigned. reflexivity. Qed.
#[using="Type"] Lemma u_add : forall a b, bv_unsigned (lden E (ladd a b)) = (bv_unsigned (lden E a) + bv_unsigned (lden E b)) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b. rewrite lden_ladd, bv_add_unsigned. reflexivity. Qed.
#[using="Type"] Lemma u_scale : forall k a, bv_unsigned (lden E (lscale k a)) = (k * bv_unsigned (lden E a)) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros k a. rewrite lden_lscale, u_Z_to_bv. reflexivity. Qed.
#[using="Type"] Lemma u_addc : forall a c, bv_unsigned (lden E (laddc a c)) = (bv_unsigned (lden E a) + c) mod two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros a c. rewrite lden_laddc, u_Z_to_bv. reflexivity. Qed.
#[using="Type"] Lemma Bl : forall l, 0 <= bv_unsigned (lden E l) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros l. pose proof (bv_unsigned_in_range _ (lden E l)) as X. unfold bv_modulus in X. exact X. Qed.

#[using="ms L Hd Hok"] Lemma pay_okF : Forall (fact_ok E) (pay_facts g).
Proof. LiaFast.lf_pins (fun (ms L Hd Hok : LiaFast.U) => LiaFast.u0).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _).
  unfold pay_ok in Hok. apply andb_prop in Hok as [Hok1 _]. apply andb_prop in Hok1 as [_ Hfx].
  rewrite forallb_forall in Hfx. apply Forall_forall. intros f Hf. exact (fact_implied_ok E _ _ HF (Hfx f Hf)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u6_arith : forall TUz SBUz, 0 <= TUz <= 7 -> 0 <= SBUz <= 7 -> 0 <= (TUz + 1 - SBUz) mod two64 <= 8 ->
  ((TUz + 1 - SBUz) mod two64) mod 2 ^ 3 = 0 -> (SBUz = 0 /\ TUz = 7) \/ (SBUz <> 0 /\ TUz + 1 = SBUz).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros TUz SBUz H1 H2 H3 H4. change (2 ^ 3) with 8 in H4.
  assert (Hc : TUz + 1 - SBUz < 0 \/ 0 <= TUz + 1 - SBUz) by lia. destruct Hc as [Hc|Hc].
  - exfalso. clear H4. replace (TUz + 1 - SBUz) with ((TUz + 1 - SBUz + two64) + (-1) * two64) in H3 by lia.
    rewrite Z_mod_plus_full in H3.
    rewrite (Z.mod_small (TUz + 1 - SBUz + two64) two64) in H3 by (unfold two64; lia). unfold two64 in H3. lia.
  - rewrite (Z.mod_small (TUz + 1 - SBUz) two64) in H3, H4 by (unfold two64; lia). Z.div_mod_to_equations. lia.
Qed.

#[using="ms L Hd Hok"] Lemma pay_bounds : Pz mod 8 = 0 /\ PAYPMIN <= Pz <= 140737488355072 /\ 8 * (PSz - SHBz) = Pz /\ 1 <= Nz <= PAYMAX /\
  Nz = 8 * Qz + Rz /\ 0 <= Rz <= 7 /\ 0 <= Qz <= PAYQMAX.
Proof. LiaFast.lf_pins (fun (ms L Hd Hok : LiaFast.U) => LiaFast.u0).
  pose proof pay_okF as HF. destruct g as [P N PS Q R|P N PS QU TU SBU Zl]; cbn [pay_facts pg_P pg_N pg_PS pay_Qz pay_Rz] in *.
  - repeat match type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF as [?X HF] end.
    cbn [fact_ok] in X, X0, X1, X2, X3, X4, X5, X6.
    rewrite u_sub, u_scale, u_addc in X1. rewrite u_sub, u_add, u_scale in X3. rewrite u_addc in X6.
    pose proof (Bl P). pose proof (Bl N). pose proof (Bl PS). pose proof (Bl Q). pose proof (Bl R).
    set (Pv := bv_unsigned (lden E P)) in *. set (Nv := bv_unsigned (lden E N)) in *. set (PSv := bv_unsigned (lden E PS)) in *.
    set (Qv := bv_unsigned (lden E Q)) in *. set (Rv := bv_unsigned (lden E R)) in *.
    assert (X' : Pv mod 8 = 0) by (change (2 ^ 4) with 16 in X; Z.div_mod_to_equations; lia).
    assert (Y8 : (PSv + - SHBz) mod two64 = PSv - SHBz) by (unfold SHBz, two64 in *; Z.div_mod_to_equations; nia).
    rewrite Y8 in X1, X6.
    assert (Y3 : (8 * (PSv - SHBz)) mod two64 = 8 * (PSv - SHBz)) by (apply Z.mod_small; unfold two64 in *; lia).
    rewrite Y3 in X1.
    assert (Y5 : (8 * Qv) mod two64 = 8 * Qv) by (apply Z.mod_small; unfold two64 in *; lia).
    rewrite Y5 in X3. rewrite (Z.mod_small (8 * Qv + Rv)) in X3 by (unfold two64 in *; lia).
    split; [exact X'|]. split; [lia|].
    split; [unfold two64 in *; Z.div_mod_to_equations; nia|]. split; [lia|].
    split; [unfold two64 in *; Z.div_mod_to_equations; nia|]. split; lia.
  - repeat match type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF as [?X HF] end.
    cbn [fact_ok] in X, X0, X1, X2, X3, X4, X5, X6, X7, X8, X9.
    rewrite u_sub, u_scale, u_addc in X1. rewrite u_sub, u_addc, u_add, u_scale in X3. rewrite u_addc in X6.
    rewrite u_sub, u_addc in X8, X9.
    pose proof (Bl P). pose proof (Bl N). pose proof (Bl PS). pose proof (Bl QU). pose proof (Bl TU). pose proof (Bl SBU).
    set (Pv := bv_unsigned (lden E P)) in *. set (Nv := bv_unsigned (lden E N)) in *. set (PSv := bv_unsigned (lden E PS)) in *.
    set (Qv := bv_unsigned (lden E QU)) in *. set (Tv := bv_unsigned (lden E TU)) in *. set (Sv := bv_unsigned (lden E SBU)) in *.
    assert (X' : Pv mod 8 = 0) by (change (2 ^ 3) with 8 in X; exact X).
    assert (Y8 : (PSv + - SHBz) mod two64 = PSv - SHBz) by (unfold SHBz, two64 in *; Z.div_mod_to_equations; nia).
    rewrite Y8 in X1, X6.
    assert (Y3 : (8 * (PSv - SHBz)) mod two64 = 8 * (PSv - SHBz)) by (apply Z.mod_small; unfold two64 in *; lia).
    rewrite Y3 in X1.
    assert (Y5 : (8 * Qv) mod two64 = 8 * Qv) by (apply Z.mod_small; unfold two64 in *; lia).
    rewrite Y5 in X3. rewrite (Z.mod_small (8 * Qv + Tv)) in X3 by (unfold two64 in *; lia).
    rewrite (Z.mod_small (8 * Qv + Tv + 1)) in X3 by (unfold two64 in *; lia).
    rewrite (Z.mod_small (Tv + 1)) in X8, X9 by (unfold two64 in *; lia).
    assert (EN : Nv = 8 * Qv + Tv + 1) by (unfold two64 in *; Z.div_mod_to_equations; nia).
    destruct (u6_arith Tv Sv ltac:(lia) ltac:(lia) X8 X9) as [[S0 T7]|[S1 TS]].
    + rewrite S0. cbn [Z.eqb].
      split; [exact X'|]. split; [lia|]. split; [unfold two64 in *; Z.div_mod_to_equations; nia|]. split; [lia|]. split; lia.
    + destruct (Z.eqb_spec Sv 0) as [e|_]; [contradiction|].
      split; [exact X'|]. split; [lia|]. split; [unfold two64 in *; Z.div_mod_to_equations; nia|]. split; [lia|]. split; lia.
Qed.

(* [comment removed for export] *)
#[using="ms L Hd Hok"] Lemma pay_ZN : Nz <= bv_unsigned (lden E (pg_Z g)).
Proof. LiaFast.lf_pins (fun (ms L Hd Hok : LiaFast.U) => LiaFast.u0).
  pose proof pay_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  pose proof pay_okF as HF. pose proof pay_okF as HF2.
  destruct g as [P N PS Q R|P N PS QU TU SBU Zl]; cbn [pay_facts pg_P pg_N pg_PS pg_Z pay_Qz pay_Rz] in *; [lia|].
  rewrite Forall_forall in HF, HF2.
  pose proof (HF (FRange (lsub Zl N) 0 65536) ltac:(cbn; tauto)) as X1. pose proof (HF2 (FRange Zl 1 (2 * PAYMAX)) ltac:(cbn; tauto)) as X2.
  cbn [fact_ok] in X1, X2. rewrite u_sub in X1.
  set (Zv := bv_unsigned (lden E Zl)) in *. set (Nv := bv_unsigned (lden E N)) in *.
  assert (Hc : Zv - Nv < 0 \/ 0 <= Zv - Nv) by lia. destruct Hc as [Hc|Hc]; [|lia].
  exfalso. replace (Zv - Nv) with ((Zv - Nv + two64) + (-1) * two64) in X1 by lia.
  rewrite Z_mod_plus_full in X1. rewrite (Z.mod_small (Zv - Nv + two64) two64) in X1 by (unfold two64; lia). unfold two64 in X1. lia.
Qed.

#[using="L Hd Hok"] Lemma pay_bytes : exists pbs, bytes_at ASEGS (ms_mem ms) Pz pbs /\ Z.of_nat (length pbs) = Nz.
Proof. LiaFast.lf_pins (fun (L Hd Hok : LiaFast.U) => LiaFast.u0).
  pose proof pay_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof pay_ZN as BZ.
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _ & _ & _).
  unfold pay_ok in Hok. apply andb_prop in Hok as [Hok1 _]. apply andb_prop in Hok1 as [Hok1 _].
  apply existsb_exists in Hok1 as (R0 & HR0 & Hrg). unfold is_rg in Hrg.
  apply andb_prop in Hrg as [Hrg Hk]. apply andb_prop in Hrg as [Hb Hs]. apply lin_eqb_eq in Hb, Hs.
  destruct (rg_kind R0) eqn:Hkd; cbn in Hk; try discriminate.
  rewrite Forall_forall in HG. pose proof (HG R0 HR0) as G0.
  destruct (bytes_exist ASEGS (ms_mem ms) Pz (Z.to_nat Nz) ltac:(lia) ltac:(unfold two64 in *; lia)) as (bs & Hbs & Hl).
  { intros i Hi. pose proof (rd_of_rg ASEGS E (ms_mem ms) R0 (Z.of_nat i) G0) as Y.
    unfold rsz in Y. rewrite Hb, Hs in Y. apply Y; [lia|]. rewrite Hkd. discriminate. }
  exists bs. split; [exact Hbs | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzA_zero : forall RA b s i, rg_ok ASEGS E (ms_mem ms) RA -> is_rzA RA b s = true -> 1 <= i < rsz E RA ->
  mrd ASEGS (ms_mem ms) (wa (bv_unsigned (lden E (rg_base RA)) + i)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros RA b s i (_ & _ & H & _) Hz Hi. unfold is_rzA, is_rg in Hz. apply andb_prop in Hz as [Hz Ho].
  apply andb_prop in Hz as [_ Hk]. destruct (rg_kind RA) eqn:Hkd; cbn in Hk; try discriminate.
  pose proof (H i ltac:(lia)) as X. try rewrite Hkd in X. destruct X as (_ & X).
  rewrite <- rd1_mrd. unfold wa. apply X. apply only0_get; [exact Ho|].
  unfold okey. intros e. assert (Zpos (Z.to_pos (i + 1)) = 1) by (rewrite e; reflexivity). rewrite Z2Pos.id in H0 by lia. lia.
Qed.

#[using="L Hd Hok"] Lemma pay_shadow : shz ASEGS (ms_mem ms) PSz Qz /\ (Rz <> 0 -> bytes_at ASEGS (ms_mem ms) (PSz + Qz) [Z_to_bv 8 Rz]).
Proof. LiaFast.lf_pins (fun (L Hd Hok : LiaFast.U) => LiaFast.u0).
  pose proof pay_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _ & HF & _). rewrite Forall_forall in HG.
  unfold pay_ok in Hok. apply andb_prop in Hok as [_ Hg].
  destruct g as [P N PS Q R|P N PS QU TU SBU Zl]; cbn [pg_P pg_N pg_PS pay_Qz pay_Rz] in *.
  - apply andb_prop in Hg as [Hz Hor]. split.
    + apply existsb_exists in Hz as (R1 & HR1 & Hrz).
      unfold is_rz0, is_rg in Hrz. apply andb_prop in Hrz as [Hrz Hc]. apply andb_prop in Hrz as [Hrz Hk]. apply andb_prop in Hrz as [Hb Hs].
      apply lin_eqb_eq in Hb, Hs. destruct (rg_kind R1) eqn:Hkd; cbn in Hk; try discriminate.
      destruct (rg_cont R1) eqn:Hcn; [|discriminate].
      pose proof (HG R1 HR1) as G1. split; [lia|].
      apply (zeros_bytes_of_rz ASEGS E (ms_mem ms) R1 _ (Z.to_nat (bv_unsigned (lden E Q))) G1 Hkd Hcn).
      * rewrite Hb. reflexivity.
      * unfold rsz. rewrite Hs. lia.
    + intros HR. apply orb_prop in Hor as [H0|H1].
      * exfalso. pose proof (fact_implied_ok E _ _ HF H0) as X. cbn [fact_ok] in X. lia.
      * apply andb_prop in H1 as [_ Hx]. apply existsb_exists in Hx as (R2 & HR2 & Hpb).
        unfold is_pb in Hpb. apply andb_prop in Hpb as [Hb Ht]. apply lin_eqb_eq in Hb.
        pose proof (HG R2 HR2) as G2.
        pose proof (cont_bytes_at ASEGS E (ms_mem ms) R2 0 [BV R 0] G2 ltac:(lia) ltac:(cbn; lia) Ht) as X.
        rewrite Hb, u_add, Z.add_0_r in X. rewrite Z.mod_small in X by (unfold two64, SHBz in *; lia).
        cbn [List.map] in X. replace (bden E (BV R 0)) with (Z_to_bv 8 (bv_unsigned (lden E R))) in X; [exact X|].
        cbn [bden]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - apply andb_prop in Hg as [HA HB].
    apply existsb_exists in HA as (RA & HRA & HzA). apply existsb_exists in HB as (RB & HRB & Hpb).
    pose proof (HG RA HRA) as GA. pose proof (HG RB HRB) as GB.
    pose proof HzA as HzA'. unfold is_rzA, is_rg in HzA'. apply andb_prop in HzA' as [HzA' _]. apply andb_prop in HzA' as [HzA' _].
    apply andb_prop in HzA' as [HbA HsA]. apply lin_eqb_eq in HbA, HsA.
    unfold is_pb in Hpb. apply andb_prop in Hpb as [HbB HtB]. apply lin_eqb_eq in HbB.
    pose proof (Bl PS). pose proof (Bl QU). pose proof (Bl SBU).
    set (PSv := bv_unsigned (lden E PS)) in *. set (Qv := bv_unsigned (lden E QU)) in *. set (Sv := bv_unsigned (lden E SBU)) in *.
    (* [comment removed for export] *)
    pose proof (cont_bytes_at ASEGS E (ms_mem ms) RB 0 [BV SBU 0] GB ltac:(lia) ltac:(cbn; lia) HtB) as XB.
    rewrite HbB, u_add, Z.add_0_r in XB. fold PSv Qv in XB.
    cbn [List.map] in XB. replace (bden E (BV SBU 0)) with (Z_to_bv 8 Sv) in XB
      by (cbn [bden]; rewrite Z.mul_0_r, Z.shiftr_0_r; reflexivity).
    (* [comment removed for export] *)
    assert (EbA : bv_unsigned (lden E (rg_base RA)) = PSv - 1).
    { rewrite HbA, u_addc. fold PSv. apply Z.mod_small. unfold two64, SHBz in *. lia. }
    assert (EsA : rsz E RA = Qv + 1).
    { unfold rsz. rewrite HsA, u_addc. fold Qv. apply Z.mod_small. unfold two64 in *.
      destruct (Z.eqb Sv 0); lia. }
    assert (ZA : forall j, 0 <= j < Qv -> mrd ASEGS (ms_mem ms) (wa (PSv + j)) = Some (Z_to_bv 8 0)).
    { intros j Hj. pose proof (rzA_zero RA _ _ (j + 1) GA HzA ltac:(lia)) as X. rewrite EbA in X.
      replace (PSv - 1 + (j + 1)) with (PSv + j) in X by lia. exact X. }
    assert (EQm : (PSv + Qv) mod two64 = PSv + Qv) by (apply Z.mod_small; unfold two64, SHBz in *; destruct (Z.eqb Sv 0); lia).
    rewrite EQm in XB.
    destruct (Z.eqb_spec Sv 0) as [S0|S1].
    + split; [|intros HR; contradiction].
      split; [lia|]. rewrite S0 in XB.
      split; [unfold SHBz in *; lia|]. split; [rewrite zeros_length; unfold two64, SHBz in *; lia|].
      intros i Hi. rewrite zeros_length in Hi. rewrite nth_error_zeros by exact Hi.
      destruct (Z.eq_dec (Z.of_nat i) Qv) as [e|ne].
      * destruct XB as (_ & _ & XB). pose proof (XB 0%nat ltac:(cbn; lia)) as Y. cbn [nth_error Z.of_nat] in Y.
        rewrite Z.add_0_r in Y. rewrite e. exact Y.
      * apply ZA. lia.
    + split; [|intros _; exact XB].
      split; [lia|]. split; [unfold SHBz in *; lia|]. split; [rewrite zeros_length; unfold two64, SHBz in *; lia|].
      intros i Hi. rewrite zeros_length in Hi. rewrite nth_error_zeros by exact Hi. apply ZA. lia.
Qed.
#[using="L Hd Hok"] Lemma pay_shadowA : shz ASEGS (ms_mem ms) PSz Qz. Proof. LiaFast.lf_pins (fun (L Hd Hok : LiaFast.U) => LiaFast.u0). exact (proj1 pay_shadow). Qed.
#[using="L Hd Hok"] Lemma pay_shadowB : Rz <> 0 -> bytes_at ASEGS (ms_mem ms) (PSz + Qz) [Z_to_bv 8 Rz]. Proof. LiaFast.lf_pins (fun (L Hd Hok : LiaFast.U) => LiaFast.u0). exact (proj2 pay_shadow). Qed.
End Open.

(* [comment removed for export] *)
Definition hcall_rule (segs : list Segment) (S K : sst) : Prop :=
  forall E ms, sden segs E S ms ->
  exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next S) E E'' /\
    (forall x, fr_pt E (s_rgs S) x -> ms_mem ms'' x = ms_mem ms x).
Definition hpost (pc0 pc1 : Z) (keys : list Z) (chk : sst -> bool) (newf : sst -> list fact) (S : sst) : option sst :=
  match hx_reg pc0 pc1 keys chk newf (fun _ => []) (XST S []) with Some [K] => Some (xs_st K) | _ => None end.
Theorem hpost_ok : forall segs pc0 pc1 keys chk newf, hx_kit segs xok0 pc0 pc1 keys chk newf (fun _ => []) ->
  forall S K, hpost pc0 pc1 keys chk newf S = Some K ->
  hcall_rule segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof.
  intros segs pc0 pc1 keys chk newf HK S K Hp. unfold hpost in Hp.
  pose proof (hx_ok segs xok0 pc0 pc1 keys chk newf (fun _ => []) HK) as Hf.
  destruct (hx_reg pc0 pc1 keys chk newf (fun _ => []) (XST S [])) as [[|K0 [|]]|] eqn:Hfs; try discriminate. injection Hp as <-.
  assert (HK0 : K0 = hx_cont pc1 keys newf (fun _ => []) (XST S [])).
  { unfold hx_reg in Hfs. destruct (_ && _)%bool; [|discriminate]. injection Hfs as <-. reflexivity. }
  split; [|split].
  - intros E ms Hd. destruct (Hf (XST S []) [K0] E ms (ms_mem ms) Hfs Hd (Forall_nil _) eq_refl (fun x _ => eq_refl))
      as (K' & ms' & E' & Hin & Hst & Hd' & Ha & Hfr & _).
    destruct Hin as [<-|[]]. exists ms', E'. split; [exact Hst|]. split; [exact Hd'|]. split; [exact Ha | exact Hfr].
  - rewrite HK0. unfold hx_cont. cbn [xs_st s_next]. apply Pos2Nat.inj_le. rewrite Nat2Pos.id by lia. lia.
  - rewrite HK0. reflexivity.
Qed.

(* [comment removed for export] *)
Section PC1.
Variable g : pgeo.
Definition PC1_KEYS : list Z := [11; 12].
Definition pc1_chk (L : sst) : bool :=
  match s_resv L with
  | RNone => (pay_ok g L && lin_eqb (rgl L 20) (lconst SHBz) && forallb (fact_implied (s_facts L)) (acc_facts g (rgl L 10)))%bool
  | _ => false
  end.
Definition pc1_newf (L : sst) : list fact := [FRange (lvar (fv (s_next L) 0)) 0 255].
Definition H_PC1 : sst -> option sst := hpost 0x906a4 0x906b8 PC1_KEYS pc1_chk pc1_newf.

#[using="Type"] Theorem pc1_kit : hx_kit ASEGS xok0 0x906a4 0x906b8 PC1_KEYS pc1_chk pc1_newf (fun _ => []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold pc1_chk in Hchk. destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hacc]. apply andb_prop in Hchk as [Hok H20]. apply lin_eqb_eq in H20.
  pose proof (pay_bounds g E ms L Hd Hok) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (pay_bytes g E ms L Hd Hok) as (pbs & PAYB & Hlen).
  pose proof (pay_shadowA g E ms L Hd Hok) as SHA.
  pose proof (pay_shadowB g E ms L Hd Hok) as SHB.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Pz := bv_unsigned (lden E (pg_P g))) in *. set (Nz := bv_unsigned (lden E (pg_N g))) in *.
  set (PSz := bv_unsigned (lden E (pg_PS g))) in *. set (Qz := pay_Qz g E) in *.
  set (Rz := pay_Rz g E) in *.
  set (Al := rgl L 10) in *. set (Az := bv_unsigned (lden E Al)).
  pose proof (Bl E Al) as BA. fold Az in BA.
  unfold acc_facts in Hacc. cbn [forallb] in Hacc. apply andb_prop in Hacc as [F1 Hacc]. apply andb_prop in Hacc as [F2 _].
  pose proof (fact_implied_ok E _ _ HF F1) as X1. pose proof (fact_implied_ok E _ _ HF F2) as X2. cbn [fact_ok] in X1, X2.
  rewrite (u_sub E) in X1, X2. rewrite (u_sub E), lden_laddc, u_Z_to_bv in X2. fold Pz Nz Az in X1, X2.
  assert (HNm : (Nz + -1) mod two64 = Nz - 1) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite HNm in X2.
  assert (HI : 0 <= Az - Pz < Nz) by (unfold two64 in *; Z.div_mod_to_equations; nia).
  set (i := Az - Pz).
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 (Pz + i)).
  { transitivity (lden E (rgl L 10)); [exact (RG 10)|]. replace (Pz + i) with Az by (unfold i; lia). symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R20 : getr (ms_regs ms) 20%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 20)); [exact (RG 20)|]. rewrite H20. rewrite lden_lconst. reflexivity. }
  set (R := ms_regs ms) in *.
  assert (HK : evt ASEGS (c1_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                 (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 21) (getr R 22)
                 (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) pbs Pz i)
             (kms ASEGS ms)).
  { unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R10, R20, Hpc.
    refine (blockC1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ms) pbs Pz PSz Qz Rz i PAYB _ _ _ _ SHA _ _ _ _).
    - lia. - unfold two64 in *; lia. - unfold SHBz in *; lia. - lia. - intros HR0. exact (SHB HR0). - lia. }
  destruct (kit_run ASEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y12 & Hms2). subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  exists ms1, [Z_to_bv 64 (tx pbs i); y12].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split]].
  - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold PC1_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R10) | (symmetry; exact R20)
                                            | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - intros i0 k v Hi Hv. rewrite (E1 _).
    destruct i0 as [|[|i0]]; cbn in Hi, Hv;
      first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i0; discriminate) ].
  - unfold pc1_newf. constructor; [|constructor]. cbn [fact_ok].
    assert (Hv0 : E_of PC1_KEYS [Z_to_bv 64 (tx pbs i); y12] (s_next L) E (fv (s_next L) 0) = Z_to_bv 64 (tx pbs i))
      by exact (E_of_nth PC1_KEYS [Z_to_bv 64 (tx pbs i); y12] (s_next L) E 0 _ eq_refl eq_refl).
    rewrite lden_lvar, Hv0.
    pose proof (tx_range pbs i). rewrite unsigned_lit by lia. lia.
  - constructor.
Qed.

#[using="Type"] Theorem H_PC1_ok : forall S K, H_PC1 S = Some K ->
  hcall_rule ASEGS S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0. exact (hpost_ok ASEGS _ _ _ _ _ pc1_kit). Qed.
End PC1.

(* [comment removed for export] *)
Lemma pay_open : forall g E ms L (a : lin), sden ASEGS E L ms -> pay_ok g L = true ->
  forallb (fact_implied (s_facts L)) (acc_facts g a) = true ->
  exists pbs, bytes_at ASEGS (ms_mem ms) (bv_unsigned (lden E (pg_P g))) pbs /\
    Z.of_nat (length pbs) = bv_unsigned (lden E (pg_N g)) /\
    0 <= bv_unsigned (lden E a) - bv_unsigned (lden E (pg_P g)) < bv_unsigned (lden E (pg_N g)).
Proof.
  intros g E ms L a Hd Hok Hacc.
  pose proof (pay_bounds g E ms L Hd Hok) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (pay_bytes g E ms L Hd Hok) as (pbs & PAYB & Hlen).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _).
  exists pbs. split; [exact PAYB|]. split; [exact Hlen|].
  pose proof (Bl E a) as BA.
  unfold acc_facts in Hacc. cbn [forallb] in Hacc. apply andb_prop in Hacc as [F1 Hacc]. apply andb_prop in Hacc as [F2 _].
  pose proof (fact_implied_ok E _ _ HF F1) as X1. pose proof (fact_implied_ok E _ _ HF F2) as X2. cbn [fact_ok] in X1, X2.
  rewrite (u_sub E) in X1, X2. rewrite (u_sub E), lden_laddc, u_Z_to_bv in X2.
  assert (HNm : (bv_unsigned (lden E (pg_N g)) + -1) mod two64 = bv_unsigned (lden E (pg_N g)) - 1) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite HNm in X2. unfold two64 in *. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Section PAF.
Variable g : pgeo.
Definition PAF_KEYS : list Z := [10; 11; 13].
Definition paf_chk (L : sst) : bool :=
  match s_resv L with
  | RNone => (pay_ok g L && lin_eqb (rgl L 12) (lconst SHBz) && forallb (fact_implied (s_facts L)) (acc_facts g (rgl L 10)))%bool
  | _ => false
  end.
Definition paf_newf (L : sst) : list fact := [FRange (lvar (fv (s_next L) 0)) 0 255].
Definition H_PAF : sst -> option sst := hpost 0x8ffc0 0x8ffd4 PAF_KEYS paf_chk paf_newf.

#[using="Type"] Theorem paf_kit : hx_kit ASEGS xok0 0x8ffc0 0x8ffd4 PAF_KEYS paf_chk paf_newf (fun _ => []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold paf_chk in Hchk. destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hacc]. apply andb_prop in Hchk as [Hok H12]. apply lin_eqb_eq in H12.
  pose proof (pay_bounds g E ms L Hd Hok) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (pay_open g E ms L (rgl L 10) Hd Hok Hacc) as (pbs & PAYB & Hlen & HI).
  pose proof (pay_shadowA g E ms L Hd Hok) as SHA.
  pose proof (pay_shadowB g E ms L Hd Hok) as SHB.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Pz := bv_unsigned (lden E (pg_P g))) in *. set (Nz := bv_unsigned (lden E (pg_N g))) in *.
  set (PSz := bv_unsigned (lden E (pg_PS g))) in *. set (Qz := pay_Qz g E) in *.
  set (Rz := pay_Rz g E) in *.
  set (Az := bv_unsigned (lden E (rgl L 10))) in *. set (i := Az - Pz) in *.
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 (Pz + i)).
  { transitivity (lden E (rgl L 10)); [exact (RG 10)|]. replace (Pz + i) with Az by (unfold i; lia). symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 12)); [exact (RG 12)|]. rewrite H12. rewrite lden_lconst. reflexivity. }
  set (R := ms_regs ms) in *.
  assert (HK : evt ASEGS (af_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                 (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                 (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) pbs i)
             (kms ASEGS ms)).
  { unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R10, R12, Hpc.
    refine (blockAF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ms) pbs Pz PSz Qz Rz i PAYB _ _ _ _ SHA _ _ _ _).
    - lia. - unfold two64 in *; lia. - unfold SHBz in *; lia. - lia. - intros HR0. exact (SHB HR0). - lia. }
  destruct (kit_run ASEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y11 & y13 & Hms2). subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  exists ms1, [Z_to_bv 64 (tx pbs i); y11; y13].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split]].
  - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold PAF_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R12)
                                            | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - intros i0 k v Hi Hv. rewrite (E1 _).
    destruct i0 as [|[|[|i0]]]; cbn in Hi, Hv;
      first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i0; discriminate) ].
  - unfold paf_newf. constructor; [|constructor]. cbn [fact_ok].
    assert (Hv0 : E_of PAF_KEYS [Z_to_bv 64 (tx pbs i); y11; y13] (s_next L) E (fv (s_next L) 0) = Z_to_bv 64 (tx pbs i))
      by exact (E_of_nth PAF_KEYS [Z_to_bv 64 (tx pbs i); y11; y13] (s_next L) E 0 _ eq_refl eq_refl).
    rewrite lden_lvar, Hv0. pose proof (tx_range pbs i). rewrite unsigned_lit by lia. lia.
  - constructor.
Qed.

#[using="Type"] Theorem H_PAF_ok : forall S K, H_PAF S = Some K ->
  hcall_rule ASEGS S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0. exact (hpost_ok ASEGS _ _ _ _ _ paf_kit). Qed.
End PAF.

(* [comment removed for export] *)
Section PC2.
Variable g : pgeo.
Definition PC2_KEYS : list Z := [14; 15].
Definition pc2_chk (L : sst) : bool :=
  match s_resv L with
  | RNone => (pay_ok g L && lin_eqb (rgl L 20) (lconst SHBz) && forallb (fact_implied (s_facts L)) (acc_facts g (rgl L 12)))%bool
  | _ => false
  end.
Definition H_PC2 : sst -> option sst := hpost 0x906d8 0x906e8 PC2_KEYS pc2_chk (fun _ => []).

#[using="Type"] Theorem pc2_kit : hx_kit ASEGS xok0 0x906d8 0x906e8 PC2_KEYS pc2_chk (fun _ => []) (fun _ => []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold pc2_chk in Hchk. destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hacc]. apply andb_prop in Hchk as [Hok H20]. apply lin_eqb_eq in H20.
  pose proof (pay_bounds g E ms L Hd Hok) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (pay_open g E ms L (rgl L 12) Hd Hok Hacc) as (pbs & PAYB & Hlen & HI).
  pose proof (pay_shadowA g E ms L Hd Hok) as SHA.
  pose proof (pay_shadowB g E ms L Hd Hok) as SHB.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Pz := bv_unsigned (lden E (pg_P g))) in *. set (Nz := bv_unsigned (lden E (pg_N g))) in *.
  set (PSz := bv_unsigned (lden E (pg_PS g))) in *. set (Qz := pay_Qz g E) in *.
  set (Rz := pay_Rz g E) in *.
  set (Az := bv_unsigned (lden E (rgl L 12))) in *. set (i := Az - Pz) in *.
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (R12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 (Pz + i)).
  { transitivity (lden E (rgl L 12)); [exact (RG 12)|]. replace (Pz + i) with Az by (unfold i; lia). symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R20 : getr (ms_regs ms) 20%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 20)); [exact (RG 20)|]. rewrite H20. rewrite lden_lconst. reflexivity. }
  set (R := ms_regs ms) in *.
  assert (HK : evt ASEGS (c2_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                 (getr R 10) (getr R 11) (getr R 13) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 21) (getr R 22)
                 (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) Pz i)
             (kms ASEGS ms)).
  { unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R12, R20, Hpc.
    refine (blockC2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ms) pbs Pz PSz Qz Rz i _ _ _ _ SHA _ _ _ _).
    - lia. - unfold two64 in *; lia. - unfold SHBz in *; lia. - lia. - intros HR0. exact (SHB HR0). - lia. }
  destruct (kit_run ASEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y14 & y15 & Hms2). subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  exists ms1, [y14; y15].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split]].
  - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold PC2_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R12) | (symmetry; exact R20)
                                            | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - intros i0 k v Hi Hv. rewrite (E1 _).
    destruct i0 as [|[|i0]]; cbn in Hi, Hv;
      first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i0; discriminate) ].
  - constructor.
  - constructor.
Qed.

#[using="Type"] Theorem H_PC2_ok : forall S K, H_PC2 S = Some K ->
  hcall_rule ASEGS S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0. exact (hpost_ok ASEGS _ _ _ _ _ pc2_kit). Qed.
End PC2.

(* [comment removed for export] *)
Section PLD.
Variable g : pgeo.
Definition PLD_KEYS : list Z := [12].
Definition pld_chk (L : sst) : bool :=
  match s_resv L with
  | RNone => (pay_ok g L && fact_implied (s_facts L) (FRange (lsub (rgl L 10) (pg_P g)) 0 (PAYMAX - 1))
              && forallb (fact_implied (s_facts L)) (acc_facts g (laddc (rgl L 10) 1)))%bool
  | _ => false
  end.
Definition pld_newf (L : sst) : list fact := [FRange (lvar (fv (s_next L) 0)) 0 255].
Definition H_PLD : sst -> option sst := hpost 0x906f0 0x906f4 PLD_KEYS pld_chk pld_newf.

#[using="Type"] Theorem pld_kit : hx_kit ASEGS xok0 0x906f0 0x906f4 PLD_KEYS pld_chk pld_newf (fun _ => []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold pld_chk in Hchk. destruct (s_resv L) eqn:Hrv; try discriminate.
  apply andb_prop in Hchk as [Hchk Hacc]. apply andb_prop in Hchk as [Hok Hge].
  pose proof (pay_bounds g E ms L Hd Hok) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct (pay_open g E ms L (laddc (rgl L 10) 1) Hd Hok Hacc) as (pbs & PAYB & Hlen & HI).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  pose proof (fact_implied_ok E _ _ HF Hge) as X. cbn [fact_ok] in X. rewrite (u_sub E) in X.
  set (Pz := bv_unsigned (lden E (pg_P g))) in *. set (Nz := bv_unsigned (lden E (pg_N g))) in *.
  set (Az := bv_unsigned (lden E (rgl L 10))) in *.
  pose proof (Bl E (rgl L 10)) as BA. fold Az in BA.
  rewrite lden_laddc, u_Z_to_bv in HI. fold Az in HI.
  assert (HA1 : (Az + 1) mod two64 = Az + 1).
  { apply Z.mod_small. unfold two64 in *. Z.div_mod_to_equations. nia. }
  rewrite HA1 in HI.
  assert (HAz : Pz <= Az) by (unfold two64 in *; Z.div_mod_to_equations; nia).
  set (i := Az + 1 - Pz) in *.
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 (Pz + i - 1)).
  { transitivity (lden E (rgl L 10)); [exact (RG 10)|]. replace (Pz + i - 1) with Az by (unfold i; lia). symmetry. apply Z_to_bv_bv_unsigned. }
  set (R := ms_regs ms) in *.
  assert (HK : evt ASEGS (ld_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                 (getr R 11) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21)
                 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) pbs Pz i)
             (kms ASEGS ms)).
  { unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R10, Hpc.
    eapply blockLD; first [exact PAYB | unfold i; lia | unfold two64 in *; lia]. }
  destruct (kit_run ASEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  unfold ld_post in Hpost. subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  exists ms1, [Z_to_bv 64 (tx pbs i)].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split]].
  - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold PLD_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R10)
                                            | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - intros i0 k v Hi Hv. rewrite (E1 _).
    destruct i0 as [|i0]; cbn in Hi, Hv;
      first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i0; discriminate) ].
  - unfold pld_newf. constructor; [|constructor]. cbn [fact_ok].
    assert (Hv0 : E_of PLD_KEYS [Z_to_bv 64 (tx pbs i)] (s_next L) E (fv (s_next L) 0) = Z_to_bv 64 (tx pbs i))
      by exact (E_of_nth PLD_KEYS [Z_to_bv 64 (tx pbs i)] (s_next L) E 0 _ eq_refl eq_refl).
    rewrite lden_lvar, Hv0. pose proof (tx_range pbs i). rewrite unsigned_lit by lia. lia.
  - constructor.
Qed.

#[using="Type"] Theorem H_PLD_ok : forall S K, H_PLD S = Some K ->
  hcall_rule ASEGS S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0. exact (hpost_ok ASEGS _ _ _ _ _ pld_kit). Qed.
End PLD.
