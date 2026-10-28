(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import StartupTac SmearLemma.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import A_code_maxva.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
  rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof. intros; subst; reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_or_srli : forall (a : word) (s : Z), (0 <= s)%Z ->
  v_or a (v_srli a s) = Z_to_bv 64 (smear_step (bv_unsigned a) s).
Proof.
  intros a s Hs. unfold v_or, v_srli, smear_step. pose proof (u64_range a) as Ha.
  pose proof (shiftr_lt_pow2 (bv_unsigned a) s 64 ltac:(lia) Hs) as Hr.
  rewrite (u_Z2bv (Z.shiftr (bv_unsigned a) s)) by lia. reflexivity.
Qed.

Lemma smear_step_range : forall z s, (0 <= z < 2 ^ 64)%Z -> (0 <= s)%Z -> (0 <= smear_step z s < 2 ^ 64)%Z.
Proof. intros z s Hz Hs. unfold smear_step. apply lor_lt_pow2; [lia|]. apply shiftr_lt_pow2; lia. Qed.

Definition maxva_kept : list reg := [3; 4; 5; 6; 7; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition MAXVA : Z := 0x7fffffffffff.

(* [comment removed for export] *)
Ltac fold_smear zt :=
  match goal with
  | |- context [v_or ?a (v_srli ?a ?s)] =>
      replace (v_or a (v_srli a s)) with (Z_to_bv 64 zt)
        by (rewrite v_or_srli by lia; rewrite ?u_Z2bv by lia; reflexivity)
  end.
Ltac fold_smear_eq zt E :=
  match goal with
  | |- context [v_or ?a (v_srli ?a ?s)] =>
      replace (v_or a (v_srli a s)) with (Z_to_bv 64 zt)
        by (rewrite v_or_srli by lia; rewrite ?u_Z2bv by lia; rewrite E; reflexivity)
  end.

Definition MAXVA_PTRCELL : Z := 0x6fc5d0.   (* [comment removed for export] *)

Theorem A_maxva_run : forall regs mem rom (sp s0v ret v : word),
  (MAXVA_PTRCELL + 8 + 16 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z ->
  getr regs 2 = sp -> getr regs 8 = s0v -> getr regs 1 = ret -> ret_ok ret ->
  store_ok ASEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  store_ok ASEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = true ->
  (* [comment removed for export] *)
  rdn ASEGS mem (Z_to_bv 64 0x5a45f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  rdn ASEGS mem (Z_to_bv 64 0x5a5188) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 MAXVA_PTRCELL)) ->
  rdn ASEGS mem (Z_to_bv 64 MAXVA_PTRCELL) 8 = Some (word_to_le_bytes 8 v) ->
  (2 ^ 46 <= bv_unsigned v < 2 ^ 47)%Z ->
  exists regs',
    msteps ASEGS (mkst regs (0x1d6584 : word) mem rom)
                 (mkst regs' ret
                    (wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret))
                            (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0v)) rom)
    /\ getr regs' 10 = Z_to_bv 64 MAXVA /\ getr regs' 2 = sp /\ getr regs' 8 = s0v /\ getr regs' 1 = ret
    /\ (forall r, In r maxva_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp s0v ret v Hsplo Hsphi H2 H8 H1 Hret SOK8 SOK16 Hg Hq Hv Hvr.
  unfold MAXVA_PTRCELL in *.
  pose proof (u64_range sp) as Hsp'. pose proof (u64_range v) as Hv'.
  set (z1 := smear_step (bv_unsigned v) 1). set (z2 := smear_step z1 2). set (z3 := smear_step z2 4).
  set (z4 := smear_step z3 8). set (z5 := smear_step z4 16).
  assert (R1 : (0 <= z1 < 2 ^ 64)%Z) by (apply smear_step_range; lia).
  assert (R2 : (0 <= z2 < 2 ^ 64)%Z) by (apply smear_step_range; lia).
  assert (R3 : (0 <= z3 < 2 ^ 64)%Z) by (apply smear_step_range; lia).
  assert (R4 : (0 <= z4 < 2 ^ 64)%Z) by (apply smear_step_range; lia).
  assert (R5 : (0 <= z5 < 2 ^ 64)%Z) by (apply smear_step_range; lia).
  assert (E6 : smear_step z5 32 = MAXVA).
  { unfold z5, z4, z3, z2, z1. change (smear6 (bv_unsigned v) = MAXVA). rewrite (smear6_47 _ Hvr). reflexivity. }
  eexists. split.
  - sv F_1d1570 D_1d1570 (Z_to_bv 64 (bv_unsigned sp - 16)).                      (* [comment removed for export] *)
    stw F_1d1574 D_1d1574 (Z_to_bv 64 (bv_unsigned sp - 8)) ret ltac:(store_ok_peel; exact SOK8).     (* [comment removed for export] *)
    stw F_1d1578 D_1d1578 (Z_to_bv 64 (bv_unsigned sp - 16)) s0v ltac:(store_ok_peel; exact SOK16).   (* [comment removed for export] *)
    sv F_1d157c D_1d157c sp.                                                       (* [comment removed for export] *)
    sn F_1d1580 D_1d1580.                                                          (* [comment removed for export] *)
    ld_step F_1d1584 D_1d1584 (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(peel; eapply rdn_addr; [exact Hg | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    stepb_ft F_1d1588 D_1d1588 ltac:(pin; cond_compute).                          (* [comment removed for export] *)
    sn F_1d158c D_1d158c.                                                          (* [comment removed for export] *)
    ld_step F_1d1590 D_1d1590 (word_to_le_bytes 8 (Z_to_bv 64 0x6fc5d0)) (Z_to_bv 64 0x6fc5d0) ltac:(peel; eapply rdn_addr; [exact Hq | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    ld_step F_1d1594 D_1d1594 (word_to_le_bytes 8 v) v ltac:(peel; eapply rdn_addr; [exact Hv | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    sn F_1d1598 D_1d1598.                                                          (* [comment removed for export] *)
    (* [comment removed for export] *)
    sn F_1d15a4 D_1d15a4.                                                          (* [comment removed for export] *)
    sn F_1d15a8 D_1d15a8. sn F_1d15ac D_1d15ac. sn F_1d15b0 D_1d15b0. sn F_1d15b4 D_1d15b4.   (* [comment removed for export] *)
    sn F_1d15b8 D_1d15b8. fold_smear z1.                                          (* [comment removed for export] *)
    sn F_1d15bc D_1d15bc. sn F_1d15c0 D_1d15c0. sn F_1d15c4 D_1d15c4. sn F_1d15c8 D_1d15c8.   (* [comment removed for export] *)
    sn F_1d15cc D_1d15cc.                                                          (* [comment removed for export] *)
    sn F_1d15d0 D_1d15d0. fold_smear z2.                                          (* [comment removed for export] *)
    sn F_1d15d4 D_1d15d4. sn F_1d15d8 D_1d15d8. sn F_1d15dc D_1d15dc. sn F_1d15e0 D_1d15e0.
    sn F_1d15e4 D_1d15e4. sn F_1d15e8 D_1d15e8. sn F_1d15ec D_1d15ec. sn F_1d15f0 D_1d15f0.   (* [comment removed for export] *)
    sn F_1d15f4 D_1d15f4.                                                          (* [comment removed for export] *)
    sn F_1d15f8 D_1d15f8. fold_smear z3.
    sn F_1d15fc D_1d15fc.                                                          (* [comment removed for export] *)
    sn F_1d1600 D_1d1600. fold_smear z4.
    sn F_1d1604 D_1d1604.                                                          (* [comment removed for export] *)
    sn F_1d1608 D_1d1608. fold_smear z5.
    sn F_1d160c D_1d160c.                                                          (* [comment removed for export] *)
    sn F_1d1610 D_1d1610. fold_smear_eq MAXVA E6.                               (* [comment removed for export] *)
    (* [comment removed for export] *)
    sn F_1d1614 D_1d1614. sn F_1d1618 D_1d1618. sn F_1d161c D_1d161c. sn F_1d1620 D_1d1620.
    sn F_1d1624 D_1d1624. sn F_1d1628 D_1d1628. sn F_1d162c D_1d162c. sn F_1d1630 D_1d1630.
    sn F_1d1634 D_1d1634. sn F_1d1638 D_1d1638. sn F_1d163c D_1d163c. sn F_1d1640 D_1d1640.
    sn F_1d1644 D_1d1644. sn F_1d1648 D_1d1648. sn F_1d164c D_1d164c. sn F_1d1650 D_1d1650.
    sn F_1d1654 D_1d1654.
    ld_step F_1d1658 D_1d1658 (word_to_le_bytes 8 ret) ret ltac:(rd_hit8) ltac:(apply bytes_le_to_Z_8).    (* [comment removed for export] *)
    ld_step F_1d165c D_1d165c (word_to_le_bytes 8 s0v) s0v ltac:(rd_hit8) ltac:(apply bytes_le_to_Z_8).    (* [comment removed for export] *)
    sv F_1d1660 D_1d1660 sp.                                                       (* [comment removed for export] *)
    stepret F_1d1664 D_1d1664 ret ltac:(pin; first [reflexivity | bveq]).         (* [comment removed for export] *)
    apply mst_refl.
  - split; [gres; apply bv_eq; vm_compute; reflexivity|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr; cbv [maxva_kept In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.
