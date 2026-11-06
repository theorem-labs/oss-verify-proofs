(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import StartupTac SmearLemma.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import B_code_maxva.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
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

Definition MAXVA_PTRCELL : Z := 0x733510.   (* [comment removed for export] *)

Theorem B_maxva_run : forall regs mem rom (sp s0v ret v : word),
  (MAXVA_PTRCELL + 8 + 16 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z ->
  getr regs 2 = sp -> getr regs 8 = s0v -> getr regs 1 = ret -> ret_ok ret ->
  store_ok ASEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  store_ok ASEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = true ->
  (* [comment removed for export] *)
  rdn ASEGS mem (Z_to_bv 64 0x5e0f98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  rdn ASEGS mem (Z_to_bv 64 0x5e1b28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 MAXVA_PTRCELL)) ->
  rdn ASEGS mem (Z_to_bv 64 MAXVA_PTRCELL) 8 = Some (word_to_le_bytes 8 v) ->
  (2 ^ 46 <= bv_unsigned v < 2 ^ 47)%Z ->
  exists regs',
    msteps ASEGS (mkst regs (0x1d14f0 : word) mem rom)
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
  - sv F_1d1504 D_1d1504 (Z_to_bv 64 (bv_unsigned sp - 16)).                      (* [comment removed for export] *)
    stw F_1d1508 D_1d1508 (Z_to_bv 64 (bv_unsigned sp - 8)) ret ltac:(store_ok_peel; exact SOK8).     (* [comment removed for export] *)
    stw F_1d150c D_1d150c (Z_to_bv 64 (bv_unsigned sp - 16)) s0v ltac:(store_ok_peel; exact SOK16).   (* [comment removed for export] *)
    sv F_1d1510 D_1d1510 sp.                                                       (* [comment removed for export] *)
    sn F_1d1514 D_1d1514.                                                          (* [comment removed for export] *)
    ld_step F_1d1518 D_1d1518 (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(peel; eapply rdn_addr; [exact Hg | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    stepb_ft F_1d151c D_1d151c ltac:(pin; cond_compute).                          (* [comment removed for export] *)
    sn F_1d1520 D_1d1520.                                                          (* [comment removed for export] *)
    ld_step F_1d1524 D_1d1524 (word_to_le_bytes 8 (Z_to_bv 64 0x733510)) (Z_to_bv 64 0x733510) ltac:(peel; eapply rdn_addr; [exact Hq | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    ld_step F_1d1528 D_1d1528 (word_to_le_bytes 8 v) v ltac:(peel; eapply rdn_addr; [exact Hv | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    sn F_1d152c D_1d152c.                                                          (* [comment removed for export] *)
    (* [comment removed for export] *)
    sn F_1d1538 D_1d1538.                                                          (* [comment removed for export] *)
    sn F_1d153c D_1d153c. sn F_1d1540 D_1d1540. sn F_1d1544 D_1d1544. sn F_1d1548 D_1d1548.   (* [comment removed for export] *)
    sn F_1d154c D_1d154c. fold_smear z1.                                          (* [comment removed for export] *)
    sn F_1d1550 D_1d1550. sn F_1d1554 D_1d1554. sn F_1d1558 D_1d1558. sn F_1d155c D_1d155c.   (* [comment removed for export] *)
    sn F_1d1560 D_1d1560.                                                          (* [comment removed for export] *)
    sn F_1d1564 D_1d1564. fold_smear z2.                                          (* [comment removed for export] *)
    sn F_1d1568 D_1d1568. sn F_1d156c D_1d156c. sn F_1d1570 D_1d1570. sn F_1d1574 D_1d1574.
    sn F_1d1578 D_1d1578. sn F_1d157c D_1d157c. sn F_1d1580 D_1d1580. sn F_1d1584 D_1d1584.   (* [comment removed for export] *)
    sn F_1d1588 D_1d1588.                                                          (* [comment removed for export] *)
    sn F_1d158c D_1d158c. fold_smear z3.
    sn F_1d1590 D_1d1590.                                                          (* [comment removed for export] *)
    sn F_1d1594 D_1d1594. fold_smear z4.
    sn F_1d1598 D_1d1598.                                                          (* [comment removed for export] *)
    sn F_1d159c D_1d159c. fold_smear z5.
    sn F_1d15a0 D_1d15a0.                                                          (* [comment removed for export] *)
    sn F_1d15a4 D_1d15a4. fold_smear_eq MAXVA E6.                               (* [comment removed for export] *)
    (* [comment removed for export] *)
    sn F_1d15a8 D_1d15a8. sn F_1d15ac D_1d15ac. sn F_1d15b0 D_1d15b0. sn F_1d15b4 D_1d15b4.
    sn F_1d15b8 D_1d15b8. sn F_1d15bc D_1d15bc. sn F_1d15c0 D_1d15c0. sn F_1d15c4 D_1d15c4.
    sn F_1d15c8 D_1d15c8. sn F_1d15cc D_1d15cc. sn F_1d15d0 D_1d15d0. sn F_1d15d4 D_1d15d4.
    sn F_1d15d8 D_1d15d8. sn F_1d15dc D_1d15dc. sn F_1d15e0 D_1d15e0. sn F_1d15e4 D_1d15e4.
    sn F_1d15e8 D_1d15e8.
    ld_step F_1d15ec D_1d15ec (word_to_le_bytes 8 ret) ret ltac:(rd_hit8) ltac:(apply bytes_le_to_Z_8).    (* [comment removed for export] *)
    ld_step F_1d15f0 D_1d15f0 (word_to_le_bytes 8 s0v) s0v ltac:(rd_hit8) ltac:(apply bytes_le_to_Z_8).    (* [comment removed for export] *)
    sv F_1d15f4 D_1d15f4 sp.                                                       (* [comment removed for export] *)
    stepret F_1d15f8 D_1d15f8 ret ltac:(pin; first [reflexivity | bveq]).         (* [comment removed for export] *)
    apply mst_refl.
  - split; [gres; apply bv_eq; vm_compute; reflexivity|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr; cbv [maxva_kept In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.
