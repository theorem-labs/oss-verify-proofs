(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import StartupTac SmearLemma HB_code_maxva.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation HASEGS0 := AsanUbsan.M.loaded_segments.
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

Definition MAXVA_PTRCELL : Z := 0x731510.   (* [comment removed for export] *)

Theorem ha_maxva_run : forall regs mem rom (sp s0v ret v : word),
  (MAXVA_PTRCELL + 8 + 16 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2 ^ 63)%Z ->
  getr regs 2 = sp -> getr regs 8 = s0v -> getr regs 1 = ret -> ret_ok ret ->
  store_ok HASEGS0 mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  store_ok HASEGS0 mem (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = true ->
  (* [comment removed for export] *)
  rdn HASEGS0 mem (Z_to_bv 64 0x5deb18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  rdn HASEGS0 mem (Z_to_bv 64 0x5df6a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 MAXVA_PTRCELL)) ->
  rdn HASEGS0 mem (Z_to_bv 64 MAXVA_PTRCELL) 8 = Some (word_to_le_bytes 8 v) ->
  (2 ^ 46 <= bv_unsigned v < 2 ^ 47)%Z ->
  exists regs',
    msteps HASEGS0 (mkst regs (0x1d1b68 : word) mem rom)
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
  - sv F_1d6b98 D_1d6b98 (Z_to_bv 64 (bv_unsigned sp - 16)).                      (* [comment removed for export] *)
    stw F_1d6b9c D_1d6b9c (Z_to_bv 64 (bv_unsigned sp - 8)) ret ltac:(store_ok_peel; exact SOK8).     (* [comment removed for export] *)
    stw F_1d6ba0 D_1d6ba0 (Z_to_bv 64 (bv_unsigned sp - 16)) s0v ltac:(store_ok_peel; exact SOK16).   (* [comment removed for export] *)
    sv F_1d6ba4 D_1d6ba4 sp.                                                       (* [comment removed for export] *)
    sn F_1d6ba8 D_1d6ba8.                                                          (* [comment removed for export] *)
    ld_step F_1d6bac D_1d6bac (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(peel; eapply rdn_addr; [exact Hg | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    stepb_ft F_1d6bb0 D_1d6bb0 ltac:(pin; cond_compute).                          (* [comment removed for export] *)
    sn F_1d6bb4 D_1d6bb4.                                                          (* [comment removed for export] *)
    ld_step F_1d6bb8 D_1d6bb8 (word_to_le_bytes 8 (Z_to_bv 64 0x731510)) (Z_to_bv 64 0x731510) ltac:(peel; eapply rdn_addr; [exact Hq | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    ld_step F_1d6bbc D_1d6bbc (word_to_le_bytes 8 v) v ltac:(peel; eapply rdn_addr; [exact Hv | bveq]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    sn F_1d6bc0 D_1d6bc0.                                                          (* [comment removed for export] *)
    (* [comment removed for export] *)
    sn F_1d6bcc D_1d6bcc.                                                          (* [comment removed for export] *)
    sn F_1d6bd0 D_1d6bd0. sn F_1d6bd4 D_1d6bd4. sn F_1d6bd8 D_1d6bd8. sn F_1d6bdc D_1d6bdc.   (* [comment removed for export] *)
    sn F_1d6be0 D_1d6be0. fold_smear z1.                                          (* [comment removed for export] *)
    sn F_1d6be4 D_1d6be4. sn F_1d6be8 D_1d6be8. sn F_1d6bec D_1d6bec. sn F_1d6bf0 D_1d6bf0.   (* [comment removed for export] *)
    sn F_1d6bf4 D_1d6bf4.                                                          (* [comment removed for export] *)
    sn F_1d6bf8 D_1d6bf8. fold_smear z2.                                          (* [comment removed for export] *)
    sn F_1d6bfc D_1d6bfc. sn F_1d6c00 D_1d6c00. sn F_1d6c04 D_1d6c04. sn F_1d6c08 D_1d6c08.
    sn F_1d6c0c D_1d6c0c. sn F_1d6c10 D_1d6c10. sn F_1d6c14 D_1d6c14. sn F_1d6c18 D_1d6c18.   (* [comment removed for export] *)
    sn F_1d6c1c D_1d6c1c.                                                          (* [comment removed for export] *)
    sn F_1d6c20 D_1d6c20. fold_smear z3.
    sn F_1d6c24 D_1d6c24.                                                          (* [comment removed for export] *)
    sn F_1d6c28 D_1d6c28. fold_smear z4.
    sn F_1d6c2c D_1d6c2c.                                                          (* [comment removed for export] *)
    sn F_1d6c30 D_1d6c30. fold_smear z5.
    sn F_1d6c34 D_1d6c34.                                                          (* [comment removed for export] *)
    sn F_1d6c38 D_1d6c38. fold_smear_eq MAXVA E6.                               (* [comment removed for export] *)
    (* [comment removed for export] *)
    sn F_1d6c3c D_1d6c3c. sn F_1d6c40 D_1d6c40. sn F_1d6c44 D_1d6c44. sn F_1d6c48 D_1d6c48.
    sn F_1d6c4c D_1d6c4c. sn F_1d6c50 D_1d6c50. sn F_1d6c54 D_1d6c54. sn F_1d6c58 D_1d6c58.
    sn F_1d6c5c D_1d6c5c. sn F_1d6c60 D_1d6c60. sn F_1d6c64 D_1d6c64. sn F_1d6c68 D_1d6c68.
    sn F_1d6c6c D_1d6c6c. sn F_1d6c70 D_1d6c70. sn F_1d6c74 D_1d6c74. sn F_1d6c78 D_1d6c78.
    sn F_1d6c7c D_1d6c7c.
    ld_step F_1d6c80 D_1d6c80 (word_to_le_bytes 8 ret) ret ltac:(rd_hit8) ltac:(apply bytes_le_to_Z_8).    (* [comment removed for export] *)
    ld_step F_1d6c84 D_1d6c84 (word_to_le_bytes 8 s0v) s0v ltac:(rd_hit8) ltac:(apply bytes_le_to_Z_8).    (* [comment removed for export] *)
    sv F_1d6c88 D_1d6c88 sp.                                                       (* [comment removed for export] *)
    stepret F_1d6c8c D_1d6c8c ret ltac:(pin; first [reflexivity | bveq]).         (* [comment removed for export] *)
    apply mst_refl.
  - split; [gres; apply bv_eq; vm_compute; reflexivity|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr; cbv [maxva_kept In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.
