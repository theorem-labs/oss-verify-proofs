(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtSizes CtWire.   (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma u8_lit : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Section WithCeiling. Context {CE__ : Ceiling}.

Definition SCT_GET_SIGNATURE_NID : Z := 0x19d69c.

Definition nid_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma SCT_get_signature_nid_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A v h g : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (0 < A /\ A + SCT_SIZE <= lo)%Z -> A mod 8 = 0 ->
  ro_cells ctusegs m (A + SCTO_VERSION) [C4 (Z_to_bv 64 v)] -> ro_cells ctusegs m (A + SCTO_ALGS) [C1 (Z_to_bv 8 h); C1 (Z_to_bv 8 g)] ->
  (v = 0 \/ v = 1 \/ v = 2^32 - 1)%Z -> (0 <= h < 256)%Z -> (0 <= g < 256)%Z ->
  a0 = Z_to_bv 64 A ->
  evt ctusegs (nid_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (sig_nid (if v =? 2^32 - 1 then -1 else v) h g))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_GET_SIGNATURE_NID) fc None m (seg_rom ctusegs)).
Proof.
  intros until g. intros ST MI GLO LO HA AL8 HV HAL Hv Hh Hg ->. unfold GLOBALS_TOP in GLO.
  unfold SCT_GET_SIGNATURE_NID, SCTO_VERSION, SCTO_ALGS, SCT_SIZE in *. rewrite Z.add_0_r in HV.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPA : A + 104 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by lia.
  unfold sig_nid, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption, NID_undef.
  carve_frame 16%nat ST. do 4 zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia| clear K0].
  zstep. zstep. let K := fresh "K" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; try (change 7 with (Z.ones 3) in K; rewrite Z.land_ones in K by lia); clear - K AL8; Z.div_mod_to_equations; lia | clear K].
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K.
  - assert (E : ((if v =? 2^32 - 1 then -1 else v) =? 0) = false).
    { destruct Hv as [-> | [-> | ->]]; cbn; try reflexivity. exfalso. apply K. vm_compute. reflexivity. }
    rewrite E. cbn [andb]. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
  - assert (Hv0 : v = 0).
    { destruct Hv as [-> | [-> | ->]]; [reflexivity| exfalso| exfalso]; revert K; vm_compute; congruence. }
    subst v. cbn [Z.eqb andb].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    + assert (E : (h =? 4) = false) by (apply Z.eqb_neq; intros ->; apply K1; rewrite ?u8_lit by lia; reflexivity).
      rewrite E. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    + assert (Hh4 : h = 4) by (revert K1; rewrite ?u8_lit by lia; intros K1; lia). subst h. cbn [Z.eqb].
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      * (* [comment removed for export] *)
        assert (E : (g =? 3) = false) by (apply Z.eqb_neq; intros ->; apply K2; rewrite ?u8_lit by lia; reflexivity). rewrite E.
        zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        setreg 10%Z (Z_to_bv 64 (if g =? 1 then 668 else 0))
          ltac:(symmetry; apply bv_eq; rewrite (u8_lit g) by lia; destruct (Z.eq_dec g 1) as [->|NE1];
                  [vm_compute; reflexivity
                  | rewrite (proj2 (Z.eqb_neq g 1) NE1);
                    replace (0 <? Z.land (g + -1) 18446744073709551615) with true
                      by (symmetry; apply Z.ltb_lt; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia;
                          destruct (Z.eq_dec g 0) as [->|NE0]; [vm_compute; reflexivity| rewrite Z.mod_small by lia; lia]);
                    cbn [Z.b2z]; rewrite ?Z.land_0_l; reflexivity]).
        zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
      * assert (Hg3 : g = 3) by (revert K2; rewrite ?u8_lit by lia; intros K2; lia). subst g. cbn [Z.eqb].
        zstep. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.
End WithCeiling.
