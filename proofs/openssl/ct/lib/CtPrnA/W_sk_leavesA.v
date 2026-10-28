(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Definition OPENSSL_SK_NUM_A : Z := 0x1fca48.
Definition OPENSSL_SK_VALUE_A : Z := 0x1fcaa4.
Definition SCT_GET_SIGNATURE_NID_A : Z := 0x33783c.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma OPENSSL_sk_num_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z) (kb : bptr) (SA num : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  In (kb, SA, STACK_SIZE) (OW ++ LB) -> SA mod 16 = 0 ->
  ro_cells ctasegs m SA [C4 (wz num)] -> (0 <= num < 2^31)%Z ->
  a0 = wz SA ->
  evt ctasegs (leaf16A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 num))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz OPENSSL_SK_NUM_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until num. intros HEAP ST MI CEIL LO HIN AL16 HN Hn ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold OPENSSL_SK_NUM_A, STACK_SIZE, SEGTOP_A, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPA : SA + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= SA) by alia.
  carve_frame 16%nat ST. do 4 step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  setreg 10%Z (Z_to_bv 64 num) ltac:(symmetry; apply bv_eq; rewrite ?sx32_small, ?unsigned_lit by lia; reflexivity).
  apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
Qed.

(* [comment removed for export] *)
Lemma OPENSSL_sk_value_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z) (kb q : bptr) (SA num D na i V : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  In (kb, SA, STACK_SIZE) (OW ++ LB) -> SA mod 16 = 0 ->
  In (q, D, 8 * na) (OW ++ LB) -> D mod 16 = 0 -> (num <= na)%Z ->
  ro_cells ctasegs m SA [C4 (wz num)] -> ro_cells ctasegs m (SA + SKO_DATA) [C8 (wz D)] -> (0 <= i < num)%Z -> (num < 2^31)%Z ->
  ro_cells ctasegs m (D + 8 * i) [C8 (wz V)] ->
  a0 = wz SA -> a1 = wz i ->
  evt ctasegs (leaf16A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 V))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz OPENSSL_SK_VALUE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until V. intros HEAP ST MI CEIL LO HIN AL16 HIND ALD NA HN HD Hi Hn HV -> ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIND) as (D0 & _ & _ & DC & DI). cbn [blk_addr blk_size fst snd] in D0, DC, DI.
  ablock HEAP HIN ACC OFF. ablock HEAP HIND ACCD OFFD.
  unfold OPENSSL_SK_VALUE_A, STACK_SIZE, SKO_DATA, SEGTOP_A, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SEPA : SA + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= SA) by alia.
  assert (SEPD : D + 8 * na <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) by alia.
  remember (D + 8 * i) as Di eqn:EDi.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step.
  step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  step. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?signed_small, ?unsigned_lit by lia; lia|]. clear K1.
  (* [comment removed for export] *)
  step.
  step. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?sx32_small, ?signed_small, ?unsigned_lit by lia; lia|]. clear K2.
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  rstep. setreg 10%Z (Z_to_bv 64 Di) ltac:(symmetry; apply bv_eq; subst Di; rewrite ?unsigned_lit by lia; bv_solve).
  step. step.
  (* [comment removed for export] *)
  step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
Qed.

(* [comment removed for export] *)
Lemma SCT_get_signature_nid_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z) (xb : bptr) (A v h g : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  In (xb, A, SCT_SIZE) (OW ++ LB) -> A mod 16 = 0 ->
  ro_cells ctasegs m (A + SCTO_VERSION) [C4 (Z_to_bv 64 v)] -> ro_cells ctasegs m (A + SCTO_ALGS) [C1 (Z_to_bv 8 h); C1 (Z_to_bv 8 g)] ->
  (v = 0 \/ v = 1 \/ v = 2^32 - 1)%Z -> (0 <= h < 256)%Z -> (0 <= g < 256)%Z ->
  a0 = Z_to_bv 64 A ->
  evt ctasegs (leaf16A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (Z_to_bv 64 (sig_nid (if v =? 2^32 - 1 then -1 else v) h g)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_GET_SIGNATURE_NID_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until g. intros HEAP ST MI CEIL LO HIN AL16 HV HAL Hv Hh Hg ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold SCT_GET_SIGNATURE_NID_A, SCTO_VERSION, SCTO_ALGS, SCT_SIZE, SEGTOP_A in *. rewrite Z.add_0_r in HV.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPA : A + 104 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by alia.
  unfold sig_nid, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption, NID_undef.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K.
  - assert (E : ((if v =? 2^32 - 1 then -1 else v) =? 0) = false).
    { destruct Hv as [-> | [-> | ->]]; cbn; try reflexivity. exfalso. apply K. vm_compute. reflexivity. }
    rewrite E. cbn [andb]. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
  - assert (Hv0 : v = 0).
    { destruct Hv as [-> | [-> | ->]]; [reflexivity| exfalso| exfalso]; revert K; vm_compute; congruence. }
    subst v. cbn [Z.eqb andb].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    + assert (E : (h =? 4) = false) by (apply Z.eqb_neq; intros ->; apply K1; rewrite ?u8_lit by lia; reflexivity).
      rewrite E. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
      apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
      repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
    + assert (Hh4 : h = 4) by (revert K1; rewrite ?u8_lit by lia; intros K1; lia). subst h. cbn [Z.eqb].
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      * (* [comment removed for export] *)
        assert (E : (g =? 3) = false) by (apply Z.eqb_neq; intros ->; apply K2; rewrite ?u8_lit by lia; reflexivity). rewrite E.
        zstep. zstep. zstep. zstep.
        setreg 10%Z (Z_to_bv 64 (if g =? 1 then 668 else 0))
          ltac:(symmetry; apply bv_eq; rewrite (u8_lit g) by lia; destruct (Z.eq_dec g 1) as [->|NE1];
                  [vm_compute; reflexivity
                  | rewrite (proj2 (Z.eqb_neq g 1) NE1);
                    replace (0 <? Z.land (g + -1) 18446744073709551615) with true
                      by (symmetry; apply Z.ltb_lt; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia;
                          destruct (Z.eq_dec g 0) as [->|NE0]; [vm_compute; reflexivity| rewrite Z.mod_small by lia; lia]);
                    cbn [Z.b2z]; rewrite ?Z.land_0_l; reflexivity]).
        zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
        apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
        repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
      * assert (Hg3 : g = 3) by (revert K2; rewrite ?u8_lit by lia; intros K2; lia). subst g. cbn [Z.eqb].
        zstep. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
        apply evt_done. unfold leaf16A_post, leafA_post. do 14 eexists. eexists. split; [reflexivity|].
        repeat match goal with |- _ /\ _ => split end; try assumption. exact I.
Qed.

End WithRT.
