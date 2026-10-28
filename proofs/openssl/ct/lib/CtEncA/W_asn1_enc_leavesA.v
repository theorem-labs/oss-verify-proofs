(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase ApState ApOwner.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRep W_get_objectA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA W_sct_completeA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?signed_of_Z, ?unsigned_lit by lia; first [apply Z.ltb_ge| apply Z.eqb_neq| apply Z.leb_gt]; lia); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?signed_of_Z, ?unsigned_lit by lia; first [apply Z.ltb_lt| apply Z.eqb_eq| apply Z.leb_le]; lia); cbv iota end.

(* [comment removed for export] *)
Lemma set0_len_normA : forall len, 0 <= len < 2^31 ->
  Z.land (Z.land (0 + - Z.b2z (9223372036854775808 <? Z.lxor len 9223372036854775808)) 18446744073709551615) len = len.
Proof.
  intros len Hl. destruct (Z.eq_dec len 0) as [->|NE]; [reflexivity|].
  change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia.
  replace (2^63 <? len + 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  change (Z.land (0 + - Z.b2z true) 18446744073709551615) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CRYPTO_clear_free_null_specA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> mem_inv ctasegs m ->
  a0 = wz 0 ->
  evt ctasegs (fun ms' => exists m',
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom ctasegs)
               /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
               /\ stk ctasegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_CLEAR_FREE) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO MI ->.
  unfold CRYPTO_CLEAR_FREE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 48%nat ST. do 7 zstep. zstep. if_true.
  do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. eexists. split; [reflexivity|]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASN1_object_size_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo len : Z),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> lo <= bv_unsigned sp - 16 ->
  0 <= len < 65536 ->
  a0 = wz 0 -> a1 = wz len -> a2 = wz V_ASN1_OCTET_STRING ->
  evt ctasegs (leaf16_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (der_hl len + len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_OBJECT_SIZE_A) fc None m (seg_rom ctasegs)).
Proof.
  (* [comment removed for export] *)
  intros until len. intros ST MI LO LEN -> -> ->. unfold ASN1_OBJECT_SIZE_A, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  zstep. sfalse. zstep. zstep. strue. zstep. zstep. zstep. if_cases K0; [| exfalso; revert K0; vm_compute; congruence]. clear K0.
  zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?signed_of_Z, ?unsigned_lit in K by lia.
  (* [comment removed for export] *)
  Ltac os_tail r len FR ST sp :=
    zstep; zstep; zstep; rewrite ?(lxor_ones31 len) by lia;
    zstep; setreg 12%Z (Z_to_bv 64 1) ltac:(f_equal; lazymatch goal with |- _ = Z.b2z (?c <? Z.lxor ?x ?k) => change k with (2^63); rewrite (zb_lxor_pow2_small x 63) by lia; replace (c <? x + 2^63) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity end);
    zstep; zstep; zstep; setreg 10%Z (Z_to_bv 64 (r + len)) ltac:(f_equal; rewrite Z.lor_0_l; lazymatch goal with |- _ = Z.land _ ?k => change k with (Z.ones 64) end; rewrite Z.land_ones, swrap32_small by lia; symmetry; apply Z.mod_small; lia);
    do 2 zstep; release_frame FR ST (bv_unsigned sp); do 2 zstep; finish.
  - (* [comment removed for export] *)
    rewrite der_hl_small by lia. os_tail 2 len FR ST sp.
  - (* [comment removed for export] *)
    zstep. zstep. rewrite (srliw8_small len) by lia. zstep. rewrite ?(swrap32_small 3) by lia. zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      assert (L256 : 256 <= len) by (rewrite ?land64_small in K1 by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]);
                                    destruct (Z.lt_ge_cases len 256) as [Hl|Hl]; [exfalso; apply K1; rewrite Z.div_small by lia; reflexivity| exact Hl]).
      rewrite der_hl_big by lia.
      zstep. rewrite (srliw8_small (len / 256)) by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
      rewrite (Z.div_small (len / 256) 256) by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
      zstep. rewrite ?(swrap32_small 4) by lia. zstep. if_cases K2; [exfalso; revert K2; vm_compute; congruence|]. clear K2.
      os_tail 4 len FR ST sp.
    + assert (L256 : len < 256).
      { destruct (Z.lt_ge_cases len 256) as [Hl|Hl]; [exact Hl|]. exfalso. revert K1. rewrite ?land64_small by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
        intros K1. assert (1 <= len / 256) by (apply Z.div_le_lower_bound; lia). lia. }
      rewrite der_hl_mid by lia. os_tail 3 len FR ST sp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASN1_put_object_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Σ : rts RT) (OW LB : list block) (lo len PP P : Z) (junk : list byte),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 16 ->
  0 <= len < 65536 ->
  cellA_in (OW ++ LB) PP 8 -> PP mod 8 = 0 -> cellA_in (OW ++ LB) P (der_hl len) -> (PP + 8 <= P \/ P + der_hl len <= PP) ->
  rw_cells ctasegs m PP [C8 (wz P)] -> rw_cells ctasegs m P [CB (Z.to_nat (der_hl len)) junk] ->
  a0 = wz PP -> a1 = wz 0 -> a2 = wz len -> a3 = wz V_ASN1_OCTET_STRING -> a4 = wz 0 ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctasegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + der_hl len); (PP, PP + 8)]%Z m m' /\ wmono ctasegs m m'
               /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
               /\ rw_cells ctasegs m' PP [C8 (wz (P + der_hl len))] /\ (exists hb, rw_cells ctasegs m' P [CB (Z.to_nat (der_hl len)) hb]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_PUT_OBJECT_A) fc None m (seg_rom ctasegs)).
Proof.
  (* [comment removed for export] *)
  intros until junk. intros HEAP ST MI CEIL LO LEN ([[bq bQ] bqn] & QIN & QL & QH) AL8 ([[bp bB] bpn] & PIN & PL & PH) APT HPP HP -> -> -> -> ->.
  cbn [blk_addr blk_size fst snd] in QL, QH, PL, PH.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CE1, CE2, CE3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP QIN) as (QB0 & _ & _ & QBC & QBI). cbn [blk_addr blk_size fst snd] in QB0, QBC, QBI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP PIN) as (PB0 & _ & _ & PBC & PBI). cbn [blk_addr blk_size fst snd] in PB0, PBC, PBI.
  ablock HEAP QIN ACCQ OFFQ. ablock HEAP PIN ACCP OFFP.
  unfold ASN1_PUT_OBJECT_A, V_ASN1_OCTET_STRING, SEGTOP_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  pose proof (der_hl_range len LEN) as HLR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + der_hl len); (PP, PP + 8)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + der_hl len); (PP, PP + 8)]%Z) by (cbn [offshW]; alia).
  assert (SEPQ : bQ + bqn <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bQ) by alia.
  assert (SEPP : bB + bpn <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bB) by alia.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  Ltac bfalse := let K := fresh "Kb" in if_cases K; [exfalso; revert K; vm_compute; congruence|]; try clear K.
  Ltac btrue := let K := fresh "Kb" in if_cases K; [| exfalso; revert K; vm_compute; congruence]; try clear K.
  Ltac po_head P := do 8 zstep; zstep; sfalse; zstep; zstep; zstep; setreg 13%Z (Z_to_bv 64 (P + 1)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve);
                    zstep; zstep; zstep; zstep; let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0; zstep; zstep.
  Ltac po_fin FR ST sp P := do 3 zstep; release_frame FR ST (bv_unsigned sp); do 2 zstep;
                         apply evt_done; do 14 eexists; eexists; split; [reflexivity|]; repeat (split; [assumption|]);
                         lazymatch goal with H : rw_cells _ _ P ?cs |- _ =>
                           exists (cells_bytes cs); eapply (rw_cells_recast _ _ _ _ H); [cbn; repeat split; reflexivity| cbn; rewrite ?app_nil_r; reflexivity| reflexivity] end.
  Ltac setp r v := setreg r (Z_to_bv 64 v) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
  destruct (Z_lt_le_dec len 128) as [LT1|LE1].
  { rewrite der_hl_small in * by lia. change (Z.to_nat 2) with 2%nat in *.
    po_head P. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia; [exfalso; lia|]. clear K.
    (* [comment removed for export] *)
    zstep. setp 11%Z (P + 2). zstep. zstep. po_fin FR ST sp P. }
  destruct (Z_lt_le_dec len 256) as [LT2|LE2].
  { rewrite der_hl_mid in * by lia. change (Z.to_nat 3) with 3%nat in *.
    po_head P. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia; [| exfalso; lia]. clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite (srliw8_small len), (Z.div_small len 256) by lia. zstep. zstep.
    zstep. bfalse. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite (srliw8_small len), (Z.div_small len 256) by lia. zstep. bfalse.
    zstep. zstep. zstep. po_fin FR ST sp P. }
  { rewrite der_hl_big in * by lia. change (Z.to_nat 4) with 4%nat in *.
    po_head P. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia; [| exfalso; lia]. clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite (srliw8_small len) by lia. zstep. zstep.
    zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?land64_small by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]);
                                         intros K1; assert (1 <= len / 256) by (apply Z.div_le_lower_bound; lia); lia].
    (* [comment removed for export] *)
    zstep. rewrite (srliw8_small (len / 256)) by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
    rewrite (Z.div_small (len / 256) 256) by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
    zstep. zstep. zstep. bfalse. clear K1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. rewrite (srliw8_small len) by lia. zstep. btrue.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. bfalse.
    zstep. zstep. zstep. po_fin FR ST sp P. }
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_STRING_SET0_STACK_A : Z := 96 + 48.        (* [comment removed for export] *)
Definition A_ASN1_LIB_C_A : Z := 0x713c0.     (* [comment removed for export] *)

Lemma ASN1_STRING_set0_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (q : bptr) (A D ty len : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_SET0_STACK_A ->
  In (q, A, ASN1_STRING_SIZE) (OW ++ LB) -> A mod 16 = 0 ->
  0 <= D < 2^64 -> 0 <= len < 2^31 -> 0 <= ty < 2^31 ->
  rw_cells ctasegs m A (asn1_string_cells 0 ty 0 0) ->
  a0 = wz A -> a1 = wz D -> a2 = wz len ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctasegs)
               /\ munch [(bv_unsigned sp - ASN1_STRING_SET0_STACK_A, bv_unsigned sp); (A, A + ASN1_STRING_SIZE)]%Z m m' /\ wmono ctasegs m m'
               /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
               /\ rw_cells ctasegs m' A (asn1_string_cells len ty D 0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_SET0_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until len. intros HEAP ST MI CEIL LO HIN AL16 DR LR TR HS -> -> ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CE1, CE2, CE3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HIN ACC OFF.
  unfold ASN1_STRING_SET0_A, ASN1_STRING_SET0_STACK_A, ASN1_STRING_SIZE, SEGTOP_A, MallocRep.wz in *. unfold asn1_string_cells, MallocRep.wz in HS.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; alia).
  assert (SEPX : A + 24 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= A) by alia.
  carve_frame 80%nat ST. do 13 zstep.
  (* [comment removed for export] *)
  zstep. zstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (HR : rw_cells ctasegs mx A ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6)]))
      by (eapply (rw_cells_recast _ _ _ _ HS); [cbn; tauto| cbn; bytes_lit_eq| reflexivity]);
    apply rw_cells_app in HR as [_ HR];
    lazymatch type of HR with rw_cells _ _ ?a ?cs => assert (HS17 : ro_cells ctasegs mx (A + 17) cs) by (replace (A + 17) with a by (cbn; lia); exact (proj1 HR)) end;
    clear HR end.
  zstep. zstep. zstep. zstep. zstep. if_false.
  (* [comment removed for export] *)
  zstep. ab_shload 4. zstep. step. rewrite ?zxb_z8, ?sxb_z8. if_false.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply CRYPTO_clear_free_null_specA with (lo := lo); [rewrite ESP; exact ST| rewrite ESP; lia| assumption| reflexivity]. }
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 0x22492c)) with (Z_to_bv 64 0x22492c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (MU' : munch [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 24)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros y Hy. lia. }
  assert (WM' : wmono ctasegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HS; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  clear MU WM MU2 WM2 MI ST HS17. rename MU' into MU. rename WM' into WM. rename MI2 into MI. rename ST2 into ST. try clear SHB1_ SHB2_. clear m1.
  (* [comment removed for export] *)
  zstep. zstep. change (Z.land 0 (-257)) with 0. zstep.
  zstep.
  zstep. zstep. zstep. zstep. rewrite set0_len_normA in HS by lia.
  (* [comment removed for export] *)
  do 10 zstep. release_frame FR ST (bv_unsigned sp). do 2 zstep.
  apply evt_done. do 15 eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  unfold asn1_string_cells, MallocRep.wz. exact HS.
Qed.
End WithRT.
