(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_locks.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac al8chk A := zstep; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 7 with (Z.ones 3) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].
Local Ltac litf := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (vm_compute; reflexivity); cbv iota end.
Local Ltac litt := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true by (vm_compute; reflexivity); cbv iota end.
Local Ltac litchk := zstep; litf.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition AP_DEFAULT_CTX : Z := 0x330788.        (* [comment removed for export] *)
Definition GET_DEFAULT_CONTEXT : Z := 0xe51a4.
Definition GET_EX_DATA_GLOBAL : Z := 0xe5464.
Definition GET_AND_LOCK : Z := 0xe5948.
Definition CRYPTO_EX_INDEX_BIO : Z := 12.

(* [comment removed for export] *)
Definition dc_statics (m : mem) : Prop :=
  ro_cells ctusegs m AP_DC_INITED [C1 (Z_to_bv 8 1)]
  /\ ro_cells ctusegs m AP_DC_KEY [C4 (wz V_DC_KEY)]
  /\ ro_cells ctusegs m AP_DC_ONCE1 [C4 (wz 2); C4 (wz 1)]
  /\ ro_cells ctusegs m AP_DC_ONCE2 [C4 (wz 2); C4 (wz 1)]
  /\ ro_cells ctusegs m TCB_TSD [C8 (wz TSD_MAIN)]
  /\ ro_cells ctusegs m AP_TSD_DC_SLOT [C8 (wz 0)].

Lemma dc_statics_of_fixed : forall m E, ap_statics_fixed m E -> dc_statics m.
Proof.
  intros m E (CS & RS & HBO & HMO & HMK & HDI & HDK & HO1 & HO2 & HXLp & HXM & HCD & HSTP & HBO1 & HIK & HOL & HTCB & HTS0 & HTSM & HTU).
  unfold dc_statics. tauto.
Qed.

Lemma dc_statics_transport : forall W m m', dc_statics m -> munch W m m' ->
  disjoint_from W AP_DC_INITED 40 -> disjoint_from W TCB_TSD 8 -> disjoint_from W AP_TSD_DC_SLOT 8 -> dc_statics m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4 & H5 & H6) MU D1 D2 D3. unfold dc_statics.
  assert (DD : forall a n, AP_DC_INITED <= a -> a + n <= AP_DC_INITED + 40 -> disjoint_from W a n).
  { intros a n Ha Hn. revert D1. clear -Ha Hn. induction W as [|[lo hi] W IH]; cbn; [tauto|]. intros [A B]. split; [lia| apply IH; exact B]. }
  unfold AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE2 in *.
  split; [eapply ro_cells_transport; [exact H1| exact MU| apply DD; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact H2| exact MU| apply DD; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact H3| exact MU| apply DD; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact H4| exact MU| apply DD; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact H5| exact MU| exact D2]|].
  eapply ro_cells_transport; [exact H6| exact MU| exact D3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_default_context_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 48)%Z ->
  tp = wz RATP -> dc_statics m ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 AP_DEFAULT_CTX) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GET_DEFAULT_CONTEXT) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO TP (HDI & HDK & HO1 & HO2 & HTCB & HTS0).
  unfold GET_DEFAULT_CONTEXT, AP_DEFAULT_CTX, GLOBALS_TOP, AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE2, V_DC_KEY in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof HTCB as HTCB'. pose proof HTS0 as HTS0'. unfold TCB_TSD in HTCB'. unfold AP_TSD_DC_SLOT in HTS0'.
  unfold MallocRep.wz in HDI, HDK, HO1, HO2, HTCB', HTS0'.
  carve_frame 32%nat ST. do 5 zstep. do 5 zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  name_mem m1. eapply evt_cut.
  { eapply CRYPTO_THREAD_run_once_spec with (lo := lo) (rest := [C4 (Z_to_bv 64 1)]);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact HO1| cbn; unfold GLOBALS_TOP; lia| reflexivity]. }
  post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -32) |- _ => rename H into ST end.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. rewrite (sx32_small 1) by lia. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  do 3 zstep. zstep.
  (* [comment removed for export] *)
  name_mem m2. eapply evt_cut.
  { eapply CRYPTO_THREAD_run_once_spec with (lo := lo) (rest := [C4 (Z_to_bv 64 1)]);
      [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact HO2| cbn; unfold GLOBALS_TOP; lia| reflexivity]. }
  post_call_esp ESP m2. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -32) |- _ => rename H into ST end.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. rewrite (sx32_small 1) by lia. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep.
  (* [comment removed for export] *)
  name_mem m3. eapply evt_cut.
  { eapply CRYPTO_THREAD_get_local_spec with (lo := lo) (k := 3) (v := 0) (KEYA := 3344244);
      [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact TP| exact HDK| unfold GLOBALS_TOP; lia| lia
      | exact HTCB'| unfold TSD_MAIN; cbn [Z.mul Z.add]; exact HTS0'| reflexivity]. }
  post_call_esp ESP m3. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -32) |- _ => rename H into ST end.
  zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. (* [comment removed for export] *)
  do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_ex_data_global_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 64)%Z ->
  tp = wz RATP -> dc_statics m -> a0 = Z_to_bv 64 0 ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 AP_DC_EXLOCK) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GET_EX_DATA_GLOBAL) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO TP DC ->.
  unfold GET_EX_DATA_GLOBAL, AP_DC_EXLOCK, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  carve_frame 16%nat ST. do 4 zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  name_mem m1. eapply evt_cut.
  { eapply get_default_context_spec with (lo := lo);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact TP
      | eapply dc_statics_transport; [exact DC| exact MU| cbn; unfold AP_DC_INITED; lia| cbn; unfold TCB_TSD; lia| cbn; unfold AP_TSD_DC_SLOT; lia]]. }
  post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -16) |- _ => rename H into ST end.
  unfold AP_DEFAULT_CTX.
  do 3 zstep. release_frame FR ST (bv_unsigned sp).
  zstep. litf. zstep. litchk. zstep. (* [comment removed for export] *)
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_and_lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (xl lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 48)%Z ->
  ro_cells ctusegs m AP_DC_EXLOCK [C8 (wz xl)] ->
  rw_cells ctusegs m xl mutex_free_cells -> obj_range xl MUTEX_SIZE lo -> (xl mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 AP_DC_EXLOCK -> a1 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a2 = Z_to_bv 64 1 ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 AP_DC_EXMETH_BIO) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (xl, xl + 40)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp) /\ rw_cells ctusegs m' xl mutex_locked_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GET_AND_LOCK) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HXLp HX HXLO AL -> -> ->.
  pose proof HXLO as HXLO'. unfold obj_range in HXLO'.
  unfold GET_AND_LOCK, AP_DC_EXLOCK, AP_DC_EXMETH_BIO, CRYPTO_EX_INDEX_BIO, GLOBALS_TOP, MUTEX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (xl, xl + 40)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : xl + 40 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= xl) by lia.
  unfold MallocRep.wz in HXLp. unfold mutex_free_cells, zeros4, MallocRep.wz in HX. cbn [repeat] in HX.
  carve_frame 32%nat ST. do 6 zstep.
  zstep. zstep. zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
  zstep. zstep. litchk. zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. (* [comment removed for export] *)
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  name_mem m1. eapply evt_cut.
  { eapply CRYPTO_THREAD_read_lock_spec with (lo := lo) (X := xl);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact HX| exact HXLO| exact AL| reflexivity]. }
  clear HX. post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -32) |- _ => rename H into ST end.
  zstep. litt.
  zstep. zstep. zstep. litchk. zstep. zstep. (* [comment removed for export] *)
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRYPTO_NEW_EX_DATA : Z := 0xe5f94.
(* [comment removed for export] *)
Definition NEW_EX_DATA_STACK : Z := 304.

Lemma CRYPTO_new_ex_data_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (E : ap_env) (ad c0 k0 lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - NEW_EX_DATA_STACK)%Z ->
  tp = wz RATP -> ap_statics_fixed m E -> exlock_free m E -> obj_range (e_xl E) MUTEX_SIZE lo -> ((e_xl E) mod 4 = 0)%Z ->
  rw_cells ctusegs m ad [C8 (wz c0); C8 (wz k0)] -> obj_range ad 16 lo -> (ad mod 8 = 0)%Z -> (ad + 16 <= e_xl E \/ e_xl E + MUTEX_SIZE <= ad)%Z ->
  a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a2 = Z_to_bv 64 ad ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (ad, ad + 16)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' ad [C8 (wz 0); C8 (wz 0)] /\ exlock_free m' E)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_NEW_EX_DATA) fc None m (seg_rom ctusegs)).
Proof using CE__.
  intros until lo. intros ST MI GLO LO TP SF HXL HXLO AL HAD HADLO ADAL DJ -> ->.
  pose proof (dc_statics_of_fixed _ _ SF) as DC.
  destruct SF as (CS & RS & HBO & HMO & HMK & HDI & HDK & HO1 & HO2 & HXLp & HXM & HCD & HSTP & HBO1 & HIK & HOL & HTCB & HTS0 & HTSM & HTU).
  clear RS HBO HMO HMK HDI HDK HO1 HO2 HCD HSTP HBO1 HIK HOL HTCB HTS0 HTSM HTU.
  pose proof HXLO as HXLO'. pose proof HADLO as HADLO'. unfold obj_range in HXLO', HADLO'.
  unfold NEW_EX_DATA_STACK, CRYPTO_NEW_EX_DATA, CRYPTO_EX_INDEX_BIO, GLOBALS_TOP, MUTEX_SIZE in *.
  unfold exlock_free in HXL. unfold mutex_free_cells, zeros4, MallocRep.wz in HXL. cbn [repeat] in HXL.
  assert (HXL0 : frozen (rw_cells ctusegs m (e_xl E) mutex_free_cells)) by exact HXL.
  unfold AP_DC_EXLOCK, MallocRep.wz in HXLp. unfold AP_DC_EXMETH_BIO, MallocRep.wz in HXM. unfold MallocRep.wz in HAD.
  pose proof (munch_refl [(e_xl E, e_xl E + 40); (bv_unsigned sp - 304, bv_unsigned sp); (ad, ad + 16)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : e_xl E + 40 <= bv_unsigned sp - 304 \/ bv_unsigned sp <= e_xl E) by lia.
  assert (SEPA : ad + 16 <= bv_unsigned sp - 304 \/ bv_unsigned sp <= ad) by lia.
  assert (SEPM : 3344272 + 8 <= bv_unsigned sp - 304 \/ bv_unsigned sp <= 3344272) by lia.
  assert (SEPM2 : 3344376 + 8 <= bv_unsigned sp - 304 \/ bv_unsigned sp <= 3344376) by lia.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 8 zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  (* [comment removed for export] *)
  carve_frame 192%nat ST. do 15 zstep. do 4 zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -192)) = bv_unsigned sp + -192) by (apply unsigned_lit; lia).
  name_mem m1. eapply evt_cut.
  { eapply get_ex_data_global_spec with (lo := lo);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact TP
      | eapply dc_statics_transport; [exact DC| exact MU| cbn; unfold AP_DC_INITED; lia| cbn; unfold TCB_TSD; lia| cbn; unfold AP_TSD_DC_SLOT; lia]
      | reflexivity]. }
  post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -192) |- _ => rename H into ST end.
  unfold AP_DC_EXLOCK. zstep. if_false. (* [comment removed for export] *)
  do 3 zstep. zstep.
  name_mem m2. eapply evt_cut.
  { eapply get_and_lock_spec with (lo := lo) (xl := e_xl E);
      [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact HXLp
      | exact HXL| exact HXLO| exact AL| reflexivity| reflexivity| reflexivity]. }
  clear HXL. post_call_esp ESP m2. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -192) |- _ => rename H into ST end.
  match goal with H : rw_cells ctusegs _ (e_xl E) _ |- _ => rename H into HXL end.
  unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz in HXL. cbn [repeat app] in HXL.
  zstep. if_false. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. al8chk ADAL.
  zstep. zstep. (* [comment removed for export] *)
  zstep. litchk. unfold AP_DC_EXMETH_BIO. zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  name_mem m3. eapply evt_cut.
  { eapply OPENSSL_sk_num_null_spec with (lo := lo); [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| reflexivity]. }
  post_call_esp ESP m3. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -192) |- _ => rename H into ST end.
  zstep. zstep. if_true. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  zstep. litchk. zstep. zstep. (* [comment removed for export] *)
  name_mem m4. eapply evt_cut.
  { eapply CRYPTO_THREAD_unlock_spec with (lo := lo) (X := e_xl E);
      [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia
      | unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz; cbn [repeat app]; exact HXL| exact HXLO| exact AL| reflexivity]. }
  clear HXL. post_call_esp ESP m4. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -192) |- _ => rename H into ST end.
  match goal with H : rw_cells ctusegs _ (e_xl E) _ |- _ => rename H into HXL end.
  unfold mutex_free_cells, zeros4, MallocRep.wz in HXL. cbn [repeat] in HXL.
  zstep. if_true. zstep. if_true. (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  do 4 zstep. zstep. (* [comment removed for export] *)
  name_mem m5.
  assert (CS5 : crypto_statics m5).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU)| | exact CS]; [eassumption|].
    intros a Ha. cbn. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
  eapply evt_cut.
  { eapply CRYPTO_free_null_spec with (lo := lo); [rewrite ESP; exact ST| unfold GLOBALS_TOP; lia| rewrite ESP; lia| eassumption| exact CS5| reflexivity]. }
  post_call_esp ESP m5. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -192) |- _ => rename H into ST end.
  zstep. zstep. (* [comment removed for export] *)
  do 14 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  name_mem m6.
  match goal with H : munch _ m m6 |- _ => rename H into MU6 end. match goal with H : wmono ctusegs m m6 |- _ => rename H into WM6 end.
  assert (MU' : munch [(bv_unsigned sp - 304, bv_unsigned sp); (ad, ad + 16)]%Z m m6).
  { eapply (munch_restore _ m m6 (e_xl E) mutex_free_cells); change (Z.of_nat (cells_size mutex_free_cells)) with 40.
    - eapply munch_weaken; [|exact MU6]. unfold sub_fp. cbn [outside]. intros y Hy. lia.
    - exact HXL0.
    - unfold mutex_free_cells, zeros4, MallocRep.wz. cbn [repeat]. assumption.
    - unfold GLOBALS_TOP. lia. }
  clear MU6.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRYPTO_FREE_EX_DATA : Z := 0xe6380.
(* [comment removed for export] *)
Definition FREE_EX_DATA_STACK : Z := 384.

Lemma CRYPTO_free_ex_data_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (E : ap_env) (ad lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - FREE_EX_DATA_STACK)%Z ->
  tp = wz RATP -> ap_statics_fixed m E -> exlock_free m E -> obj_range (e_xl E) MUTEX_SIZE lo -> ((e_xl E) mod 4 = 0)%Z ->
  rw_cells ctusegs m ad [C8 (wz 0); C8 (wz 0)] -> obj_range ad 16 lo -> (ad mod 8 = 0)%Z -> (ad + 16 <= e_xl E \/ e_xl E + MUTEX_SIZE <= ad)%Z ->
  a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a2 = Z_to_bv 64 ad ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 384, bv_unsigned sp); (ad, ad + 16)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' ad [C8 (wz 0); C8 (wz 0)] /\ exlock_free m' E)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_FREE_EX_DATA) fc None m (seg_rom ctusegs)).
Proof using CE__.
  intros until lo. intros ST MI GLO LO TP SF HXL HXLO AL HAD HADLO ADAL DJ -> ->.
  pose proof (dc_statics_of_fixed _ _ SF) as DC.
  destruct SF as (CS & RS & HBO & HMO & HMK & HDI & HDK & HO1 & HO2 & HXLp & HXM & HCD & HSTP & HBO1 & HIK & HOL & HTCB & HTS0 & HTSM & HTU).
  clear RS HBO HMO HMK HDI HDK HO1 HO2 HCD HSTP HBO1 HIK HOL HTCB HTS0 HTSM HTU.
  pose proof HXLO as HXLO'. pose proof HADLO as HADLO'. unfold obj_range in HXLO', HADLO'.
  unfold FREE_EX_DATA_STACK, CRYPTO_FREE_EX_DATA, CRYPTO_EX_INDEX_BIO, GLOBALS_TOP, MUTEX_SIZE in *.
  unfold exlock_free in HXL. unfold mutex_free_cells, zeros4, MallocRep.wz in HXL. cbn [repeat] in HXL.
  assert (HXL0 : frozen (rw_cells ctusegs m (e_xl E) mutex_free_cells)) by exact HXL.
  unfold AP_DC_EXLOCK, MallocRep.wz in HXLp. unfold AP_DC_EXMETH_BIO, MallocRep.wz in HXM. unfold MallocRep.wz in HAD.
  pose proof (munch_refl [(e_xl E, e_xl E + 40); (bv_unsigned sp - 384, bv_unsigned sp); (ad, ad + 16)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : e_xl E + 40 <= bv_unsigned sp - 384 \/ bv_unsigned sp <= e_xl E) by lia.
  assert (SEPA : ad + 16 <= bv_unsigned sp - 384 \/ bv_unsigned sp <= ad) by lia.
  assert (SEPM : 3344272 + 8 <= bv_unsigned sp - 384 \/ bv_unsigned sp <= 3344272) by lia.
  assert (SEPM2 : 3344376 + 8 <= bv_unsigned sp - 384 \/ bv_unsigned sp <= 3344376) by lia.
  carve_frame 272%nat ST. do 15 zstep.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. zstep. al8chk ADAL. zstep. zstep. (* [comment removed for export] *)
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
  name_mem m1. eapply evt_cut.
  { eapply get_ex_data_global_spec with (lo := lo);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact TP
      | eapply dc_statics_transport; [exact DC| exact MU| cbn; unfold AP_DC_INITED; lia| cbn; unfold TCB_TSD; lia| cbn; unfold AP_TSD_DC_SLOT; lia]
      | reflexivity]. }
  post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -272) |- _ => rename H into ST end.
  unfold AP_DC_EXLOCK. zstep. if_false.
  do 3 zstep. zstep.
  name_mem m2. eapply evt_cut.
  { eapply get_and_lock_spec with (lo := lo) (xl := e_xl E);
      [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact HXLp
      | exact HXL| exact HXLO| exact AL| reflexivity| reflexivity| reflexivity]. }
  clear HXL. post_call_esp ESP m2. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -272) |- _ => rename H into ST end.
  match goal with H : rw_cells ctusegs _ (e_xl E) _ |- _ => rename H into HXL end.
  unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz in HXL. cbn [repeat app] in HXL.
  zstep. if_false.
  zstep. zstep. litchk. unfold AP_DC_EXMETH_BIO. zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  name_mem m3. eapply evt_cut.
  { eapply OPENSSL_sk_num_null_spec with (lo := lo); [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| reflexivity]. }
  post_call_esp ESP m3. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -272) |- _ => rename H into ST end.
  zstep. zstep. if_true. (* [comment removed for export] *)
  zstep. zstep. litchk. zstep. zstep. (* [comment removed for export] *)
  name_mem m4. eapply evt_cut.
  { eapply CRYPTO_THREAD_unlock_spec with (lo := lo) (X := e_xl E);
      [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia
      | unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz; cbn [repeat app]; exact HXL| exact HXLO| exact AL| reflexivity]. }
  clear HXL. post_call_esp ESP m4. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -272) |- _ => rename H into ST end.
  match goal with H : rw_cells ctusegs _ (e_xl E) _ |- _ => rename H into HXL end.
  unfold mutex_free_cells, zeros4, MallocRep.wz in HXL. cbn [repeat] in HXL.
  zstep. litt. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. (* [comment removed for export] *)
  do 4 zstep. zstep. (* [comment removed for export] *)
  name_mem m5.
  assert (CS5 : crypto_statics m5).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU)| | exact CS]; [eassumption|].
    intros a Ha. cbn. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
  eapply evt_cut.
  { eapply CRYPTO_free_null_spec with (lo := lo); [rewrite ESP; exact ST| unfold GLOBALS_TOP; lia| rewrite ESP; lia| eassumption| exact CS5| reflexivity]. }
  post_call_esp ESP m5. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -272) |- _ => rename H into ST end.
  zstep. zstep. (* [comment removed for export] *)
  name_mem m6. eapply evt_cut.
  { eapply OPENSSL_sk_free_null_spec with (lo := lo); [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| reflexivity]. }
  post_call_esp ESP m6. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -272) |- _ => rename H into ST end.
  zstep. zstep. (* [comment removed for export] *)
  do 14 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  name_mem m7.
  match goal with H : munch _ m m7 |- _ => rename H into MU7 end.
  assert (MU' : munch [(bv_unsigned sp - 384, bv_unsigned sp); (ad, ad + 16)]%Z m m7).
  { eapply (munch_restore _ m m7 (e_xl E) mutex_free_cells); change (Z.of_nat (cells_size mutex_free_cells)) with 40.
    - eapply munch_weaken; [|exact MU7]. unfold sub_fp. cbn [outside]. intros y Hy. lia.
    - exact HXL0.
    - unfold mutex_free_cells, zeros4, MallocRep.wz. cbn [repeat]. assumption.
    - unfold GLOBALS_TOP. lia. }
  clear MU7.
  finish.
Qed.
End WithCeiling0.
