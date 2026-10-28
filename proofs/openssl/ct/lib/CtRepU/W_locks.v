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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs W_bio_push.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
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
Local Ltac al4chk A := zstep; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 3 with (Z.ones 2) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_outside_eq : forall m m' A bs a,
  bytes_at ctusegs m A bs -> bytes_at ctusegs m' A bs -> (A + Z.of_nat (length bs) <= 65536 \/ 3493888 <= A)%Z ->
  (A <= a < A + Z.of_nat (length bs))%Z -> m' (wa a) = m (wa a).
Proof using CE__.
  intros m m' A bs a (H0 & H1 & HB) (_ & _ & HB') HR Ha.
  assert (E : a = A + Z.of_nat (Z.to_nat (a - A))) by lia.
  specialize (HB (Z.to_nat (a - A)) ltac:(lia)). specialize (HB' (Z.to_nat (a - A)) ltac:(lia)). rewrite <- E in HB, HB'.
  rewrite !RMallocRep.ref_mrd_overlay in HB, HB' by (unfold wa; rewrite unsigned_lit by lia; lia). congruence.
Qed.

Lemma munch_restore : forall W m m' X cs,
  munch ((X, X + Z.of_nat (cells_size cs)) :: W)%Z m m' -> rw_cells ctusegs m X cs -> rw_cells ctusegs m' X cs ->
  (X + Z.of_nat (cells_size cs) <= 65536 \/ GLOBALS_TOP <= X)%Z -> munch W m m'.
Proof using CE__.
  intros W m m' X cs MU [[Hwf HBm] _] [[_ HBm'] _] HR x Hx. unfold GLOBALS_TOP in HR.
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
  pose proof (cells_bytes_length cs Hwf) as LEN.
  destruct (Z_lt_dec (bv_unsigned x) X) as [L|NL]; [apply MU; cbn; split; [lia| exact Hx]|].
  destruct (Z_lt_dec (bv_unsigned x) (X + Z.of_nat (cells_size cs))) as [L2|NL2]; [| apply MU; cbn; split; [lia| exact Hx]].
  rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
  eapply bytes_at_outside_eq; [exact HBm| exact HBm'| rewrite LEN; lia| rewrite LEN; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PTHREAD_MUTEX_LOCK : Z := 0x2c09f8.
Definition PTHREAD_MUTEX_UNLOCK : Z := 0x2c0ee4.
Definition CRYPTO_THREAD_READ_LOCK : Z := 0xe41b8.
Definition CRYPTO_THREAD_WRITE_LOCK : Z := 0xe41e4.
Definition CRYPTO_THREAD_UNLOCK : Z := 0xe4210.
Definition EBUSY : Z := 16.
(* [comment removed for export] *)
Definition mutex_locked_cells : list cell := [C4 (wz 0); C4 (wz EBUSY)] ++ zeros4 8.

(* [comment removed for export] *)
Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].

(* [comment removed for export] *)
Lemma mutex_type_bytes : forall m X (lk : Z) rest,
  rw_cells ctusegs m X (C4 (wz 0) :: C4 (wz lk) :: rest) ->
  rw_cells ctusegs m X (C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C4 (wz lk) :: rest).
Proof.
  intros m X lk rest H. eapply rw_cells_recast; [exact H| | | reflexivity].
  - destruct H as [[Hwf _] _]. cbn in Hwf |- *. tauto.
  - cbn [cells_bytes cbytes app]. f_equal.
Qed.
Lemma mutex_type_word : forall m X (lk : Z) rest,
  rw_cells ctusegs m X (C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C4 (wz lk) :: rest) ->
  rw_cells ctusegs m X (C4 (wz 0) :: C4 (wz lk) :: rest).
Proof.
  intros m X lk rest H. eapply rw_cells_recast; [exact H| | | reflexivity].
  - destruct H as [[Hwf _] _]. cbn in Hwf |- *. tauto.
  - cbn [cells_bytes cbytes app]. f_equal.
Qed.

(* [comment removed for export] *)
Lemma pthread_mutex_lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> (lo <= bv_unsigned sp)%Z ->
  rw_cells ctusegs m X mutex_free_cells -> obj_range X MUTEX_SIZE lo -> (X mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 X ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(X, X + 40)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp) /\ rw_cells ctusegs m' X mutex_locked_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PTHREAD_MUTEX_LOCK) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI LOS HX HXLO AL ->.
  unfold obj_range in HXLO. unfold PTHREAD_MUTEX_LOCK, GLOBALS_TOP, MUTEX_SIZE in *.
  pose proof (munch_refl [(X, X + 40)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (X + 4)) = true) by (apply amo_aligned_w_intro; lia).
  unfold mutex_free_cells, zeros4 in HX. cbn [repeat] in HX. apply mutex_type_bytes in HX. unfold MallocRep.wz in HX.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep.
  zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. zstep.
  finish.
  unfold mutex_locked_cells, zeros4, EBUSY. cbn [repeat app]. apply mutex_type_word. unfold MallocRep.wz. assumption.
Qed.

(* [comment removed for export] *)
Lemma pthread_mutex_unlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 96)%Z ->
  rw_cells ctusegs m X mutex_locked_cells -> obj_range X MUTEX_SIZE lo -> (X mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 X ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (X, X + 40)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp) /\ rw_cells ctusegs m' X mutex_free_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PTHREAD_MUTEX_UNLOCK) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HX HXLO AL ->.
  unfold obj_range in HXLO. unfold PTHREAD_MUTEX_UNLOCK, GLOBALS_TOP, MUTEX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (X, X + 40)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : X + 40 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= X) by lia.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (X + 4)) = true) by (apply amo_aligned_w_intro; lia).
  unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz in HX. cbn [repeat app] in HX.
  carve_frame 96%nat ST.
  do 12 zstep.
  zstep. zstep. rewrite (zx32_small 0) by lia. (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. do 12 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma CRYPTO_THREAD_read_lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  rw_cells ctusegs m X mutex_free_cells -> obj_range X MUTEX_SIZE lo -> (X mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 X ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (X, X + 40)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp) /\ rw_cells ctusegs m' X mutex_locked_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_READ_LOCK) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HX HXLO AL ->.
  pose proof HXLO as HXLO'. unfold obj_range in HXLO'. unfold CRYPTO_THREAD_READ_LOCK, GLOBALS_TOP, MUTEX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (X, X + 40)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : X + 40 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= X) by lia.
  unfold mutex_free_cells, zeros4, MallocRep.wz in HX. cbn [repeat] in HX.
  carve_frame 16%nat ST. do 4 zstep. zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply pthread_mutex_lock_spec with (lo := lo) (X := X);
      [rewrite ESP; exact ST| exact MI| rewrite ESP; lia| exact HX| exact HXLO| exact AL| reflexivity]. }
  clear HX. post_call ctusegs m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST end.
  (* [comment removed for export] *)
  zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma CRYPTO_THREAD_unlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 112)%Z ->
  rw_cells ctusegs m X mutex_locked_cells -> obj_range X MUTEX_SIZE lo -> (X mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 X ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (X, X + 40)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp) /\ rw_cells ctusegs m' X mutex_free_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_UNLOCK) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HX HXLO AL ->.
  pose proof HXLO as HXLO'. unfold obj_range in HXLO'. unfold CRYPTO_THREAD_UNLOCK, GLOBALS_TOP, MUTEX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (X, X + 40)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : X + 40 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= X) by lia.
  unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz in HX. cbn [repeat app] in HX.
  carve_frame 16%nat ST. do 4 zstep. zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply pthread_mutex_unlock_spec with (lo := lo) (X := X);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia
      | unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz; cbn [repeat app]; exact HX| exact HXLO| exact AL| reflexivity]. }
  clear HX. post_call ctusegs m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -16) |- _ => rename H into ST end.
  zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRYPTO_THREAD_RUN_ONCE : Z := 0xe4288.

Lemma CRYPTO_THREAD_run_once_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ONCE lo : Z) (rest : list cell),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  ro_cells ctusegs m ONCE (C4 (wz 2) :: rest) -> (0 < ONCE /\ ONCE + 4 + Z.of_nat (cells_size rest) <= GLOBALS_TOP)%Z ->
  a0 = Z_to_bv 64 ONCE ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_RUN_ONCE) fc None m (seg_rom ctusegs)).
Proof.
  intros until rest. intros ST MI GLO LO HO HOR ->.
  unfold CRYPTO_THREAD_RUN_ONCE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPO : ONCE + 4 + Z.of_nat (cells_size rest) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= ONCE) by lia.
  unfold MallocRep.wz in HO.
  carve_frame 16%nat ST. do 4 zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRYPTO_THREAD_GET_LOCAL : Z := 0xe42e0.

Lemma shl32_shr29 : forall k, 0 <= k < 2^32 -> Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl k 32))) 29 = 8 * k.
Proof.
  intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (k * 2^32) with (8 * k * 2^29) by lia. apply Z.div_mul. lia.
Qed.
Lemma shl32_shr29' : forall k, 0 <= k < 2^32 -> Z.shiftr (Z.shiftl k 32) 29 = 8 * k.
Proof.
  intros k Hk. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (k * 2^32) with (8 * k * 2^29) by lia. apply Z.div_mul. lia.
Qed.
(* [comment removed for export] *)
Lemma shl32_shr29'' : forall k, 0 <= k < 2^32 -> Z.shiftr (Z.land (Z.shiftl k 32) 18446744073709551615) 29 = 8 * k.
Proof.
  intros k Hk. change 18446744073709551615 with (Z.ones 64). rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (k * 2^32) with (8 * k * 2^29) by lia. apply Z.div_mul. lia.
Qed.

Lemma CRYPTO_THREAD_get_local_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (KEYA k v lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  tp = wz RATP ->
  ro_cells ctusegs m KEYA [C4 (wz k)] -> (0 < KEYA /\ KEYA + 4 <= GLOBALS_TOP /\ KEYA mod 4 = 0)%Z -> (0 <= k < 16)%Z ->
  ro_cells ctusegs m TCB_TSD [C8 (wz TSD_MAIN)] ->
  ro_cells ctusegs m (TSD_MAIN + 8 * k) [C8 (wz v)] ->
  a0 = Z_to_bv 64 KEYA ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_GET_LOCAL) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO -> HK HKR KR HT HS ->.
  unfold CRYPTO_THREAD_GET_LOCAL, GLOBALS_TOP, TCB_TSD, TSD_MAIN, RATP, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (KAL : (KEYA mod 4 = 0)%Z) by tauto.
  assert (SEPK : KEYA + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= KEYA) by lia.
  assert (SEPT : 3355088 + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= 3355088) by lia.
  assert (SEPS : 3491216 + 8 * k + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= 3491216 + 8 * k) by lia.
  carve_frame 16%nat ST. do 4 zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. al4chk KAL.
  zstep. rewrite (sx32_small k) by lia. (* [comment removed for export] *)
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *)
  zstep. rewrite (shl32_shr29'' k) by lia. (* [comment removed for export] *)
  pose proof (ro_cells_read_at ctusegs m1 _ _ 0%nat (C8 (Z_to_bv 64 v)) 8%nat (Z_to_bv 64 (3491216 + 8 * k)) HS eq_refl eq_refl
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. (* [comment removed for export] *)
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPENSSL_SK_NUM : Z := 0xe7798.
Definition OPENSSL_SK_FREE : Z := 0xe6cc4.

Lemma OPENSSL_sk_num_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  a0 = Z_to_bv 64 0 ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_SK_NUM) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO ->.
  unfold OPENSSL_SK_NUM, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 16%nat ST. do 4 zstep.
  zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

Lemma OPENSSL_sk_free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 32)%Z ->
  a0 = Z_to_bv 64 0 ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_SK_FREE) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO ->. unfold OPENSSL_SK_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST. do 6 zstep.
  zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.
End WithCeiling0.
