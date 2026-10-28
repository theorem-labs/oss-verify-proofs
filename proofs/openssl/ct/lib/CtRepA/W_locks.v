(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
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
(* [comment removed for export] *)
Lemma seg_rom_off_hull : forall a : word, bv_unsigned a + 1 <= img_hull_lo \/ img_hull_hi <= bv_unsigned a -> seg_rom ctasegs a = None.
Proof.
  intros a H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  assert (FS : find_segment ctasegs (bv_unsigned a) 1 = None).
  { destruct H as [H|H].
    - apply find_segment_below. exact (forallb_mono_bot ctasegs (bv_unsigned a + 1) img_hull_lo H asegs_bot).
    - apply find_segment_above; [pose proof (bv_unsigned_in_range 64 a); lia | exact (forallb_mono_top ctasegs img_hull_hi _ H asegs_top)]. }
  rewrite FS. reflexivity.
Qed.
Lemma mrd_off_img : forall m (x : word), (bv_unsigned x + 1 <= 0x10000 \/ SEGTOP_A <= bv_unsigned x)%Z -> mrd ctasegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply seg_rom_off_hull. unfold img_hull_lo, img_hull_hi, SEGTOP_A in *. lia. Qed.

Lemma bytes_at_outside_eq : forall m m' A bs a,
  bytes_at ctasegs m A bs -> bytes_at ctasegs m' A bs -> (A + Z.of_nat (length bs) <= 65536 \/ SEGTOP_A <= A)%Z ->
  (A <= a < A + Z.of_nat (length bs))%Z -> m' (wa a) = m (wa a).
Proof.
  intros m m' A bs a (H0 & H1 & HB) (_ & _ & HB') HR Ha. unfold SEGTOP_A in HR.
  assert (E : a = A + Z.of_nat (Z.to_nat (a - A))) by lia.
  specialize (HB (Z.to_nat (a - A)) ltac:(lia)). specialize (HB' (Z.to_nat (a - A)) ltac:(lia)). rewrite <- E in HB, HB'.
  rewrite !mrd_off_img in HB, HB' by (unfold wa, SEGTOP_A; rewrite unsigned_lit by lia; lia). congruence.
Qed.

Lemma munch_restore : forall W m m' X cs,
  munch ((X, X + Z.of_nat (cells_size cs)) :: W)%Z m m' -> rw_cells ctasegs m X cs -> rw_cells ctasegs m' X cs ->
  (X + Z.of_nat (cells_size cs) <= 65536 \/ SEGTOP_A <= X)%Z -> munch W m m'.
Proof.
  intros W m m' X cs MU [[Hwf HBm] _] [[_ HBm'] _] HR x Hx.
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
  pose proof (cells_bytes_length cs Hwf) as LEN.
  destruct (Z_lt_dec (bv_unsigned x) X) as [L|NL]; [apply MU; cbn; split; [lia| exact Hx]|].
  destruct (Z_lt_dec (bv_unsigned x) (X + Z.of_nat (cells_size cs))) as [L2|NL2]; [| apply MU; cbn; split; [lia| exact Hx]].
  rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
  eapply bytes_at_outside_eq; [exact HBm| exact HBm'| rewrite LEN; lia| rewrite LEN; lia].
Qed.

(* [comment removed for export] *)
Definition obj_range (X n lo : Z) : Prop := (0 < X /\ X + n <= lo /\ (X + n <= 65536 \/ SEGTOP_A <= X))%Z.
Lemma obj_range_of_block : forall Σ OW LB m b lo,
  AHEAP Σ OW LB m -> In b (OW ++ LB) -> ACEIL <= lo -> obj_range (blk_addr b) (blk_size b) lo.
Proof.
  intros Σ OW LB m b lo HEAP IN CEIL. pose proof (AH_range_gen _ _ _ _ b HEAP IN) as (B0 & _ & B2 & B3 & B4).
  unfold obj_range, SEGTOP_A. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PTHREAD_MUTEX_LOCK : Z := 0x52e4d4.
Definition PTHREAD_MUTEX_UNLOCK : Z := 0x52e9c0.
Definition CRYPTO_THREAD_READ_LOCK : Z := 0x1f6f2c.
Definition CRYPTO_THREAD_WRITE_LOCK : Z := 0x1f6f58.
Definition CRYPTO_THREAD_UNLOCK : Z := 0x1f6f84.
Definition EBUSY : Z := 16.
(* [comment removed for export] *)
Definition mutex_locked_cells : list cell := [C4 (wz 0); C4 (wz EBUSY)] ++ zeros4 8.

(* [comment removed for export] *)
Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].

(* [comment removed for export] *)
Lemma mutex_type_bytes : forall m X (lk : Z) rest,
  rw_cells ctasegs m X (C4 (wz 0) :: C4 (wz lk) :: rest) ->
  rw_cells ctasegs m X (C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C4 (wz lk) :: rest).
Proof.
  intros m X lk rest H. eapply rw_cells_recast; [exact H| | | reflexivity].
  - destruct H as [[Hwf _] _]. cbn in Hwf |- *. tauto.
  - cbn [cells_bytes cbytes app]. f_equal.
Qed.
Lemma mutex_type_word : forall m X (lk : Z) rest,
  rw_cells ctasegs m X (C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C4 (wz lk) :: rest) ->
  rw_cells ctasegs m X (C4 (wz 0) :: C4 (wz lk) :: rest).
Proof.
  intros m X lk rest H. eapply rw_cells_recast; [exact H| | | reflexivity].
  - destruct H as [[Hwf _] _]. cbn in Hwf |- *. tauto.
  - cbn [cells_bytes cbytes app]. f_equal.
Qed.

(* [comment removed for export] *)
Lemma pthread_mutex_lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> (lo <= bv_unsigned sp)%Z ->
  rw_cells ctasegs m X mutex_free_cells -> obj_range X MUTEX_SIZE lo -> (X mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 X ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(X, X + 40)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ rw_cells ctasegs m' X mutex_locked_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PTHREAD_MUTEX_LOCK) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST MI LOS HX HXLO AL ->.
  unfold obj_range in HXLO. unfold PTHREAD_MUTEX_LOCK, SEGTOP_A, MUTEX_SIZE in *.
  pose proof (munch_refl [(X, X + 40)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
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
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> SEGTOP_A <= lo -> (lo <= bv_unsigned sp - 96)%Z ->
  rw_cells ctasegs m X mutex_locked_cells -> obj_range X MUTEX_SIZE lo -> (X mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 X ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (X, X + 40)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ rw_cells ctasegs m' X mutex_free_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PTHREAD_MUTEX_UNLOCK) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST MI GLO LO HX HXLO AL ->.
  unfold obj_range in HXLO. unfold PTHREAD_MUTEX_UNLOCK, SEGTOP_A, MUTEX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (X, X + 40)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
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
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> SEGTOP_A <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  rw_cells ctasegs m X mutex_free_cells -> obj_range X MUTEX_SIZE lo -> (X mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 X ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (X, X + 40)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ rw_cells ctasegs m' X mutex_locked_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_READ_LOCK) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST MI GLO LO HX HXLO AL ->.
  pose proof HXLO as HXLO'. unfold obj_range in HXLO'. unfold CRYPTO_THREAD_READ_LOCK, SEGTOP_A, MUTEX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (X, X + 40)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : X + 40 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= X) by lia.
  unfold mutex_free_cells, zeros4, MallocRep.wz in HX. cbn [repeat] in HX.
  carve_frame 16%nat ST. do 4 zstep. idtac. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply pthread_mutex_lock_spec with (lo := lo) (X := X);
      [rewrite ESP; exact ST| exact MI| rewrite ESP; lia| exact HX| exact HXLO| exact AL| reflexivity]. }
  clear HX. post_call ctasegs m1. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end.
  (* [comment removed for export] *)
  zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma CRYPTO_THREAD_unlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> SEGTOP_A <= lo -> (lo <= bv_unsigned sp - 112)%Z ->
  rw_cells ctasegs m X mutex_locked_cells -> obj_range X MUTEX_SIZE lo -> (X mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 X ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (X, X + 40)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ rw_cells ctasegs m' X mutex_free_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_UNLOCK) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST MI GLO LO HX HXLO AL ->.
  pose proof HXLO as HXLO'. unfold obj_range in HXLO'. unfold CRYPTO_THREAD_UNLOCK, SEGTOP_A, MUTEX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (X, X + 40)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : X + 40 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= X) by lia.
  unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz in HX. cbn [repeat app] in HX.
  carve_frame 16%nat ST. do 4 zstep. idtac. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply pthread_mutex_unlock_spec with (lo := lo) (X := X);
      [rewrite ESP; exact ST| exact MI| unfold SEGTOP_A; lia| rewrite ESP; lia
      | unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz; cbn [repeat app]; exact HX| exact HXLO| exact AL| reflexivity]. }
  clear HX. post_call ctasegs m1. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo (bv_unsigned sp + -16) |- _ => rename H into ST end.
  zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRYPTO_THREAD_RUN_ONCE : Z := 0x1f700c.

Lemma CRYPTO_THREAD_run_once_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ONCE lo : Z) (rest : list cell),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> SEGTOP_A <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  ro_cells ctasegs m ONCE (C4 (wz 2) :: rest) -> (0 < ONCE /\ ONCE + 4 + Z.of_nat (cells_size rest) <= SEGTOP_A)%Z ->
  a0 = Z_to_bv 64 ONCE ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_RUN_ONCE) fc None m (seg_rom ctasegs)).
Proof.
  intros until rest. intros ST MI GLO LO HO HOR ->.
  unfold CRYPTO_THREAD_RUN_ONCE, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPO : ONCE + 4 + Z.of_nat (cells_size rest) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= ONCE) by lia.
  unfold MallocRep.wz in HO.
  carve_frame 16%nat ST. do 4 zstep. idtac. zstep. (* [comment removed for export] *)
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
Definition CRYPTO_THREAD_GET_LOCAL : Z := 0x1f7064.

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
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (KEYA k v lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  tp = wz TP_A ->
  ro_cells ctasegs m KEYA [C4 (wz k)] -> (0 < KEYA /\ KEYA + 4 <= SEGTOP_A /\ KEYA mod 8 = 0)%Z -> acc ctasegs m KEYA 4 -> (0 <= k < 16)%Z ->
  ro_cells ctasegs m (TSD_MAIN + 8 * k) [C8 (wz v)] ->
  a0 = Z_to_bv 64 KEYA ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_GET_LOCAL) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO -> HK HKR ACCK KR HS ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (af_tsd RT AF Σ m (AH_art _ _ _ _ HEAP)) as HT.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold CRYPTO_THREAD_GET_LOCAL, SEGTOP_A, TSD_MAIN, TP_A, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPK : KEYA + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= KEYA) by lia.
  assert (SEPT : 12227480 + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= 12227480) by alia.
  assert (SEPS : 12363672 + 8 * k + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= 12363672 + 8 * k) by alia.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  zstep. rewrite (sx32_small k) by lia.
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *)
  zstep. rewrite (shl32_shr29'' k) by lia. (* [comment removed for export] *)
  name_mem m1.
  match goal with H : ro_cells ctasegs m1 (12363672 + 8 * k) _ |- _ => rename H into HS1 end.
  pose proof (ro_cells_read_at ctasegs m1 _ _ 0%nat (C8 (Z_to_bv 64 v)) 8%nat (Z_to_bv 64 (12363672 + 8 * k)) HS1 eq_refl eq_refl
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. (* [comment removed for export] *)
  zstep.
  finish.
  eapply AH_frame; [exact HEAP| eassumption| eassumption| constructor; [left; cbn; alia| constructor]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPENSSL_SK_NUM : Z := 0x1fca48.
Definition OPENSSL_SK_FREE : Z := 0x1fb7d8.

Lemma OPENSSL_sk_num_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> SEGTOP_A <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  a0 = Z_to_bv 64 0 ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_SK_NUM) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST MI GLO LO ->.
  unfold OPENSSL_SK_NUM, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 16%nat ST. do 4 zstep.
  zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

Lemma OPENSSL_sk_free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> SEGTOP_A <= lo -> (lo <= bv_unsigned sp - 32)%Z ->
  a0 = Z_to_bv 64 0 ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_SK_FREE) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST MI GLO LO ->. unfold OPENSSL_SK_FREE, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST. do 6 zstep.
  zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.
End WithRT.
