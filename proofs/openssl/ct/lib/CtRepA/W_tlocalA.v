(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog ApBase ApState ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep W_locks.
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

Definition CRYPTO_ATOMIC_LOAD : Z := 0x1f727c.
Definition CRYPTO_THREAD_GET_LOCAL_EX : Z := 0x1f75e8.
Definition GET_LOCAL_EX_STACK : Z := 64.      (* [comment removed for export] *)
Definition V_ERR_KEY : Z := 3.                 (* [comment removed for export] *)
Definition V_NO_CONTEXT : Z := 1.              (* [comment removed for export] *)

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
Lemma CRYPTO_atomic_load_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (VAL RET v lo : Z) (old : list byte),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  rw_cells ctasegs m VAL [C8 (wz v)] -> (0 < VAL /\ VAL + 8 <= SEGTOP_A /\ VAL mod 8 = 0)%Z -> acc ctasegs m VAL 8 ->
  rw_cells ctasegs m RET [CB 8 old] -> (SEGTOP_A <= RET /\ RET + 8 <= ACEIL /\ RET mod 8 = 0)%Z ->
  (RET + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= RET)%Z -> acc ctasegs m RET 8 ->
  a0 = Z_to_bv 64 VAL -> a1 = Z_to_bv 64 RET ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (RET, RET + 8)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ rw_cells ctasegs m' RET [C8 (wz v)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_ATOMIC_LOAD) fc None m (seg_rom ctasegs)).
Proof.
  intros until old. intros HEAP ST MI CEIL LO HV HVR ACCV HR HRR OFFR ACCR -> ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  unfold CRYPTO_ATOMIC_LOAD, SEGTOP_A, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (RET, RET + 8)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (RET, RET + 8)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPV : VAL + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VAL) by alia.
  assert (SEPR : RET + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= RET) by alia.
  assert (SEPVR : VAL + 8 <= RET \/ RET + 8 <= VAL) by alia.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  zstep.
  zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep.
  zstep. (* [comment removed for export] *)
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CRYPTO_THREAD_get_local_ex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (E : ap_env) (st : ap_st bptr) (bo : Z * Z) (lo : Z),
  AHEAP Σ OW LB m -> ap_state st m OW E bo ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - GET_LOCAL_EX_STACK)%Z ->
  tp = wz TP_A -> a0 = Z_to_bv 64 V_ERR_KEY -> a1 = Z_to_bv 64 V_NO_CONTEXT ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (e_es E)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CRYPTO_THREAD_GET_LOCAL_EX) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP AS ST MI CEIL LO TP -> ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof AS as (HE & HSF & _ & HTL & _).
  destruct (env_in E OW HE) as (_ & IMK & ISA & IND & _).
  pose proof HE as (_ & ND & HP). unfold CtRepP.ApRepDefs.env_blocks in HP.
  apply Forall_cons_iff in HP as [_ HP]. apply Forall_cons_iff in HP as [PMK HP].
  apply Forall_cons_iff in HP as [PSA HP]. apply Forall_cons_iff in HP as [PND _]. cbn [blk_addr blk_size fst snd] in PMK, PSA, PND.
  destruct HTL as (TMK & (pad & TSA) & TND). unfold OFF_MK_SA in TMK. unfold sa_cells in TSA.
  pose proof HSF as (_ & _ & _ & HONCE & _ & HKEY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSLOT & _).
  assert (IMK' : In (p_mk E, e_mk E, 72) (OW ++ LB)) by (apply in_or_app; left; exact IMK).
  assert (ISA' : In (p_sa E, e_sa E, 32) (OW ++ LB)) by (apply in_or_app; left; exact ISA).
  assert (IND' : In (p_nd E, e_nd E, 128) (OW ++ LB)) by (apply in_or_app; left; exact IND).
  pose proof (AH_range_gen _ _ _ _ _ HEAP IMK') as (_ & _ & _ & BKC & BKI). cbn [blk_addr blk_size fst snd] in BKC, BKI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP ISA') as (_ & _ & _ & BSC & BSI). cbn [blk_addr blk_size fst snd] in BSC, BSI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP IND') as (_ & _ & _ & BNC & BNI). cbn [blk_addr blk_size fst snd] in BNC, BNI.
  ablock HEAP IMK' ACCK OFFK. ablock HEAP ISA' ACCS OFFS. ablock HEAP IND' ACCN OFFN.
  unfold CRYPTO_THREAD_GET_LOCAL_EX, GET_LOCAL_EX_STACK, V_ERR_KEY, V_NO_CONTEXT, SEGTOP_A, TL_MASTER_ONCE, TL_MASTER_KEY, TSD_MK_SLOT, TSD_MAIN,
    K_MASTER_KEY, TP_A, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPK : e_mk E + 72 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= e_mk E) by alia.
  assert (SEPS : e_sa E + 32 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= e_sa E) by alia.
  assert (SEPN : e_nd E + 128 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= e_nd E) by alia.
  carve_frame 48%nat ST. do 7 zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  if_true.
  zstep. (* [comment removed for export] *)
  do 4 zstep. zstep. (* [comment removed for export] *)
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  name_mem m1. eapply evt_cut.
  { eapply CRYPTO_THREAD_run_once_spec with (lo := lo) (rest := []);
      [rewrite ESP; exact ST| exact MI| alia| rewrite ESP; lia| exact HONCE| cbn; alia| reflexivity]. }
  post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST end.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. zstep. (* [comment removed for export] *)
  name_mem m2.
  assert (HEAP2 : AHEAP Σ OW LB m2) by (eapply AH_frame; [exact HEAP| exact MU| exact WM| constructor; [left; cbn; alia| constructor]]).
  eapply evt_cut.
  { eapply CRYPTO_THREAD_get_local_spec with (lo := lo) (k := 3) (v := e_mk E) (KEYA := 12208672);
      [exact HEAP2| rewrite ESP; exact ST| eassumption| exact CEIL| rewrite ESP; lia| exact TP| exact HKEY| alia
      | eapply (af_lib_acc_lit RT AF Σ m2 (0xba4a20, 4, 32)); [exact (AH_art _ _ _ _ HEAP2)| vm_compute; reflexivity| cbn; lia| cbn; lia]
      | lia| exact HSLOT| reflexivity]. }
  clear HEAP2. post_call_esp ESP m2. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST end.
  match goal with H : BnHeapA.AHEAP _ _ _ _ |- _ => rename H into HEAP3 end.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. (* [comment removed for export] *)
  do 6 zstep. release_frame FR ST (bv_unsigned sp).
  zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep.
  (* [comment removed for export] *)
  zstep.
  if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  do 4 zstep.
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
  eapply AH_frame; [exact HEAP| eassumption| eassumption| constructor; [left; cbn; alia| constructor]].
Qed.

End WithRT.
