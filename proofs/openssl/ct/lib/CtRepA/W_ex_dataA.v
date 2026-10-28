(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge RzCPS SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_small R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct ImplAX BnIfaceA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 ImplA RtCallA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_locks W_akit Fr_ossl_crypto_new_ex_data_ex Fr_CRYPTO_free_ex_data.
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

Definition GET_DEFAULT_CONTEXT_A : Z := 0x1f85c4.
Definition GET_EX_DATA_GLOBAL_A : Z := 0x1f8924.
Definition GET_AND_LOCK_A : Z := 0x1f92c0.
Definition CRYPTO_EX_INDEX_BIO : Z := 12.
(* [comment removed for export] *)
Local Notation E_cned_tail := (E_CRYPTO_new_ex_data_1f52a8 : uk_tail 0x1f9d68 0x1f97a4).                      (* [comment removed for export] *)
Local Notation E_cned_free := (E_ossl_crypto_new_ex_data_ex_1f5004 : uk_call 0x1f97a4 0x1f9c60 0x1fd334).      (* [comment removed for export] *)


Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition dc_staticsA (m : mem) : Prop :=
  ro_cells ctasegs m AP_DC_INITED [C1 (Z_to_bv 8 1)] /\ ro_cells ctasegs m AP_DC_KEY [C4 (wz V_DC_KEY)]
  /\ ro_cells ctasegs m AP_DC_ONCE1 [C4 (wz 2)] /\ ro_cells ctasegs m AP_DC_ONCE1_RET [C4 (wz 1)]
  /\ ro_cells ctasegs m AP_DC_ONCE2 [C4 (wz 2)] /\ ro_cells ctasegs m AP_DC_ONCE2_RET [C4 (wz 1)]
  /\ ro_cells ctasegs m AP_TSD_DC_SLOT [C8 (wz 0)].

Lemma dc_staticsA_of_fixed : forall m E, ap_statics_fixed m E -> dc_staticsA m.
Proof.
  intros m E H. destruct H as (_ & _ & _ & _ & _ & _ & H1 & H2 & H3 & H4 & H5 & H6 & _ & _ & _ & _ & _ & _ & _ & _ & H7 & _).
  repeat (split; [assumption|]). exact H7.
Qed.

Lemma dc_staticsA_transport : forall W m m', dc_staticsA m -> munch W m m' ->
  Forall (fun iv => SEGTOP_A <= fst iv) W -> dc_staticsA m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4 & H5 & H6 & H7) MU HW.
  assert (D : forall A n, A + n <= SEGTOP_A /\ 0 <= n -> disjoint_from W A n).
  { intros A n [HA Hn]. clear - HW HA Hn. induction W as [|[l h] W IH]; [exact I|]. apply Forall_cons_iff in HW as [X1 HW]. cbn [disjoint_from fst snd] in *. split; [lia| exact (IH HW)]. }
  unfold dc_staticsA, AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE1_RET, AP_DC_ONCE2, AP_DC_ONCE2_RET, AP_TSD_DC_SLOT, TSD_MAIN, V_DC_KEY, AP_DC_INT, SEGTOP_A in *.
  repeat match goal with |- _ /\ _ => split end;
    (eapply ro_cells_transport; [eassumption| exact MU| apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Lemma ro_cells_libS : forall OW m m' A cs lo' hi',
  ro_cells ctasegs m A cs -> agree_on (lib_addr OW) m m' -> In (lo', hi') LIBW_S -> lo' <= A -> A + Z.of_nat (cells_size cs) <= hi' ->
  ro_cells ctasegs m' A cs.
Proof.
  intros OW m m' A cs lo' hi' H AG Hin H1 H2. eapply ro_cells_agree; [exact AG| exact H|].
  intros a Ha. apply (lib_addr_static OW a lo' hi' Hin). lia.
Qed.

Lemma dc_staticsA_lib : forall OW m m', dc_staticsA m -> agree_on (lib_addr OW) m m' -> dc_staticsA m'.
Proof.
  intros OW m m' (H1 & H2 & H3 & H4 & H5 & H6 & H7) AG.
  unfold dc_staticsA, AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE1_RET, AP_DC_ONCE2, AP_DC_ONCE2_RET, AP_TSD_DC_SLOT, TSD_MAIN, V_DC_KEY in *.
  repeat match goal with |- _ /\ _ => split end;
    first [ eapply (ro_cells_libS OW m m' _ _ 0xba46c0 0xba8ae0); [eassumption| exact AG| unfold LIBW_S; cbn; tauto| cbn; lia| cbn; lia]
          | eapply (ro_cells_libS OW m m' _ _ 0xbca7a0 0xbcab98); [eassumption| exact AG| unfold LIBW_S; cbn; tauto| cbn; lia| cbn; lia] ].
Qed.

Lemma aclient_lib : forall OW LB SP m m', agree_on (aclient_addr (OW ++ LB) SP) m m' -> agree_on (lib_addr OW) m m'.
Proof. intros OW LB SP m m' AG. eapply agree_on_mono; [exact AG|]. intros a Ha. exact (lib_addr_aclient OW LB SP a Ha). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_default_context_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 32)%Z -> bv_unsigned sp <= USTACK_TOP ->
  tp = wz TP_A -> dc_staticsA m ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 AP_DC_INT) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GET_DEFAULT_CONTEXT_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO SPT TP (HDI & HDK & HO1 & HR1 & HO2 & HR2 & HTS).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  unfold GET_DEFAULT_CONTEXT_A, AP_DC_INT, AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE1_RET, AP_DC_ONCE2, AP_DC_ONCE2_RET, AP_TSD_DC_SLOT, TSD_MAIN, V_DC_KEY in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  unfold MallocRep.wz in HDK, HO1, HR1, HO2, HR2, HTS.
  carve_frame 16%nat ST. do 4 zstep. do 4 zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  name_mem m1. eapply evt_cut.
  { eapply CRYPTO_THREAD_run_once_spec with (lo := lo) (rest := []);
      [rewrite ESP; exact ST| exact MI| unfold SEGTOP_A; alia| rewrite ESP; lia| exact HO2| cbn; unfold SEGTOP_A; lia| reflexivity]. }
  post_call ctasegs m1. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI' end.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. rewrite ?(sx32_small_A 1) by lia. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  do 4 zstep. zstep.
  (* [comment removed for export] *)
  name_mem m2. eapply evt_cut.
  { eapply CRYPTO_THREAD_run_once_spec with (lo := lo) (rest := []);
      [rewrite ESP; exact ST| exact MI'| unfold SEGTOP_A; alia| rewrite ESP; lia| exact HO1| cbn; unfold SEGTOP_A; lia| reflexivity]. }
  post_call ctasegs m2. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI'' end.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. rewrite ?(sx32_small_A 1) by lia. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  name_mem m3.
  match goal with H : munch _ m m3 |- _ => rename H into MU3 end. match goal with H : wmono ctasegs m m3 |- _ => rename H into WM3 end.
  assert (HEAP3 : AHEAP Σ OW LB m3).
  { eapply AH_frame; [exact HEAP| exact MU3| exact WM3|]. constructor; [left; cbn; clear - CEIL LO SPT; alia| constructor]. }
  assert (ACCK : acc ctasegs m3 12209184 4).
  { eapply (af_lib_acc_lit _ AF Σ m3 (0xba4c20, 4, 32)); [exact (AH_art _ _ _ _ HEAP3)| vm_compute; reflexivity| cbn; lia| cbn; lia]. }
  eapply evt_cut.
  { eapply CRYPTO_THREAD_get_local_spec with (lo := lo) (k := 4) (v := 0) (KEYA := 12209184);
      [exact HEAP3| rewrite ESP; exact ST| exact MI''| exact CEIL| rewrite ESP; lia| exact TP| exact HDK| unfold SEGTOP_A; lia| exact ACCK| lia
      | exact HTS| reflexivity]. }
  clear HEAP3 ACCK. post_call ctasegs m3. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end.
  match goal with H : AHEAP Σ OW LB _ |- _ => rename H into HEAP4 end.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. zstep. zstep. zstep. zstep.
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_ex_data_global_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 48)%Z -> bv_unsigned sp <= USTACK_TOP ->
  tp = wz TP_A -> dc_staticsA m -> a0 = Z_to_bv 64 0 ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 AP_DC_EXLOCK) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GET_EX_DATA_GLOBAL_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO SPT TP DC ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  unfold GET_EX_DATA_GLOBAL_A, AP_DC_EXLOCK, AP_DC_INT in *. change (12208768 + 8) with 12208776.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 16%nat ST. do 4 zstep.
  zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; clear - CEIL LO SPT; alia| constructor]. }
  eapply evt_cut.
  { eapply get_default_context_specA with (lo := lo);
      [exact HEAP1| rewrite ESP; exact ST| exact MI| exact CEIL| rewrite ESP; lia| rewrite ESP; unfold USTACK_TOP in *; lia| exact TP
      | eapply dc_staticsA_transport; [exact DC| exact MU1| constructor; [cbn; unfold SEGTOP_A; clear - C1 CEIL LO; alia| constructor]]]. }
  clear HEAP1. post_call ctasegs m1. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end.
  unfold AP_DC_INT.
  (* [comment removed for export] *)
  zstep. setreg 11 (Z_to_bv 64 0) ltac:(vm_compute; reflexivity).
  zstep.
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_and_lock_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (xl lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 48)%Z -> bv_unsigned sp <= USTACK_TOP ->
  ro_cells ctasegs m AP_DC_EXLOCK [C8 (wz xl)] ->
  rw_cells ctasegs m xl mutex_free_cells -> obj_range xl MUTEX_SIZE lo -> (xl mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 AP_DC_EXLOCK -> a1 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a2 = Z_to_bv 64 1 ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 AP_DC_EXMETH_BIO) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (xl, xl + 40)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ rw_cells ctasegs m' xl mutex_locked_cells)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GET_AND_LOCK_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO SPT HXLp HX HXLO AL -> -> ->.
  pose proof HXLO as HXLO'. unfold obj_range in HXLO'.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  unfold GET_AND_LOCK_A, AP_DC_EXLOCK, AP_DC_EXMETH_BIO, AP_DC_INT, CRYPTO_EX_INDEX_BIO, SEGTOP_A, MUTEX_SIZE in *.
  change (12208768 + 8) with 12208776 in *. change (12208768 + 112) with 12208880 in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (xl, xl + 40)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPX : xl + 40 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= xl) by (unfold BnHeapA.ACEIL in *; lia).
  unfold MallocRep.wz in HXLp. unfold mutex_free_cells, zeros4, MallocRep.wz in HX. cbn [repeat] in HX.
  (* [comment removed for export] *)
  assert (ACCG : acc ctasegs m 12208776 8).
  { eapply (af_lib_acc_lit _ AF Σ m (0xba4a80, 328, 416)); [exact (AH_art _ _ _ _ HEAP)| vm_compute; reflexivity| cbn; lia| cbn; lia]. }
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU0.
  assert (OFF0 : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]%Z).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. split; [clear - C2 CEIL LO; lia| exact I]. }
  carve_frame 32%nat ST. do 6 zstep.
  zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
  (* [comment removed for export] *)
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. (* [comment removed for export] *)
  clear MU0 OFF0 ACCG SHB1 SHB2.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  name_mem m1. eapply evt_cut.
  { eapply CRYPTO_THREAD_read_lock_spec with (lo := lo) (X := xl);
      [rewrite ESP; exact ST| exact MI| unfold SEGTOP_A, BnHeapA.ACEIL in *; lia| rewrite ESP; lia| exact HX| exact HXLO| exact AL| reflexivity]. }
  clear HX. post_call ctasegs m1. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.   (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *)
  do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.
End WithRT.

(* [comment removed for export] *)
Lemma c8_blur1 : forall m A (v : word) rest, rw_cells ctasegs m A (C8 v :: rest) -> rw_cells ctasegs m A (CB 8 (le8 v) :: rest).
Proof.
  intros m A v rest H. change (C8 v :: rest) with ([C8 v] ++ rest) in H. change (CB 8 (le8 v) :: rest) with ([CB 8 (le8 v)] ++ rest).
  apply rw_cells_app in H. destruct H as [H1 H2]. apply rw_cells_app. split; [| exact H2].
  eapply rw_cells_recast; [exact H1| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
Qed.
Lemma low3_blur : forall m A c0 c1 c2 c3 c4 (v5 v6 v7 : word) rest,
  rw_cells ctasegs m A ([c0; c1; c2; c3; c4] ++ C8 v5 :: C8 v6 :: C8 v7 :: rest) ->
  rw_cells ctasegs m A ([c0; c1; c2; c3; c4] ++ CB 8 (le8 v5) :: CB 8 (le8 v6) :: CB 8 (le8 v7) :: rest).
Proof.
  intros m A c0 c1 c2 c3 c4 v5 v6 v7 rest H. apply rw_cells_app in H. destruct H as [H1 H2]. apply rw_cells_app. split; [exact H1|].
  apply c8_blur1 in H2. change (CB 8 (le8 v5) :: C8 v6 :: C8 v7 :: rest) with ([CB 8 (le8 v5)] ++ (C8 v6 :: C8 v7 :: rest)) in H2.
  apply rw_cells_app in H2. destruct H2 as [H3 H4]. apply c8_blur1 in H4.
  change (CB 8 (le8 v6) :: C8 v7 :: rest) with ([CB 8 (le8 v6)] ++ (C8 v7 :: rest)) in H4. apply rw_cells_app in H4. destruct H4 as [H5 H6]. apply c8_blur1 in H6.
  change (CB 8 (le8 v5) :: CB 8 (le8 v6) :: CB 8 (le8 v7) :: rest) with ([CB 8 (le8 v5)] ++ ([CB 8 (le8 v6)] ++ (CB 8 (le8 v7) :: rest))).
  apply rw_cells_app. split; [exact H3|]. apply rw_cells_app. split; [exact H5| exact H6].
Qed.

Lemma low7_blurB : forall m A c0 (v1 v2 v3 v4 v5 v6 v7 : word) rest,
  rw_cells ctasegs m A (c0 :: C8 v1 :: C8 v2 :: C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest) ->
  rw_cells ctasegs m A (c0 :: CB 8 (le8 v1) :: CB 8 (le8 v2) :: CB 8 (le8 v3) :: CB 8 (le8 v4) :: CB 8 (le8 v5) :: CB 8 (le8 v6) :: CB 8 (le8 v7) :: rest).
Proof.
  intros m A c0 v1 v2 v3 v4 v5 v6 v7 rest H.
  change (c0 :: C8 v1 :: C8 v2 :: C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest) with ([c0] ++ (C8 v1 :: C8 v2 :: C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest)) in H. apply rw_cells_app in H. destruct H as [H0 H].
  apply c8_blur1 in H.
  change (CB 8 (le8 v1) :: C8 v2 :: C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest) with ([CB 8 (le8 v1)] ++ (C8 v2 :: C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest)) in H. apply rw_cells_app in H. destruct H as [H1 H].
  apply c8_blur1 in H.
  change (CB 8 (le8 v2) :: C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest) with ([CB 8 (le8 v2)] ++ (C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest)) in H. apply rw_cells_app in H. destruct H as [H2 H].
  apply c8_blur1 in H.
  change (CB 8 (le8 v3) :: C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest) with ([CB 8 (le8 v3)] ++ (C8 v4 :: C8 v5 :: C8 v6 :: C8 v7 :: rest)) in H. apply rw_cells_app in H. destruct H as [H3 H].
  apply c8_blur1 in H.
  change (CB 8 (le8 v4) :: C8 v5 :: C8 v6 :: C8 v7 :: rest) with ([CB 8 (le8 v4)] ++ (C8 v5 :: C8 v6 :: C8 v7 :: rest)) in H. apply rw_cells_app in H. destruct H as [H4 H].
  apply c8_blur1 in H.
  change (CB 8 (le8 v5) :: C8 v6 :: C8 v7 :: rest) with ([CB 8 (le8 v5)] ++ (C8 v6 :: C8 v7 :: rest)) in H. apply rw_cells_app in H. destruct H as [H5 H].
  apply c8_blur1 in H.
  change (CB 8 (le8 v6) :: C8 v7 :: rest) with ([CB 8 (le8 v6)] ++ (C8 v7 :: rest)) in H. apply rw_cells_app in H. destruct H as [H6 H].
  apply c8_blur1 in H.
  change (c0 :: CB 8 (le8 v1) :: CB 8 (le8 v2) :: CB 8 (le8 v3) :: CB 8 (le8 v4) :: CB 8 (le8 v5) :: CB 8 (le8 v6) :: CB 8 (le8 v7) :: rest) with ([c0] ++ ([CB 8 (le8 v1)] ++ ([CB 8 (le8 v2)] ++ ([CB 8 (le8 v3)] ++ ([CB 8 (le8 v4)] ++ ([CB 8 (le8 v5)] ++ ([CB 8 (le8 v6)] ++ (CB 8 (le8 v7) :: rest)))))))).
  apply rw_cells_app; split; [exact H0|]. apply rw_cells_app; split; [exact H1|]. apply rw_cells_app; split; [exact H2|]. apply rw_cells_app; split; [exact H3|]. apply rw_cells_app; split; [exact H4|]. apply rw_cells_app; split; [exact H5|]. apply rw_cells_app; split; [exact H6|]. exact H.
Qed.

(* [comment removed for export] *)
Section WithRT2.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRYPTO_NEW_EX_DATA_A : Z := 0x1f9d68.

Definition new_ex_data_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (ad lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (ad <= a < ad + 16)) m m'
    /\ AHEAP Σ' OW LB m'
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ'
    /\ rw_cells ctasegs m' ad [C8 (wz 0); C8 (wz 0)] /\ exlock_free m' E.

(* [comment removed for export] *)
Definition NEW_EX_DATA_STACK_A : Z := 64 + CNED_FRAME + RT_STACK.
Definition FREE_EX_DATA_STACK_A : Z := 64 + CFED_FRAME + RT_STACK.

Lemma CRYPTO_new_ex_data_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (pb : bptr) (bio : Z) (c0 k0 : word) (ras : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + NEW_EX_DATA_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ap_statics_fixed m E -> exlock_free m E -> In (p_xl E, e_xl E, MUTEX_SIZE) OW ->
  In (pb, bio, BIO_SIZE) OW -> pb <> p_xl E -> rw_cells ctasegs m (bio + 112) [C8 c0; C8 k0] ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_NEW_EX_DATA_A (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a1 = wz bio -> a2 = wz (bio + 112) ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz CRYPTO_NEW_EX_DATA_A) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (new_ex_data_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E (bio + 112) lo m Σ') c
                /\ rt_live RT Σ' = rt_live RT Σ)      (* [comment removed for export] *).
Proof.
  intros until ras. intros HEAP ST CEIL LO SPT SP16 MI -> FLEN CRED SF HXL HXIN HBIN NBX HAD UW CTX -> -> ->.
  pose proof (dc_staticsA_of_fixed _ _ SF) as DC.
  destruct SF as (CS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HXLp & HXM & _).
  unfold NEW_EX_DATA_STACK_A, CNED_FRAME, RT_STACK, CRYPTO_NEW_EX_DATA_A, CRYPTO_EX_INDEX_BIO, BIO_SIZE, MUTEX_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pb, bio, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  assert (HXIN' : In (p_xl E, e_xl E, 40) (OW ++ LB)) by (apply in_or_app; left; exact HXIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HXIN') as (XB0 & _ & _ & XB3 & XB4). cbn [blk_addr blk_size fst snd] in XB0, XB3, XB4.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HXIN)) as ALX. pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.   (* [comment removed for export] *)
  pose proof (AH_disjoint_gen _ _ _ _ (pb, bio, 128) (p_xl E, e_xl E, 40) HEAP HBIN' HXIN' NBX) as DJX. cbn [blk_addr blk_size fst snd] in DJX.
  assert (XLO : obj_range (e_xl E) 40 lo) by (unfold obj_range, SEGTOP_A; unfold BnHeapA.ACEIL in *; clear - XB0 XB3 XB4 CEIL; lia).
  assert (AL4 : e_xl E mod 4 = 0) by (clear - ALX; Z.div_mod_to_equations; lia).
  unfold AP_DC_EXLOCK, AP_DC_EXMETH_BIO, AP_DC_INT, MallocRep.wz in HXLp, HXM. change (12208768 + 8) with 12208776 in HXLp. change (12208768 + 112) with 12208880 in HXM.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 8 zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  try clear junk. name_mem m0.
  match goal with H : munch _ m m0 |- _ => rename H into MU0 end. match goal with H : wmono ctasegs m m0 |- _ => rename H into WM0 end.
  assert (HEAP0 : AHEAP Σ OW LB m0).
  { eapply AH_frame; [exact HEAP| exact MU0| exact WM0|]. constructor; [left; cbn; unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - CEIL LO SPT; lia| constructor]. }
  assert (AG0 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m0).
  { eapply (stack_munch_agree Σ OW LB m m0 _ (bv_unsigned sp) HEAP MU0). constructor; [cbn [fst snd]; clear - CEIL LO; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  apply evt_done.
  eapply (cned_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP0 | exact ST | exact CEIL | unfold CNED_FRAME, RT_STACK; clear - LO; lia
    | unfold USTACK_TOP; clear - SPT; lia | exact SP16 | assumption | reflexivity | exact FLEN | exact CRED |].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j40 j48 j64 j72 jf24 jf32 jf112 jst
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold CNED_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  pose proof (@AH_ceil (push AR f 2) _ _ _ _ HEAP3) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3. cbn [ar_SP0 push amb] in D1, D2, D3.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 2) with 256 in G3, G5. unfold SEGTOP_A in G4.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0; lia).
  pose proof (FRESH _ HBIN') as OFFB. unfold off_fr in OFFB. cbn [blk_addr blk_size fst snd] in OFFB. change (fs_size 2) with 256 in OFFB.
  pose proof (FRESH _ HXIN') as OFFX. unfold off_fr in OFFX. cbn [blk_addr blk_size fst snd] in OFFX. change (fs_size 2) with 256 in OFFX.
  pose proof (agree_on_trans _ _ _ _ AG0 AGF) as AG3. pose proof (aclient_lib _ _ _ _ _ AG3) as AGL3. pose proof (aclient_lib _ _ _ _ _ AGF) as AGLF.
  (* [comment removed for export] *)
  first [ apply (rw_cells_agree _ _ _ _ _ AGF) in HAD | apply (rw_cells_agree _ _ _ _ _ AG3) in HAD ];
    [| intros a Ha; cbn in Ha; right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  unfold exlock_free in HXL.
  first [ apply (rw_cells_agree _ _ _ _ _ AGF) in HXL | apply (rw_cells_agree _ _ _ _ _ AG3) in HXL ];
    [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]].
  rename HXL into HXL3.
  pose proof (crypto_statics_agree' _ _ _ CS AGL3) as CS3. clear CS.
  pose proof (dc_staticsA_lib _ _ _ DC AGL3) as DC3. clear DC.
  first [ apply (ro_cells_libS OW m0 m3 _ _ 0xba46c0 0xba8ae0) in HXLp; [| exact AGLF| unfold LIBW_S; cbn; tauto| cbn; clear; lia| cbn; clear; lia]
        | apply (ro_cells_libS OW m m3 _ _ 0xba46c0 0xba8ae0) in HXLp; [| exact AGL3| unfold LIBW_S; cbn; tauto| cbn; clear; lia| cbn; clear; lia] ].
  first [ apply (ro_cells_libS OW m0 m3 _ _ 0xba46c0 0xba8ae0) in HXM; [| exact AGLF| unfold LIBW_S; cbn; tauto| cbn; clear; lia| cbn; clear; lia]
        | apply (ro_cells_libS OW m m3 _ _ 0xba46c0 0xba8ae0) in HXM; [| exact AGL3| unfold LIBW_S; cbn; tauto| cbn; clear; lia| cbn; clear; lia] ].
  unfold exlock_free, mutex_free_cells, zeros4, MallocRep.wz in HXL3. cbn [repeat] in HXL3.
  assert (HXL30 : frozen (rw_cells ctasegs m3 (e_xl E) mutex_free_cells)) by exact HXL3.
  (* [comment removed for export] *)
  ablock HEAP3 HBIN' ACCB OFFBS.
  assert (ACCG : acc ctasegs m3 12208768 328).
  { eapply (af_lib_acc_lit _ AF Σ1 m3 (0xba4a80, 328, 416)); [exact (@AH_art (push AR f 2) _ _ _ _ HEAP3)| vm_compute; reflexivity| cbn; clear; lia| cbn; clear; lia]. }
  destruct (@AH_shb (push AR f 2) _ _ _ _ HEAP3) as [SHB1 SHB2].
  assert (SHR : 2147450880 <= shad f /\ shad f + 32 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)) as DP.
    assert (DQ : f / 8 + 32 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 32); [apply Z.div_lt_upper_bound; [clear; lia| clear - G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]| clear - H; lia]).
    clear - DP DQ. lia. }
  assert (SHF : shad f + 32 <= lo) by (clear - SHR D2 CEIL; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia).
  ablock HEAP3 HXIN' ACCX OFFXS. clear ACCX.
  pose proof (munch_refl [(e_xl E, e_xl E + 40); (lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  assert (OFF : offshW [(e_xl E, e_xl E + 40); (lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. cbn [ar_SP0 push amb] in *. split; [revert OFFXS; unfold SHLO, SHHI; clear; intros; lia|].
    split; [clear - D2 CEIL; lia|]. split; [revert OFFBS; unfold SHLO, SHHI; clear; intros; lia| exact I]. }
  assert (STK : lo <= spa - 65552) by (clear - LO SPAL; lia).
  pose proof CEIL as CEILP. unfold BnHeapA.ACEIL in CEILP.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep.
  eapply evt_cut.
  { eapply (@get_ex_data_global_specA (push AR f 2)) with (lo := lo);
      [exact HEAP3| rewrite ESPA; exact ST3| exact MI3| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEILP| rewrite ESPA; clear - STK; lia
      | rewrite ESPA; unfold USTACK_TOP; clear - SPAH SPT; lia| reflexivity| exact DC3| reflexivity]. }
  clear DC3. post_call ctasegs m3. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST4 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI4 end.
  match goal with H : @BnHeapA.AHEAP _ Σ1 OW LB _ |- _ => rename H into HEAP4 end.
  (* [comment removed for export] *)
  unfold AP_DC_EXLOCK, AP_DC_INT. change (12208768 + 8) with 12208776.
  zstep. first [if_false| idtac].
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => pose proof (munch_refl [(lo, bv_unsigned sp + -16)]%Z mq) as MUq; pose proof (wmono_refl ctasegs mq) as WMq end.
  zstep. zstep. zstep.
  name_mem m4.
  assert (HEAP4' : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m4).
  { eapply AH_frame; [exact HEAP4| exact MUq| exact WMq|].
    constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; cbn [ar_SP0 push amb] in *; clear - CEIL SPT; lia| constructor]. }
  clear HEAP4 MUq WMq. rename HEAP4' into HEAP4.
  eapply evt_cut.
  { eapply (@get_and_lock_specA (push AR f 2)) with (lo := lo) (xl := e_xl E);
      [exact HEAP4| rewrite ESPA; exact ST4| exact MI4| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEILP| rewrite ESPA; clear - STK; lia
      | rewrite ESPA; unfold USTACK_TOP; clear - SPAH SPT; lia| exact HXLp| exact HXL3| exact XLO| exact AL4| reflexivity| reflexivity| reflexivity]. }
  clear HXL3 HEAP4. post_call ctasegs m4. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST5 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI5 end.
  match goal with H : rw_cells ctasegs _ (e_xl E) _ |- _ => rename H into HXL5 end.
  unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz in HXL5. cbn [repeat app] in HXL5.
  (* [comment removed for export] *)
  unfold AP_DC_EXMETH_BIO, AP_DC_INT. change (12208768 + 112) with 12208880.
  zstep. first [if_false| idtac].
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep.
  zstep.
  zstep.
  name_mem m5.
  match goal with H : stk ctasegs m5 lo spa |- _ => rename H into ST6 end. match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI6 end.
  eapply evt_cut.
  { eapply OPENSSL_sk_num_null_spec with (lo := lo); [rewrite ESPA; exact ST6| exact MI6| unfold SEGTOP_A; clear - CEILP D1 C1 CEIL; cbn [ar_SP0 push amb] in *; lia| rewrite ESPA; clear - STK; lia| reflexivity]. }
  post_call ctasegs m5. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST7 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI7 end.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. first [if_true| idtac].
  zstep.
  zstep.
  zstep.
  name_mem m6.
  match goal with H : stk ctasegs m6 lo spa |- _ => rename H into ST8 end. match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI8 end.
  eapply evt_cut.
  { eapply CRYPTO_THREAD_unlock_spec with (lo := lo) (X := e_xl E);
      [rewrite ESPA; exact ST8| exact MI8| unfold SEGTOP_A; clear - CEILP D1 C1 CEIL; cbn [ar_SP0 push amb] in *; lia| rewrite ESPA; clear - STK; lia
      | exact HXL5| exact XLO| exact AL4| reflexivity]. }
  clear HXL5. post_call ctasegs m6. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST9 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI9 end.
  match goal with H : rw_cells ctasegs _ (e_xl E) _ |- _ => rename H into HXL9 end.
  (* [comment removed for export] *)
  zstep. first [if_true| idtac]. zstep. first [if_true| idtac].
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?Ef, ?unsigned_lit in K by (clear - G1 G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia); clear - K G1; lia|]. clear K.
  zstep. zstep. zstep. zstep. zstep.
  name_mem m7.
  match goal with H : stk ctasegs m7 lo spa |- _ => rename H into ST10 end. match goal with H : mem_inv ctasegs m7 |- _ => rename H into MI10 end.
  match goal with H : munch _ m3 m7 |- _ => rename H into MU7 end. match goal with H : wmono ctasegs m3 m7 |- _ => rename H into WM7 end.
  (* [comment removed for export] *)
  assert (MU7' : munch [(lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z m3 m7).
  { eapply (munch_restore _ m3 m7 (e_xl E) mutex_free_cells); change (Z.of_nat (cells_size mutex_free_cells)) with 40.
    - exact MU7.
    - exact HXL30.
    - unfold mutex_free_cells, zeros4, MallocRep.wz. cbn [repeat]. exact HXL9.
    - unfold SEGTOP_A. clear - XB4. lia. }
  assert (HEAP7 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m7).
  { eapply AH_frame; [exact HEAP3| exact MU7'| exact WM7|].
    constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; cbn [ar_SP0 push amb] in *; clear - CEIL SPT; lia|].
    constructor; [right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear; lia]| constructor]. }
  assert (CS7 : crypto_statics m7).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU7')| | exact CS3].
    intros a Ha. cbn [outside fst snd]. revert Ha BB0 BB3 BB4 CEILP D1. unfold libw, LIBW_A, BnHeapA.ACEIL. cbn [rin_ivs fst snd ar_SP0 push amb]. clear. intros. lia. }
  apply evt_done. eapply cps_step_same.
  { eapply (@CRYPTO_free_null_cpsA (push AR f 2) UK BE) with (lo := lo);
      [exact HEAP7| rewrite ESPA; exact ST10| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEILP| rewrite ESPA; unfold CRYPTO_FREE_STACK, RT_STACK; clear - STK; lia
      | rewrite ESPA; unfold USTACK_TOP; clear - SPAH SPT; lia| rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia| exact MI10| reflexivity| exact CS7| reflexivity
      | (* [comment removed for export] *)
        rewrite ESPA; eapply (uw_call m m7 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [ exact UW
        | eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU0)|]; intros a Ha; cbn [outside fst snd]; clear - Ha; lia
          | eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha
          | eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU7')|]; intros a Ha; cbn [outside fst snd];
            clear - Ha BB0 BB3 BB4 CEIL CEILP LO; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]]
        | reflexivity | clear - SPAH; lia | uchk_open; clear - SP16; Z.div_mod_to_equations; lia | clear - SPT; unfold USTACK_TOP in *; lia
        | apply bv_unsigned_in_range
        | rewrite !Z_to_bv_bv_unsigned; cbn [app]; match goal with H : rw_cells ctasegs m7 (bv_unsigned sp + -16) _ |- _ => exact H end ]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_cned_free (uk_ctx_tail _ _ _ E_cned_tail CTX))]. }
  cbv beta. intros ms8 PO. unfold cfree_null_post in PO. rewrite ?ESPA in PO.
  destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F8 & fc8 & m8 & -> & MI11 & ST11 & HEAP8 & AG8).
  match goal with H : rw_cells ctasegs m7 spa _ |- _ => rename H into FRL7 end.
  match goal with H : rw_cells ctasegs m7 (bv_unsigned sp + -16) _ |- _ => rename H into FRH7 end.
  match goal with H : rw_cells ctasegs m7 (bio + 112) _ |- _ => rename H into HAD7 end.
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRL7; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; clear - Ha SPT SPAH GSZ; lia].
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRH7; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; clear - Ha SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG8) in HAD7; [| intros a Ha; cbn in Ha; right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG8) in HXL9; [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]].
  pose proof (munch_refl [] m8) as MU8. pose proof (wmono_refl ctasegs m8) as WM8.
  rewrite (ret_pc_even 2071648) by (clear; lia).
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  apply evt_done.
  (* [comment removed for export] *)
  lazymatch type of FRL7 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; C8 ?v5; C8 ?v6; C8 ?v7; ?c8; ?c9; ?c10; ?c11] =>
    pose proof (low3_blur m8 spa c0 c1 c2 c3 c4 v5 v6 v7 [c8; c9; c10; c11] FRL7) as FRL8
  end.   (* [comment removed for export] *)
  eapply (cned_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAP8 | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb | exact ST11 | exact CEIL | clear - STK; lia | unfold USTACK_TOP; clear - SPT; lia
    | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | exact MI11 | exact FRL8 | exact FRH7 | reflexivity |].
  intros Σ' m' HEAP' CR' EL' ST' MI' AG'.
  apply (rw_cells_agree _ _ _ _ _ AG') in HAD7; [| intros a Ha; cbn in Ha; right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG') in HXL9; [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]].
  apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold new_ex_data_postA, MallocRep.wz.
  do 16 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG3|]; intros a [Ha _]; exact Ha|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU7')|]|].
    { intros a [Ha Hx]. cbn [outside fst snd].
      assert (A1 : ~ (bv_unsigned sp - (bv_unsigned sp - lo) <= a < bv_unsigned sp)) by (eapply (acl_off_frame _ _ _ _ _ _ lo); [exact HEAP| exact INC| exact CEIL| clear; lia| exact Ha]).
      clear - A1 Hx. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG8|]; intros a [Ha _]; eapply acl_sub; [exact INC| | exact Ha]; clear - SPAH; lia|].
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. eapply acl_sub; [exact INC| | exact Ha]. clear - SPAH; lia. }
  split; [exact HEAP'|].
  split; [rewrite EL', EL1; reflexivity|]. split; [rewrite CR', CR1; clear; lia|].
  split; [exact HAD7|].
  unfold exlock_free, mutex_free_cells, zeros4, MallocRep.wz. cbn [repeat]. exact HXL9.
Qed.
End WithRT2.
