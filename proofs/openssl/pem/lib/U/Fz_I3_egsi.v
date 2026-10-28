(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_calloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_key. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_once Fz_T_atomic Fz_T_local Fz_T_sa Fz_T_master Fz_T_glx0 Fz_T_sk Fz_T_lock_new Fz_T_tevent Fz_T_mtl Fz_T_its Fz_I3_base Fz_G_OSSL_ERR_STATE_new.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

(* [comment removed for export] *)
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

Definition FZ_EGSI : Z := 0xe8140.
Definition EGSI_STACK : Z := 48 + ITS_STACK.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition EGSI_W : list (Z * Z) := [(0x351cd0, 0x351cd0 + 8); (RATP + -150, RATP + -149); (0x32de90, 0x32dea0); (RATP + -96, RATP + -88)].
Definition FZ_ERR_DEL_THREAD_STATE : Z := 0xe8940.

Definition egsi_res (psa pn : bptr) (SA P : Z) (pad : word) (oldcb : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pe ptn ph pg psk plk pd : bptr) (E N H G SK LK D : Z) (u' : byte) (top ne : word),
       v = Z_to_bv 64 E
    /\ LBall' = (ptn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: (pe, E, 904) :: LBall
    /\ L' = (ptn, 32) :: (pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: (pe, 904) :: L
    /\ rblock_range E 904 /\ rblock_range N 32 /\ rblock_range H 8 /\ rblock_range G 16 /\ rblock_range SK 56 /\ rblock_range LK 40 /\ rblock_range D 32
    /\ rw_cells usegs m' E [CB 904 (zeros 904)]
    /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P)) /\ rw_cells usegs m' P [C8 (Z_to_bv 64 E); CB 120 (zeros 120)]
    /\ rw_cells usegs m' 0x351cd0 [C8 (Z_to_bv 64 H)] /\ rw_cells usegs m' (RATP + -150) [C1 u']
    /\ rw_cells usegs m' 0x32de90 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)]
    /\ rw_cells usegs m' (RATP + -96) [C8 oldcb]
    /\ rw_cells usegs m' H [C8 (Z_to_bv 64 N)]
    /\ rw_cells usegs m' N [C8 z64; C8 z64; C8 (Z_to_bv 64 FZ_ERR_DEL_THREAD_STATE); C8 z64]
    /\ rw_cells usegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
    /\ rw_cells usegs m' SK (sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 0xe2d48) (Z_to_bv 64 0xe2d20) (Z_to_bv 64 0xe2d74))
    /\ rw_cells usegs m' LK (mutex_cells z64 z64)
    /\ rw_cells usegs m' D [C8 (Z_to_bv 64 H); CB 24 (zeros 24)]
    (* [comment removed for export] *)
    /\ bv_unsigned ne <> 0.

Definition egsi_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (pm psa pn : bptr) (MK SA P : Z) (pad top ne : word) (u : byte) (r0 g0 oldcb : word),
  (7 <= f)%nat -> croom L 6 1 (904 + 8192) ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - EGSI_STACK ->
  a0 = z64 ->
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells usegs m (IC_S + 96) [C8 (Z_to_bv 64 2)] ->
  rw_cells usegs m 0x32dea4 [C4 (Z_to_bv 64 2)] -> rw_cells usegs m 0x32dea8 [C4 (Z_to_bv 64 2)] ->
  rw_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] -> rw_cells usegs m (0x351cd0 + 8 * 2) [C8 (Z_to_bv 64 MK)] ->
  In (pm, MK, 72) LBall -> In (psa, SA, 32) LBall -> In (pn, P, 128) LBall ->
  rw_cells usegs m MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)] ->
  rw_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P)) -> bv_unsigned ne <= 1 -> rw_cells usegs m P [C8 z64; CB 120 (zeros 120)] ->
  rw_cells usegs m 0x31d4d0 [C4 z64; C4 (Z_to_bv 64 0xffffffff)] -> rw_cells usegs m 0x351cd0 [C8 z64] -> rw_cells usegs m (RATP + -150) [C1 u] ->
  rw_cells usegs m 0x32de90 [C4 z64; C4 r0; C8 g0] -> rw_cells usegs m (RATP + -96) [C8 oldcb] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_EGSI) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun q => q = psa \/ q = pn) EGSI_W 7 6 1 (904 + 8192)
           (egsi_res psa pn SA P pad oldcb LBall L)).

Theorem egsi_first_spec : OSSL_ERR_STATE_new_stmt -> T_its_first_stmt -> egsi_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ESN ITS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
         pm psa pn MK SA P pad top ne u r0 g0 oldcb
         Hf ROOM CST SLO -> STOP ONCE OD OC KC TSD SLOT INM INS INP BLKM HDR NEB PBLK DK SL0 USED TEV CBC.
  unfold OSSL_ERR_STATE_new_stmt in ESN. unfold T_its_first_stmt in ITS.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  subst tp.
  unfold EGSI_STACK, ITS_STACK, MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_EGSI, RATP, IC_S in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  change (3333664 + 8) with 3333672 in STOP. change (3333664 + 32) with 0x32de40 in ONCE. change (3333664 + 96) with 3333760 in OD.
  destruct ROOM as (RA & RB & RC).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INM) as (M0 & M16 & _ & M72 & MIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (S0 & S16 & _ & S32 & SIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INP) as (P0 & P16 & _ & P128 & PIMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [ND0 NDL0].
  assert (NEsn : psa <> pn). { intros E. subst psa. destruct (cown_block_eq _ _ _ _ _ _ ND0 INS INP) as [_ X]. discriminate X. }
  assert (NEms : pm <> psa). { intros E. subst pm. destruct (cown_block_eq _ _ _ _ _ _ ND0 INM INS) as [_ X]. discriminate X. }
  assert (NEmn : pm <> pn). { intros E. subst pm. destruct (cown_block_eq _ _ _ _ _ _ ND0 INM INP) as [_ X]. discriminate X. }
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INS INP NEsn) as APSP.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INM INS NEms) as APMS.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST INM INP NEmn) as APMP.
  (* [comment removed for export] *)
  pose proof BLKM as BLKM0.
  change [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)] with ([CB 24 (zeros 24)] ++ [C8 (Z_to_bv 64 SA)] ++ [CB 40 (zeros 40)]) in BLKM0.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in BLKM0. destruct BLKM0 as [_ BLKM0]. apply (proj1 (rw_cells_app usegs m _ _ _)) in BLKM0. destruct BLKM0 as [MK24 _].
  assert (MK24r : ro_cells usegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)]) by exact (proj1 MK24). clear MK24.
  change [C8 z64; CB 120 (zeros 120)] with ([C8 z64] ++ [CB 120 (zeros 120)]) in PBLK.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in PBLK. destruct PBLK as [PV PJ]. cbn [cells_size csize Nat.add] in PJ. change (Z.of_nat 8) with 8 in PJ.
  unfold sa_hdr in HDR.
  hide NEsn. hide NEms. hide NEmn. hide M16. hide S16. hide P16.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (SA + 8, SA + 24); (P, P + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUp.
  pose proof (conj STOP (conj ONCE (conj OD (conj OC (conj KC (conj TSD (conj SLOT (conj BLKM (conj HDR (conj PV (conj PJ (conj MK24r (conj DK (conj SL0 (conj USED (conj TEV CBC)))))))))))))))) as CELLS.
  clear STOP ONCE OD OC KC TSD SLOT BLKM HDR PV PJ MK24r DK SL0 USED TEV CBC.
  (* [comment removed for export] *)
  cprefix. step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (TR : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= 3485696 \/ (0 < A /\ A + Z.of_nat (cells_size cs) <= alloc_ceiling)) -> rw_cells usegs mm A cs)
      by (intros A cs H HB; eapply rw_cells_transport; [exact H| exact MUp| exact WM| cbn [disjoint_from]; lia]);
    assert (TRr : forall A cs, ro_cells usegs m A cs -> (0 < A /\ A + Z.of_nat (cells_size cs) <= alloc_ceiling) -> ro_cells usegs mm A cs)
      by (intros A cs H HB; eapply ro_cells_transport; [exact H| exact MUp| cbn [disjoint_from]; lia]) end.
  destruct CELLS as (STOP & ONCE & OD & OC & KC & TSD & SLOT & BLKM & HDR & PV & PJ & MK24r & DK & SL0 & USED & TEV & CBC).
  apply TR in STOP; [| cbn; lia]. apply TR in ONCE; [| cbn; lia]. apply TR in OD; [| cbn; lia]. apply TR in OC; [| cbn; lia]. apply TR in KC; [| cbn; lia].
  apply TR in TSD; [| cbn; lia]. apply TR in SLOT; [| cbn; lia]. apply TR in BLKM; [| cbn; lia]. apply TR in HDR; [| cbn; lia]. apply TR in PV; [| cbn; lia].
  apply TR in PJ; [| cbn; lia]. apply TRr in MK24r; [| cbn; lia]. apply TR in DK; [| cbn; lia]. apply TR in SL0; [| cbn; lia]. apply TR in USED; [| cbn; lia].
  apply TR in TEV; [| cbn; lia]. apply TR in CBC; [| cbn; lia].
  clear TR TRr MUp.
  step. step. step. th_if_lit. step. do 2 step. step.
  calle (eapply init_crypto_base_spec with (lo := lo) (od := Z_to_bv 64 2)); try (unfold IC_BASE_STACK; lia).
  step. th_if_lit. do 2 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  assert (OCr : ro_cells usegs ma 3333796 [C4 (Z_to_bv 64 2)]) by (lazymatch goal with H : rw_cells usegs ma 3333796 _ |- _ => exact (proj1 H) end).
  assert (KCr : ro_cells usegs ma 0x32dea8 [C4 (Z_to_bv 64 2)]) by (lazymatch goal with H : rw_cells usegs ma 0x32dea8 _ |- _ => exact (proj1 H) end).
  assert (TSDr : ro_cells usegs ma (3344744 + -88) [C8 (Z_to_bv 64 3480784)]) by (lazymatch goal with H : rw_cells usegs ma (3344744 + -88) _ |- _ => exact (proj1 H) end).
  assert (SLOTr : ro_cells usegs ma (3480784 + 8 * 2) [C8 (Z_to_bv 64 MK)]) by (lazymatch goal with H : rw_cells usegs ma (3480784 + 8 * 2) _ |- _ => exact (proj1 H) end).
  assert (HDRr : ro_cells usegs ma SA [C4 (Z_to_bv 64 1); C4 pad; C8 top; C8 ne; C8 (Z_to_bv 64 P)]) by (lazymatch goal with H : rw_cells usegs ma SA _ |- _ => exact (proj1 H) end).
  assert (PVr : ro_cells usegs ma P [C8 z64]) by (lazymatch goal with H : rw_cells usegs ma P [C8 _] |- _ => exact (proj1 H) end).
  assert (MK8 : MK mod 8 = 0). { clear - M16 M0. unfold hideP in M16. apply Z.mod_divide in M16; [| lia]. apply Z.mod_divide; [lia|]. destruct M16 as [q Hq]. exists (2 * q). lia. }
  assert (SA8 : SA mod 8 = 0). { clear - S16 S0. unfold hideP in S16. apply Z.mod_divide in S16; [| lia]. apply Z.mod_divide; [lia|]. destruct S16 as [q Hq]. exists (2 * q). lia. }
  assert (P8 : P mod 8 = 0). { clear - P16 P0. unfold hideP in P16. apply Z.mod_divide in P16; [| lia]. apply Z.mod_divide; [lia|]. destruct P16 as [q Hq]. exists (2 * q). lia. }
  pose proof T_get_local_ex_zero_proof as GLX. unfold T_get_local_ex_zero_stmt, sa_hdr in GLX.
  tcall (GLX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3480784 2 3 MK SA P pad top ne).
  all: try first [eassumption | reflexivity | lia].
  clear GLX OCr KCr TSDr SLOTr HDRr PVr. cbv beta delta [mkR]. try th_ret_lit.
  step. step. th_if_lit. step. step. th_if_lit. do 3 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mb end.
  assert (OCr : ro_cells usegs mb 3333796 [C4 (Z_to_bv 64 2)]) by (lazymatch goal with H : rw_cells usegs mb 3333796 _ |- _ => exact (proj1 H) end).
  assert (KCr : ro_cells usegs mb 0x32dea8 [C4 (Z_to_bv 64 2)]) by (lazymatch goal with H : rw_cells usegs mb 0x32dea8 _ |- _ => exact (proj1 H) end).
  assert (TSDr : ro_cells usegs mb (3344744 + -88) [C8 (Z_to_bv 64 3480784)]) by (lazymatch goal with H : rw_cells usegs mb (3344744 + -88) _ |- _ => exact (proj1 H) end).
  assert (SLOTr : ro_cells usegs mb (3480784 + 8 * 2) [C8 (Z_to_bv 64 MK)]) by (lazymatch goal with H : rw_cells usegs mb (3480784 + 8 * 2) _ |- _ => exact (proj1 H) end).
  pose proof T_set_local_ex_steady_proof as SLS. unfold T_set_local_ex_steady_stmt, sa_hdr in SLS.
  tcall (SLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3480784 2 3 MK SA P pad top ne z64).
  all: try first [eassumption | reflexivity | lia].
  clear OCr KCr TSDr SLOTr MK24r. cbv beta delta [mkR]. try th_ret_lit.
  try (lazymatch goal with H : bv_unsigned _ = Z.max _ _ |- _ => clear H end).
  lazymatch goal with H : rw_cells usegs _ SA [_; _; C8 ?t; C8 ?n; _] |- _ =>
    assert (NE1F : bv_unsigned n = bv_unsigned ne + 1)
      by (lazymatch n with context [sa_delta ?a ?b] => let v := eval vm_compute in (sa_delta a b) in change (sa_delta a b) with v end;
          rewrite unsigned_lit by (clear - NEB; pose proof (bv_unsigned_in_range _ ne); lia); reflexivity);
    set (top1 := t) in *; set (ne1 := n) in *; clearbody top1 ne1 end.
  (* [comment removed for export] *)
  step. th_if_lit. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mc end.
  lazymatch goal with H : stk _ mc _ _ |- _ => rename H into STc end.
  lazymatch goal with H : mem_inv _ mc |- _ => rename H into MIc end.
  assert (CSTc : cstate s LBall LB L mc (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m mc _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIc| | lia| lia| | rewrite unsigned_lit by lia; exact STc| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (psa, SA, 32)); [exact INS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pn, P, 128)); [exact INP| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRc : cframe (fun q => q = psa \/ q = pn) EGSI_W (bv_unsigned sp) s LBall L m s LBall L mc).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (psa, SA, 32)); [exact INS| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..]. intros b0 _ NT E. apply NT. left. exact E. }
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (pn, P, 128)); [exact INP| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..]. intros b0 _ NT E. apply NT. right. exact E. }
    apply Forall_nil. }
  destruct (wB_big 904 ltac:(unfold TIER_A_MAX; lia)) as (WE1 & WE2 & WE3).
  eapply climpl_seq.
  { eapply ESN with (lo := lo) (B := Bd); [lia| rewrite WE1, WE2, WE3; unfold croom; lia| exact CSTc| rewrite unsigned_lit by lia; unfold OSSL_ERR_STATE_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pe & E & -> & -> & -> & RNGE & EBLK)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). rewrite WE1, WE2, WE3 in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  lazymatch goal with FRh : rw_cells _ mc (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  lazymatch goal with H : rw_cells _ mc 3333672 _ |- _ => cst_static CFR1 H STOP1 end.
  lazymatch goal with H : rw_cells _ mc 3333760 _ |- _ => cst_static CFR1 H OD1 end.
  lazymatch goal with H : rw_cells _ mc 3333796 _ |- _ => cst_static CFR1 H OC1 end.
  lazymatch goal with H : rw_cells _ mc 0x32dea8 _ |- _ => cst_static CFR1 H KC1 end.
  lazymatch goal with H : rw_cells _ mc (3344744 + -88) _ |- _ => cst_static CFR1 H TSD1 end.
  lazymatch goal with H : rw_cells _ mc (3480784 + 8 * 2) _ |- _ => cst_static CFR1 H SLOT1 end.
  lazymatch goal with H : rw_cells _ mc 3265744 _ |- _ => cst_static CFR1 H DK1 end.
  lazymatch goal with H : rw_cells _ mc 3480784 _ |- _ => cst_static CFR1 H SL01 end.
  lazymatch goal with H : rw_cells _ mc (3344744 + -150) _ |- _ => cst_static CFR1 H USED1 end.
  lazymatch goal with H : rw_cells _ mc 3333776 _ |- _ => cst_static CFR1 H TEV1 end.
  lazymatch goal with H : rw_cells _ mc (3344744 + -96) _ |- _ => cst_static CFR1 H CBC1 end.
  lazymatch goal with H : rw_cells _ mc MK _ |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pm, MK, 72) CFR1 H INM (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                  ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add length repeat]; lia)) as BLKM1 end.
  lazymatch goal with H : rw_cells _ mc SA _ |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (psa, SA, 32) CFR1 H INS (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                  ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HDR1 end.
  lazymatch goal with H : rw_cells _ mc P [C8 _] |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pn, P, 128) CFR1 H INP (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                  ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as PV1 end.
  lazymatch goal with H : rw_cells _ mc (P + 8) _ |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pn, P, 128) CFR1 H INP (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                  ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add length repeat]; lia)) as PJ1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNGE as (E0 & _ & _ & E904 & EIMG).
  assert (INE1 : In (pe, E, 904) ((pe, E, 904) :: LBall)) by (left; reflexivity).
  assert (INS1 : In (psa, SA, 32) ((pe, E, 904) :: LBall)) by (right; exact INS).
  assert (INP1 : In (pn, P, 128) ((pe, E, 904) :: LBall)) by (right; exact INP).
  pose proof (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INS) as NEse.
  pose proof (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INP) as NEpe.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INE1 INS1 (fun E1 => NEse (eq_sym E1))) as APES.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INE1 INP1 (fun E1 => NEpe (eq_sym E1))) as APEP.
  hide NEse. hide NEpe.
  assert (FRM0 : cframe (fun q => q = psa \/ q = pn) EGSI_W (bv_unsigned sp) s LBall L m st1 ((pe, E, 904) :: LBall) ((pe, 904) :: L) m1).
  { eapply cframe_call; [exact FRc| exact FRM1| lia| intros a X; destruct X| intros q _ _ X; destruct X]. }
  clear FRc CSTc CFR1 FRM1.
  destruct (wA_small 8 ltac:(unfold TIER_A_MAX; lia)) as (W8a & W8b & W8c). destruct (wA_small 16 ltac:(unfold TIER_A_MAX; lia)) as (W16a & W16b & W16c).
  destruct (wA_small 56 ltac:(unfold TIER_A_MAX; lia)) as (W56a & W56b & W56c). destruct (wA_small 40 ltac:(unfold TIER_A_MAX; lia)) as (W40a & W40b & W40c).
  destruct (wA_small 32 ltac:(unfold TIER_A_MAX; lia)) as (W32a & W32b & W32c).
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. step. do 2 step. step. chere.
  eapply climpl_seq.
  { eapply ITS with (lo := lo) (B := Bd) (T := 3480784) (k := 0);
      [lia| rewrite W8a, W8b, W8c, W16a, W16b, W16c, W56a, W56b, W56c, W40a, W40b, W40c, W32a, W32b, W32c; unfold croom, cgrow in *; lia| exact CST1
      | rewrite unsigned_lit by lia; unfold ITS_STACK, MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia
      | exact DK1| lia| rewrite unsigned_lit by lia; exact TSD1| exact SL01| lia| lia| lia| rewrite unsigned_lit by lia; exact USED1| exact TEV1| rewrite unsigned_lit by lia; exact CBC1]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & IRES).
  destruct IRES as (ptn & N & ph & H & pg & G & psk & SK & plk & LK & pd & D & u' & -> & -> & -> & RN & RH & RG & RSK & RLK & RD & SL02 & USED2 & TEV2 & CBC2 & HC & NC & GC & SKC & LKC & DC).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia). repeat (rewrite unsigned_lit in USED2 by lia). repeat (rewrite unsigned_lit in CBC2 by lia). unfold mtl_W in FRM2. repeat (rewrite unsigned_lit in FRM2 by lia).
  rewrite W8a, W8b, W8c, W16a, W16b, W16c, W56a, W56b, W56c, W40a, W40b, W40c, W32a, W32b, W32c in GR2.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  cst_static CFR2 STOP1 STOP2. cst_static CFR2 OD1 OD2. cst_static CFR2 OC1 OC2. cst_static CFR2 KC1 KC2. cst_static CFR2 TSD1 TSD2. cst_static CFR2 SLOT1 SLOT2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pm, MK, 72) CFR2 BLKM1 (or_intror INM) (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add length repeat]; lia)) as BLKM2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (psa, SA, 32) CFR2 HDR1 INS1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HDR2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pn, P, 128) CFR2 PV1 INP1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as PV2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pn, P, 128) CFR2 PJ1 INP1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add length repeat]; lia)) as PJ2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pe, E, 904) CFR2 EBLK INE1 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add length repeat]; lia)) as EBLK2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  set (LB3 := (ptn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: (pe, E, 904) :: LBall) in *.
  assert (INS3 : In (psa, SA, 32) LB3) by (subst LB3; do 7 right; exact INS).
  assert (INP3 : In (pn, P, 128) LB3) by (subst LB3; do 7 right; exact INP).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND3 _].
  (* [comment removed for export] *)
  pose proof BLKM2 as MK24. clear BLKM1.
  change [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)] with ([CB 24 (zeros 24)] ++ [C8 (Z_to_bv 64 SA)] ++ [CB 40 (zeros 40)]) in MK24.
  apply (proj1 (rw_cells_app usegs m2 _ _ _)) in MK24. destruct MK24 as [_ MK24]. apply (proj1 (rw_cells_app usegs m2 _ _ _)) in MK24. destruct MK24 as [MK24 _].
  assert (MK24r : ro_cells usegs m2 (MK + 8 * 3) [C8 (Z_to_bv 64 SA)]) by exact (proj1 MK24). clear MK24.
  pose proof (conj HC (conj NC (conj GC (conj SKC (conj LKC (conj DC (conj EBLK2 BLKM2))))))) as BLOCKS. clear HC NC GC SKC LKC DC EBLK2 BLKM2.
  assert (OCr : ro_cells usegs m2 3333796 [C4 (Z_to_bv 64 2)]) by exact (proj1 OC2).
  assert (KCr : ro_cells usegs m2 0x32dea8 [C4 (Z_to_bv 64 2)]) by exact (proj1 KC2).
  assert (TSDr : ro_cells usegs m2 (3344744 + -88) [C8 (Z_to_bv 64 3480784)]) by exact (proj1 TSD2).
  assert (SLOTr : ro_cells usegs m2 (3480784 + 8 * 2) [C8 (Z_to_bv 64 MK)]) by exact (proj1 SLOT2).
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp - 48); (SA + 8, SA + 24); (P, P + 8)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  hide RN. hide RH. hide RG. hide RSK. hide RLK. hide RD. hide RNGE. hide EIMG. hide APES. hide APEP. hide E0. hide E904.
  hide FU1. hide FU2. hide GR1. hide GR2. hide Hf. clear W8a W8b W8c W16a W16b W16c W56a W56b W56c W40a W40b W40c W32a W32b W32c WE1 WE2 WE3 RA RB RC.
  (* [comment removed for export] *)
  cprefix. step. th_if_lit. do 3 step. step.
  tcall (SLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3480784 2 3 MK SA P pad top1 ne1 (Z_to_bv 64 (-1))).
  all: try first [eassumption | reflexivity | lia].
  clear OCr KCr TSDr SLOTr SLS. cbv beta delta [mkR]. try th_ret_lit.
  try (lazymatch goal with H : bv_unsigned _ = Z.max _ _ |- _ => clear H end).
  lazymatch goal with H : rw_cells usegs _ SA [_; _; C8 ?t; C8 ?n; _] |- _ =>
    assert (NE2F : bv_unsigned n <> 0)
      by (pose proof E0 as E0'; pose proof E904 as E904'; unfold hideP in E0', E904'; unfold sa_delta;
          rewrite (bv_eqb_Z (Z_to_bv 64 E) (Z_to_bv 64 0));
          rewrite (unsigned_lit E) by (clear - E0' E904' CEIL_RANGE__; try unfold ceil_window in CEIL_RANGE__; lia); rewrite (unsigned_lit 0) by (clear; lia);
          replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; clear - E0'; lia); cbv iota;
          match goal with |- context [bv_eqb ?a ?b] => let v := eval vm_compute in (bv_eqb a b) in change (bv_eqb a b) with v end; cbv iota;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; clear - NE1F NEB; pose proof (bv_unsigned_in_range _ ne); lia);
    set (top2 := t) in *; set (ne2 := n) in *; clearbody top2 ne2 end.
  step. th_if_lit. do 2 step. step.
  calle (eapply init_crypto_fast_spec with (lo := lo) (od := Z_to_bv 64 2) (opts := 2)); try (unfold IC_BASE_STACK; lia).
  step. th_if_lit. step. do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into ST3 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -48) _ |- _ => rename H into FR3 end.
  release_frame FR3 ST3 (bv_unsigned sp). step. step.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  lazymatch goal with H : rw_cells usegs mf SA _ |- _ => rename H into HDRf end.
  lazymatch goal with H : rw_cells usegs mf P [C8 _] |- _ => rename H into PVf end.
  lazymatch goal with H : rw_cells usegs mf (P + 8) _ |- _ => rename H into PJf end.
  unfold hideP in *.
  chere. apply climpl_done.
  exists (Z_to_bv 64 E), mf, LB3.
  split; [unfold cret; do 14 eexists; reflexivity|].
  split; [clear - Hf FU1 FU2; lia|].
  split; [pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) as GR; clear - GR; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m2 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (psa, SA, 32)); [exact INS3| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pn, P, 128)); [exact INP3| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SIMG PIMG S0 P0 GLO SLO SPR LO; lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRM0| exact FRM2| lia| | intros q _ _ X; destruct X]| exact MU2| exact WM2| exact HP2| lia|].
    - intros a X. unfold EGSI_W, RATP. cbn [rin_ivs fst snd] in X |- *. lia.
    - apply Forall_cons; [apply cseg_ok_stack; lia|].
      apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (psa, SA, 32)); [exact INS3| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..]. intros b0 _ NT E1. apply NT. left. exact E1. }
      apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (pn, P, 128)); [exact INP3| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..]. intros b0 _ NT E1. apply NT. right. exact E1. }
      apply Forall_nil. }
  (* [comment removed for export] *)
  assert (TRB : forall (q : bptr) A n cs, In (q, A, n) LB3 -> q <> psa -> q <> pn -> rw_cells usegs m2 A cs -> Z.of_nat (cells_size cs) <= n -> rw_cells usegs mf A cs).
  { intros q A n cs Hq N1 N2 HA Hsz. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST2 Hq) as (Q0 & _ & _ & QC & _).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 Hq INS3 N1) as D1.
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 Hq INP3 N2) as D2.
    eapply rw_cells_transport; [exact HA| exact MU2| exact WM2|]. cbn [disjoint_from]. clear - Q0 QC D1 D2 Hsz LO SLO SPR. lia. }
  assert (NQ : forall b, In b [(ptn, N, 32); (pd, D, 32); (plk, LK, 40); (psk, SK, 56); (pg, G, 16); (ph, H, 8); (pe, E, 904)] -> blk_id b <> psa /\ blk_id b <> pn).
  { intros b Hb. pose proof (t_nodup_prefix blk_id [(ptn, N, 32); (pd, D, 32); (plk, LK, 40); (psk, SK, 56); (pg, G, 16); (ph, H, 8); (pe, E, 904)] LBall b ND3 Hb) as NI.
    split; intros E1; apply NI; rewrite E1; [change psa with (blk_id (psa, SA, 32))| change pn with (blk_id (pn, P, 128))]; apply in_map; assumption. }
  destruct BLOCKS as (HC & NC & GC & SKC & LKC & DC & EBLK2 & BLKM2).
  unfold egsi_res, sa_hdr, RATP, FZ_ERR_DEL_THREAD_STATE. exists pe, ptn, ph, pg, psk, plk, pd, E, N, H, G, SK, LK, D, u', top2, ne2.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RNGE|]. split; [exact RN|]. split; [exact RH|]. split; [exact RG|]. split; [exact RSK|]. split; [exact RLK|]. split; [exact RD|].
  assert (INQ : forall b, In b [(ptn, N, 32); (pd, D, 32); (plk, LK, 40); (psk, SK, 56); (pg, G, 16); (ph, H, 8); (pe, E, 904)] -> In b LB3).
  { intros b Hb. subst LB3. cbn [In] in Hb |- *. clear - Hb. intuition. }
  split. { eapply (TRB pe E 904); [apply INQ; cbn [In]; do 6 right; left; reflexivity| | | exact EBLK2| cbn; lia]; apply (NQ (pe, E, 904)); cbn [In]; do 6 right; left; reflexivity. }
  split; [exact HDRf|].
  split. { change [C8 (Z_to_bv 64 E); CB 120 (zeros 120)] with ([C8 (Z_to_bv 64 E)] ++ [CB 120 (zeros 120)]). apply rw_cells_app. split; [exact PVf|].
           cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8. exact PJf. }
  repeat match goal with |- _ /\ _ => split end; try eassumption.
  - eapply (TRB ph H 8); [apply INQ; cbn [In]; do 5 right; left; reflexivity| | | exact HC| cbn; lia]; apply (NQ (ph, H, 8)); cbn [In]; do 5 right; left; reflexivity.
  - eapply (TRB ptn N 32); [apply INQ; cbn [In]; left; reflexivity| | | exact NC| cbn; lia]; apply (NQ (ptn, N, 32)); cbn [In]; left; reflexivity.
  - eapply (TRB pg G 16); [apply INQ; cbn [In]; do 4 right; left; reflexivity| | | exact GC| cbn; lia]; apply (NQ (pg, G, 16)); cbn [In]; do 4 right; left; reflexivity.
  - eapply (TRB psk SK 56); [apply INQ; cbn [In]; do 3 right; left; reflexivity| | | exact SKC| unfold sk_cells; cbn; lia]; apply (NQ (psk, SK, 56)); cbn [In]; do 3 right; left; reflexivity.
  - eapply (TRB plk LK 40); [apply INQ; cbn [In]; do 2 right; left; reflexivity| | | exact LKC| unfold mutex_cells; cbn; lia]; apply (NQ (plk, LK, 40)); cbn [In]; do 2 right; left; reflexivity.
  - eapply (TRB pd D 32); [apply INQ; cbn [In]; right; left; reflexivity| | | exact DC| cbn; lia]; apply (NQ (pd, D, 32)); cbn [In]; right; left; reflexivity.
Qed.
End WithCeiling0.
