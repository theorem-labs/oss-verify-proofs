(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_M_free.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_key. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_sa Fz_T_sk Fz_T_lock_new Fz_T_tevent Fz_T_mtl Fz_T_its Fz_I3_base Fz_G_OSSL_ERR_STATE_new Fz_I3_egsi Fz_I3_eciter Fz_I3_eciter2 Fz_I3_eciter3.
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

Definition FZ_ERR_CLEAR : Z := 0xe80c8.
Definition ECL_STACK : Z := 64 + EGSI_STACK.

(* [comment removed for export] *)
Definition es_clean : list cell :=
  repeat (C4 z64) 16 ++ repeat (C4 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C4 z64) 16 ++ repeat (C8 z64) 16
  ++ repeat (C4 ECL_LNW) 16 ++ repeat (C8 z64) 16 ++ [C8 z64].

Definition eclear_res (psa pn : bptr) (SA P : Z) (pad : word) (oldcb : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun _ LBall' L' m' => exists (pe ptn ph pg psk plk pd : bptr) (E N H G SK LK D : Z) (u' : byte) (top ne : word),
       LBall' = (ptn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: (pe, E, 904) :: LBall
    /\ L' = (ptn, 32) :: (pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: (pe, 904) :: L
    /\ rblock_range E 904 /\ rblock_range N 32 /\ rblock_range H 8 /\ rblock_range G 16 /\ rblock_range SK 56 /\ rblock_range LK 40 /\ rblock_range D 32
    /\ rw_cells usegs m' E es_clean
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

Definition eclear_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (pm psa pn : bptr) (MK SA P : Z) (pad top ne : word) (u : byte) (r0 g0 oldcb : word),
  (7 <= f)%nat -> croom L 6 1 (904 + 8192) ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - ECL_STACK ->
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells usegs m (IC_S + 96) [C8 (Z_to_bv 64 2)] ->
  rw_cells usegs m 0x32dea4 [C4 (Z_to_bv 64 2)] -> rw_cells usegs m 0x32dea8 [C4 (Z_to_bv 64 2)] ->
  rw_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] -> rw_cells usegs m (0x351cd0 + 8 * 2) [C8 (Z_to_bv 64 MK)] ->
  In (pm, MK, 72) LBall -> In (psa, SA, 32) LBall -> In (pn, P, 128) LBall ->
  rw_cells usegs m MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)] ->
  rw_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P)) -> bv_unsigned ne <= 1 -> rw_cells usegs m P [C8 z64; CB 120 (zeros 120)] ->
  rw_cells usegs m 0x31d4d0 [C4 z64; C4 (Z_to_bv 64 0xffffffff)] -> rw_cells usegs m 0x351cd0 [C8 z64] -> rw_cells usegs m (RATP + -150) [C1 u] ->
  rw_cells usegs m 0x32de90 [C4 z64; C4 r0; C8 g0] -> rw_cells usegs m (RATP + -96) [C8 oldcb] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_ERR_CLEAR) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun q => q = psa \/ q = pn) EGSI_W 7 6 1 (904 + 8192)
           (eclear_res psa pn SA P pad oldcb LBall L)).

Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.
(* [comment removed for export] *)
Ltac ecl_norm :=
  cbv beta delta [mkR]; cbn [Nat.eqb]; unfold FZ_ECL_LOOP, FZ_ECL_DONE;
  repeat match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    match R with context [Z_to_bv 64 (_ + (Z.add ?a ?b))] => let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v end end.

Theorem eclear_first_spec : egsi_first_stmt -> eclear_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros EGSI ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
         pm psa pn MK SA P pad top ne u r0 g0 oldcb
         Hf ROOM CST SLO STOP ONCE OD OC KC TSD SLOT INM INS INP BLKM HDR NEB PBLK DK SL0 USED TEV CBC.
  unfold egsi_first_stmt in EGSI.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  subst tp.
  unfold ECL_STACK, EGSI_STACK, ITS_STACK, MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_ERR_CLEAR, RATP, IC_S in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INM) as (M0 & _ & _ & M72 & MIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (S0 & _ & _ & S32 & SIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INP) as (P0 & _ & _ & P128 & PIMG).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (conj STOP (conj ONCE (conj OD (conj OC (conj KC (conj TSD (conj SLOT (conj BLKM (conj HDR (conj PBLK (conj DK (conj SL0 (conj USED (conj TEV CBC)))))))))))))) as CELLS.
  clear STOP ONCE OD OC KC TSD SLOT BLKM HDR PBLK DK SL0 USED TEV CBC.
  (* [comment removed for export] *)
  cprefix. step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (TR : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= 3485696 \/ (0 < A /\ A + Z.of_nat (cells_size cs) <= alloc_ceiling)) -> rw_cells usegs mm A cs)
      by (intros A cs H HB; eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from]; lia]) end.
  destruct CELLS as (STOP & ONCE & OD & OC & KC & TSD & SLOT & BLKM & HDR & PBLK & DK & SL0 & USED & TEV & CBC).
  apply TR in STOP; [| cbn; lia]. apply TR in ONCE; [| cbn; lia]. apply TR in OD; [| cbn; lia]. apply TR in OC; [| cbn; lia]. apply TR in KC; [| cbn; lia].
  apply TR in TSD; [| cbn; lia]. apply TR in SLOT; [| cbn; lia]. apply TR in BLKM; [| cbn; lia]. apply TR in HDR; [| unfold sa_hdr; cbn; lia]. apply TR in PBLK; [| cbn; lia].
  apply TR in DK; [| cbn; lia]. apply TR in SL0; [| cbn; lia]. apply TR in USED; [| cbn; lia]. apply TR in TEV; [| cbn; lia]. apply TR in CBC; [| cbn; lia].
  clear TR.
  step. step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa0 : cframe (fun q => q = psa \/ q = pn) EGSI_W (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply EGSI with (lo := lo) (Bd := Bd) (pm := pm); [lia| exact ROOM| exact CSTa| rewrite unsigned_lit by lia; unfold EGSI_STACK, ITS_STACK, MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity
      | exact STOP| exact ONCE| exact OD| exact OC| exact KC| exact TSD| exact SLOT| exact INM| exact INS| exact INP| exact BLKM| exact HDR| exact NEB| exact PBLK| exact DK| exact SL0| exact USED| exact TEV| exact CBC]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & ERES).
  destruct ERES as (pe & ptn & ph & pg & psk & plk & pd & E & N & H & G & SK & LK & D & u' & top1 & ne1 & -> & -> & -> & RNGE & RN & RH & RG & RSK & RLK & RD
                    & EBLK & HDR1 & PBLK1 & SL01 & USED1 & TEV1 & CBC1 & HC & NC & GC & SKC & LKC & DC & NEF).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). unfold EGSI_W, RATP in FRM1. repeat (rewrite unsigned_lit in FRM1 by lia). unfold RATP in USED1, CBC1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & LXS1 & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof LXS1 as (_ & _ & _ & _ & GOTF & IMPL & _). change (LX_GOT_FLAGS + 16) with 0x31c088 in GOTF. change (LX_STORAGE_FN + 16) with 0x31d4f0 in IMPL.
  pose proof RNGE as (E0 & E16 & _ & E904 & EIMG).
  assert (E8 : E mod 8 = 0). { clear - E16. apply Z.mod_divide in E16; [| lia]. apply Z.mod_divide; [lia|]. destruct E16 as [q Hq]. exists (2 * q). lia. }
  set (LB1 := (ptn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: (pe, E, 904) :: LBall) in *.
  assert (INE1 : In (pe, E, 904) LB1) by (subst LB1; do 6 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  (* [comment removed for export] *)
  pose proof (conj HDR1 (conj PBLK1 (conj SL01 (conj USED1 (conj TEV1 (conj CBC1 (conj HC (conj NC (conj GC (conj SKC (conj LKC DC))))))))))) as KEEP.
  clear HDR1 PBLK1 SL01 USED1 TEV1 CBC1 HC NC GC SKC LKC DC STOP ONCE OD OC KC TSD SLOT BLKM HDR PBLK DK SL0 USED TEV CBC CSTa CFR1.
  hide RNGE. hide RN. hide RH. hide RG. hide RSK. hide RLK. hide RD. hide MIMG. hide SIMG. hide PIMG. hide M0. hide M72. hide S0. hide S32. hide P0. hide P128. hide FU1. hide GR1. hide Hf. clear ROOM.
  change (Z.to_nat 904) with 904%nat in EBLK.
  apply (th_cells_congr usegs m1 E _ (es_pre 0 (repeat z64 16))) in EBLK; [| vm_compute; reflexivity| vm_compute; reflexivity| unfold es_pre; es_wf].
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp - 48); (E, E + 904)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. step.
  tcallr eclear_iter_0. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_1. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_2. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_3. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_4. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_5. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_6. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_7. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_8. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_9. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_10. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_11. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_12. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_13. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_14. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  tcallr eclear_iter_15. all: try first [eassumption | reflexivity | lia]. ecl_norm.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells usegs _ E (es_pre _ _) |- _ => unfold es_pre, ECL_LNW in H; cbn [repeat map app Nat.sub upd] in H; rename H into EBf end.
  step. step. ec_F. cstep. do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into ST3 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -48) _ |- _ => rename H into FR3 end.
  release_frame FR3 ST3 (bv_unsigned sp). step. step.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  unfold hideP in *.
  chere. apply climpl_done.
  eexists. exists mf, LB1.
  split; [unfold cret; do 14 eexists; reflexivity|].
  split; [clear - Hf FU1; lia|].
  split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pe, E, 904)); [exact INE1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - EIMG E0 GLO SLO SPR LO; lia. }
  assert (NPE : ~ In pe (map blk_id LBall)).
  { pose proof (t_nodup_prefix blk_id [(ptn, N, 32); (pd, D, 32); (plk, LK, 40); (psk, SK, 56); (pg, G, 16); (ph, H, 8); (pe, E, 904)] LBall (pe, E, 904) ND1) as NI.
    apply NI. do 6 right. left. reflexivity. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRa0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pe, E, 904)); [exact INE1| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E1. apply NPE. cbn [blk_id fst] in E1. rewrite <- E1. apply in_map. exact Hb0. }
  (* [comment removed for export] *)
  assert (TRS : forall A cs, rw_cells usegs m1 A cs -> 65536 <= A /\ A + Z.of_nat (cells_size cs) <= 3485696 -> rw_cells usegs mf A cs).
  { intros A cs HA HB. eapply rw_cells_transport; [exact HA| exact MU1| exact WM1|]. cbn [disjoint_from]. clear - HB EIMG E0 GLO SLO SPR LO. lia. }
  assert (TRB : forall (q : bptr) A n cs, In (q, A, n) LB1 -> q <> pe -> rw_cells usegs m1 A cs -> Z.of_nat (cells_size cs) <= n -> rw_cells usegs mf A cs).
  { intros q A n cs Hq N1 HA Hsz. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 Hq) as (Q0 & _ & _ & QC & _).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 Hq INE1 N1) as D1.
    eapply rw_cells_transport; [exact HA| exact MU1| exact WM1|]. cbn [disjoint_from]. clear - Q0 QC D1 Hsz LO SLO SPR. lia. }
  cbn [map blk_id fst] in ND1.
  inversion ND1 as [|? ? NI0 NDa]; subst. inversion NDa as [|? ? NI1 NDb]; subst. inversion NDb as [|? ? NI2 NDc]; subst.
  inversion NDc as [|? ? NI3 NDd]; subst. inversion NDd as [|? ? NI4 NDe]; subst. inversion NDe as [|? ? NI5 NDf]; subst.
  destruct KEEP as (HDR1 & PBLK1 & SL01 & USED1 & TEV1 & CBC1 & HC & NC & GC & SKC & LKC & DC).
  unfold eclear_res, RATP, FZ_ERR_DEL_THREAD_STATE. exists pe, ptn, ph, pg, psk, plk, pd, E, N, H, G, SK, LK, D, u', top1, ne1.
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact RNGE|]. split; [exact RN|]. split; [exact RH|]. split; [exact RG|]. split; [exact RSK|]. split; [exact RLK|]. split; [exact RD|].
  split; [unfold es_clean, ECL_LNW; cbn [repeat app]; exact EBf|].
  split. { eapply (TRB psa SA 32); [subst LB1; do 7 right; exact INS| intros E1; apply NPE; rewrite <- E1; change psa with (blk_id (psa, SA, 32)); apply in_map; exact INS| exact HDR1| unfold sa_hdr; cbn; lia]. }
  split. { eapply (TRB pn P 128); [subst LB1; do 7 right; exact INP| intros E1; apply NPE; rewrite <- E1; change pn with (blk_id (pn, P, 128)); apply in_map; exact INP| exact PBLK1| cbn; lia]. }
  split; [apply TRS; [exact SL01| cbn; lia]|]. split; [apply TRS; [exact USED1| cbn; lia]|]. split; [apply TRS; [exact TEV1| cbn; lia]|]. split; [apply TRS; [exact CBC1| cbn; lia]|].
  split. { eapply (TRB ph H 8); [subst LB1; do 5 right; left; reflexivity| intros E1; apply NI5; rewrite E1; left; reflexivity| exact HC| cbn; lia]. }
  split. { eapply (TRB ptn N 32); [subst LB1; left; reflexivity| intros E1; apply NI0; rewrite E1; do 5 right; left; reflexivity| exact NC| cbn; lia]. }
  split. { eapply (TRB pg G 16); [subst LB1; do 4 right; left; reflexivity| intros E1; apply NI4; rewrite E1; right; left; reflexivity| exact GC| cbn; lia]. }
  split. { eapply (TRB psk SK 56); [subst LB1; do 3 right; left; reflexivity| intros E1; apply NI3; rewrite E1; do 2 right; left; reflexivity| exact SKC| unfold sk_cells; cbn; lia]. }
  split. { eapply (TRB plk LK 40); [subst LB1; do 2 right; left; reflexivity| intros E1; apply NI2; rewrite E1; do 3 right; left; reflexivity| exact LKC| unfold mutex_cells; cbn; lia]. }
  split. { eapply (TRB pd D 32); [subst LB1; right; left; reflexivity| intros E1; apply NI1; rewrite E1; do 4 right; left; reflexivity| exact DC| cbn; lia]. }
  exact NEF.
Qed.
End WithCeiling0.
