(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_aligned_frame.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_kit_ra Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_M_aligned F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_lock_new Fz_T_rcu.
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
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_ANL : Z := 0xf8934.
Definition ANL_STACK : Z := 32 + CAA_STACK.
Definition NB_BYTES : Z := 32768.          (* [comment removed for export] *)

Definition anl_res (FP Af nf : Z) (LBall : list block) (L : @clist bptr) (m : mem) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (p : bptr) (A : Z), v = Z_to_bv 64 A /\ LBall' = (p, A, NB_BYTES) :: LBall /\ L' = (p, NB_BYTES + 48) :: L
      /\ rblock_range A NB_BYTES /\ A mod 64 = 0
      /\ rw_cells usegs m' A [CB (Z.to_nat NB_BYTES) (zeros (Z.to_nat NB_BYTES))] /\ rw_cells usegs m' FP [C8 (Z_to_bv 64 A)] /\ bkeep Af nf FP m m'.

Definition anl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat)
         (pf : bptr) (Af nf nmf FP lo B : Z) (oldfp : word),
  (1 <= f)%nat -> croom L 0 1 (NB_BYTES + 48 + 8192) ->
  cown LBall L pf Af nf nmf -> Af <= FP -> FP + 8 <= Af + nf -> FP mod 8 = 0 -> rw_cells usegs m FP [C8 oldfp] ->
  rw_cells usegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - ANL_STACK ->
  a0 = Z_to_bv 64 512 -> a1 = Z_to_bv 64 FP ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_ANL) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq pf) [] 1 0 1 (NB_BYTES + 48 + 8192) (anl_res FP Af nf LBall L m)).

Theorem anl_spec : crypto_aligned_alloc_array_stmt -> anl_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CAA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f pf Af nf nmf FP lo Bd oldfp
         Hf ROOM OWNf FP1 FP2 FP8 FPC REPL CST SLO -> ->.
  unfold crypto_aligned_alloc_array_stmt in CAA.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNf)) as (FA0 & _ & FN0 & FAC & FAIMG).
  unfold ANL_STACK, CAA_STACK, RMEMALIGN_STACK, RMALLOC_STACK, FZ_ANL, GLOBALS_TOP, RMALLOC_REPLACED, NB_BYTES in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  destruct (wB_big 32816 ltac:(unfold TIER_A_MAX; lia)) as (WBa & WBb & WBc).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 4 step. step. do 2 step. do 7 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe (eq pf) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  lazymatch goal with H : rw_cells usegs ma FP _ |- _ => rename H into FPa end.
  lazymatch goal with H : rw_cells usegs ma 3477520 _ |- _ => rename H into REPLa end.
  eapply climpl_seq.
  { eapply CAA with (pf := pf) (Af := Af) (nf := nf) (nmf := nmf) (FP := FP) (num := 512) (sz := 64) (oldfp := oldfp) (lo := lo) (B := Bd);
      [exact Hf| change (512 * 64 + 48) with 32816; rewrite WBa, WBb, WBc; exact ROOM| lia| lia| lia| unfold MMAP_THRESHOLD; lia| exact OWNf| exact FP1| exact FP2| exact FP8| exact FPa
      | unfold RMALLOC_REPLACED; exact REPLa| exact CSTa| rewrite unsigned_lit by lia; unfold CAA_STACK, RMEMALIGN_STACK, RMALLOC_STACK; lia
      | reflexivity| reflexivity| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (p & A & junkA & -> & -> & -> & RA & A64 & ABLK & FPA & BKa)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). change (512 * 64) with 32768 in *. change (32768 + 48) with 32816 in *. rewrite WBa, WBb, WBc in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RA as (A0 & _ & _ & AC & AIMG).
  (* [comment removed for export] *)
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. cbn [map blk_id fst] in ND1.
  assert (INf1 : In (pf, Af, nf) ((p, A, 32768) :: LBall)) by (right; exact (proj1 OWNf)).
  assert (NEf : blk_id (pf, Af, nf) <> blk_id (p, A, 32768)).
  { cbn [blk_id fst]. pose proof (proj1 (proj1 (NoDup_cons_iff _ _) ND1)) as NI. intros E. apply NI. rewrite <- E. apply in_map_iff. exists (pf, Af, nf). split; [reflexivity| exact (proj1 OWNf)]. }
  assert (DISJ : Af + nf <= A \/ A + 32768 <= Af).
  { destruct (RHEAP_blocks_disjoint_proof _ _ _ (pf, Af, nf) (p, A, 32768) HP1 INf1 ltac:(left; reflexivity) NEf) as [X|X];
      unfold blk_addr, blk_size in X; cbn [fst snd] in X; [left| right]; lia. }
  clear NEf.
  assert (FRM0 : cframe (eq pf) [] (bv_unsigned sp) s LBall L m st1 ((p, A, 32768) :: LBall) ((p, 32816) :: L) m1).
  { eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRa CSTa CFR1 FRM1.
  pose proof (munch_refl [(A, A + 32768)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. 2: { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. do 4 step.
  lazymatch goal with H : stk usegs m1 lo _ |- _ => rename H into ST2 end.
  release_frame FR1 ST2 (bv_unsigned sp). step. step.
  tcall (memset_callZ ra sp gp tp _ _ _ s0 s1 _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 A 0 32768 junkA).
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  lazymatch goal with H : rw_cells usegs mf A _ |- _ => rename H into BLKf end.
  lazymatch goal with H : rw_cells usegs mf FP _ |- _ => rename H into FPf end.
  assert (INA : In (p, A, 32768) ((p, A, 32768) :: LBall)) by (left; reflexivity).
  chere. apply climpl_done.
  exists (Z_to_bv 64 A), mf, ((p, A, 32768) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [| apply Forall_nil]. apply (cwin_block _ _ _ (p, A, 32768)); [exact INA| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [exact FRM0| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (p, A, 32768)); [exact INA| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 Hb0 _ E. apply (proj1 (proj1 (NoDup_cons_iff _ _) ND1)). cbn [blk_id fst] in E. rewrite <- E. apply in_map. exact Hb0. }
  exists p, A. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RA|]. split; [exact A64|]. split; [exact BLKf|]. split; [exact FPf|].
  eapply agree_on_trans; [eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)| intros a Ha; cbv beta in Ha; cbn [outside]; lia]|].
  eapply agree_on_trans; [exact BKa|].
  eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU1 WM1)| intros a Ha; cbv beta in Ha; cbn [outside]; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_HT_NEW : Z := 0xf8708.
Definition HTN_STACK : Z := 64 + RCU_STACK.     (* [comment removed for export] *)
Definition HT_CTX : Z := 0x32dec8.               (* [comment removed for export] *)
Definition ht_conf : list cell :=
  [C8 (Z_to_bv 64 HT_CTX); C8 z64; C8 z64; C8 (Z_to_bv 64 512); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 z64; C4 z64].

Definition ht_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (ph pka pmd pn pr pq : bptr) (HT LKa MD NB R Q : Z),
       v = Z_to_bv 64 HT
    /\ LBall' = (pq, Q, 16) :: (pr, R, 264) :: (pn, NB, NB_BYTES) :: (pmd, MD, 24) :: (pka, LKa, 40) :: (ph, HT, 96) :: LBall
    /\ L' = (pq, 16) :: (pr, 264) :: (pn, NB_BYTES + 48) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: L
    /\ rblock_range HT 96 /\ rblock_range LKa 40 /\ rblock_range MD 24 /\ rblock_range NB NB_BYTES /\ rblock_range R 264 /\ rblock_range Q 16.

Definition ht_new_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (CONF lo B : Z),
  (6 <= f)%nat -> croom L 4 2 (NB_BYTES + 48 + 8192 + (264 + 8192)) -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - HTN_STACK ->
  a0 = Z_to_bv 64 CONF -> bv_unsigned sp <= CONF -> CONF mod 8 = 0 -> rw_cells usegs m CONF ht_conf ->
  rw_cells usegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_HT_NEW) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 6 4 2 (NB_BYTES + 48 + 8192 + (264 + 8192)) (ht_res LBall L)).

Theorem ht_new_fp_spec : crypto_zalloc_stmt -> T_lock_new_stmt -> anl_stmt -> T_rcu_new_stmt -> ht_new_fp_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ LKN ANL RCU ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f CONF lo Bd
         Hf ROOM CST SLO -> CGE CONF8 CONFc REPL.
  unfold crypto_zalloc_stmt in CZ. unfold T_lock_new_stmt in LKN. unfold anl_stmt in ANL. unfold T_rcu_new_stmt in RCU.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold HTN_STACK, ANL_STACK, CAA_STACK, RMEMALIGN_STACK, RCU_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_HT_NEW, RMALLOC_REPLACED, NB_BYTES, HT_CTX in *.
  unfold ht_conf, HT_CTX in CONFc.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (rw_cells_bound _ _ _ _ CONFc) as CB0. cbn [cells_size csize Nat.add] in CB0.
  destruct (wA_small 96 ltac:(unfold TIER_A_MAX; lia)) as (W96a & W96b & W96c). destruct (wA_small 40 ltac:(unfold TIER_A_MAX; lia)) as (W40a & W40b & W40c).
  destruct (wA_small 24 ltac:(unfold TIER_A_MAX; lia)) as (W24a & W24b & W24c). destruct (wA_small 16 ltac:(unfold TIER_A_MAX; lia)) as (W16a & W16b & W16c).
  destruct (wB_big 264 ltac:(unfold TIER_A_MAX; lia)) as (W264a & W264b & W264c).
  destruct ROOM as (RA & RB & RC).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 5 step. step. step. do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  lazymatch goal with H : rw_cells usegs ma CONF _ |- _ => rename H into CONFa end.
  lazymatch goal with H : rw_cells usegs ma 3477520 _ |- _ => rename H into REPLa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply CZ with (n := 96) (lo := lo) (B := Bd); [lia| rewrite W96a, W96b, W96c; unfold croom; lia| lia| exact CSTa| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (ph & HT & -> & -> & -> & RH & HBLK)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). rewrite W96a, W96b, W96c in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 CONFa ltac:(lia)) as CONF1.
  cst_static CFR1 REPLa REPL1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RH as (H0 & _ & _ & HC & HIMG).
  change (Z.to_nat 96) with 96%nat in HBLK.
  apply (th_cells_congr usegs m1 HT _ ([CB (Z.to_nat 48) (zeros 48)] ++ [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64])) in HBLK; [| reflexivity | reflexivity | cbn; repeat split; reflexivity].
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in HBLK. destruct HBLK as [HTA HTB]. change (Z.of_nat (cells_size [CB (Z.to_nat 48) (zeros 48)])) with 48 in HTB.
  assert (FRM0 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st1 ((ph, HT, 96) :: LBall) ((ph, 96) :: L) m1).
  { eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRa CSTa CFR1 FRM1 CONFa REPLa FR.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. if_cases KC0; zify_cond KC0. { exfalso. rewrite ?unsigned_lit in KC0 by lia. lia. } clear KC0.
  step. step. step. rewrite ?(unsigned_lit CONF) by lia. rewrite (ubs_land7 CONF) by exact CONF8.
  if_cases KC1; zify_cond KC1. { exfalso. apply KC1. reflexivity. } clear KC1.
  step. step. step. th_if_lit. step. step. th_if_lit. step. step. th_if_lit. step. chere.
  eapply climpl_seq.
  { eapply LKN with (lo := lo) (B := Bd); [lia| rewrite W40a, W40b, W40c; unfold croom, cgrow in *; lia| exact CST1| rewrite unsigned_lit by lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (pka & LKa & -> & -> & -> & RKa & MCa)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia). rewrite W40a, W40b, W40c in GR2.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 CONF1 ltac:(lia)) as CONF2.
  cst_static CFR2 REPL1 REPL2.
  assert (INH2 : In (ph, HT, 96) ((pka, LKa, 40) :: (ph, HT, 96) :: LBall)) by (right; left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, HT, 96) CFR2 HTA ltac:(left; reflexivity) (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd]; change (Z.of_nat (cells_size [CB (Z.to_nat 48) (zeros 48)])) with 48; lia)) as HTA2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, HT, 96) CFR2 HTB ltac:(left; reflexivity) (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HTB2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RKa as (Ka0 & _ & _ & KaC & KaIMG). unfold mutex_cells in MCa.
  assert (FRM02 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st2 ((pka, LKa, 40) :: (ph, HT, 96) :: LBall) ((pka, 40) :: (ph, 96) :: L) m2).
  { eapply cframe_call; [exact FRM0| exact FRM2| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRM0 CFR2 FRM2 FR1 CONF1 REPL1 HTA HTB.
  pose proof (munch_refl [(HT + 48, HT + 96); (HT, HT + 48)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. step. rewrite ?(unsigned_lit HT) by lia. rewrite (ubs_land7 HT) by (destruct RH as (_ & RH16 & _); lia).
  if_cases KH1; zify_cond KH1. { exfalso. apply KH1. reflexivity. } clear KH1.
  cstep. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step. step. step.
  lazymatch goal with H : rw_cells usegs ?mx HT [CB _ _] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HTAc end.
  tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cells_bytes ht_conf)).
  all: try first [eassumption | lia].
  { exact (proj2 (proj1 CONF2)). }
  { reflexivity. }
  cbv beta delta [mkR].
  lazymatch goal with H : rw_cells usegs ?mx HT [CB _ _] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HTAm end.
  apply (th_cells_congr usegs _ HT _ [C8 (Z_to_bv 64 3333832); C8 z64; C8 z64; C8 (Z_to_bv 64 512); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 z64; C4 z64]) in HTAm;
    [| reflexivity | reflexivity | cbn; repeat split; exact I].
  (* [comment removed for export] *)
  step. step. th_if_lit. do 12 step. step.
  step. cstep. step. th_if_lit. step. step. cstep.
  (* [comment removed for export] *)
  do 4 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mb end.
  lazymatch goal with H : stk _ mb _ _ |- _ => rename H into STb end.
  lazymatch goal with H : mem_inv _ mb |- _ => rename H into MIb end.
  lazymatch goal with H : rw_cells usegs mb HT _ |- _ => rename H into HTAb end.
  lazymatch goal with H : rw_cells usegs mb (HT + 48) _ |- _ => rename H into HTBb end.
  lazymatch goal with H : rw_cells usegs mb CONF _ |- _ => rename H into CONFb end.
  lazymatch goal with H : rw_cells usegs mb 3477520 _ |- _ => rename H into REPLb end.
  lazymatch goal with H : rw_cells usegs mb (bv_unsigned sp + -48) _ |- _ => rename H into FRmb end.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. cbn [map blk_id fst] in ND1.
  assert (NPH : forall b0, In b0 LBall -> ~ False -> blk_id b0 <> ph).
  { intros b0 Hb0 _ E. apply (proj1 (proj1 (NoDup_cons_iff _ _) ND1)). rewrite <- E. apply in_map. exact Hb0. }
  assert (CSTb : cstate st2 ((pka, LKa, 40) :: (ph, HT, 96) :: LBall) LB ((pka, 40) :: (ph, 96) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m2 mb _ _ _ lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIb| | lia| lia| | rewrite unsigned_lit by lia; exact STb| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply (cwin_block _ _ _ (ph, HT, 96)); [exact INH2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (ph, HT, 96)); [exact INH2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRb : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st2 ((pka, LKa, 40) :: (ph, HT, 96) :: LBall) ((pka, 40) :: (ph, 96) :: L) mb).
  { eapply cframe_seg; [exact FRM02| exact MU2| exact WM2| exact HP2| lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (ph, HT, 96)); [exact INH2| exact NPH| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (ph, HT, 96)); [exact INH2| exact NPH| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil]. }
  clear FRM02 MU2 WM2.
  eapply climpl_seq.
  { eapply CZ with (n := 24) (lo := lo) (B := Bd); [clear - Hf FU1 FU2; lia| rewrite W24a, W24b, W24c; clear - RA RB RC GR1 GR2; unfold croom, cgrow in *; lia| lia| exact CSTb
      | rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f3 L3 st3 ms3 (v3 & m3 & LBall3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (pmd & MD & -> & -> & -> & RMD & MDBLK)).
  destruct RET3 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM3 by lia). rewrite W24a, W24b, W24c in GR3.
  pose proof FRM3 as (CFR3 & KP3 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FRmb ltac:(lia)) as FR3.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 CONFb ltac:(lia)) as CONF3.
  cst_static CFR3 REPLb REPL3.
  set (LB3 := (pmd, MD, 24) :: (pka, LKa, 40) :: (ph, HT, 96) :: LBall) in *.
  assert (INH3 : In (ph, HT, 96) LB3) by (subst LB3; do 2 right; left; reflexivity).
  assert (INK3 : In (pka, LKa, 40) LB3) by (subst LB3; right; left; reflexivity).
  assert (INM3 : In (pmd, MD, 24) LB3) by (subst LB3; left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, HT, 96) CFR3 HTAb ltac:(right; left; reflexivity) (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HTA3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, HT, 96) CFR3 HTBb ltac:(right; left; reflexivity) (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HTB3.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by lia.
  pose proof RMD as (MD0 & _ & _ & MDC & MDIMG).
  change (Z.to_nat 24) with 24%nat in MDBLK.
  apply (th_cells_congr usegs m3 MD _ [C8 z64; C8 z64; C8 z64]) in MDBLK; [| reflexivity | reflexivity | cbn; repeat split; exact I].
  assert (FRM03 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st3 LB3 ((pmd, 24) :: (pka, 40) :: (ph, 96) :: L) m3).
  { eapply cframe_call; [exact FRb| exact FRM3| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRb CSTb CFR3 FRM3 HTAb HTBb CONFb REPLb FRmb.
  pose proof (munch_refl [(HT + 48, HT + 96)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  (* [comment removed for export] *)
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 NDL3].
  assert (NEhm : ph <> pmd) by (eapply cstate_head_fresh; [exact CST3|]; right; left; reflexivity).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 INM3 INH3 (fun E => NEhm (eq_sym E))) as APmh.
  assert (NPM : forall b0, In b0 LBall -> ~ False -> blk_id b0 <> pmd).
  { intros b0 Hb0 _. apply (t_fresh_notin (fun _ => False) LBall (pmd, MD, 24)); [| exact Hb0| intros X; exact X].
    exact (t_nodup_prefix blk_id [(pmd, MD, 24); (pka, LKa, 40); (ph, HT, 96)] LBall (pmd, MD, 24) ND3 ltac:(left; reflexivity)). }
  assert (PMDF : forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ False -> pmd <> q).
  { intros q [Hq|Hq] _ E; subst q.
    - exact (t_nodup_prefix blk_id [(pmd, MD, 24); (pka, LKa, 40); (ph, HT, 96)] LBall (pmd, MD, 24) ND3 ltac:(left; reflexivity) Hq).
    - exact (t_nodup_prefix fst [(pmd, 24); (pka, 40); (ph, 96)] L (pmd, 24) NDL3 ltac:(left; reflexivity) Hq). }
  hide NEhm. hide NPM. hide PMDF. clear ND3 NDL3 ND1.
  cprefix. cstep. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. } clear K3.
  step. step. rewrite ?(unsigned_lit MD) by lia. rewrite (ubs_land7 MD) by (destruct RMD as (_ & RMD16 & _); lia).
  if_cases KM1; zify_cond KM1. { exfalso. apply KM1. reflexivity. } clear KM1.
  step. step. step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mc end.
  lazymatch goal with H : stk _ mc _ _ |- _ => rename H into STc end.
  lazymatch goal with H : mem_inv _ mc |- _ => rename H into MIc end.
  lazymatch goal with H : rw_cells usegs mc MD _ |- _ => rename H into MDc end.
  lazymatch goal with H : rw_cells usegs mc HT _ |- _ => rename H into HTAc end.
  lazymatch goal with H : rw_cells usegs mc (HT + 48) _ |- _ => rename H into HTBc end.
  lazymatch goal with H : rw_cells usegs mc CONF _ |- _ => rename H into CONFc end.
  lazymatch goal with H : rw_cells usegs mc 3477520 _ |- _ => rename H into REPLc end.
  lazymatch goal with H : rw_cells usegs mc (bv_unsigned sp + -48) _ |- _ => rename H into FRc end.
  change [C8 z64; C8 z64; C8 z64] with ([C8 z64] ++ [C8 z64; C8 z64]) in MDc.
  apply (proj1 (rw_cells_app usegs mc _ _ _)) in MDc. destruct MDc as [MDa MDf].
  change [C8 z64; C8 z64] with ([C8 z64] ++ [C8 z64]) in MDf.
  apply (proj1 (rw_cells_app usegs mc _ _ _)) in MDf. destruct MDf as [MDf MDb]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in MDf, MDb.
  replace (MD + 8 + 8) with (MD + 16) in MDb by lia.
  assert (CSTc : cstate st3 LB3 LB ((pmd, 24) :: (pka, 40) :: (ph, 96) :: L) mc (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m3 mc _ _ _ lo Bd (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| exact MIc| | lia| lia| | rewrite unsigned_lit by lia; exact STc| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply (cwin_block _ _ _ (ph, HT, 96)); [exact INH3| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRMc : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st3 LB3 ((pmd, 24) :: (pka, 40) :: (ph, 96) :: L) mc).
  { eapply cframe_seg; [exact FRM03| exact MU3| exact WM3| exact HP3| lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (ph, HT, 96)); [exact INH3| exact NPH| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil]. }
  clear FRM03 MU3 WM3.
  eapply climpl_seq.
  { eapply ANL with (pf := pmd) (Af := MD) (nf := 24) (nmf := 24) (FP := MD + 8) (oldfp := Z_to_bv 64 0) (lo := lo) (B := Bd);
      [clear - Hf FU1 FU2 FU3; lia| clear - RA RB RC GR1 GR2 GR3; unfold croom, cgrow in *; lia| split; [exact INM3| left; reflexivity]| lia| lia| clear - RMD; destruct RMD as (_ & RMD16 & _); lia| exact MDf
      | unfold RMALLOC_REPLACED; exact REPLc| exact CSTc| rewrite unsigned_lit by lia; lia| reflexivity| reflexivity]. }
  intros f4 L4 st4 ms4 (v4 & m4 & LBall4 & RET4 & FU4 & GR4 & CST4 & FRM4 & (pn & NB & -> & -> & -> & RNB & NB64 & NBBLK & FP4 & BK4)).
  destruct RET4 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). unfold NB_BYTES in *. change (32768 + 48) with 32816 in *.
  cret_lit. repeat (rewrite unsigned_lit in FRM4 by lia). clear NBBLK.
  pose proof FRM4 as (CFR4 & KP4 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 FRc ltac:(lia)) as FR4.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 CONFc ltac:(lia)) as CONF4.
  cst_static CFR4 REPLc REPL4.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, HT, 96) CFR4 HTAc INH3 (fun E => NEhm (eq_sym E)) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HTA4.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, HT, 96) CFR4 HTBc INH3 (fun E => NEhm (eq_sym E)) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HTB4.
  pose proof (bkeep_cells _ _ _ _ _ _ _ BK4 MDa ltac:(lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as MD04.
  pose proof (bkeep_cells _ _ _ _ _ _ _ BK4 MDb ltac:(lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as MD164.
  pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _).
  rewrite unsigned_lit in ST4 by lia.
  pose proof RNB as (NB0 & _ & _ & NBC & NBIMG).
  set (LB4 := (pn, NB, 32768) :: LB3) in *.
  assert (INH4 : In (ph, HT, 96) LB4) by (subst LB4 LB3; do 3 right; left; reflexivity).
  assert (INM4 : In (pmd, MD, 24) LB4) by (subst LB4 LB3; right; left; reflexivity).
  assert (FRM04 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st4 LB4 ((pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: L) m4).
  { eapply cframe_call; [exact FRMc| exact FRM4| lia| intros a X; exact X| exact PMDF]. }
  clear FRMc CSTc CFR4 FRM4 KP4 FRc CONFc REPLc HTAc HTBc MDa MDb MDf BK4.
  pose proof (munch_refl [(MD, MD + 24)]%Z m4) as MU4. pose proof (wmono_refl usegs m4) as WM4.
  (* [comment removed for export] *)
  cprefix. step. step. if_cases KM2; zify_cond KM2. { exfalso. rewrite ?unsigned_lit in KM2 by lia. lia. } clear KM2.
  step. step. rewrite ?(unsigned_lit MD) by lia. rewrite (ubs_land7 MD) by (destruct RMD as (_ & RMD16 & _); lia).
  if_cases KM3; zify_cond KM3. { exfalso. apply KM3. reflexivity. } clear KM3.
  cstep. step. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. } clear K4.
  step. step. step. cstep. step. th_if_lit. step. step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into md end.
  lazymatch goal with H : stk _ md _ _ |- _ => rename H into STd end.
  lazymatch goal with H : mem_inv _ md |- _ => rename H into MId end.
  assert (CSTd : cstate st4 LB4 LB ((pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: L) md (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m4 md _ _ _ lo Bd (bv_unsigned sp)); [exact CST4| exact MU4| exact WM4| exact MId| | lia| lia| | rewrite unsigned_lit by lia; exact STd| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply (cwin_block _ _ _ (pmd, MD, 24)); [exact INM4| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRd : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st4 LB4 ((pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: L) md).
  { eapply cframe_seg; [exact FRM04| exact MU4| exact WM4| exact HP4| lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (pmd, MD, 24)); [exact INM4| exact NPM| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil]. }
  clear FRM04 MU4 WM4.
  eapply climpl_seq.
  { eapply RCU with (lo := lo) (B := Bd); [clear - Hf FU1 FU2 FU3 FU4; lia| rewrite W264a, W264b, W264c, W16a, W16b, W16c; clear - RA RB RC GR1 GR2 GR3 GR4; unfold croom, cgrow in *; lia
      | exact CSTd| rewrite unsigned_lit by lia; lia| reflexivity| rewrite unsigned_lit by lia; lia]. }
  intros f5 L5 st5 ms5 (v5 & m6 & LBall5 & RET5 & FU5 & GR5 & CST5 & FRM5 & (pq & Q & pr & R & -> & -> & -> & RR & RQ & _)).
  destruct RET5 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM5 by lia). rewrite W264a, W264b, W264c, W16a, W16b, W16c in GR5.
  pose proof FRM5 as (CFR5 & KP5 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 FR4 ltac:(lia)) as FR5.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, HT, 96) CFR5 HTA4 INH4 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HTA5.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ph, HT, 96) CFR5 HTB4 INH4 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HTB5.
  pose proof CST5 as (HP5 & _ & (errv5 & _ & _ & ST5 & _ & _ & MI5 & _) & _).
  rewrite unsigned_lit in ST5 by lia.
  pose proof RR as (Rg0 & _ & _ & RgC & RgIMG).
  set (LB5 := (pq, Q, 16) :: (pr, R, 264) :: LB4) in *.
  assert (INH5 : In (ph, HT, 96) LB5) by (subst LB5 LB4 LB3; do 5 right; left; reflexivity).
  assert (FRM05 : cframe (fun _ : bptr => False) [] (bv_unsigned sp) s LBall L m st5 LB5 ((pq, 16) :: (pr, 264) :: (pn, 32816) :: (pmd, 24) :: (pka, 40) :: (ph, 96) :: L) m6).
  { eapply cframe_call; [exact FRd| exact FRM5| lia| intros a X; exact X| intros q _ X; exact X]. }
  clear FRd CSTd CFR5 FRM5 KP5 FR4 HTA4 HTB4 CONF4 REPL4 FP4 MD04 MD164.
  pose proof (munch_refl [(HT, HT + 96)]%Z m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
  (* [comment removed for export] *)
  cprefix. cstep. step. if_cases K5; zify_cond K5. { exfalso. rewrite ?unsigned_lit in K5 by lia. lia. } clear K5.
  step. step. th_if_lit. step. step. cstep. step. step. do 5 step.
  lazymatch goal with H : stk usegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into STz end.
  release_frame FR5 STz (bv_unsigned sp). step. step.
  chere. apply climpl_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mz end.
  lazymatch goal with H : stk usegs mz lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIf end.
  exists (Z_to_bv 64 HT), mz, LB5.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear - Hf FU1 FU2 FU3 FU4 FU5; lia|]. split; [clear - GR1 GR2 GR3 GR4 GR5; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m6 mz _ sp _ lo Bd (bv_unsigned sp)); [exact CST5| exact MU6| exact WM6| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [| apply Forall_nil]. apply (cwin_block _ _ _ (ph, HT, 96)); [exact INH5| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [exact FRM05| exact MU6| exact WM6| exact HP5| lia|].
    apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (ph, HT, 96)); [exact INH5| exact NPH| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia. }
  exists ph, pka, pmd, pn, pr, pq, HT, LKa, MD, NB, R, Q. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RH|]. split; [exact RKa|]. split; [exact RMD|]. split; [exact RNB|]. split; [exact RR| exact RQ].
Qed.
End WithCeiling0.
