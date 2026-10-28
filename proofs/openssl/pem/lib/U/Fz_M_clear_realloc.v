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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memcpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_M_malloc Fz_M_clear_free.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_CLEAR_REALLOC : Z := 0xe9540.
Definition CCR_STACK : Z := 64 + CCF_STACK.

Definition cs_grow_res (p : bptr) (nm num : Z) (src : list byte) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q A' tail i, v = Z_to_bv 64 A' /\ LBall' = (q, A', num) :: lb_remove p LBall
      /\ nth_error L i = Some (p, nm) /\ L' = (q, num) :: cremove i L
      /\ rblock_range A' num /\ rw_cells usegs m' A' [CB (Z.to_nat num) (src ++ tail)].

Definition crypto_clear_realloc_grow_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n nm old num lo B : Z) (src : list byte),
  (2 <= f)%nat -> croom L (wA num) (wB num) (wBig num) ->
  cown LBall L p A n nm -> 0 < old <= n -> old <= num < 2^31 -> rw_cells usegs m A [CB (Z.to_nat old) src] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CCR_STACK -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 old -> a2 = Z_to_bv 64 num ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CLEAR_REALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 2
                (wA num - wA nm) (wB num - wB nm) (wBig num - wBig nm) (cs_grow_res p nm num src LBall L)).

Theorem crypto_clear_realloc_grow : crypto_malloc_stmt -> crypto_clear_free_stmt -> crypto_clear_realloc_grow_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM CCF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n nm old num lo B src
         Hf ROOM OWNp OLD NUM BLK CST SLO A0 A1 A2. subst a0 a1 a2.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNp)) as (A0 & _ & _ & AC & AIMG).
  unfold CCR_STACK, CCF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_CLEAR_REALLOC, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  (* [comment removed for export] *)
  cprefix. step. carve_frame 64%nat ST. do 10 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 2 step.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 4 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ s LBall LB L m ma sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  eapply climpl_seq.
  { eapply CM with (n := num); [lia| exact ROOM| lia| exact CSTa| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & A' & jk & -> & -> & -> & RNG & NEW)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & KP1 & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -64) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  assert (BLK1 : rw_cells usegs m1 A [CB (Z.to_nat old) src]).
  { eapply (cfr_cells_block _ _ _ _ _ _ _ _ (p, A, n) CFR1); [exact BLK| exact (proj1 OWNp)| intros X; exact X| |]; unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia. }
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A'0 & _ & _ & A'C & A'IMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (QP : q <> p).
  { intros E. cbn [map blk_id fst] in ND1. inversion ND1 as [|x l NI _]; subst. apply NI. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact (proj1 OWNp)]. }
  assert (APART : A + n <= A' \/ A' + num <= A).
  { pose proof (RHEAP_blocks_disjoint_proof _ _ _ (p, A, n) (q, A', num) HP1 (or_intror (proj1 OWNp)) (or_introl eq_refl)) as D.
    unfold blk_id, blk_addr, blk_size in D. cbn [fst snd] in D. apply D. intros E. apply QP. symmetry. exact E. }
  (* [comment removed for export] *)
  destruct (rw_cells_CB_split_at usegs m1 A' (Z.to_nat num) jk (Z.to_nat old) ltac:(lia) NEW) as [NEWa NEWb].
  rewrite Z2Nat.id in NEWb by lia.
  pose proof (rw_cells_CB_length usegs m1 A _ _ BLK1) as LSRC.
  pose proof (rw_cells_bytes_at usegs m1 A _ BLK1) as SRC1. cbn [cells_bytes cbytes] in SRC1. rewrite app_nil_r in SRC1.
  (* [comment removed for export] *)
  pose proof (munch_refl [(A', A' + old)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  do 4 step.
  calle (eapply memcpy_spec with (src := src)); try lia.
  do 5 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mb end.
  assert (INQ : In (q, A', num) ((q, A', num) :: LBall)) by (left; reflexivity).
  assert (CSTb : cstate st1 ((q, A', num) :: LBall) LB ((q, num) :: L) mb (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 mb _ _ tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | |].
    - constructor; [| constructor]. unfold cwin. cbn [fst snd]. do 5 right. exists (q, A', num). split; [exact INQ|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST1.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRa : cframe (eq p) [] (bv_unsigned sp) s LBall L m st1 ((q, A', num) :: LBall) ((q, num) :: L) m1).
  { eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ _ X; exact X]. }
  assert (FRb : cframe (eq p) [] (bv_unsigned sp) s LBall L m st1 ((q, A', num) :: LBall) ((q, num) :: L) mb).
  { eapply cframe_seg; [exact FRa| exact MU1| exact WM1| exact HP1| lia|].
    constructor; [| constructor]. unfold cseg_ok. cbn [fst snd]. do 3 right. exists (q, A', num). split; [exact INQ|]. split.
    - destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1).
    - unfold blk_addr, blk_size. cbn [fst snd]. lia. }
  eapply climpl_seq.
  { eapply CCF with (p := p) (A := A) (n := n) (nm := nm) (num := old) (junk := src);
      [lia| apply cown_cons; exact OWNp| lia| exact BLK1| exact CSTb| rewrite unsigned_lit by lia; unfold CCF_STACK, RFREE_STACK; lia| reflexivity| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (-> & i & HN & ->)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  destruct i as [|i]; [cbn in HN; exfalso; apply QP; congruence|]. cbn [nth_error] in HN. cbn [cremove] in *.
  rewrite (lb_remove_cons_ne p (q, A', num) LBall) in * by (unfold blk_id; cbn [fst]; exact QP).
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
  assert (NQ : ~ p = blk_id (q, A', num)) by (unfold blk_id; cbn [fst]; intros E; apply QP; symmetry; exact E).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q, A', num) CFR2 PC INQ NQ
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as PC2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q, A', num) CFR2 NEWb INQ NQ
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as NEWb2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. do 12 step.
  release_frame FR2 ST2 (bv_unsigned sp).
  chere. apply climpl_done.
  exists (Z_to_bv 64 A'), m2, ((q, A', num) :: lb_remove p LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)| lia| lia| lia]. }
  split. { eapply (cstate_seg [] _ _ _ _ m2 m2 _ sp tp lo B (bv_unsigned sp)); [exact CST2| apply munch_refl| apply wmono_refl| exact MI2| apply Forall_nil| lia| lia| exact I| exact ST2| exact HB]. }
  split. { eapply cframe_call; [exact FRb| exact FRM2| lia| intros a X; exact X| intros q0 _ X; exact X]. }
  exists q, A', (drop (Z.to_nat old) jk), i. split; [reflexivity|]. split; [reflexivity|]. split; [exact HN|]. split; [reflexivity|]. split; [exact RNG|].
  pose proof (rw_cells_CB_join usegs m2 A' _ _ _ _ PC2 ltac:(rewrite Z2Nat.id by lia; exact NEWb2)) as J.
  replace (Z.to_nat old + (Z.to_nat num - Z.to_nat old))%nat with (Z.to_nat num) in J by lia. exact J.
Qed.
(* [comment removed for export] *)
Definition crypto_clear_realloc_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (num lo B : Z),
  (1 <= f)%nat -> croom L (wA num) (wB num) (wBig num) -> 0 < num < 2^31 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CCR_STACK -> a0 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 num ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CLEAR_REALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA num) (wB num) (wBig num)
                (cs_malloc_res num LBall L)).

Theorem crypto_clear_realloc_null : crypto_malloc_stmt -> crypto_clear_realloc_null_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f num lo B
         Hf ROOM NUM CST SLO A0 A2. subst a0 a2.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold CCR_STACK, CCF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_CLEAR_REALLOC, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 64%nat ST. do 10 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  do 12 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate s LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  eapply climpl_mono.
  { eapply CM with (n := num); [exact Hf| exact ROOM| lia| exact CSTc| unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
End WithCeiling0.
