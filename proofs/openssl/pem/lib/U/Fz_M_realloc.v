(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_impl RF_realloc_spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_kit_ra.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_CRYPTO_REALLOC : Z := 0xe93e0.
Definition FZ_CRYPTO_REALLOC_ARRAY : Z := 0xe72c0.
Definition CRE_STACK : Z := 48 + RREALLOC_STACK.

Definition crypto_realloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n0 nm n lo B : Z) (src : list byte),
  (2 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 < n < MMAP_THRESHOLD ->
  cown LBall L p A n0 nm -> rw_cells usegs m A [CB (Z.to_nat n0) src] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CRE_STACK -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CRYPTO_REALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 2 (wA n) (wB n) (wBig n)
                (cs_realloc_res p A nm n src LBall L)).

Theorem crypto_realloc_spec : rrealloc_prefix_stmt -> rmalloc_impl_stmt -> rfree_impl_stmt -> crypto_realloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros PRE MAL FRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n0 nm n lo B src
         Hf ROOM N OWNp BLK CST SLO A0 A1. subst a0 a1.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNp)) as (PA0 & _ & PN0 & PAC & PAIMG).
  unfold CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, MMAP_THRESHOLD, FZ_CRYPTO_REALLOC, GLOBALS_TOP in *.
  cimg_cell CIMG m 0x31d4e8 [C8 (Z_to_bv 64 0xe93e0)] IMPL.
  cimg_cell CIMG m 0x31c080 [C8 (Z_to_bv 64 0xe93e0)] GOTR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  (* [comment removed for export] *)
  cprefix. step. carve_frame 48%nat ST. do 14 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 2 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ s LBall LB L m ma sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - constructor; [apply cwin_stack; lia| constructor].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply (cs_realloc PRE MAL FRE) with (p := p) (A := A) (n0 := n0) (nm := nm) (n := n) (src := src);
      [exact Hf| exact ROOM| unfold MMAP_THRESHOLD; lia| exact OWNp| exact BLK| exact CSTa| rewrite unsigned_lit by lia; unfold RREALLOC_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & A' & tail & -> & -> & RNG & NEW & ARM)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A'0 & _ & _ & A'C & A'IMG).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  do 8 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  chere. apply climpl_done.
  exists (Z_to_bv 64 A'), m1, ((q, A', n) :: lb_remove p LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|]. split; [exact GR1|].
  split. { eapply (cstate_seg [] _ _ _ _ m1 m1 _ sp tp lo B (bv_unsigned sp)); [exact CST1| apply munch_refl| apply wmono_refl| exact MI1| apply Forall_nil| lia| lia| exact I| exact ST1| exact HB]. }
  split. { eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ X; exact X]. }
  exists q, A', tail. auto 6.
Qed.

(* [comment removed for export] *)
Definition crypto_realloc_array_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n0 nm num sz lo B : Z) (src : list byte),
  (2 <= f)%nat -> croom L (wA (num * sz)) (wB (num * sz)) (wBig (num * sz)) -> 0 <= num < 2^32 -> 0 <= sz < 2^32 -> 0 < num * sz < MMAP_THRESHOLD ->
  cown LBall L p A n0 nm -> rw_cells usegs m A [CB (Z.to_nat n0) src] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CRE_STACK -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 num -> a2 = Z_to_bv 64 sz ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CRYPTO_REALLOC_ARRAY) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 2
                (wA (num * sz)) (wB (num * sz)) (wBig (num * sz)) (cs_realloc_res p A nm (num * sz) src LBall L)).

Theorem crypto_realloc_array_spec : crypto_realloc_stmt -> crypto_realloc_array_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n0 nm num sz lo B src
         Hf ROOM NUM SZ N OWNp BLK CST SLO A0 A1 A2. subst a0 a1 a2.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNp)) as (PA0 & _ & PN0 & PAC & PAIMG).
  unfold CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, MMAP_THRESHOLD, FZ_CRYPTO_REALLOC_ARRAY, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MH : (bv_unsigned (Z_to_bv 64 num) * bv_unsigned (Z_to_bv 64 sz)) ≫ 64 = 0).
  { rewrite !unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
  cprefix. step. carve_frame 32%nat ST. do 8 step.
  step. rewrite MH. if_true.
  do 9 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate s LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  unfold crypto_realloc_stmt in CR.
  eapply climpl_mono.
  { eapply CR with (p := p) (A := A) (n0 := n0) (nm := nm) (n := num * sz) (src := src);
      [exact Hf| exact ROOM| unfold MMAP_THRESHOLD; lia| exact OWNp| exact BLK| exact CSTc| unfold CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| reflexivity|].
    rewrite !unsigned_lit by lia. reflexivity. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
End WithCeiling0.
