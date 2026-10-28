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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_calloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

(* [comment removed for export] *)
Definition sk_cells (num pad data sorted nalloc comp cmpt freet copyt : word) : list cell :=
  [C4 num; C4 pad; C8 data; C4 sorted; C4 nalloc; C8 comp; C8 cmpt; C8 freet; C8 copyt].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_sk_set_stmt (ENTRY : Z) (upd : word -> word -> word -> word -> word * word * word) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A : Z) (num pad data sorted nalloc comp cmpt freet copyt : word),
    a0 = Z_to_bv 64 A -> 0 < A -> A mod 8 = 0 ->
    rw_cells usegs m A (sk_cells num pad data sorted nalloc comp cmpt freet copyt) ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (A + 56 <= lo \/ bv_unsigned sp <= A) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 z64 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (A + 32, A + 56)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' A (sk_cells num pad data sorted nalloc comp
                                                  (fst (fst (upd a1 cmpt freet copyt))) (snd (fst (upd a1 cmpt freet copyt))) (snd (upd a1 cmpt freet copyt))))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Ltac sk_set_walk sp A HC ST :=
  pose proof (rw_cells_bound _ _ _ _ HC) as HB; cbn [cells_size csize Nat.add] in HB;
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A + 32, A + 56)]%Z mm) as MU; pose proof (wmono_refl usegs mm) as WM end;
  ths; th_frame 16%nat [8; 8]%nat ST; do 3 ths;
  ths; (let K0 := fresh "K" in if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]);
  ths; ths; ubs_if;
  ths; do 3 ths;
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end;
  ths; cbn [fst snd]; finish; eassumption.

Theorem T_sk_set_thunks_proof : T_sk_set_stmt 0xe63fc (fun v c f k => (c, v, k)).
Proof. unfold T_sk_set_stmt, sk_cells; intros until copyt; intros -> HA HA8 HC ST LO0 LO SEP MI. sk_set_walk sp A HC ST. Qed.
Theorem T_sk_set_cmp_thunks_proof : T_sk_set_stmt 0xe6430 (fun v c f k => (v, f, k)).
Proof. unfold T_sk_set_stmt, sk_cells; intros until copyt; intros -> HA HA8 HC ST LO0 LO SEP MI. sk_set_walk sp A HC ST. Qed.
Theorem T_sk_set_copy_thunks_proof : T_sk_set_stmt 0xe6464 (fun v c f k => (c, f, v)).
Proof. unfold T_sk_set_stmt, sk_cells; intros until copyt; intros -> HA HA8 HC ST LO0 LO SEP MI. sk_set_walk sp A HC ST. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_SK_NEW_NULL : Z := 0xe60d4.
Definition SK_NEW_STACK : Z := 16 + CZ_STACK.

Definition sk_new_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists p A, v = Z_to_bv 64 A /\ LBall' = (p, A, 56) :: LBall /\ L' = (p, 56) :: L /\ rblock_range A 56
     /\ rw_cells usegs m' A (sk_cells z64 z64 z64 (Z_to_bv 64 1) z64 z64 z64 z64 z64).

Definition T_sk_new_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (1 <= f)%nat -> croom L (wA 56) (wB 56) (wBig 56) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SK_NEW_STACK ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_SK_NEW_NULL) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [] 1 (wA 56) (wB 56) (wBig 56)
                (sk_new_res LBall L)).

Theorem T_sk_new_null_spec : crypto_zalloc_stmt -> T_sk_new_null_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         Hf ROOM CST SLO.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold SK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_SK_NEW_NULL, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 16%nat ST. do 3 step. do 5 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -16)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CZ with (n := 56); [exact Hf| exact ROOM| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (p & A & -> & -> & -> & RNG & BLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ m0 (bv_unsigned sp + -16) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A0 & A16 & _ & AC & AIMG).
  change (Z.to_nat 56) with 56%nat in BLK.
  apply (th_cells_congr usegs m1 A _ (sk_cells z64 z64 z64 z64 z64 z64 z64 z64 z64)) in BLK; [| reflexivity | reflexivity | cbn; tauto].
  unfold sk_cells in BLK.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 56)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. step. ubs_if. ths. ths. ths. do 2 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 A), m2, ((p, A, 56) :: LBall).
  assert (INB : In (p, A, 56) ((p, A, 56) :: LBall)) by (left; reflexivity).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 56)]%Z _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp));
           [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption | exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (p, A, 56)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (p, A, 56)); [exact INB| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    destruct FR0 as (_ & KP0 & _). destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  exists p, A. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_SK_RESERVE : Z := 0xe621c.
Definition SK_RESERVE_STACK : Z := 48 + CZ_STACK.

Definition sk_reserve_res (A : Z) (pad srt comp cmpt freet copyt : word) (LBall : list block) (L : @clist bptr)
    : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pd D, v = Z_to_bv 64 1 /\ LBall' = (pd, D, 32) :: LBall /\ L' = (pd, 32) :: L /\ rblock_range D 32
     /\ rw_cells usegs m' A (sk_cells z64 pad (Z_to_bv 64 D) srt (Z_to_bv 64 4) comp cmpt freet copyt)
     /\ rw_cells usegs m' D [CB 32 (zeros 32)].

Definition T_sk_reserve_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (psk : bptr) (A : Z)
         (pad srt nalloc comp cmpt freet copyt : word),
  (1 <= f)%nat -> croom L (wA 32) (wB 32) (wBig 32) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SK_RESERVE_STACK ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 1 ->
  In (psk, A, 56) LBall -> rw_cells usegs m A (sk_cells z64 pad z64 srt nalloc comp cmpt freet copyt) ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_SK_RESERVE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (eq psk) [] 1 (wA 32) (wB 32) (wBig 32)
                (sk_reserve_res A pad srt comp cmpt freet copyt LBall L)).

Theorem T_sk_reserve_first_spec : crypto_calloc_stmt -> T_sk_reserve_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B psk A
         pad srt nalloc comp cmpt freet copyt Hf ROOM CST SLO -> -> INSK HC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INSK) as (A0 & A16 & _ & AC & AIMG).
  unfold SK_RESERVE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_SK_RESERVE, GLOBALS_TOP, sk_cells in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 48%nat ST. do 5 step. do 2 step.
  step. step. ubs_if.
  step. rewrite (t_sx32_small 0) by lia.
  do 4 step.
  step. th_if_lit.
  step. step. th_if_lit.
  step. step. step. th_if_lit.
  step. step. step. th_if_lit. step.
  step. step. th_if_lit.
  do 6 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq psk) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CC with (num := 4) (sz := 8); [exact Hf| exact ROOM| lia| lia| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  change (4 * 8) with 32.
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (pd & D & -> & -> & -> & RNG & BLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (psk, A, 56) CFR1 HC INSK ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HC1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (D0 & D16 & _ & DC & DIMG).
  assert (INS : In (psk, A, 56) ((pd, D, 32) :: LBall)) by (right; exact INSK).
  assert (INB : In (pd, D, 32) ((pd, D, 32) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (SEPB : A + 56 <= D \/ D + 32 <= A).
  { cbn [map] in ND1. inversion ND1 as [|hd tl NI _]; subst.
    apply (RHEAP_blocks_disjoint_proof _ _ _ (psk, A, 56) (pd, D, 32) HP1 INS INB).
    unfold blk_id. cbn [fst snd]. intros E. apply NI. rewrite <- E. exact (in_map blk_id _ _ INSK). }
  change (Z.to_nat 32) with 32%nat in BLK.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 56)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. ths. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  ths. step. step. do 5 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 1), m2, ((pd, D, 32) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 56)]%Z _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp));
           [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption | exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (psk, A, 56)); [exact INS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (psk, A, 56)); [exact INS| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 _ NT E. apply NT. unfold blk_id in E. cbn [fst snd] in E. symmetry. exact E. }
  exists pd, D. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. split; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_SK_INSERT : Z := 0xe6498.
Definition SK_INSERT_STACK : Z := 48 + SK_RESERVE_STACK.

Definition sk_push_res (A : Z) (val pad comp cmpt freet copyt : word) (LBall : list block) (L : @clist bptr)
    : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pd D, v = Z_to_bv 64 1 /\ LBall' = (pd, D, 32) :: LBall /\ L' = (pd, 32) :: L /\ rblock_range D 32
     /\ rw_cells usegs m' A (sk_cells (Z_to_bv 64 1) pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt)
     /\ rw_cells usegs m' D [C8 val; CB 24 (zeros 24)].

Definition T_sk_insert_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (psk : bptr) (A : Z)
         (pad nalloc comp cmpt freet copyt : word),
  (1 <= f)%nat -> croom L (wA 32) (wB 32) (wBig 32) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SK_INSERT_STACK ->
  a0 = Z_to_bv 64 A -> a2 = z64 ->
  In (psk, A, 56) LBall -> rw_cells usegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_SK_INSERT) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (eq psk) [] 1 (wA 32) (wB 32) (wBig 32)
                (sk_push_res A a1 pad comp cmpt freet copyt LBall L)).

Theorem T_sk_insert_first_spec : crypto_calloc_stmt -> T_sk_insert_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B psk A
         pad nalloc comp cmpt freet copyt Hf ROOM CST SLO -> -> INSK HC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INSK) as (A0 & A16 & _ & AC & AIMG).
  unfold SK_INSERT_STACK, SK_RESERVE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_SK_INSERT, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold sk_cells in HC.
  cprefix. step. carve_frame 48%nat ST. do 6 step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. step. ubs_if.
  step. step. rewrite (t_sx32_small 0) by lia.
  do 2 step. step. th_if_lit.
  do 5 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq psk) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply (T_sk_reserve_first_spec CC) with (psk := psk) (A := A);
      [exact Hf| exact ROOM| exact CSTc| rewrite unsigned_lit by lia; unfold SK_RESERVE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity| exact INSK| exact HC]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (pd & D & -> & -> & -> & RNG & HC1 & BLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (D0 & D16 & _ & DC & DIMG).
  assert (INS : In (psk, A, 56) ((pd, D, 32) :: LBall)) by (right; exact INSK).
  assert (INB : In (pd, D, 32) ((pd, D, 32) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (SEPB : A + 56 <= D \/ D + 32 <= A).
  { cbn [map] in ND1. inversion ND1 as [|hd tl NI _]; subst.
    apply (RHEAP_blocks_disjoint_proof _ _ _ (psk, A, 56) (pd, D, 32) HP1 INS INB).
    unfold blk_id. cbn [fst snd]. intros E. apply NI. rewrite <- E. exact (in_map blk_id _ _ INSK). }
  unfold sk_cells in HC1.
  apply (rw_cells_split_CB usegs _ _ [] 32%nat _ _ [8; 24]%nat) in BLK; [|reflexivity].
  cbn [mk_CB_cells app] in BLK.
  change (take 8 (zeros 32)) with (zeros 8) in BLK. change (take 24 (drop 8 (zeros 32))) with (zeros 24) in BLK.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 56); (D, D + 32)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. th_if_lit.
  step. rewrite (t_sx32_small 0) by lia. step.
  step. th_if_lit. step. th_if_lit.
  do 4 step.
  step. if_cases KP1; zify_cond KP1.
  { exfalso. rewrite (proj2 (Z.ltb_lt 0 D)), (proj2 (Z.ltb_ge D 1)) in KP1 by lia. cbv in KP1. discriminate KP1. }
  do 4 step.
  step. if_cases KP2; zify_cond KP2.
  { exfalso. rewrite Z.ltb_irrefl in KP2. cbv in KP2. discriminate KP2. }
  step. ubs_if.
  step. step. ubs_if.
  step. step. step.
  step. th_if_lit.
  step. rewrite (t_sx32_small 1) by lia. ths.
  step. th_if_lit. step. step. th_if_lit.
  step. rewrite (t_sx32_small 1) by lia.
  do 6 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 1), m2, ((pd, D, 32) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 56); (D, D + 32)]%Z _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp));
           [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption | exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (psk, A, 56)); [exact INS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pd, D, 32)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply (cseg_ok_block _ _ _ _ _ (psk, A, 56)); [exact INS| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 _ NT E. apply NT. unfold blk_id in E. cbn [fst snd] in E. symmetry. exact E.
    - apply (cseg_ok_block _ _ _ _ _ (pd, D, 32)); [exact INB| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      destruct FR0 as (_ & KP0 & _). exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  exists pd, D. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. split; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZ_SK_PUSH : Z := 0xe6c80.
Definition SK_PUSH_STACK : Z := SK_INSERT_STACK.

Definition T_sk_push_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (psk : bptr) (A : Z)
         (pad nalloc comp cmpt freet copyt : word),
  (1 <= f)%nat -> croom L (wA 32) (wB 32) (wBig 32) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SK_PUSH_STACK ->
  a0 = Z_to_bv 64 A ->
  In (psk, A, 56) LBall -> rw_cells usegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_SK_PUSH) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (eq psk) [] 1 (wA 32) (wB 32) (wBig 32)
                (sk_push_res A a1 pad comp cmpt freet copyt LBall L)).

Theorem T_sk_push_first_spec : crypto_calloc_stmt -> T_sk_push_first_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B psk A
         pad nalloc comp cmpt freet copyt Hf ROOM CST SLO -> INSK HC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INSK) as (A0 & A16 & _ & AC & AIMG).
  unfold SK_PUSH_STACK, SK_INSERT_STACK, SK_RESERVE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_SK_PUSH, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold sk_cells in HC.
  cprefix. step. carve_frame 16%nat ST. do 3 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. ubs_if.
  step. rewrite (t_sx32_small 0) by lia.
  do 2 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  do 2 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate st LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe (eq psk) [] (bv_unsigned sp) st LBall L m st LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_mono.
  { eapply (T_sk_insert_first_spec CC) with (psk := psk) (A := A);
      [exact Hf| exact ROOM| exact CSTc| unfold SK_INSERT_STACK, SK_RESERVE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity| exact INSK| exact HC]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
End WithCeiling0.
