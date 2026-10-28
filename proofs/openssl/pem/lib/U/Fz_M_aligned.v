(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_impl RF_aligned_frame RF_aligned_spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_kit_ra.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_ALIGNED_ALLOC : Z := 0xe9278.
Definition CAA_STACK : Z := 64 + RMEMALIGN_STACK.

Lemma rw_cells_CB8_word : forall m A bs, rw_cells usegs m A [CB 8 bs] -> rw_cells usegs m A [C8 (le_bytes_to_word bs)].
Proof.
  intros m A bs H. pose proof (rw_cells_CB_length usegs m A _ _ H) as LEN.
  eapply rw_cells_recast; [exact H| cbn; auto| | reflexivity]. cbn [cells_bytes cbytes]. rewrite le8_le_bytes_to_word by exact LEN. reflexivity.
Qed.

(* [comment removed for export] *)
Definition bkeep (Af nf FP : Z) (m m' : mem) : Prop := agree_on (fun a => Af <= a < Af + nf /\ (a + 1 <= FP \/ FP + 8 <= a)) m m'.
Lemma bkeep_cells : forall Af nf FP m m' A cs, bkeep Af nf FP m m' -> rw_cells usegs m A cs -> Af <= A -> A + Z.of_nat (cells_size cs) <= Af + nf ->
  (A + Z.of_nat (cells_size cs) <= FP \/ FP + 8 <= A) -> rw_cells usegs m' A cs.
Proof. intros Af nf FP m m' A cs H C H1 H2 H3. eapply rw_cells_agree; [exact H| exact C|]. intros a Ha. cbv beta. lia. Qed.

Definition cs_aligned_res (len FP Af nf : Z) (LBall : list block) (L : @clist bptr) (m : mem) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists p A' junk, v = Z_to_bv 64 A' /\ LBall' = (p, A', len) :: LBall /\ L' = (p, len + 48) :: L
      /\ rblock_range A' len /\ A' mod 64 = 0 /\ rw_cells usegs m' A' [CB (Z.to_nat len) junk] /\ rw_cells usegs m' FP [C8 (Z_to_bv 64 A')]
      /\ bkeep Af nf FP m m'.

Definition crypto_aligned_alloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat)
         (pf : bptr) (Af nf nmf FP len lo B : Z) (oldfp : word),
  (1 <= f)%nat -> croom L (wA (len + 48)) (wB (len + 48)) (wBig (len + 48)) -> 0 < len -> len + 48 < MMAP_THRESHOLD ->
  cown LBall L pf Af nf nmf -> Af <= FP -> FP + 8 <= Af + nf -> FP mod 8 = 0 -> rw_cells usegs m FP [C8 oldfp] ->
  rw_cells usegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CAA_STACK ->
  a0 = Z_to_bv 64 len -> a1 = Z_to_bv 64 64 -> a2 = Z_to_bv 64 FP ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_ALIGNED_ALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq pf) [] 1
                (wA (len + 48)) (wB (len + 48)) (wBig (len + 48)) (cs_aligned_res len FP Af nf LBall L m)).

Theorem crypto_aligned_alloc_spec : rmemalign_prefix_stmt -> rmalloc_impl_stmt2 -> rmemalign_tail_stmt -> crypto_aligned_alloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros PRE MAL2 TAILS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f pf Af nf nmf FP len lo B oldfp
         Hf ROOM LEN0 LTH OWNf FP1 FP2 FPA FPC REPL CST SLO A0 A1 A2. subst a0 a1 a2.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & (_ & _ & GOTM & IMPL & _ & _) & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNf)) as (FA0 & _ & FN0 & FAC & FAIMG).
  unfold CAA_STACK, RMEMALIGN_STACK, RMALLOC_STACK, MMAP_THRESHOLD, FZ_ALIGNED_ALLOC, GLOBALS_TOP, LX_GOT_FLAGS, LX_STORAGE_FN, FZ_CRYPTO_MALLOC, RMALLOC_REPLACED in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (FP, FP + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  cprefix. step. carve_frame 64%nat ST. do 8 step.
  step. if_cases KF0; zify_cond KF0. { exfalso. rewrite ?unsigned_lit in KF0 by lia. lia. }
  do 3 step.
  step. rewrite (unsigned_lit FP) by lia. rewrite (ubs_land7 FP) by exact FPA. if_cases KF1; zify_cond KF1. { exfalso. apply KF1. reflexivity. }
  do 3 step.
  (* [comment removed for export] *)
  cstep.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 19 step.
  (* [comment removed for export] *)
  do 2 step.
  step. if_cases K2. { exfalso. vm_compute in K2. discriminate K2. }
  (* [comment removed for export] *)
  do 4 step.
  step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. }
  step.
  step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  do 4 step. chere. clear K2.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma end.
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -64) (CB 8 ?jj :: ?rest) |- _ =>
    change (CB 8 jj :: rest) with ([CB 8 jj] ++ rest) in FRh; apply (proj1 (rw_cells_app usegs ma _ _ _)) in FRh; destruct FRh as [FRres FRrest];
    apply rw_cells_CB8_word in FRres; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRrest end.
  replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FRrest by lia.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ s LBall LB L m ma sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - constructor; [apply cwin_stack; lia| constructor; [| constructor]].
      apply (cwin_block _ _ _ (pf, Af, nf)); [exact (proj1 OWNf)| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq pf) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
    apply (cseg_ok_block _ _ _ _ _ (pf, Af, nf)); [exact (proj1 OWNf)| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
    intros b0 _ NT E. apply NT. symmetry. exact E. }
  eapply climpl_seq.
  { eapply (cs_memalign PRE MAL2 TAILS) with (len := len) (res := bv_unsigned sp + -64);
      [exact Hf| exact ROOM| lia| unfold MMAP_THRESHOLD; lia| exact CSTa| rewrite unsigned_lit by lia; unfold RMEMALIGN_STACK, RMALLOC_STACK; lia
      | unfold RMALLOC_REPLACED; exact REPL| exact FRres| rewrite unsigned_lit by lia; lia| lia| reflexivity| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m2 & LB1 & RET & FU & GR & CST1 & FRM1 & (p & A' & jk & -> & -> & -> & RNG & AL & NEW & RESC)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRrest ltac:(lia)) as FRrest1.
  lazymatch goal with FPh : rw_cells _ ma FP _ |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pf, Af, nf) CFR1 FPh (proj1 OWNf) (fun X => X)
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as FPC1 end.
  lazymatch type of FRrest1 with rw_cells _ _ _ ?rest =>
    assert (FR1 : rw_cells usegs m2 (bv_unsigned sp + -64) ([C8 (Z_to_bv 64 A')] ++ rest))
      by (apply rw_cells_app; split; [exact RESC|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) by lia; exact FRrest1) end.
  cbn [app] in FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A'0 & _ & _ & A'C & A'IMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (PPF : p <> pf).
  { intros E. cbn [map blk_id fst] in ND1. inversion ND1 as [|x l NI _]; subst. apply NI. apply in_map_iff. exists (pf, Af, nf). split; [reflexivity| exact (proj1 OWNf)]. }
  assert (APART : Af + nf <= A' \/ A' + len <= Af).
  { pose proof (RHEAP_blocks_disjoint_proof _ _ _ (pf, Af, nf) (p, A', len) HP1 (or_intror (proj1 OWNf)) (or_introl eq_refl)) as D.
    unfold blk_id, blk_addr, blk_size in D. cbn [fst snd] in D. apply D. intros E. apply PPF. symmetry. exact E. }
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (FP, FP + 8)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. step. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  step. cstep. do 10 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  chere. apply climpl_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => rename mc into mz end.
  exists (Z_to_bv 64 A'), mz, ((p, A', len) :: LBall).
  assert (INF : In (pf, Af, nf) ((p, A', len) :: LBall)) by (right; exact (proj1 OWNf)).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg _ _ _ _ _ m2 mz _ sp tp lo B (bv_unsigned sp)); [exact CST1| exact MU2| exact WM2| eassumption| | lia| lia| | exact ST1| exact HB].
    - constructor; [apply cwin_stack; lia| constructor; [| constructor]].
      apply (cwin_block _ _ _ (pf, Af, nf)); [exact INF| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ _ X; exact X]| exact MU2| exact WM2| exact HP1| lia|].
    constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
    apply (cseg_ok_block _ _ _ _ _ (pf, Af, nf)); [exact INF| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
    intros b0 _ NT E. apply NT. symmetry. exact E. }
  exists p, A', jk. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. split; [exact AL|].
  split; [eassumption|]. split; [eassumption|].
  eapply agree_on_trans; [eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)| intros a Ha; cbv beta in Ha; cbn [outside]; lia]|].
  eapply agree_on_trans; [eapply agree_on_mono; [exact CFR1|]|].
  { intros a Ha. cbv beta in Ha. right; left. exists (pf, Af, nf). split; [exact (proj1 OWNf)|]. split; [intros X; exact X|]. unfold blk_addr, blk_size; cbn [fst snd]. lia. }
  eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU2 WM2)| intros a Ha; cbv beta in Ha; cbn [outside]; lia].
Qed.

(* [comment removed for export] *)
Definition FZ_ALIGNED_ALLOC_ARRAY : Z := 0xe7204.

Definition crypto_aligned_alloc_array_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat)
         (pf : bptr) (Af nf nmf FP num sz lo B : Z) (oldfp : word),
  (1 <= f)%nat -> croom L (wA (num * sz + 48)) (wB (num * sz + 48)) (wBig (num * sz + 48)) ->
  0 <= num < 2^32 -> 0 <= sz < 2^32 -> 0 < num * sz -> num * sz + 48 < MMAP_THRESHOLD ->
  cown LBall L pf Af nf nmf -> Af <= FP -> FP + 8 <= Af + nf -> FP mod 8 = 0 -> rw_cells usegs m FP [C8 oldfp] ->
  rw_cells usegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CAA_STACK ->
  a0 = Z_to_bv 64 num -> a1 = Z_to_bv 64 sz -> a2 = Z_to_bv 64 64 -> a3 = Z_to_bv 64 FP ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_ALIGNED_ALLOC_ARRAY) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq pf) [] 1
                (wA (num * sz + 48)) (wB (num * sz + 48)) (wBig (num * sz + 48)) (cs_aligned_res (num * sz) FP Af nf LBall L m)).

Theorem crypto_aligned_alloc_array_spec : crypto_aligned_alloc_stmt -> crypto_aligned_alloc_array_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CAA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f pf Af nf nmf FP num sz lo B oldfp
         Hf ROOM NUM SZ N0 LTH OWNf FP1 FP2 FPA FPC REPL CST SLO A0 A1 A2 A3. subst a0 a1 a2 a3.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNf)) as (FA0 & _ & FN0 & FAC & FAIMG).
  unfold CAA_STACK, RMEMALIGN_STACK, RMALLOC_STACK, MMAP_THRESHOLD, FZ_ALIGNED_ALLOC_ARRAY, GLOBALS_TOP, RMALLOC_REPLACED in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MH : (bv_unsigned (Z_to_bv 64 num) * bv_unsigned (Z_to_bv 64 sz)) ≫ 64 = 0).
  { rewrite !unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
  cprefix. step. carve_frame 48%nat ST. do 10 step.
  step. rewrite MH. if_true.
  do 12 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate s LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (eq pf) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  unfold crypto_aligned_alloc_stmt in CAA.
  eapply climpl_mono.
  { eapply CAA with (pf := pf) (Af := Af) (nf := nf) (nmf := nmf) (FP := FP) (len := num * sz) (oldfp := oldfp);
      [exact Hf| exact ROOM| lia| unfold MMAP_THRESHOLD; lia| exact OWNf| exact FP1| exact FP2| exact FPA| eassumption| unfold RMALLOC_REPLACED; eassumption| exact CSTc
      | unfold CAA_STACK, RMEMALIGN_STACK, RMALLOC_STACK; lia| | reflexivity| reflexivity].
    rewrite !unsigned_lit by lia. reflexivity. }
  intros f' L' s' ms' H1. pose proof (cpost_rebase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR0 (fun a X => X) (fun q _ X => X) H1)
    as (v & mz & LB1 & RET & FU & GR & CST1 & FRM1 & (p & A' & jk & E1 & E2 & E3 & RNG & AL & NEW & RESC & BK)).
  exists v, mz, LB1. split; [exact RET|]. split; [exact FU|]. split; [exact GR|]. split; [exact CST1|]. split; [exact FRM1|].
  exists p, A', jk. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact RNG|]. split; [exact AL|]. split; [exact NEW|]. split; [exact RESC|].
  eapply agree_on_trans; [eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)| intros a Ha; cbv beta in Ha; cbn [outside]; lia]| exact BK].
Qed.
End WithCeiling0.
