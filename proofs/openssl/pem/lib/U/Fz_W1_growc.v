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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_free Fz_M_clear_free Fz_M_clear_realloc Fz_M_secure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W1_arith. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_grow.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition FZ_GROW_CLEAN : Z := 0x116dcc.
Definition GROW_STACK : Z := 96 + CCR_STACK + CSM_STACK + CSF_STACK.
Definition grow_n (len' : Z) : Z := (len' + 3) / 3 * 4.

Lemma grow_n_bounds : forall len', 0 < len' < 1610612733 -> len' < grow_n len' < 2 ^ 31.
Proof.
  intros len' H. unfold grow_n. pose proof (Z.div_mod (len' + 3) 3 ltac:(lia)). pose proof (Z.mod_pos_bound (len' + 3) 3 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma bufmem_byte_view : forall segs m A len data max sec, (sec = 0 \/ sec = 1) ->
  rw_cells segs m A (bufmem_cells len data max (Z_to_bv 64 sec)) <-> rw_cells segs m A (bufmem_bcells len data max sec).
Proof.
  intros segs m A len data max sec SEC. unfold bufmem_cells, bufmem_bcells.
  split; intros H; destruct SEC as [-> | ->];
    (eapply th_cells_congr; [| | | exact H]; [reflexivity | reflexivity | cbn; tauto]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition grow_new_res (BM len' sec : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pd D junk', v = Z_to_bv 64 len' /\ LBall' = (pd, D, grow_n len') :: LBall /\ L' = (pd, grow_n len') :: L
     /\ rblock_range D (grow_n len')
     /\ rw_cells usegs m' BM (bufmem_cells len' D (grow_n len') (Z_to_bv 64 sec))
     /\ length junk' = Z.to_nat (grow_n len') /\ rw_cells usegs m' D [CB (Z.to_nat (grow_n len')) junk'].

Definition W1_grow_null_stmt (sec : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbm : bptr) (BM len' : Z),
  (1 <= f)%nat -> croom L (wA (grow_n len')) (wB (grow_n len')) (wBig (grow_n len')) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - GROW_STACK ->
  a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 len' -> 0 < len' < 1610612733 -> cown LBall L pbm BM 32 32 ->
  rw_cells usegs m BM (bufmem_cells 0 0 0 (Z_to_bv 64 sec)) ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_GROW_CLEAN) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (eq pbm) [] 1
                (wA (grow_n len')) (wB (grow_n len')) (wBig (grow_n len')) (grow_new_res BM len' sec LBall L)).

Theorem W1_grow_null_spec : crypto_clear_realloc_null_stmt -> W1_grow_null_stmt 0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CRN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM len' Hf ROOM CST SLO -> -> HLEN OWN BMC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (grow_n_bounds len' HLEN) as HN.
  unfold GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_GROW_CLEAN, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  apply (proj1 (bufmem_byte_view usegs m BM 0 0 0 0 ltac:(left; reflexivity))) in BMC. unfold bufmem_bcells in BMC.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 48%nat ST. do 6 step.
  step. ubs_if. step. step. step. ubs_if. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 2 step.
  step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 11 step.
  rewrite (t_grow_n (len' + 3)) by lia. fold (grow_n len').
  step. th_if_lit.
  do 6 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq pbm) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CRN with (num := grow_n len'); [exact Hf| exact ROOM| lia| exact CSTc
      | rewrite unsigned_lit by lia; unfold CCR_STACK, CCF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; lia| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (pd & D & jnew & -> & -> & -> & RNG & NEW)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbm, BM, 32) CFR1 BMC (proj1 OWN) ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BMC1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (D0 & _ & _ & DCe & DIMG).
  pose proof (rw_cells_CB_length usegs m1 D _ _ NEW) as LJ.
  assert (INPD : In (pd, D, grow_n len') ((pd, D, grow_n len') :: LBall)) by (left; reflexivity).
  assert (INBM : In (pbm, BM, 32) ((pd, D, grow_n len') :: LBall)) by (right; exact (proj1 OWN)).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INPD INBM
                ltac:(intros E; eapply cstate_head_fresh; [exact CST1| exact (proj1 OWN)| symmetry; exact E])) as APDM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + grow_n len'); (BM, BM + 24)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  pose proof W1_grow_tail_proof as TAIL. unfold W1_grow_tail_stmt, bufmem_bcells in TAIL.
  tcall (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp) BM D 0 0 0 (grow_n len') len' 0 jnew).
  all: try first [eassumption | lia].
  clear TAIL. cbv beta delta [mkR]. rewrite Z_to_bv_bv_unsigned.
  chere. apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 len'), m2, ((pd, D, grow_n len') :: LBall).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (_ & _ & _ & _ & BMIMG).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp)); [exact CST1| eassumption| eassumption| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pd, D, grow_n len')); [exact INPD| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbm, BM, 32)); [exact INBM| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ _ X; exact X]| eassumption| eassumption| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply (cseg_ok_block _ _ _ _ _ (pd, D, grow_n len')); [exact INPD| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      destruct FR0 as (_ & KP0 & _). destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. exact (cfresh_new _ _ _ _ _ _ KP0 ND1).
    - apply (cseg_ok_block _ _ _ _ _ (pbm, BM, 32)); [exact INBM| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 _ NT E. apply NT. unfold blk_id in E. cbn [fst snd] in E. symmetry. exact E. }
  lazymatch goal with Hj : length ?jj = Z.to_nat (grow_n len') |- _ => exists pd, D, jj end.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|].
  split; [apply (proj2 (bufmem_byte_view usegs m2 BM len' D (grow_n len') 0 ltac:(left; reflexivity))); unfold bufmem_bcells; eassumption|].
  split; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition grow_re_res (BM len' sec : Z) (pd : bptr) (nm : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q D' junk' i, v = Z_to_bv 64 len' /\ LBall' = (q, D', grow_n len') :: lb_remove pd LBall
     /\ nth_error L i = Some (pd, nm) /\ L' = (q, grow_n len') :: cremove i L
     /\ rblock_range D' (grow_n len')
     /\ rw_cells usegs m' BM (bufmem_cells len' D' (grow_n len') (Z_to_bv 64 sec))
     /\ length junk' = Z.to_nat (grow_n len') /\ rw_cells usegs m' D' [CB (Z.to_nat (grow_n len')) junk'].

Definition W1_grow_re_stmt (sec : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbm : bptr) (BM : Z) (pd : bptr) (D len max nm len' : Z) (junk : list byte),
  (2 <= f)%nat -> croom L (wA (grow_n len')) (wB (grow_n len')) (wBig (grow_n len')) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - GROW_STACK ->
  a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 len' -> len' < 1610612733 -> cown LBall L pbm BM 32 32 ->
  cown LBall L pd D max nm -> pbm <> pd -> 0 <= len <= max -> 0 < max -> max < len' ->
  rw_cells usegs m BM (bufmem_cells len D max (Z_to_bv 64 sec)) -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_GROW_CLEAN) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun q => q = pbm \/ q = pd) [] 2
                (wA (grow_n len')) (wB (grow_n len')) (wBig (grow_n len')) (grow_re_res BM len' sec pd nm LBall L)).

Theorem W1_grow_re_spec : crypto_clear_realloc_grow_stmt -> W1_grow_re_stmt 0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CRG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM pd D len max nm len' junk Hf ROOM CST SLO -> -> HLIM OWN OWND NEQ HLEN HMAX0 HMAX BMC DBLK.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & _ & _ & DCe & _).
  pose proof (grow_n_bounds len' ltac:(lia)) as HN.
  unfold GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_GROW_CLEAN, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  apply (proj1 (bufmem_byte_view usegs m BM len D max 0 ltac:(left; reflexivity))) in BMC. unfold bufmem_bcells in BMC.
  cprefix. step. carve_frame 48%nat ST. do 6 step.
  step. ubs_if. step. step. step. ubs_if. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 2 step.
  step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 11 step.
  rewrite (t_grow_n (len' + 3)) by lia. fold (grow_n len').
  step. th_if_lit.
  do 6 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun q => q = pbm \/ q = pd) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply CRG with (p := pd) (A := D) (n := max) (nm := nm) (old := max) (num := grow_n len') (src := junk);
      [exact Hf| exact ROOM| exact OWND| lia| lia| eassumption| exact CSTc
      | rewrite unsigned_lit by lia; unfold CCR_STACK, CCF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; lia| reflexivity| reflexivity| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & D' & tail & i & -> & -> & HI & -> & RNG & NEW)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  lazymatch goal with BMh : rw_cells _ m0 BM _ |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbm, BM, 32) CFR1 BMh (proj1 OWN) ltac:(unfold blk_id; cbn [fst snd]; intros E; apply NEQ; symmetry; exact E)
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BMC1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (D'0 & _ & _ & D'Ce & D'IMG).
  pose proof (rw_cells_CB_length usegs m1 D' _ _ NEW) as LJ.
  assert (INPD : In (q, D', grow_n len') ((q, D', grow_n len') :: lb_remove pd LBall)) by (left; reflexivity).
  assert (INBM0 : In (pbm, BM, 32) (lb_remove pd LBall)) by (apply lb_remove_In; split; [exact (proj1 OWN)| unfold blk_id; cbn [fst snd]; exact NEQ]).
  assert (INBM : In (pbm, BM, 32) ((q, D', grow_n len') :: lb_remove pd LBall)) by (right; exact INBM0).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INPD INBM
                ltac:(intros E; eapply cstate_head_fresh; [exact CST1| exact INBM0| symmetry; exact E])) as APDM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (D', D' + grow_n len'); (BM, BM + 24)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  pose proof W1_grow_tail_proof as TAIL. unfold W1_grow_tail_stmt, bufmem_bcells in TAIL.
  tcall (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp) BM D' len D max (grow_n len') len' 0 (junk ++ tail)).
  all: try first [eassumption | lia].
  clear TAIL. cbv beta delta [mkR]. rewrite Z_to_bv_bv_unsigned.
  chere. apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 len'), m2, ((q, D', grow_n len') :: lb_remove pd LBall).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (_ & _ & _ & _ & BMIMG).
  assert (WNM : 0 <= wA nm /\ 0 <= wB nm /\ 0 <= wBig nm).
  { unfold wA, wB, wBig, TIER_A_MAX. destruct (nm <=? 236) eqn:E1; destruct (236 <? nm) eqn:E2; try apply Z.ltb_lt in E2; lia. }
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|].
  split. { eapply cgrow_weaken; [exact GR1| lia| lia| lia]. }
  split. { eapply (cstate_seg _ _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp)); [exact CST1| eassumption| eassumption| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (q, D', grow_n len')); [exact INPD| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbm, BM, 32)); [exact INBM| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ NT E; apply NT; right; symmetry; exact E]
                              | eassumption| eassumption| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply (cseg_ok_block _ _ _ _ _ (q, D', grow_n len')); [exact INPD| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 NT E. destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
      apply (t_nodup_prefix blk_id [(q, D', grow_n len')] (lb_remove pd LBall) (q, D', grow_n len') ND1 ltac:(left; reflexivity)).
      rewrite <- E. apply in_map. apply lb_remove_In. split; [exact Hb0|]. intros X. apply NT. right. exact X.
    - apply (cseg_ok_block _ _ _ _ _ (pbm, BM, 32)); [exact INBM| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 _ NT E. apply NT. left. exact E. }
  lazymatch goal with Hj : length ?jj = Z.to_nat (grow_n len') |- _ => exists q, D', jj, i end.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HI|]. split; [reflexivity|]. split; [exact RNG|].
  split; [apply (proj2 (bufmem_byte_view usegs m2 BM len' D' (grow_n len') 0 ltac:(left; reflexivity))); unfold bufmem_bcells; eassumption|].
  split; eassumption.
Qed.
End WithCeiling0.
