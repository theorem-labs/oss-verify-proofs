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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memcpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W1_arith. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_grow Fz_W1_growc.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition FZ_SEC_REALLOC : Z := 0x116d1c.
Definition SEC_REALLOC_STACK : Z := 48 + CSM_STACK + CSF_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W1_secre_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbm : bptr) (BM n len max sec : Z),
  (1 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 < n < 2 ^ 31 ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SEC_REALLOC_STACK ->
  a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 n -> In (pbm, BM, 32) LBall ->
  rw_cells usegs m BM (bufmem_bcells len 0 max sec) ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_SEC_REALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n)
                (cs_malloc_res n LBall L)).

Theorem W1_secre_null_spec : crypto_secure_malloc_stmt -> W1_secre_null_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CSM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM n len max sec Hf ROOM HN CST SLO -> -> INBM BMC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INBM) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  unfold SEC_REALLOC_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_SEC_REALLOC, GLOBALS_TOP, bufmem_bcells in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 48%nat ST. do 7 step. do 7 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
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
  { eapply CSM with (n := n); [exact Hf| exact ROOM| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CSM_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (p & A & jnew & -> & -> & -> & RNG & NEW)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbm, BM, 32) CFR1 BMC INBM ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BMC1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. step. ubs_if. step. step. step. th_if_lit. step. do 6 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  exists (Z_to_bv 64 A), m1, ((p, A, n) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 m1 _ sp tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  exists p, A, jnew. auto 6.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition secre_res (BM len max sec : Z) (pd : bptr) (nm n : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q A' jk i, v = Z_to_bv 64 A' /\ LBall' = (q, A', n) :: lb_remove pd LBall
     /\ nth_error L i = Some (pd, nm) /\ L' = (q, n) :: cremove i L /\ rblock_range A' n
     /\ length jk = Z.to_nat n /\ rw_cells usegs m' A' [CB (Z.to_nat n) jk] /\ rw_cells usegs m' BM (bufmem_bcells len 0 max sec).

Definition W1_secre_re_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (pbm : bptr) (BM : Z) (pd : bptr) (D n len max nm sec : Z) (junk : list byte),
  (2 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> max < n -> n < 2 ^ 31 ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SEC_REALLOC_STACK ->
  a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 n ->
  cown LBall L pbm BM 32 32 -> cown LBall L pd D max nm -> pbm <> pd -> 0 <= len <= max ->
  rw_cells usegs m BM (bufmem_bcells len D max sec) -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_SEC_REALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun q => q = pbm \/ q = pd) [] 2 (wA n) (wB n) (wBig n)
                (secre_res BM len max sec pd nm n LBall L)).

Theorem W1_secre_re_spec : crypto_secure_malloc_stmt -> crypto_secure_clear_free_stmt -> W1_secre_re_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CSM CSCF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM pd D n len max nm sec junk Hf ROOM HMN HN CST SLO -> -> OWN OWND NEQ HLEN BMC DBLK.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & _ & _ & DCe & _).
  unfold SEC_REALLOC_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_SEC_REALLOC, GLOBALS_TOP, bufmem_bcells in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 48%nat ST. do 7 step. do 7 step. chere.
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
  { eapply CSM with (n := n); [lia| exact ROOM| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CSM_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & A' & jnew & -> & -> & -> & RNG & NEW)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbm, BM, 32) CFR1 BMC (proj1 OWN) ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BMC1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pd, D, max) CFR1 DBLK (proj1 OWND) ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as DBLK1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A'0 & _ & _ & A'Ce & A'IMG).
  pose proof (rw_cells_CB_length usegs m1 A' _ _ NEW) as LJN.
  pose proof (rw_cells_CB_length usegs m1 D _ _ DBLK1) as LJ.
  assert (INQ : In (q, A', n) ((q, A', n) :: LBall)) by (left; reflexivity).
  assert (NEQD : pd <> q) by (eapply cstate_head_fresh; [exact CST1| exact (proj1 OWND)]).
  assert (NEQM : pbm <> q) by (eapply cstate_head_fresh; [exact CST1| exact (proj1 OWN)]).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (or_intror (proj1 OWND)) INQ NEQD) as APDQ.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (or_intror (proj1 OWN)) INQ NEQM) as APMQ.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN) (proj1 OWND) NEQ) as APMD.
  (* [comment removed for export] *)
  destruct (rw_cells_CB_split_at usegs m1 D (Z.to_nat max) junk (Z.to_nat len) ltac:(lia) DBLK1) as [DA DB].
  destruct (rw_cells_CB_split_at usegs m1 A' (Z.to_nat n) jnew (Z.to_nat len) ltac:(lia) NEW) as [NA NB].
  rewrite Z2Nat.id in DB, NB by lia. clear DBLK1 NEW.
  pose proof (rw_cells_bytes_at usegs m1 D _ DA) as SRC. cbn [cells_bytes cbytes] in SRC. rewrite app_nil_r in SRC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A', A' + len)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. step. ubs_if. step. step. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  do 4 step. step.
  tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (firstn (Z.to_nat len) junk) (firstn (Z.to_nat len) jnew)).
  all: try first [eassumption | lia | rewrite firstn_length; lia].
  cbv beta delta [mkR].
  do 5 step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma end.
  lazymatch goal with H : rw_cells usegs ma A' [CB (Z.to_nat len) _] |- _ => rename H into NAa end.
  lazymatch goal with H : stk usegs ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv usegs ma |- _ => rename H into MIa end.
  assert (CSTa : cstate st1 ((q, A', n) :: LBall) LB ((q, n) :: L) ma (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 ma _ _ tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIa| | lia| lia| | |].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (q, A', n)); [exact INQ| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact STa.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRa : cframe (fun q0 => q0 = pbm \/ q0 = pd) [] (bv_unsigned sp) st LBall L m st1 ((q, A', n) :: LBall) ((q, n) :: L) ma).
  { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (q, A', n)); [exact INQ| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
    apply (t_fresh_notin (fun q0 => q0 = pbm \/ q0 = pd)). apply (t_nodup_prefix blk_id [(q, A', n)] LBall (q, A', n) ND1). left. reflexivity. }
  eapply climpl_seq.
  { eapply CSCF with (p := pd) (A := D) (n := max) (nm := nm) (num := len) (junk := firstn (Z.to_nat len) junk);
      [lia| apply cown_cons; exact OWND| lia| eassumption| exact CSTa| rewrite unsigned_lit by lia; unfold CSF_STACK, CF_STACK, RFREE_STACK; lia| reflexivity| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (-> & i & HI & ->)).
  destruct RET2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  destruct i as [|i]; [cbn in HI; exfalso; apply NEQD; congruence|]. cbn [nth_error] in HI. cbn [cremove] in *.
  rewrite (lb_remove_cons_ne pd (q, A', n) LBall) in * by (unfold blk_id; cbn [fst]; intros E; apply NEQD; symmetry; exact E).
  pose proof FRM2 as (CFR2 & _).
  lazymatch goal with FRh : rw_cells _ ma (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRh ltac:(lia)) as FR2 end.
  assert (NQ : ~ pd = blk_id (q, A', n)) by (unfold blk_id; cbn [fst]; exact NEQD).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q, A', n) CFR2 NAa INQ NQ
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as NA2.
  lazymatch goal with H : rw_cells usegs ma (A' + len) _ |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q, A', n) CFR2 H INQ NQ
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as NB2 end.
  lazymatch goal with H : rw_cells usegs ma BM _ |- _ =>
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pbm, BM, 32) CFR2 H (or_intror (proj1 OWN)) ltac:(unfold blk_id; cbn [fst snd]; intros E; apply NEQ; symmetry; exact E)
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as BMC2 end.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (BM + 8, BM + 16)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  clear APDQ APMD.
  (* [comment removed for export] *)
  cprefix. ths. step. do 6 step.
  release_frame FR2 ST2 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  exists (Z_to_bv 64 A'), m3, ((q, A', n) :: lb_remove pd LBall).
  assert (INBM2 : In (pbm, BM, 32) ((q, A', n) :: lb_remove pd LBall)).
  { right. apply lb_remove_In. split; [exact (proj1 OWN)| unfold blk_id; cbn [fst snd]; exact NEQ]. }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (_ & _ & _ & _ & BMIMG).
  assert (WNM : 0 <= wA nm /\ 0 <= wB nm /\ 0 <= wBig nm).
  { unfold wA, wB, wBig, TIER_A_MAX. destruct (nm <=? 236) eqn:E1; destruct (236 <? nm) eqn:E2; try apply Z.ltb_lt in E2; lia. }
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split. { eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)| lia| lia| lia]. }
  split. { eapply (cstate_seg _ _ _ _ _ m2 m3 _ sp tp lo B (bv_unsigned sp)); [exact CST2| eassumption| eassumption| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbm, BM, 32)); [exact INBM2| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM2| lia| intros a X; exact X| intros q0 _ NT E; apply NT; right; symmetry; exact E]
                              | eassumption| eassumption| exact HP2| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (pbm, BM, 32)); [exact INBM2| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 _ NT E. apply NT. left. exact E. }
  exists q, A', (firstn (Z.to_nat len) junk ++ skipn (Z.to_nat len) jnew), i.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HI|]. split; [reflexivity|]. split; [exact RNG|].
  split; [rewrite length_app, firstn_length, skipn_length; lia|].
  split.
  - lazymatch goal with Ha : rw_cells usegs m3 A' [CB (Z.to_nat len) _], Hb : rw_cells usegs m3 (A' + len) _ |- _ =>
      pose proof (rw_cells_CB_join usegs m3 A' _ _ _ _ Ha ltac:(rewrite Z2Nat.id by lia; exact Hb)) as J end.
    replace (Z.to_nat len + (Z.to_nat n - Z.to_nat len))%nat with (Z.to_nat n) in J by lia. exact J.
  - eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem W1_grow_null_sec_spec : crypto_secure_malloc_stmt -> W1_grow_null_stmt 1.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CSM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM len' Hf ROOM CST SLO -> -> HLEN OWN BMC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (grow_n_bounds len' HLEN) as HN.
  unfold GROW_STACK, SEC_REALLOC_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_GROW_CLEAN, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  apply (proj1 (bufmem_byte_view usegs m BM 0 0 0 1 ltac:(right; reflexivity))) in BMC. unfold bufmem_bcells in BMC.
  cprefix. step. carve_frame 48%nat ST. do 6 step.
  step. ubs_if. step. step. step. ubs_if. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 2 step.
  step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 11 step.
  rewrite (t_grow_n (len' + 3)) by lia. fold (grow_n len').
  step. th_if_lit.
  do 3 step. chere.
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
  { eapply (W1_secre_null_spec CSM) with (pbm := pbm) (BM := BM) (n := grow_n len') (len := 0) (max := 0) (sec := 1);
      [exact Hf| exact ROOM| lia| exact CSTc
      | rewrite unsigned_lit by lia; unfold SEC_REALLOC_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; lia| reflexivity| reflexivity
      | exact (proj1 OWN)| unfold bufmem_bcells; eassumption]. }
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
  cprefix. step. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  pose proof W1_grow_tail_proof as TAIL. unfold W1_grow_tail_stmt, bufmem_bcells in TAIL.
  tcall (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp) BM D 0 0 0 (grow_n len') len' 1 jnew).
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
  split; [apply (proj2 (bufmem_byte_view usegs m2 BM len' D (grow_n len') 1 ltac:(right; reflexivity))); unfold bufmem_bcells; eassumption|].
  split; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem W1_grow_re_sec_spec : crypto_secure_malloc_stmt -> crypto_secure_clear_free_stmt -> W1_grow_re_stmt 1.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CSM CSCF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         pbm BM pd D len max nm len' junk Hf ROOM CST SLO -> -> HLIM OWN OWND NEQ HLEN HMAX0 HMAX BMC DBLK.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (BM0 & BM16 & _ & BMCe & _). assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & _ & _ & DCe & _).
  pose proof (grow_n_bounds len' ltac:(lia)) as HN.
  unfold GROW_STACK, SEC_REALLOC_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK, FZ_GROW_CLEAN, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  apply (proj1 (bufmem_byte_view usegs m BM len D max 1 ltac:(right; reflexivity))) in BMC. unfold bufmem_bcells in BMC.
  cprefix. step. carve_frame 48%nat ST. do 6 step.
  step. ubs_if. step. step. step. ubs_if. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 2 step.
  step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 11 step.
  rewrite (t_grow_n (len' + 3)) by lia. fold (grow_n len').
  step. th_if_lit.
  do 3 step. chere.
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
  { eapply (W1_secre_re_spec CSM CSCF) with (pbm := pbm) (BM := BM) (pd := pd) (D := D) (n := grow_n len') (len := len) (max := max) (nm := nm) (sec := 1) (junk := junk);
      [exact Hf| exact ROOM| lia| lia| exact CSTc
      | rewrite unsigned_lit by lia; unfold SEC_REALLOC_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; lia| reflexivity| reflexivity
      | exact OWN| exact OWND| exact NEQ| exact HLEN| unfold bufmem_bcells; eassumption| eassumption]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & D' & jnew & i & -> & -> & HI & -> & RNG & LJ & NEW & BMC1)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (D'0 & _ & _ & D'Ce & D'IMG).
  unfold bufmem_bcells in BMC1.
  assert (INPD : In (q, D', grow_n len') ((q, D', grow_n len') :: lb_remove pd LBall)) by (left; reflexivity).
  assert (INBM0 : In (pbm, BM, 32) (lb_remove pd LBall)) by (apply lb_remove_In; split; [exact (proj1 OWN)| unfold blk_id; cbn [fst snd]; exact NEQ]).
  assert (INBM : In (pbm, BM, 32) ((q, D', grow_n len') :: lb_remove pd LBall)) by (right; exact INBM0).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 INPD INBM
                ltac:(intros E; eapply cstate_head_fresh; [exact CST1| exact INBM0| symmetry; exact E])) as APDM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (D', D' + grow_n len'); (BM, BM + 24)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  pose proof W1_grow_tail_proof as TAIL. unfold W1_grow_tail_stmt, bufmem_bcells in TAIL.
  tcall (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp) BM D' len 0 max (grow_n len') len' 1 jnew).
  all: try first [eassumption | lia].
  clear TAIL. cbv beta delta [mkR]. rewrite Z_to_bv_bv_unsigned.
  chere. apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 len'), m2, ((q, D', grow_n len') :: lb_remove pd LBall).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWN)) as (_ & _ & _ & _ & BMIMG).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|]. split; [exact GR1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp)); [exact CST1| eassumption| eassumption| eassumption| | lia| lia| | eassumption| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (q, D', grow_n len')); [exact INPD| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pbm, BM, 32)); [exact INBM| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ NT X; apply NT; exact X]
                              | eassumption| eassumption| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply (cseg_ok_block _ _ _ _ _ (q, D', grow_n len')); [exact INPD| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 NT E. destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
      apply (t_nodup_prefix blk_id [(q, D', grow_n len')] (lb_remove pd LBall) (q, D', grow_n len') ND1 ltac:(left; reflexivity)).
      rewrite <- E. apply in_map. apply lb_remove_In. split; [exact Hb0|]. intros X. apply NT. right. exact X.
    - apply (cseg_ok_block _ _ _ _ _ (pbm, BM, 32)); [exact INBM| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 _ NT E. apply NT. left. exact E. }
  lazymatch goal with Hj : length ?jj = Z.to_nat (grow_n len'), Hc : rw_cells usegs m2 D' [CB _ ?jj] |- _ => exists q, D', jj, i end.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HI|]. split; [reflexivity|]. split; [exact RNG|].
  split; [apply (proj2 (bufmem_byte_view usegs m2 BM len' D' (grow_n len') 1 ltac:(right; reflexivity))); unfold bufmem_bcells; eassumption|].
  split; eassumption.
Qed.
End WithCeiling0.
