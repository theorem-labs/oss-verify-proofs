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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_strlen. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition W1_puts_prefix_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo STR : Z) (str slack : list byte),
    a1 = Z_to_bv 64 STR -> 0 <= STR ->
    bytes_at usegs m STR (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    (- (STR + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length str) < 2 ^ 31 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 32 ->
    (STR + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= STR) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 (Z_to_bv 64 STR) (Z_to_bv 64 (Z.of_nat (length str))) a3' a4' a5' a6' a7'
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 0x1832b0) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ bytes_at usegs m' STR (str ++ Z_to_bv 8 0 :: slack))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x18357c) fc None m (seg_rom usegs)).

Theorem W1_puts_prefix_proof : W1_puts_prefix_stmt.
Proof.
  unfold W1_puts_prefix_stmt. intros until slack. intros -> HSTR SRC NONUL PAD HLEN ST LO0 LO SEP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  ths. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 5 ths. do 3 ths. ths.
  tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  ths. ths. ths. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. rewrite Z.shiftr_div_pow2 in K0 by lia. apply K0. apply Z.div_small. lia. }
  do 2 ths. do 4 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths.
  apply evt_done. do 12 eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma W1_puts_compose :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B STR : Z) (str slack : list byte)
         (T : bptr -> Prop) (W : list (Z * Z)) (EV : nat) (da db dbig : Z) (R : word -> list block -> @clist bptr -> mem -> Prop),
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - 32 ->
  a1 = Z_to_bv 64 STR -> 0 <= STR ->
  bytes_at usegs m STR (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (STR + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length str) < 2 ^ 31 ->
  (STR + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= STR) ->
  (forall (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
     munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' -> wmono usegs m m' -> cstate st LBall LB L m' sp tp lo B ->
     bytes_at usegs m' STR (str ++ Z_to_bv 8 0 :: slack) ->
     climpl f L st (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 (Z_to_bv 64 STR) (Z_to_bv 64 (Z.of_nat (length str))) a3' a4' a5' a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x1832b0) fc None m' (seg_rom usegs))
            (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m' lo B T W EV da db dbig R)) ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x18357c) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B T W EV da db dbig R).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until R. intros CST SLO -> HSTR SRC NONUL PAD HLEN SEP ARM.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. eapply evt_mono.
  { eapply (W1_puts_prefix_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo STR str slack); try first [reflexivity | eassumption | lia]. }
  cbv beta. intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & SRC').
  assert (CST' : cstate st LBall LB L m' sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m' sp sp tp lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MI'| | lia| lia| | exact ST'| exact HB].
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe T W (bv_unsigned sp) st LBall L m st LBall L m').
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_mono; [exact (ARM _ _ _ _ _ _ _ _ _ _ _ _ m' MU WM CST' SRC')|].
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
End WithCeiling0.
