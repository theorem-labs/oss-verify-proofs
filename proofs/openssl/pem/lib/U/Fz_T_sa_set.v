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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_sa.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Definition FZ_SA_SET : Z := 0xf13bc.
Definition SA_SET_STACK : Z := 96 + CZ_STACK.

Definition sa_set_fresh_res (SA : Z) (val : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists pl P, v = Z_to_bv 64 1 /\ LBall' = (pl, P, 128) :: LBall /\ L' = (pl, 128) :: L /\ rblock_range P 128
     /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 (sa_delta val z64)) (Z_to_bv 64 P))
     /\ rw_cells usegs m' P [C8 val; CB 120 (repeat (Z_to_bv 8 0) 120)].

Definition T_sa_set_fresh_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (psa : bptr) (SA : Z),
  (1 <= f)%nat -> croom L (wA 128) (wB 128) (wBig 128) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SA_SET_STACK ->
  a0 = Z_to_bv 64 SA -> a1 = z64 ->
  In (psa, SA, 32) LBall -> rw_cells usegs m SA (sa_hdr z64 z64 z64 z64 z64) ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_SA_SET) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (eq psa) [] 1 (wA 128) (wB 128) (wBig 128)
                (sa_set_fresh_res SA a2 LBall L)).

Theorem T_sa_set_fresh_spec : crypto_calloc_stmt -> T_sa_set_fresh_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B psa SA
         Hf ROOM CST SLO -> -> INSA HC.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INSA) as (SA0 & SA16 & _ & SAC & SAIMG).
  unfold SA_SET_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_SA_SET, GLOBALS_TOP, sa_hdr in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 12 ths.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 5 step.
  step. th_if_lit.
  step. step. ubs_if.
  step. rewrite (t_sx32_small 0) by lia.
  step. th_if_lit.
  do 7 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (eq psa) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  eapply climpl_seq.
  { eapply CC with (num := 16) (sz := 8); [exact Hf| exact ROOM| lia| lia| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  change (16 * 8) with 128.
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (pl & P & -> & -> & -> & RNG & BLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (psa, SA, 32) CFR1 HC INSA ltac:(intros X; exact X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HC1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (P0 & P16 & _ & PC & PIMG).
  assert (SEPB : SA + 32 <= P \/ P + 128 <= SA).
  { destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. cbn [map] in ND1. inversion ND1 as [|x l NI _]; subst.
    apply (RHEAP_blocks_disjoint_proof _ _ _ (psa, SA, 32) (pl, P, 128) HP1 ltac:(right; exact INSA) ltac:(left; reflexivity)).
    unfold blk_id. cbn [fst snd]. intros E. apply NI. rewrite <- E. exact (in_map blk_id _ _ INSA). }
  change (Z.to_nat 128) with 128%nat in BLK.
  apply (rw_cells_split_CB usegs _ _ [] 128%nat _ _ [8; 120]%nat) in BLK; [|reflexivity].
  cbn [mk_CB_cells app] in BLK.
  change (take 8 (repeat (Z_to_bv 8 0) 128)) with (repeat (Z_to_bv 8 0) 8) in BLK.
  change (take 120 (drop 8 (repeat (Z_to_bv 8 0) 128))) with (repeat (Z_to_bv 8 0) 120) in BLK.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (SA, SA + 32); (P, P + 128)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  unfold ceil_window in *.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. step. ubs_if.
  step. step. rewrite (t_sx32_small 0) by lia.
  ths. ths. ths.
  ths. th_if_lit.
  ths.
  ths. th_if_lit.
  change [C8 (Z_to_bv 64 0); CB 120 (repeat (Z_to_bv 8 0) 120)] with ([C8 (Z_to_bv 64 0)] ++ [CB 120 (repeat (Z_to_bv 8 0) 120)]) in BLK.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in BLK. destruct BLK as [SLOT REST]. cbn [cells_size csize Nat.add] in REST.
  replace (P + Z.of_nat 8) with (P + 8) in REST by lia.
  replace P with (P + 8 * 0) in SLOT by lia.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply T_sa_set_mid_proof with (SP := bv_unsigned sp) (n := 0) (NODES := P) (SA := SA) (lo := lo); th_strip_ulit
    | let ms' := fresh "ms'" in let PO := fresh "POST" in
      intros ms' PO; hnf in PO; th_strip_ulit_in PO; revert ms' PO; post_call segs mm ] end.
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. rewrite Z_to_bv_bv_unsigned.
  chere. apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  lazymatch goal with H : bv_unsigned ?tw = Z.max _ 0 |- _ => rename tw into topw; rename H into HTOP end.
  assert (ETOP : topw = Z_to_bv 64 0) by (apply bv_eq; rewrite unsigned_lit in * by lia; lia). subst topw.
  exists (Z_to_bv 64 1), m2, ((pl, P, 128) :: LBall).
  assert (INB : In (pl, P, 128) ((pl, P, 128) :: LBall)) by (left; reflexivity).
  assert (INS : In (psa, SA, 32) ((pl, P, 128) :: LBall)) by (right; exact INSA).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(bv_unsigned sp - 96, bv_unsigned sp); (SA, SA + 32); (P, P + 128)]%Z _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp));
           [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption | exact HB].
    - constructor; [| constructor; [| constructor; [| constructor]]].
      + apply cwin_stack; lia.
      + apply (cwin_block _ _ _ (psa, SA, 32)); [exact INS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (pl, P, 128)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    constructor; [| constructor; [| constructor; [| constructor]]].
    - apply cseg_ok_stack; lia.
    - apply (cseg_ok_block _ _ _ _ _ (psa, SA, 32)); [exact INS| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 _ NT E. apply NT. unfold blk_id in E. cbn [fst snd] in E. symmetry. exact E.
    - apply (cseg_ok_block _ _ _ _ _ (pl, P, 128)); [exact INB| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      destruct FR0 as (_ & KP0 & _). destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. exact (cfresh_new _ _ _ _ _ _ KP0 ND1). }
  exists pl, P. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|].
  split.
  - lazymatch goal with H : rw_cells usegs m2 SA _ |- _ => rewrite unsigned_lit, Z.add_0_l in H by lia; exact H end.
  - change [C8 a2; CB 120 (repeat (Z_to_bv 8 0) 120)] with ([C8 a2] ++ [CB 120 (repeat (Z_to_bv 8 0) 120)]).
    apply (proj2 (rw_cells_app usegs _ _ _ _)). cbn [cells_size csize Nat.add].
    replace (P + Z.of_nat 8) with (P + 8) by lia. split; [| exact REST].
    lazymatch goal with H : rw_cells usegs m2 (P + 8 * 0) _ |- _ => replace (P + 8 * 0) with P in H by lia; exact H end.
Qed.
End WithCeiling0.
