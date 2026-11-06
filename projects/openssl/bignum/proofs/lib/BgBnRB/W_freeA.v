(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgPlace.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitA BnCallA W_expandA PlaceKitA.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2237860 => 1
  | 2237864 => 2
  | 2238228 => 1
  | 2238232 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_FREE : Z := 0x2226f0.
Definition BN_FREE_D0_STACK : Z := 16 + CRYPTO_FREE_STACK.
Definition BN_FREE_STACK : Z := 48 + BN_FREE_D0_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma bn_free_d0_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (p : bptr) (D n f a lo : Z) (tw dw nw : word) (bs : block) (ras : list Z)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> In (p, D, n) OW ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_FREE_D0_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> tp = wz TP_A -> BnRepDefs.crypto_statics m ->
  rw_cells bgbsegs m a [C8 (wz D); C4 tw; C4 dw; C4 nw; C4 (wz f)] -> 0 <= f <= 1 ->
  In bs (OW ++ LB) -> blk_addr bs <= a -> a + 24 <= blk_addr bs + blk_size bs -> a mod 8 = 0 ->
  a0 = wz a -> a1 = wz 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FREE_D (bv_unsigned ra :: ras) ->
  (forall Σ' ms', cfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (TFree p k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_FREE_D) fc None m (seg_rom bgbsegs)).
Proof.
  intros until Q. intros HEAP IN ST CEIL LO SPT SP16 MI -> CS BN Hf INS RS1 RS2 AL -> -> UW CTX K.
  unfold BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK, BN_FREE_D, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bs HEAP INS) as (S0 & _ & _ & SC & SI).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP IN) as (D0 & _ & _ & DC & _).
  pose proof (AH_acc_in _ _ _ _ bs a 24 HEAP INS RS1 RS2) as ACC.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  apply (flag_cell_split bgbsegs m a _ _ _ _ f Hf) in BN.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 16%nat ST. do 4 step. ub. do 3 step.
  do 3 step. shl. chk0.
  assert (EL8 : Z.land f 8 = 0) by (assert (f = 0 \/ f = 1) as [-> | ->] by lia; reflexivity).
  step. rewrite (zxb_small f) by lia. step. rewrite (unsigned_lit f), EL8 by lia. step. if_false.
  step. if_true.
  do 2 step. shl. chk0.
  step.
  do 3 step.
  do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (BnIfaceA.seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  apply evt_done.
  eapply (CRYPTO_free_walkA) with (A := D) (n := n) (lo := lo) (ras := ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - exact IN.
  - exact ST.
  - exact CEIL.
  - unfold CRYPTO_FREE_STACK, RT_STACK. lia.
  - unfold USTACK_TOP. lia.
  - exact SP16.
  - exact MI.
  - eapply BnRepA.crypto_statics_agree; [exact AG1 | | exact CS]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx).
  - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor].
  - exact (uk_ctx_tail _ _ _ (E_bn_free_d_2224bc : uk_tail BN_FREE_D BnRepDefs.CRYPTO_FREE) CTX).
  - intros Σ' ms' PO. apply (K Σ' ms'). eapply cfree_postA_weaken; [| exact PO].
    eapply agree_client_weaken; [exact AG1 | lia | intros b Hb; eapply lb_remove_incl; exact Hb].
Qed.

Lemma bn_free_d0_null_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (f a lo : Z) (tw dw nw : word) (bs : block) (ras : list Z)
    (t : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_FREE_D0_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> tp = wz TP_A -> BnRepDefs.crypto_statics m ->
  rw_cells bgbsegs m a [C8 (wz 0); C4 tw; C4 dw; C4 nw; C4 (wz f)] -> 0 <= f <= 1 ->
  In bs (OW ++ LB) -> blk_addr bs <= a -> a + 24 <= blk_addr bs + blk_size bs -> a mod 8 = 0 ->
  a0 = wz a -> a1 = wz 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FREE_D (bv_unsigned ra :: ras) ->
  (forall ms', cfree_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m ms' -> implA t Σ Q ms') ->
  implA t Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_FREE_D) fc None m (seg_rom bgbsegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS BN Hf INS RS1 RS2 AL -> -> UW CTX K.
  unfold BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK, BN_FREE_D, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bs HEAP INS) as (S0 & _ & _ & SC & SI).
  pose proof (AH_acc_in _ _ _ _ bs a 24 HEAP INS RS1 RS2) as ACC.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  apply (flag_cell_split bgbsegs m a _ _ _ _ f Hf) in BN.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 16%nat ST. do 4 step. ub. do 3 step.
  do 3 step. shl. chk0.
  assert (EL8 : Z.land f 8 = 0) by (assert (f = 0 \/ f = 1) as [-> | ->] by lia; reflexivity).
  step. rewrite (zxb_small f) by lia. step. rewrite (unsigned_lit f), EL8 by lia. step. if_false.
  step. if_true.
  do 2 step. shl. chk0.
  step.
  do 3 step.
  do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (BnIfaceA.seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  apply evt_done.
  eapply implA_step_same.
  { eapply (CRYPTO_free_null_cpsA) with (lo := lo) (ras := ras) (OW := OW) (LB := LB); try reflexivity.
    - exact HEAP1.
    - exact ST.
    - exact CEIL.
    - unfold CRYPTO_FREE_STACK, RT_STACK. lia.
    - unfold USTACK_TOP. lia.
    - exact SP16.
    - exact MI.
    - eapply BnRepA.crypto_statics_agree; [exact AG1 | | exact CS]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx).
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor].
    - exact (uk_ctx_tail _ _ _ (E_bn_free_d_2224bc : uk_tail BN_FREE_D BnRepDefs.CRYPTO_FREE) CTX). }
  intros ms' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & E & MI2 & ST2 & HEAP2 & AG2).
  apply (K ms'). do 17 eexists. exists m2. split; [exact E|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact HEAP2|].
  eapply agree_on_trans; [exact AG1 | exact AG2].
Qed.

Definition lb_remove_opt (o : option bptr) (L : list block) : list block := match o with Some p => lb_remove p L | None => L end.

Lemma BN_free_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (r : bnref) (a : Z) (q : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_FREE_STACK 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FREE (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_bn PL r = Some (PHeap a q 0) -> bn_flags (getbn r ls) = BN_FLG_MALLOCED -> a0 = wz a ->
  implA (BN_free (tree_ops bptr) r (Some q) ls) Σ
    (bn_postA_p ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA 0
                (fun _ ls' OW' PL' _ => PL' = pl_set PL r None /\ ls' = setbn r (bn_nil 0) ls /\ cnt_bal ls' OW' = cnt_bal ls OW - 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_FREE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until q. intros PRE UW CTX -> E F1 ->.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND. pose proof (AH_nodup _ _ _ _ HEAP) as NDL.
  pose proof LO as LO'. unfold BN_FREE_STACK, BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK in LO'.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (pl_wf_stored PL r _ PWF E) as SR. pose proof SR as (RN & RO & RM).
  assert (EO : pl_of PL r = Some (PHeap a q 0)) by (rewrite pl_of_stored by exact SR; exact E).
  assert (HA : ref_at ls OW PL r a) by (apply ref_at_fixed; [exact RN|]; exists (PHeap a q 0); split; [exact EO| reflexivity]).
  pose proof (hpl_heap PL r a q 0 EO) as HP.
  destruct (proj1 PLB r _ RN EO) as (n & Hinq & _ & Hn). replace (a - 0) with a in Hinq by lia. unfold BN_STRUCT_SZ in Hn.
  destruct (lib_state_open [] ls m OW PL EA r a LS ND HA ltac:(intros []) RO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_unplace_bn false [] ls m OW PL EA r a q LSH ltac:(intros []) E) as (LSU & NQ & NP).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hinq) as (SA0 & SA16 & _ & SAC & SAI).
  assert (AL : a mod 8 = 0) by (clear - SA16; Z.div_mod_to_equations; lia).
  assert (FROK' : frames_ok (pl_set PL r None) (bv_unsigned sp) USTACK_TOP) by (apply frames_ok_set_none; exact FROK).
  set (b := getbn r ls) in *.
  assert (QL : In (q, a, n) (OW ++ LB)) by (apply in_or_app; left; exact Hinq).
  assert (QNLB : ~ In q (map blk_id LB)).
  { intros H. rewrite map_app in NDL. eapply (nodup_app_disj _ _ q NDL); [apply (in_map blk_id) in Hinq; exact Hinq| exact H]. }

  assert (DFACTS : forall pd, bn_d b = Some pd -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) OW /\ pd <> q /\ ~ In pd (map blk_id LB)).
  { intros pd Ed. unfold bn_arr in ARR. rewrite Ed in ARR. destruct ARR as [HinD _]. split; [exact HinD|]. split.
    - intros ->. eapply (ids_pl_m ls PL EA q q IDS); [eapply in_pl_ids_bn; [exact RN| exact E]| eapply bn_in_m; [exact HV| exact Ed]| reflexivity].
    - intros H. rewrite map_app in NDL. eapply (nodup_app_disj _ _ pd NDL); [apply (in_map blk_id) in HinD; exact HinD| exact H]. }
  assert (DNULL : bn_d b = None -> D = 0).
  { intros Ed. exact (proj1 (bn_arr_null PL r m OW D b PWF (hpl_wref PL r HP) Ed ARR)). }
  unfold BN_FREE, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_acc_in _ _ _ _ (q, a, n) a 24 HEAP QL ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - Hn; lia)) as ACC.
  pose proof (AH_offsh _ _ _ _ (q, a, n) HEAP QL) as OFA. cbn [blk_addr blk_size fst snd] in OFA. unfold SHLO, SHHI in OFA.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BN. rewrite F1 in BN. unfold BN_FLG_MALLOCED in BN.
  pose proof BN as BN0.
  apply (flag_cell_split bgbsegs m a _ _ _ _ 1 ltac:(clear; lia)) in BN.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  assert (EA0 : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - SA0 SAC Hn C1 C2 C3; lia).
  unfold BN_free, bbind, bget, bset, bret, bfree_opt, bfree, bunr, has_flag, BN_FLG_STATIC_DATA.
  cbn [bind ret unreachable lib_free tree_ops tbind fst snd]. fold b. rewrite F1. unfold BN_FLG_MALLOCED.
  change (Z.land 1 2 =? 0) with true. change (Z.land 1 1 =? 0) with false. cbn [negb]. cbv iota.
  apply implA_from_evt.
  carve_frame 48%nat ST.
  do 7 step.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA0 in KA; clear - KA SA0; lia|]. clear KA.
  step. ub. do 3 step. do 3 step. shl_with ACC AL. chk0.
  step. rewrite (zxb_small 1) by (clear; lia). step. step. if_false.
  do 2 step. step.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  assert (CS1 : BnRepDefs.crypto_statics m1).
  { eapply BnRepA.crypto_statics_agree; [exact AG1 | | exact (proj1 LS)]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -48) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 48 [CB 8 jfr; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  assert (UWm1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }

  assert (CONT : forall (Σ1 : rts RT) (m2 : mem) (OWd : list block) (FT : bvmap 5 word) (fcT : bv 32)
                        (q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
      AHEAP Σ1 OWd LB m2 -> agree_on (aclient_addr (OWd ++ LB) (bv_unsigned sp + -48)) m1 m2 ->
      OWd = lb_remove_opt (bn_d b) OW -> rt_credit RT Σ1 = rt_credit RT Σ ->
      stk bgbsegs m2 lo (bv_unsigned sp + -48) -> mem_inv bgbsegs m2 ->
      implA (TFree q (TRet (tt, setbn r (bn_nil 0) ls))) Σ1
        (bn_postA_p ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA 0
                    (fun _ ls' OW' PL' _ => PL' = pl_set PL r None /\ ls' = setbn r (bn_nil 0) ls /\ cnt_bal ls' OW' = cnt_bal ls OW - 1))
        (MS (mkR (Z_to_bv 64 2238292) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 a) q10 q11 q12 q13 q14 q15 q16 q17
                 (Z_to_bv 64 (a + 20)) (Z_to_bv 64 (Z.shiftr (a + 20) 3 + SHB)) s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 2238292) fcT None m2 (seg_rom bgbsegs))).
  { intros Σ1 m2 OWd FT fcT q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 HEAP2 AG2 EOWd CR2 ST2 MI2.
    assert (INQd : In (q, a, n) OWd).
    { rewrite EOWd. destruct (bn_d b) as [pd|] eqn:Ed; cbn [lb_remove_opt]; [|exact Hinq].
      apply lb_remove_In. split; [exact Hinq|]. cbn [blk_id fst]. intros E'. exact (proj1 (proj2 (DFACTS pd eq_refl)) (eq_sym E')). }
    assert (INCd : forall b0, In b0 OWd -> In b0 OW).
    { rewrite EOWd. destruct (bn_d b) as [pd0|]; cbn [lb_remove_opt]; [intros bk Hbk; eapply lb_remove_incl; exact Hbk | auto]. }
    assert (QLd : In (q, a, n) (OWd ++ LB)) by (apply in_or_app; left; exact INQd).
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; clear - Hx SPT; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in BN; [| intros x Hx; right; right; exists (q, a, n); split; [exact QLd| cbn in Hx |- *; clear - Hx Hn; lia]].
    clear BN0.
    pose proof (AH_acc_in _ _ _ _ (q, a, n) a 24 HEAP2 QLd ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - Hn; lia)) as ACC2.
    assert (UW2 : uw_chain USTACK_TOP m2 (bv_unsigned sp) (bv_unsigned s0) ras).
    { apply (uw_chain_agree m1 m2 ras (bv_unsigned sp) (bv_unsigned s0) UWm1). eapply agree_on_mono; [exact AG2|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
    assert (CS2 : BnRepDefs.crypto_statics m2).
    { eapply BnRepA.crypto_statics_agree; [exact AG2 | | exact CS1]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
    clear ACC MU WM OFF SHB1 SHB2 HEAP HEAP1 ST MI.
    pose proof (munch_refl (@nil (Z * Z)) m2) as MU2.
    destruct (AH_shb _ _ _ _ HEAP2) as (SHB1 & SHB2).
    apply implA_from_evt.
    shl_with ACC2 AL. chk0.
    step. rewrite (zxb_small 1) by (clear; lia). step. step. if_true.
    do 4 step.
    do 5 step. release_frame FR ST2 (bv_unsigned sp). step. step.
    apply evt_done.
    eapply (CRYPTO_free_walkA) with (A := a) (n := n) (lo := lo) (ras := ras) (OW := OWd) (LB := LB); try reflexivity.
    - exact HEAP2.
    - exact INQd.
    - exact ST2.
    - exact CEIL.
    - unfold CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - SPT. lia.
    - exact SP16.
    - exact MI2.
    - exact CS2.
    - exact UW2.
    - exact (uk_ctx_tail _ _ _ (E_BN_free_2225c8 : uk_tail BN_FREE BnRepDefs.CRYPTO_FREE) CTX).
    - intros Σ2 ms2 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4).
      apply implA_ret.
      set (OW' := lb_remove q OWd) in *.
      assert (INC' : forall bk, In bk (OW' ++ LB) -> In bk (OWd ++ LB)).
      { intros bk Hbk. apply in_app_or in Hbk. destruct Hbk as [Hbk|Hbk]; apply in_or_app; [left; eapply lb_remove_incl; exact Hbk| right; exact Hbk]. }
      assert (EL4 : lb_remove q (OWd ++ LB) = OW' ++ LB).
      { subst OW'. rewrite lb_remove_app, (lb_remove_notin q LB QNLB). reflexivity. }
      rewrite EL4 in AG4.
      assert (AGT : agree_on (aclient_addr (OW' ++ LB) (bv_unsigned sp)) m m4).
      { eapply agree_on_trans; [eapply agree_on_trans|].
        - eapply agree_client_weaken; [exact AG1| clear; lia| intros bk Hbk; apply INC' in Hbk; apply in_app_or in Hbk; destruct Hbk as [Hbk|Hbk]; apply in_or_app; [left; exact (INCd _ Hbk)| right; exact Hbk]].
        - eapply agree_client_weaken; [exact AG2| clear; lia| exact INC'].
        - exact AG4. }
      assert (KEEP : forall q0 A0 n0, In q0 (all_ids (setbn r (bn_nil 0) ls) (pl_set PL r None) EA) -> In (q0, A0, n0) OW -> In (q0, A0, n0) OW').
      { intros q0 A0 n0 Hq0 Hin0. subst OW'. apply lb_remove_In. split; [|cbn [blk_id fst]; intros ->; exact (NQ Hq0)].
        rewrite EOWd. destruct (bn_d b) as [pd|] eqn:Ed; cbn [lb_remove_opt]; [|exact Hin0].
        apply lb_remove_In. split; [exact Hin0|]. cbn [blk_id fst]. intros ->. exact (NP pd eq_refl Hq0). }
      unfold bn_postA_p. do 17 eexists. exists m4, OW', (pl_set PL r None). split; [reflexivity|]. cbn [fst snd].
      split; [exact HEAP4|].
      split. { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ (bv_unsigned sp) (bv_unsigned sp) USTACK_TOP); [| exact FROK'| clear; lia| clear; lia| exact AGT|].
               - eapply lib_state_h_ow; [exact LSU| exact KEEP].
               - intros bk Hbk. apply in_or_app. left. exact Hbk. }
      split; [exact ST4|]. split; [exact MI4|].
      split. { eapply agree_on_mono; [exact AGT|]. intros x [_ [Hx|[Hx|(bk & Hbk & Hr)]]];
                 [left; exact Hx | right; left; exact Hx | right; right; exists bk; split; [apply in_or_app; right; exact Hbk | exact Hr]]. }
      split; [rewrite CR4, CR2; clear; lia|].
      split; [reflexivity|]. split; [reflexivity|].

      rewrite (cnt_bal_setbn r (bn_nil 0) ls OW OW' HV). fold b. unfold bn_blocks at 1. cbn [bn_d bn_nil length].
      assert (LQ : S (length OW') = length OWd).
      { subst OW'. apply lb_remove_length; [exact (AH_nodup_l _ _ _ _ HEAP2) | apply (in_map blk_id) in INQd; exact INQd]. }
      assert (LD : Z.of_nat (length OWd) + Z.of_nat (length (bn_blocks b)) = Z.of_nat (length OW)).
      { rewrite EOWd. unfold bn_blocks. destruct (bn_d b) as [pd|] eqn:Ed; cbn [lb_remove_opt length]; [|clear; lia].
        pose proof (proj1 (DFACTS pd eq_refl)) as HinD0. apply (in_map blk_id) in HinD0.
        pose proof (lb_remove_length pd OW ND HinD0) as L1. clear - L1. lia. }
      clear - LQ LD. lia. }
  destruct (bn_d b) as [pd|] eqn:Ed.
  -
    destruct (DFACTS pd eq_refl) as (HinD & NEQ & NLB).
    apply evt_done.
    eapply (bn_free_d0_walkA) with (p := pd) (D := D) (n := 8 * Z.of_nat (bn_dmax b)) (f := 1) (a := a) (bs := (q, a, n)) (lo := lo)
                                  (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + exact HinD.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
    + rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact CS1.
    + unfold MallocRep.wz. exact BN0.
    + clear. lia.
    + exact QL.
    + cbn [blk_addr blk_size fst snd]. clear - Hn. lia.
    + exact AL.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_free_22256c : uk_call BN_FREE 0x222754 BN_FREE_D) CTX).
    + intros Σ1 ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
      rewrite ?ESP in *. rewrite (ret_pc_even 2238292) by (clear; lia).
      assert (EL2 : lb_remove pd (OW ++ LB) = lb_remove pd OW ++ LB) by (rewrite lb_remove_app, (lb_remove_notin pd LB NLB); reflexivity).
      rewrite EL2 in AG2.
      eapply (CONT Σ1 m2 (lb_remove pd OW) F2 fc2); [exact HEAP2 | exact AG2 | reflexivity | exact CR2 | exact ST2 | exact MI2].
  -
    pose proof (DNULL eq_refl) as ->.
    apply evt_done.
    eapply (bn_free_d0_null_walkA) with (f := 1) (a := a) (bs := (q, a, n)) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
    + rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact CS1.
    + unfold MallocRep.wz. exact BN0.
    + clear. lia.
    + exact QL.
    + cbn [blk_addr blk_size fst snd]. clear - Hn. lia.
    + exact AL.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_free_22256c : uk_call BN_FREE 0x222754 BN_FREE_D) CTX).
    + intros ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & AG2).
      rewrite ?ESP in *. rewrite (ret_pc_even 2238292) by (clear; lia).
      eapply (CONT Σ m2 OW F2 fc2); [exact HEAP2 | exact AG2 | reflexivity | reflexivity | exact ST2 | exact MI2].
Qed.

End WithRT.
