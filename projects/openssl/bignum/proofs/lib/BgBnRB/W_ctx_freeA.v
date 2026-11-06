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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require CtxFreeModel.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP2 Require W_ctxfree3.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgTree.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitA BnCallA W_expandA PlaceKitA.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2237488 => 1
  | 2237492 => 2
  | 2258012 => 1
  | 2258016 => 2
  | 2258112 => 1
  | 2258132 => 1
  | 2258136 => 2
  | 2258180 => 2
  | 2258216 => 2
  | 2258220 => 1
  | 2258224 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_CLEAR_FREE : Z := 0x22240c.
Definition BN_CLEAR_FREE_STACK : Z := 48 + BN_FREE_D_STACK.
Definition BN_CTX_FREE : Z := 0x227418.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition pbnA (m : mem) (L : list block) (a : Z) (b : bignum bptr) : Prop :=
  exists D, rw_cells bgbsegs m a (BnRepDefs.bn_cells D b)
    /\ match bn_d b with
       | Some p => In (p, D, 8 * Z.of_nat (bn_dmax b)) L /\ u64arr bgbsegs m D (wlimbs (bn_buf b))
       | None => D = 0
       end
    /\ Z.of_nat (bn_dmax b) <= 512 /\ bn_flags b = 0.

Lemma BN_clear_free_poolA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (p : bptr) (D a lo : Z) (b : bignum bptr) (bs : block) (ras : list Z)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> In (p, D, 8 * Z.of_nat (bn_dmax b)) OW ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_CLEAR_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> tp = wz TP_A -> BnRepDefs.crypto_statics m ->
  rw_cells bgbsegs m a (BnRepDefs.bn_cells D b) -> bn_flags b = 0 -> Z.of_nat (bn_dmax b) <= 512 ->
  In bs (OW ++ LB) -> blk_addr bs <= a -> a + 24 <= blk_addr bs + blk_size bs -> a mod 8 = 0 -> blk_id bs <> p ->
  a0 = wz a ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CLEAR_FREE (bv_unsigned ra :: ras) ->
  (forall Σ' ms', cfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (TFree p k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CLEAR_FREE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until Q. intros HEAP IN ST CEIL LO SPT SP16 MI -> CS BN FL0 DM INS RS1 RS2 AL NEB -> UW CTX K.
  pose proof LO as LO'. unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK in LO'.
  unfold BN_CLEAR_FREE, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bs HEAP INS) as (S0 & _ & _ & SC & SI).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP IN) as (D0 & _ & _ & DC & _).
  pose proof (AH_acc_in _ _ _ _ bs a 24 HEAP INS RS1 RS2) as ACC.
  pose proof (AH_offsh _ _ _ _ bs HEAP INS) as OFS. unfold SHLO, SHHI in OFS.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  unfold BnRepDefs.bn_cells, MallocRep.wz in BN. rewrite FL0 in BN.
  pose proof BN as BN0.
  apply (flag_cell_split bgbsegs m a _ _ _ _ 0 ltac:(clear; lia)) in BN.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  assert (EA0 : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - S0 SC RS1 RS2 C1 C2 C3; lia).
  assert (ED0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - D0 DC DM C1 C2 C3; lia).
  apply implA_from_evt.
  carve_frame 48%nat ST.
  do 7 step.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA0 in KA; clear - KA S0 RS1; lia|]. clear KA.
  step. hide_ors. ub. unhide. do 3 step. do 2 step. shl_with ACC AL. chk0.
  step. step.
  step. if_cases KD; zify_cond KD; [exfalso; rewrite ?ED0 in KD; clear - KD D0; lia|]. clear KD.
  do 2 step. shl_with ACC AL. chk0.
  step. rewrite (zxb_small 0) by (clear; lia). step. step. if_false.
  do 2 step. step.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (BnIfaceA.seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  assert (CS1 : BnRepDefs.crypto_statics m1).
  { eapply BnRepA.crypto_statics_agree; [exact AG1 | | exact CS]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -48) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 48 [CB 8 jfr; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  apply evt_done.
  eapply (bn_free_d_walkA) with (p := p) (D := D) (n := 8 * Z.of_nat (bn_dmax b)) (dm := Z.of_nat (bn_dmax b)) (f := 0) (a := a) (bs := bs) (lo := lo)
                               (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - exact IN.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK. clear - LO'. lia.
  - rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
  - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact CS1.
  - unfold MallocRep.wz. exact BN0.
  - clear. lia.
  - clear - DM. lia.
  - exact INS.
  - exact RS1.
  - exact RS2.
  - exact AL.
  - rewrite ESP. exact UW1.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_clear_free_2222a0 : uk_call BN_CLEAR_FREE 0x222488 BN_FREE_D) CTX).
  - intros Σ1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
    rewrite ?ESP in *. rewrite (ret_pc_even 2237576) by (clear; lia).
    assert (INS2 : In bs (lb_remove p (OW ++ LB))) by (apply lb_remove_In; split; [exact INS| exact NEB]).
    assert (INS2' : In bs (lb_remove p OW ++ LB)).
    { apply in_app_or in INS. destruct INS as [Hb|Hb]; apply in_or_app; [left; apply lb_remove_In; split; [exact Hb| exact NEB] | right; exact Hb]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; clear - Hx SPT; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in BN; [| intros x Hx; right; right; exists bs; split; [exact INS2| cbn in Hx; clear - Hx RS1 RS2; lia]].
    clear BN0.
    pose proof (AH_acc_in _ _ _ _ bs a 24 HEAP2 INS2' RS1 RS2) as ACC2.
    clear ACC MU WM OFF SHB1 SHB2 HEAP HEAP1 ST MI.
    pose proof (munch_refl (@nil (Z * Z)) m2) as MU2.
    destruct (AH_shb _ _ _ _ HEAP2) as (SHB1 & SHB2).
    apply implA_from_evt.
    do 2 step. shl_with ACC2 AL. chk0.
    step. rewrite (zxb_small 0) by (clear; lia). step. step. if_false.
    do 5 step. release_frame FR ST2 (bv_unsigned sp). step. step.
    apply evt_done.
    apply (K Σ1). unfold cfree_postA. do 17 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split. { eapply agree_on_trans; [| eapply agree_client_weaken; [exact AG2| clear; lia| auto]].
             eapply agree_client_weaken; [exact AG1| clear; lia| intros bk Hbk; eapply lb_remove_incl; exact Hbk]. }
    split; [exact CR2| exact HEAP2].
Qed.

Local Notation val_ids := OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids.
Local Notation item_ids := OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.item_ids.
Local Notation opt_ids := OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.opt_ids.
Local Notation ctx_free_ids := OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.ctx_free_ids.
Local Notation lb_remove_list := OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list.
Local Notation tfrees := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees.

Fixpoint pbnsA (m : mem) (L : list block) (a : Z) (l : list (bignum bptr)) : Prop :=
  match l with [] => True | b :: l' => pbnA m L a b /\ pbnsA m L (a + 24) l' end.

Lemma pbnsA_transport : forall l m m' L L' (P : Z -> Prop) a,
  pbnsA m L a l -> agree_on P m m' ->
  (forall b p D, In b l -> bn_d b = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax b)) L ->
                 In (p, D, 8 * Z.of_nat (bn_dmax b)) L' /\ forall x, D <= x < D + 8 * Z.of_nat (bn_dmax b) -> P x) ->
  (forall x, a <= x < a + 24 * Z.of_nat (length l) -> P x) ->
  pbnsA m' L' a l.
Proof.
  intros l. induction l as [|b l IH]; intros m m' L L' P a PB AG HL HC; [exact I|].
  cbn [pbnsA] in PB |- *. cbn [length] in HC. destruct PB as [(D & BN & ARR & DM & FL) PB]. split.
  - exists D. split; [| split; [| split; [exact DM| exact FL]]].
    + eapply rw_cells_agree; [exact AG| exact BN|]. intros x Hx. cbn in Hx. apply HC. lia.
    + destruct (bn_d b) as [p|] eqn:Ed; [| exact ARR]. destruct ARR as [IND U].
      destruct (HL b p D ltac:(left; reflexivity) Ed IND) as [IND' HP]. split; [exact IND'|].
      eapply LibKitA.u64arr_agree; [exact AG| exact U|]. intros x Hx. rewrite wlimbs_len in Hx. apply HP. unfold bn_dmax. lia.
  - eapply IH; [exact PB| exact AG| |].
    + intros b' p D' Hb' Ed IND. exact (HL b' p D' ltac:(right; exact Hb') Ed IND).
    + intros x Hx. apply HC. lia.
Qed.

Definition vl_postA (sp gp s0 s1 s2 s3 s7 s9 : word) (Σ : rts RT) (OW' LB : list block) (aend : Z) (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz aend) (wz aend) (wz SHB) s7 (wz (-24)) s9 (wz (Z.shiftr aend 3 + SHB)) (wz 0) t3 t4 t5 t6)
             F' (wz 0x22751c) fc' None m' (seg_rom bgbsegs)
    /\ mem_inv bgbsegs m' /\ stk bgbsegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (OW' ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ' = rt_credit RT Σ
    /\ AHEAP Σ' OW' LB m' /\ BnRepDefs.crypto_statics m'.

Lemma vals_loopA : forall {X : Type} (vs : list (bignum bptr))
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp gp s0 s1 s2 s3 s7 s9 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (q : bptr) (H a lo : Z) (ras : list Z) (EX : list bptr)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  pbnsA m OW a vs ->
  (1 <= length vs <= 16)%nat -> a = H + 24 * (16 - Z.of_nat (length vs)) ->
  AHEAP Σ OW LB m -> In (q, H, 400) OW ->
  List.NoDup (val_ids vs ++ EX) -> In q EX -> (forall p, In p (val_ids vs) -> ~ In p (map blk_id LB)) ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_CLEAR_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> BnRepDefs.crypto_statics m ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CLEAR_FREE (2258180 :: ras) ->
  (forall Σ' ms', vl_postA sp gp s0 s1 s2 s3 s7 s9 Σ (lb_remove_list (val_ids vs) OW) LB (a + 24 * Z.of_nat (length vs)) lo m Σ' ms' ->
                  implA k Σ' Q ms') ->
  implA (tfrees (val_ids vs) k) Σ Q
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz a) (wz a) (wz SHB) s7 (wz (-24)) s9 (wz (Z.shiftr a 3 + SHB)) (wz (Z.of_nat (length vs))) t3 t4 t5 t6)
        F (wz 0x2274ec) fc None m (seg_rom bgbsegs)).
Proof.
  intros X vs. induction vs as [|b vs IH]; intros until Q; intros PB LEN Ea HEAP INQ ND INEX NLB ST CEIL LO SPT SP16 MI CS UW CTX K; [cbn in LEN; lia|].
  cbn [length] in LEN, Ea, K |- *. cbn [pbnsA] in PB. destruct PB as [(D & BN & ARR & DM & FL0) PB].
  pose proof LO as LO'. unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK in LO'.
  unfold MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP INQ) as (QA0 & QA16 & _ & QAC & QAI).
  assert (INQL : In (q, H, 400) (OW ++ LB)) by (apply in_or_app; left; exact INQ).
  assert (AL : a mod 8 = 0) by (clear - QA16 Ea; Z.div_mod_to_equations; lia).
  pose proof (AH_acc_in _ _ _ _ (q, H, 400) a 24 HEAP INQL ltac:(cbn [blk_addr fst snd]; clear - Ea LEN; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - Ea LEN; lia)) as ACC.
  assert (EA0 : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - QA0 QAC Ea LEN C1 C2 C3; lia).
  pose proof (munch_refl (@nil (Z * Z)) m) as MU.

  assert (TAIL : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σ' : rts RT),
    let L1 := lb_remove_list (opt_ids (bn_d b)) OW in
    mem_inv bgbsegs m' -> stk bgbsegs m' lo (bv_unsigned sp) ->
    agree_on (aclient_addr (L1 ++ LB) (bv_unsigned sp)) m m' -> rt_credit RT Σ' = rt_credit RT Σ -> AHEAP Σ' L1 LB m' -> BnRepDefs.crypto_statics m' ->
    pbnsA m' L1 (a + 24) vs ->
    implA (tfrees (val_ids vs) k) Σ' Q
      (MS (mkR ra' sp gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 a) (Z_to_bv 64 a) (Z_to_bv 64 SHB) s7 (Z_to_bv 64 (-24)) s9
               (Z_to_bv 64 (Z.shiftr a 3 + SHB)) (Z_to_bv 64 (Z.of_nat (S (length vs)))) t3' t4' t5' t6')
          F' (Z_to_bv 64 0x227504) fc' None m' (seg_rom bgbsegs))).
  { intros until Σ'. intros L1 MI' ST' AG' CR' HEAP' CS' PB'.
    assert (INQ1 : In (q, H, 400) L1).
    { unfold L1. apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_In; [exact INQ|]. cbn [blk_id fst snd]. intros Hi.
      rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_cons in ND.
      eapply (OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_disj _ _ q ND); [apply in_or_app; left; exact Hi| exact INEX]. }
    assert (UW' : uw_chain USTACK_TOP m' (bv_unsigned sp) (bv_unsigned s0) ras).
    { apply (uw_chain_agree m m' ras (bv_unsigned sp) (bv_unsigned s0) UW). eapply agree_on_mono; [exact AG'|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
    assert (UBa : a + 24 < 2^63) by (unfold BnHeapA.ACEIL in *; clear - QA0 QAC Ea LEN C1 C2 C3; lia).
    apply implA_from_evt. hide_ors. ub. unhide.
    step. step.
    rewrite (unsigned_lit (Z.of_nat (S (length vs)))) by (clear - LEN; lia). rewrite bk_swrap32_small by (clear - LEN; lia).
    replace (Z.of_nat (S (length vs)) + -1) with (Z.of_nat (length vs)) by (clear; lia).
    step. step.
    replace (Z.shiftr a 3 + SHB + 3) with (Z.shiftr (a + 24) 3 + SHB) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - AL; Z.div_mod_to_equations; lia).
    replace (a + 24) with (H + 24 * (16 - Z.of_nat (length vs))) in PB' |- * by (clear - Ea; lia).
    step. if_cases KB; zify_cond KB.
    -
      rewrite ?unsigned_lit in KB by (clear - LEN; lia).
      apply evt_done.
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp gp s0 s1 s2 s3 s7 s9 F' fc' m' Σ' L1 LB q H _ lo ras EX);
        [ exact PB' | clear - LEN KB; lia | reflexivity | exact HEAP' | exact INQ1 | | exact INEX | | exact ST' | exact CEIL | exact LO | exact SPT | exact SP16
        | exact MI' | exact CS' | exact UW' | exact CTX | ].
      + rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_cons, <- app_assoc in ND. exact (OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_r _ _ ND).
      + intros p0 Hp0. apply NLB. rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_cons. apply in_or_app. right. exact Hp0.
      + intros Σ'' ms'' PO. apply K. unfold vl_postA in PO |- *.
        destruct PO as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & F'' & fc'' & m'' & -> & MI'' & ST'' & AG'' & CR'' & HEAP'' & CS'').
        do 18 eexists. exists m''. split; [replace (a + 24 * Z.of_nat (S (length vs))) with (H + 24 * (16 - Z.of_nat (length vs)) + 24 * Z.of_nat (length vs)) by (clear - Ea; lia); reflexivity|].
        split; [exact MI''|]. split; [exact ST''|].
        split. { rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_cons, OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_app. fold L1.
                 eapply agree_on_trans; [| exact AG''].
                 eapply agree_client_weaken; [exact AG'| clear; lia| intros bb Hbb; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; apply in_or_app;
                   [left; eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_incl; exact Hbb| right; exact Hbb]]. }
        split; [rewrite CR''; exact CR'|]. split; [| exact CS''].
        rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_cons, OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_app. exact HEAP''.
    -
      rewrite ?unsigned_lit in KB by (clear - LEN; lia). assert (vs = []) as -> by (destruct vs; [reflexivity| cbn [length] in KB, LEN; clear - KB LEN; lia]).
      cbn [OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids flat_map OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees
           OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list app length Z.of_nat] in K |- *.
      apply evt_done.
      change (Z.of_nat 0) with 0 in *. change (Z.of_nat 1) with 1 in *.
      replace (H + 24 * (16 - 0)) with (a + 24 * 1) by (clear - Ea; cbn [length Z.of_nat] in Ea; lia).
      apply K. unfold vl_postA, MallocRep.wz. do 18 eexists. exists m'. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { rewrite app_nil_r. exact AG'. }
      split; [exact CR'|]. split; [rewrite app_nil_r; exact HEAP'| exact CS']. }
  rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_cons in K, ND |- *.
  unfold BnRepDefs.bn_cells, MallocRep.wz in BN.
  apply implA_from_evt.
  shl_with ACC AL. chk0.
  step.
  destruct (bn_d b) as [pd|] eqn:Ed; cbn [OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.opt_ids app OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees
                                           OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list] in TAIL, K, ND |- *.
  -
    destruct ARR as [IND U0].
    pose proof (AH_range _ _ _ _ _ _ _ HEAP IND) as (PD0 & _ & _ & PDC & _).
    assert (NEq : q <> pd).
    { intros E. apply List.NoDup_cons_iff in ND. apply (proj1 ND). apply in_or_app. right. rewrite <- E. exact INEX. }
    assert (NPLB : ~ In pd (map blk_id LB)) by (apply NLB; rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_cons, Ed; left; reflexivity).
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by (unfold BnHeapA.ACEIL in *; clear - PD0 PDC C1 C2 C3; lia); clear - KA PD0; lia|]. clear KA.
    step. step.
    apply evt_done.
    eapply (BN_clear_free_poolA) with (p := pd) (D := D) (a := a) (b := b) (bs := (q, H, 400)) (lo := lo) (ras := ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP.
    + exact IND.
    + exact ST.
    + exact CEIL.
    + exact LO.
    + exact SPT.
    + exact SP16.
    + exact MI.
    + exact CS.
    + unfold BnRepDefs.bn_cells, MallocRep.wz. exact BN.
    + exact FL0.
    + exact DM.
    + exact INQL.
    + cbn [blk_addr fst snd]. clear - Ea LEN. lia.
    + cbn [blk_addr blk_size fst snd]. clear - Ea LEN. lia.
    + exact AL.
    + cbn [blk_id fst]. exact NEq.
    + exact UW.
    + rewrite unsigned_lit by (clear; lia). exact CTX.
    + intros Σ1 ms1 PO.
      destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4).
      rewrite (ret_pc_even 2258180) by (clear; lia).
      assert (EL4 : lb_remove pd (OW ++ LB) = lb_remove pd OW ++ LB) by (rewrite lb_remove_app, (lb_remove_notin pd LB NPLB); reflexivity).
      rewrite EL4 in AG4.
      assert (CS4 : BnRepDefs.crypto_statics m4).
      { eapply BnRepA.crypto_statics_agree; [exact AG4 | | exact CS]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
      eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 Σ1); [exact MI4 | exact ST4 | exact AG4 | exact CR4 | exact HEAP4 | exact CS4 |].
      eapply pbnsA_transport; [exact PB| exact AG4| |].
      * intros b' p' D' Hb' Ed' IND'.
        assert (IND2 : In (p', D', 8 * Z.of_nat (bn_dmax b')) (lb_remove pd OW)).
        { apply (proj2 (lb_remove_In _ _ _)). split; [exact IND'|]. cbn [blk_id fst snd]. intros E.
          apply List.NoDup_cons_iff in ND. apply (proj1 ND). apply in_or_app. left. rewrite <- E.
          eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_In; [exact Hb'| exact Ed']. }
        split; [exact IND2|]. intros x Hx. right. right. exists (p', D', 8 * Z.of_nat (bn_dmax b')). split; [apply in_or_app; left; exact IND2|]. cbn [blk_addr blk_size fst snd]. clear - Hx. lia.
      * intros x Hx. right. right. exists (q, H, 400). split; [apply in_or_app; left; apply (proj2 (lb_remove_In _ _ _)); split; [exact INQ| cbn [blk_id fst snd]; exact NEq]|].
        cbn [blk_addr blk_size fst snd]. clear - Hx Ea LEN. lia.
  -
    subst D. step. if_cases KA; zify_cond KA; [| exfalso; rewrite ?unsigned_lit in KA by (clear; lia); clear - KA; lia]. clear KA.
    apply evt_done.
    eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m Σ); [exact MI | exact ST | apply agree_on_refl | reflexivity | exact HEAP | exact CS | exact PB].
Qed.

Lemma block_munch_agree : forall Σ OW LB m m1 W (L : list block) sp (bq : block),
  AHEAP Σ OW LB m -> munch W m m1 -> In bq (OW ++ LB) -> ACEIL <= sp ->
  Forall (fun iv => blk_addr bq <= fst iv /\ snd iv <= blk_addr bq + blk_size bq) W ->
  (forall b, In b L -> In b (OW ++ LB) /\ blk_id b <> blk_id bq) ->
  agree_on (aclient_addr L sp) m m1.
Proof.
  intros Σ OW LB m m1 W L sp bq HEAP MU INQ CE HW HL. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a Ha. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
  pose proof (AH_range_gen _ _ _ _ bq HEAP INQ) as (Q0 & _ & Qn & QC & QI). clear MU.
  induction HW as [|[x y] W [H1 H2] HW IH]; [exact I|]. cbn [outside fst snd] in *. split; [|exact IH].
  intros Hx. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia | |].
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - destruct (HL b Hb) as [Hb' NE]. pose proof (AH_disjoint_gen _ _ _ _ b bq HEAP Hb' INQ NE) as DJ. lia.
Qed.

Fixpoint pitemsA (m : mem) (L : list block) (items : list bptr) (Hs : list Z) (vals : list (bignum bptr)) (prev : Z) : Prop :=
  match items, Hs with
  | [], [] => True
  | q :: items', H :: Hs' =>
      In (q, H, 400) L /\ (16 <= length vals)%nat /\ pbnsA m L H (firstn 16 vals)
      /\ rw_cells bgbsegs m (H + 384) [C8 (wz prev); C8 (wz (hd 0 Hs'))]
      /\ pitemsA m L items' Hs' (skipn 16 vals) H
  | _, _ => False
  end.

Lemma pitemsA_transport : forall items m m' L L' (P : Z -> Prop) Hs vals prev,
  pitemsA m L items Hs vals prev -> agree_on P m m' ->
  (forall blk, In blk L -> In (blk_id blk) (item_ids items vals) ->
               In blk L' /\ forall x, blk_addr blk <= x < blk_addr blk + blk_size blk -> P x) ->
  pitemsA m' L' items Hs vals prev.
Proof.
  intros items. induction items as [|q items IH]; intros m m' L L' P Hs vals prev PI AG HL; destruct Hs as [|H Hs]; cbn [pitemsA] in PI |- *; try exact PI.
  destruct PI as (INQ & L16 & PB & LNK & PI). rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.item_ids_cons in HL.
  destruct (HL _ INQ ltac:(cbn [blk_id fst snd]; apply in_or_app; right; left; reflexivity)) as [INQ' CL]. cbn [blk_addr blk_size fst snd] in CL.
  split; [exact INQ'|]. split; [exact L16|]. split; [| split].
  - eapply pbnsA_transport; [exact PB| exact AG| |].
    + intros b p D Hb Ed IND. destruct (HL _ IND) as [IND' HP]; [cbn [blk_id fst snd]; apply in_or_app; left; eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_In; [exact Hb| exact Ed]|].
      cbn [blk_addr blk_size fst snd] in HP. split; [exact IND'| exact HP].
    + intros x Hx. rewrite length_firstn in Hx. apply CL. lia.
  - eapply rw_cells_agree; [exact AG| exact LNK|]. intros x Hx. cbn in Hx. apply CL. lia.
  - eapply IH; [exact PI| exact AG|]. intros blk Hb Hi. apply HL; [exact Hb|]. apply in_or_app. right. right. exact Hi.
Qed.

Definition ctxf_cells (hd0 cu : word) (tl pu ps de ss us es tm fl lc : word) : list cell :=
  [C8 hd0; C8 cu; C8 tl; C4 pu; C4 ps; C8 (wz 0); C4 de; C4 ss; C4 us; C4 es; C4 tm; C4 fl; C8 lc].

Definition il_postA (sp gp s0 s1 s10 s11 : word) (Σ : rts RT) (OW' LB : list block) (qc : bptr) (A : Z)
    (tl pu ps de ss us es tm fl lc : word) (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 x10 x11 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 x10 x11 t3 t4 t5 t6)
             F' (wz 0x227580) fc' None m' (seg_rom bgbsegs)
    /\ mem_inv bgbsegs m' /\ stk bgbsegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (lb_remove qc OW' ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ' = rt_credit RT Σ
    /\ AHEAP Σ' OW' LB m' /\ BnRepDefs.crypto_statics m'
    /\ rw_cells bgbsegs m' A (ctxf_cells (wz 0) (wz 0) tl pu ps de ss us es tm fl lc).

Lemma items_loopA : forall {X : Type} (items : list bptr) (Hs : list Z) (vals : list (bignum bptr)) (prev : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp gp s0 s5 s10 s11 : word) (cu tl pu ps de ss us es tm fl lc : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (qc : bptr) (A lo : Z) (ras : list Z) (EX : list bptr)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  pitemsA m OW items Hs vals prev -> items <> [] ->
  AHEAP Σ OW LB m -> In (qc, A, 72) OW ->
  List.NoDup (item_ids items vals ++ EX) -> In qc EX -> (forall p, In p (item_ids items vals) -> ~ In p (map blk_id LB)) ->
  rw_cells bgbsegs m A (ctxf_cells (wz (hd 0 Hs)) cu tl pu ps de ss us es tm fl lc) ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_CLEAR_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> BnRepDefs.crypto_statics m ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CLEAR_FREE (2258180 :: ras) -> uk_ctx BnRepDefs.CRYPTO_FREE (2258276 :: ras) ->
  (forall Σ' ms', il_postA sp gp s0 (wz A) s10 s11 Σ (lb_remove_list (item_ids items vals) OW) LB qc A tl pu ps de ss us es tm fl lc lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (tfrees (item_ids items vals) k) Σ Q
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz (A + 8)) (wz 462720) (wz (hd 0 Hs)) s5 (wz SHB) (wz (Z.shiftr A 3 + SHB)) (wz (-24))
             (wz (Z.shiftr (A + 8) 3 + SHB)) s10 s11 t3 t4 t5 t6)
        F (wz 0x2274d4) fc None m (seg_rom bgbsegs)).
Proof.
  intros X items. induction items as [|q items IH]; intros until Q; intros PI NE HEAP INQC ND INEX NLB CX ST CEIL LO SPT SP16 MI CS UW CTXB CTXF K; [exfalso; apply NE; reflexivity|].
  destruct Hs as [|H Hs]; cbn [pitemsA] in PI; [contradiction|]. cbn [hd] in CX |- *.
  destruct PI as (INQ & L16 & PB & LNK & PI). rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.item_ids_cons in ND, K, NLB |- *.
  pose proof LO as LO'. unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK in LO'.
  unfold MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP INQ) as (QA0 & QA16 & _ & QAC & QAI).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP INQC) as (CA0 & CA16 & _ & CAC & CAI).
  assert (LF : length (firstn 16 vals) = 16%nat) by (rewrite length_firstn; clear - L16; lia).
  assert (NDX : forall x, In x (val_ids (firstn 16 vals)) -> In x (q :: item_ids items (skipn 16 vals) ++ EX) -> False).
  { intros x H1 H2. eapply (OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_disj _ _ x); [rewrite <- app_assoc in ND; exact ND| exact H1| exact H2]. }

  rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees_app.
  assert (ALq0 : H mod 8 = 0) by (clear - QA16; Z.div_mod_to_equations; lia).
  assert (EH00 : bv_unsigned (Z_to_bv 64 H) = H) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - QA0 QAC C1 C2 C3; lia).
  apply implA_from_evt. hide_ors. ub. unhide. do 4 step. rewrite ?EH00.
  replace (SHB + Z.shiftr H 3) with (Z.shiftr H 3 + SHB) by (clear; lia).
  apply evt_done.
  replace (Z_to_bv 64 16) with (Z_to_bv 64 (Z.of_nat (length (firstn 16 vals)))) by (f_equal; rewrite LF; clear; lia).
  eapply (vals_loopA (firstn 16 vals)) with (a := H) (q := q) (H := H) (OW := OW) (LB := LB) (lo := lo) (ras := ras) (EX := q :: item_ids items (skipn 16 vals) ++ EX);
    [ exact PB | rewrite LF; clear; lia | rewrite LF; clear; lia | exact HEAP | exact INQ | rewrite <- app_assoc in ND; exact ND | left; reflexivity
    | intros p0 Hp0; apply NLB; apply in_or_app; left; exact Hp0
    | exact ST | exact CEIL | exact LO | exact SPT | exact SP16 | exact MI | exact CS | exact UW | exact CTXB | ].
  intros Σ1 ms1 PO. unfold vl_postA, MallocRep.wz in PO.
  destruct PO as (ra1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & -> & MI1 & ST1 & AG1 & CR1 & HEAP1 & CS1).
  set (L1 := lb_remove_list (val_ids (firstn 16 vals)) OW) in *.

  assert (KEEP1 : forall blk, In blk OW -> In (blk_id blk) (q :: item_ids items (skipn 16 vals) ++ EX) -> In blk L1).
  { intros blk Hb Hi. unfold L1. apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_In; [exact Hb|]. intros Hv. exact (NDX _ Hv Hi). }
  assert (INQC1 : In (qc, A, 72) L1) by (apply KEEP1; [exact INQC| right; apply in_or_app; right; exact INEX]).
  assert (INQ1 : In (q, H, 400) L1) by (apply KEEP1; [exact INQ| left; reflexivity]).
  assert (CLc : forall LL x, In (qc, A, 72) LL -> A <= x < A + 72 -> aclient_addr LL (bv_unsigned sp) x).
  { intros LL x Hin Hx. right. right. exists (qc, A, 72). split; [exact Hin|]. cbn [blk_addr blk_size fst snd]. clear - Hx. lia. }
  assert (CLq : forall LL x, In (q, H, 400) LL -> H <= x < H + 400 -> aclient_addr LL (bv_unsigned sp) x).
  { intros LL x Hin Hx. right. right. exists (q, H, 400). split; [exact Hin|]. cbn [blk_addr blk_size fst snd]. clear - Hx. lia. }
  apply (rw_cells_agree _ _ _ _ _ AG1) in CX; [| intros x Hx; cbn in Hx; apply CLc; [apply in_or_app; left; exact INQC1| clear - Hx; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG1) in LNK; [| intros x Hx; cbn in Hx; apply CLq; [apply in_or_app; left; exact INQ1| clear - Hx; lia]].
  assert (PI1 : pitemsA m1 L1 items Hs (skipn 16 vals) H).
  { eapply pitemsA_transport; [exact PI| exact AG1|]. intros blk Hb Hi.
    assert (Hb1 : In blk L1) by (apply KEEP1; [exact Hb| right; apply in_or_app; left; exact Hi]).
    split; [exact Hb1|]. intros x Hx. right. right. exists blk. split; [apply in_or_app; left; exact Hb1| exact Hx]. }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras).
  { apply (uw_chain_agree m m1 ras (bv_unsigned sp) (bv_unsigned s0) UW). eapply agree_on_mono; [exact AG1|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
  assert (INQCL1 : In (qc, A, 72) (L1 ++ LB)) by (apply in_or_app; left; exact INQC1).
  assert (INQL1 : In (q, H, 400) (L1 ++ LB)) by (apply in_or_app; left; exact INQ1).
  pose proof (AH_acc_in _ _ _ _ (qc, A, 72) A 72 HEAP1 INQCL1 ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear; lia)) as ACCc.
  pose proof (AH_acc_in _ _ _ _ (q, H, 400) H 400 HEAP1 INQL1 ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear; lia)) as ACCq.
  pose proof (AH_offsh _ _ _ _ (qc, A, 72) HEAP1 INQCL1) as OFC. cbn [blk_addr blk_size fst snd] in OFC. unfold SHLO, SHHI in OFC.
  assert (ALc : A mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
  assert (ALq : H mod 8 = 0) by (clear - QA16; Z.div_mod_to_equations; lia).
  clear PB HEAP MI CS ST PI UW.
  unfold ctxf_cells, MallocRep.wz in CX.
  pose proof (munch_refl [(A, A + 72)]%Z m1) as MU1. pose proof (wmono_refl bgbsegs m1) as WM1.
  assert (OFF1 : offshW [(A, A + 72)]) by (cbn [offshW]; unfold SHLO, SHHI; clear - OFC; lia).
  assert (EA0 : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - CA0 CAC C1 C2 C3; lia).
  assert (EH0 : bv_unsigned (Z_to_bv 64 H) = H) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - QA0 QAC C1 C2 C3; lia).

  cbn [tfrees].
  apply implA_from_evt.
  shl_with ACCc ALc. chk0.
  step. hide_ors. ub. unhide. step. step. step. shl_with ACCq ALq. chk0.
  shl_with ACCc ALc. chk0.
  step. clear LNK. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1' end.
  assert (WB1 : Forall (fun iv : Z * Z => blk_addr (qc, A, 72) <= fst iv /\ snd iv <= blk_addr (qc, A, 72) + blk_size (qc, A, 72)) [(A, A + 72)]).
  { constructor; [cbn; clear; lia| constructor]. }
  assert (HEAP1' : AHEAP Σ1 L1 LB m1').
  { eapply (BnIfaceA.seg_heap Σ1 L1 LB m1 m1' _ lo (bv_unsigned sp) HEAP1 MU1 WM1); [| exact CEIL | unfold USTACK_TOP; clear - SPT; lia].
    constructor; [right; exists (qc, A, 72); split; [exact INQC1| cbn; clear; lia] | constructor]. }
  assert (NEqc : qc <> q).
  { intros E. eapply (OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_disj _ _ qc ND); [| exact INEX]. apply in_or_app. right. left. symmetry. exact E. }
  assert (NIQC : ~ In qc (item_ids items (skipn 16 vals))).
  { intros Hi. eapply (OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_disj _ _ qc ND); [| exact INEX]. apply in_or_app. right. right. exact Hi. }
  assert (AGB1 : forall LL, (forall b, In b LL -> In b (L1 ++ LB) /\ blk_id b <> qc) -> agree_on (aclient_addr LL (bv_unsigned sp)) m1 m1').
  { intros LL HLL. eapply (block_munch_agree Σ1 L1 LB m1 m1' _ LL (bv_unsigned sp) (qc, A, 72) HEAP1 MU1 INQCL1); [clear - CEIL LO'; lia| exact WB1| exact HLL]. }
  assert (QCLB : ~ In qc (map blk_id LB)).
  { intros Hq. pose proof (AH_nodup _ _ _ _ HEAP1) as NDL. rewrite map_app in NDL.
    eapply (nodup_app_disj _ _ qc NDL); [apply (in_map blk_id) in INQC1; exact INQC1| exact Hq]. }
  assert (QLB : ~ In q (map blk_id LB)) by (apply NLB; apply in_or_app; right; left; reflexivity).
  assert (CS1' : BnRepDefs.crypto_statics m1').
  { eapply BnRepA.crypto_statics_agree; [exact (AGB1 [] ltac:(intros b [])) | | exact CS1]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (PI1' : pitemsA m1' L1 items Hs (skipn 16 vals) H).
  { eapply pitemsA_transport; [exact PI1| exact (AGB1 (lb_remove qc L1) ltac:(intros b Hb; apply lb_remove_In in Hb; destruct Hb as [Hb Hne]; split; [apply in_or_app; left; exact Hb| exact Hne]))|].
    intros blk Hb Hi. split; [exact Hb|]. intros x Hx. right. right. exists blk. split; [| exact Hx].
    apply lb_remove_In. split; [exact Hb|]. intros E. apply NIQC. rewrite <- E. exact Hi. }
  assert (UW1' : uw_chain USTACK_TOP m1' (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munch_nw; [exact UW1 | exact MU1 |]. constructor; [cbn; unfold BnHeapA.ACEIL in *; clear - CAC CEIL LO'; lia | constructor]. }
  apply evt_done.
  eapply (CRYPTO_free_walkA) with (p := q) (A := H) (n := 400) (lo := lo) (ras := ras) (OW := L1) (LB := LB); try reflexivity.
  - exact HEAP1'.
  - exact INQ1.
  - eassumption.
  - exact CEIL.
  - unfold CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
  - unfold USTACK_TOP. clear - SPT. lia.
  - exact SP16.
  - eassumption.
  - exact CS1'.
  - exact UW1'.
  - rewrite unsigned_lit by (clear; lia). exact CTXF.
  - intros Σ2 ms2 PO.
    destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & F2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
    rewrite (ret_pc_even 2258276) by (clear; lia).
    set (L2 := lb_remove q L1) in *.
    assert (EL2 : lb_remove q (L1 ++ LB) = L2 ++ LB) by (subst L2; rewrite lb_remove_app, (lb_remove_notin q LB QLB); reflexivity).
    rewrite EL2 in AG2.
    assert (KEEP2 : forall blk, In blk L1 -> blk_id blk <> q -> In blk L2).
    { intros blk Hb Hne. unfold L2. apply (proj2 (lb_remove_In _ _ _)). split; [exact Hb| exact Hne]. }
    assert (INQC2 : In (qc, A, 72) L2) by (apply KEEP2; [exact INQC1| cbn [blk_id fst snd]; exact NEqc]).
    assert (INQCL2 : In (qc, A, 72) (L2 ++ LB)) by (apply in_or_app; left; exact INQC2).
    lazymatch goal with CXH : rw_cells bgbsegs m1' A _ |- _ =>
      apply (rw_cells_agree _ _ _ _ _ AG2) in CXH; [rename CXH into CX2| intros x Hx; cbn in Hx; apply CLc; [exact INQCL2| clear - Hx; lia]] end.
    assert (PI2 : pitemsA m2 L2 items Hs (skipn 16 vals) H).
    { eapply pitemsA_transport; [exact PI1'| exact AG2|]. intros blk Hb Hi.
      assert (Hb2 : In blk L2).
      { apply KEEP2; [exact Hb|]. intros E. pose proof ND as NDc. rewrite <- app_assoc in NDc. apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_r in NDc. cbn in NDc.
        apply List.NoDup_cons_iff in NDc. apply (proj1 NDc). apply in_or_app. left. rewrite <- E. exact Hi. }
      split; [exact Hb2|]. intros x Hx. right. right. exists blk. split; [apply in_or_app; left; exact Hb2| exact Hx]. }
    assert (CS2 : BnRepDefs.crypto_statics m2).
    { eapply BnRepA.crypto_statics_agree; [exact AG2 | | exact CS1']. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
    assert (UW2 : uw_chain USTACK_TOP m2 (bv_unsigned sp) (bv_unsigned s0) ras).
    { apply (uw_chain_agree m1' m2 ras (bv_unsigned sp) (bv_unsigned s0) UW1'). eapply agree_on_mono; [exact AG2|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }

    assert (INC2 : forall bb, In bb (lb_remove qc L2 ++ LB) -> In bb (L1 ++ LB) /\ blk_id bb <> qc).
    { intros bb Hbb. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb].
      - apply lb_remove_In in Hbb. destruct Hbb as [Hbb Hne]. split; [apply in_or_app; left; eapply lb_remove_incl; exact Hbb| exact Hne].
      - split; [apply in_or_app; right; exact Hbb|]. intros E. apply QCLB. rewrite <- E. apply in_map. exact Hbb. }
    assert (AG02 : agree_on (aclient_addr (lb_remove qc L2 ++ LB) (bv_unsigned sp)) m m2).
    { eapply agree_on_trans; [eapply agree_client_weaken; [exact AG1| clear; lia| intros bb Hbb; exact (proj1 (INC2 bb Hbb))]|].
      eapply agree_on_trans; [exact (AGB1 _ INC2)|].
      eapply agree_client_weaken; [exact AG2| clear; lia|]. intros bb Hbb. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb]; apply in_or_app; [left; eapply lb_remove_incl; exact Hbb| right; exact Hbb]. }
    pose proof (AH_acc_in _ _ _ _ (qc, A, 72) A 72 HEAP2 INQCL2 ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear; lia)) as ACCc2.
    clear HEAP1 HEAP1' CS1 CS1' PI1 PI1' MU1 WM1 AG1 AG2 KEEP1 INQ1 INQC1 ACCc ACCq UW1 UW1' AGB1 INQCL1 INQL1 KEEP2.
    pose proof (munch_refl [(A, A + 72)]%Z m2) as MU2. pose proof (wmono_refl bgbsegs m2) as WM2.

    apply implA_from_evt.
    shl_with ACCc2 ALc. chk0.
    shl_with ACCc2 ALc. chk0.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2' end.
    assert (WB2 : Forall (fun iv : Z * Z => blk_addr (qc, A, 72) <= fst iv /\ snd iv <= blk_addr (qc, A, 72) + blk_size (qc, A, 72)) [(A, A + 72)]).
    { constructor; [cbn; clear; lia| constructor]. }
    assert (HEAP2' : AHEAP Σ2 L2 LB m2').
    { eapply (BnIfaceA.seg_heap Σ2 L2 LB m2 m2' _ lo (bv_unsigned sp) HEAP2 MU2 WM2); [| exact CEIL | unfold USTACK_TOP; clear - SPT; lia].
      constructor; [right; exists (qc, A, 72); split; [exact INQC2| cbn; clear; lia] | constructor]. }
    assert (AGB2 : forall LL, (forall b, In b LL -> In b (L2 ++ LB) /\ blk_id b <> qc) -> agree_on (aclient_addr LL (bv_unsigned sp)) m2 m2').
    { intros LL HLL. eapply (block_munch_agree Σ2 L2 LB m2 m2' _ LL (bv_unsigned sp) (qc, A, 72) HEAP2 MU2 INQCL2); [clear - CEIL LO'; lia| exact WB2| exact HLL]. }
    assert (CS2' : BnRepDefs.crypto_statics m2').
    { eapply BnRepA.crypto_statics_agree; [exact (AGB2 [] ltac:(intros b [])) | | exact CS2]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
    assert (INC2' : forall bb, In bb (lb_remove qc L2 ++ LB) -> In bb (L2 ++ LB) /\ blk_id bb <> qc).
    { intros bb Hbb. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb].
      - apply lb_remove_In in Hbb. destruct Hbb as [Hbb Hne]. split; [apply in_or_app; left; exact Hbb| exact Hne].
      - split; [apply in_or_app; right; exact Hbb|]. intros E. apply QCLB. rewrite <- E. apply in_map. exact Hbb. }
    assert (PI2' : pitemsA m2' L2 items Hs (skipn 16 vals) H).
    { eapply pitemsA_transport; [exact PI2| exact (AGB2 _ INC2')|].
      intros blk Hb Hi. split; [exact Hb|]. intros x Hx. right. right. exists blk. split; [| exact Hx].
      apply in_or_app. left. apply lb_remove_In. split; [exact Hb|]. intros E. apply NIQC. rewrite <- E. exact Hi. }
    assert (UW2' : uw_chain USTACK_TOP m2' (bv_unsigned sp) (bv_unsigned s0) ras).
    { eapply uw_chain_munch_nw; [exact UW2 | exact MU2 |]. constructor; [cbn; unfold BnHeapA.ACEIL in *; clear - CAC CEIL LO'; lia | constructor]. }
    assert (AG02' : agree_on (aclient_addr (lb_remove qc L2 ++ LB) (bv_unsigned sp)) m m2').
    { eapply agree_on_trans; [exact AG02| exact (AGB2 _ INC2')]. }
    step. if_cases KB; zify_cond KB.
    +
      destruct items as [|q' items']; [| ].
      { destruct Hs; cbn [pitemsA] in PI2'; [| contradiction]. exfalso. apply KB. reflexivity. }
      apply evt_done.
      eapply (IH Hs (skipn 16 vals) H) with (qc := qc) (OW := L2) (LB := LB) (lo := lo) (ras := ras) (EX := EX);
        [ exact PI2' | intros E; discriminate E | exact HEAP2' | exact INQC2
        | pose proof ND as NDc; rewrite <- app_assoc in NDc; apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_r in NDc; cbn in NDc; apply List.NoDup_cons_iff in NDc; exact (proj2 NDc)
        | exact INEX | intros p0 Hp0; apply NLB; apply in_or_app; right; right; exact Hp0
        | unfold ctxf_cells, MallocRep.wz; eassumption | eassumption | exact CEIL | exact LO | exact SPT | exact SP16
        | eassumption | exact CS2' | exact UW2' | exact CTXB | exact CTXF | ].
      intros Σ3 ms3 PO. apply K. unfold il_postA in PO |- *.
      destruct PO as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & F3 & fc3 & m3 & -> & MI3 & ST3 & AG3 & CR3 & HEAP3 & CS3 & CX3).
      do 28 eexists. exists m3. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|].
      rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_app. cbn [OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list]. fold L1. fold L2.
      split. { eapply agree_on_trans; [| exact AG3].
               eapply agree_client_weaken; [exact AG02'| clear; lia|]. intros bb Hbb. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb]; apply in_or_app; [left| right; exact Hbb].
               pose proof (proj1 (lb_remove_In _ _ _) Hbb) as [Hb3 Hne].
               apply (proj2 (lb_remove_In _ _ _)). split; [eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_incl; exact Hb3| exact Hne]. }
      split; [rewrite CR3, CR2; exact CR1|]. split; [exact HEAP3| split; [exact CS3| exact CX3]].
    +
      destruct items as [|q' items'].
      2: { destruct Hs as [|H' Hs']; cbn [pitemsA] in PI2'; [contradiction|]. destruct PI2' as (INQ' & _). exfalso.
           pose proof (AH_range _ _ _ _ _ _ _ HEAP2' INQ') as (Q0 & _ & _ & QC' & _). cbn [hd] in KB.
           change 18446744073709551615 with (Z.ones 64) in KB. rewrite Z.land_ones in KB by (clear; lia).
           rewrite Z.mod_small in KB by (unfold BnHeapA.ACEIL in *; clear - Q0 QC' C1 C2 C3; lia). clear - KB Q0. lia. }
      destruct Hs; cbn [pitemsA] in PI2'; [| contradiction]. cbn [hd item_ids tfrees OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.item_ids OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees
                                                                 OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list] in K |- *.
      apply evt_done.
      apply K. unfold il_postA. rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_app. cbn [OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list]. fold L1. fold L2.
      do 28 eexists. exists m2'. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|].
      split; [exact AG02'|]. split; [rewrite CR2; exact CR1|]. split; [exact HEAP2'|]. split; [exact CS2'|].
      unfold ctxf_cells, MallocRep.wz. eassumption.
Qed.

Definition ctx0_cells (hd0 cu : word) (tl pu ps : word) (ix : word) (de ss us es tm fl lc : word) : list cell :=
  [C8 hd0; C8 cu; C8 tl; C4 pu; C4 ps; C8 ix; C4 de; C4 ss; C4 us; C4 es; C4 tm; C4 fl; C8 lc].

Definition gfree_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW' LB : list block) (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bgbsegs)
    /\ mem_inv bgbsegs m' /\ stk bgbsegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (OW' ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ' = rt_credit RT Σ
    /\ AHEAP Σ' OW' LB m'.

Definition BN_CTX_FREE_STACK : Z := 112 + BN_CLEAR_FREE_STACK.

Lemma BN_CTX_free_cpsA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (qc : bptr) (oi : option bptr)
    (items : list bptr) (Hs : list Z) (vals : list (bignum bptr)) (prev : Z)
    (A IX : Z) (cu tl pu ps de ss us es tm fl lc : word) (lo : Z) (ras : list Z)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  let ids := ctx_free_ids oi items vals qc in
  AHEAP Σ OW LB m -> In (qc, A, 72) OW ->
  rw_cells bgbsegs m A (ctx0_cells (wz (hd 0 Hs)) cu tl pu ps (wz IX) de ss us es tm fl lc) ->
  match oi with Some qi => In (qi, IX, 128) OW | None => IX = 0 end ->
  pitemsA m OW items Hs vals prev ->
  List.NoDup ids -> (forall p, In p ids -> ~ In p (map blk_id LB)) ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_CTX_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> tp = wz TP_A -> BnRepDefs.crypto_statics m -> a0 = wz A ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CTX_FREE (bv_unsigned ra :: ras) ->
  (forall Σ' ms', gfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (lb_remove_list ids OW) LB lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (tfrees ids k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_FREE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until Q. intros ids HEAP INQC CX IDX PI ND NLB ST CEIL LO SPT SP16 MI -> CS -> UW CTX K.
  pose proof LO as LO'. unfold BN_CTX_FREE_STACK, BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK in LO'.
  unfold BN_CTX_FREE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP INQC) as (CA0 & CA16 & _ & CAC & CAI).
  assert (INQCL : In (qc, A, 72) (OW ++ LB)) by (apply in_or_app; left; exact INQC).
  pose proof (AH_acc_in _ _ _ _ (qc, A, 72) A 72 HEAP INQCL ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear; lia)) as ACC.
  assert (AL : A mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  assert (EA0 : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - CA0 CAC C1 C2 C3; lia).
  assert (CLc : forall LL SP x, In (qc, A, 72) LL -> A <= x < A + 72 -> aclient_addr LL SP x).
  { intros LL SP x Hin Hx. right. right. exists (qc, A, 72). split; [exact Hin|]. cbn [blk_addr blk_size fst snd]. clear - Hx. lia. }
  unfold ids, ctx_free_ids, OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.ctx_free_ids in ND, NLB, K |- *.
  rewrite !OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees_app. rewrite !OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_app in K.
  assert (NIQC : ~ In qc (item_ids items vals)).
  { intros Hi. apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_r in ND.
    eapply (OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_disj _ _ qc ND); [exact Hi| left; reflexivity]. }
  assert (QCLB : ~ In qc (map blk_id LB)) by (apply NLB; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  unfold ctx0_cells in CX.
  apply implA_from_evt.
  carve_frame 112%nat ST. do 15 step.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA0 in KA; clear - KA CA0; lia|]. clear KA.
  step. hide_ors. ub. unhide. do 3 step. do 3 step. shl_with ACC AL. chk0.
  step. step. step. step. step.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (BnIfaceA.seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  assert (CS1 : BnRepDefs.crypto_statics m1).
  { eapply BnRepA.crypto_statics_agree; [exact AG1 | | exact CS]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 112 [CB 8 jfr; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  assert (UWm1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  assert (PI1 : pitemsA m1 OW items Hs vals prev).
  { eapply pitemsA_transport; [exact PI| exact AG1|]. intros blk Hb Hi. split; [exact Hb|].
    intros x Hx. right. right. exists blk. split; [apply in_or_app; left; exact Hb| exact Hx]. }
  pose proof (uk_ctx_call _ _ _ _ (E_BN_CTX_free_22731c : uk_call BN_CTX_FREE 0x227504 BN_CLEAR_FREE) CTX) as CTXB. pose proof (uk_ctx_call _ _ _ _ (E_BN_CTX_free_22737c : uk_call BN_CTX_FREE 0x227564 BnRepDefs.CRYPTO_FREE) CTX) as CTXF.
  clear PI CS.

  assert (EXIT : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σ' : rts RT) (L' : list block),
    mem_inv bgbsegs m' -> stk bgbsegs m' lo (bv_unsigned sp + -112) ->
    agree_on (aclient_addr (lb_remove qc L' ++ LB) (bv_unsigned sp + -112)) m1 m' -> rt_credit RT Σ' = rt_credit RT Σ -> AHEAP Σ' L' LB m' -> BnRepDefs.crypto_statics m' ->
    In (qc, A, 72) L' -> (forall b, In b L' -> In b OW) ->
    lb_remove qc L' = lb_remove_list [qc] (lb_remove_list (item_ids items vals) (lb_remove_list (opt_ids oi) OW)) ->
    implA (TFree qc k) Σ' Q
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 A)
               a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6')
          F' (Z_to_bv 64 0x227580) fc' None m' (seg_rom bgbsegs))).
  { intros until L'. intros MI' ST' AG' CR' HEAP' CS' INQC' INCL EL.
    assert (FR' : rw_cells bgbsegs m' (bv_unsigned sp + -112) [CB 8 jfr; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_agree; [exact AG'| exact FR|]. intros x Hx. cbn in Hx. left. unfold USTACK_TOP. clear - Hx SPT. lia. }
    pose proof (munch_refl (@nil (Z * Z)) m') as MU'.
    assert (UW' : uw_chain USTACK_TOP m' (bv_unsigned sp) (bv_unsigned s0) ras).
    { apply (uw_chain_agree m1 m' ras (bv_unsigned sp) (bv_unsigned s0) UWm1). eapply agree_on_mono; [exact AG'|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
    apply implA_from_evt.
    do 4 step. do 13 step. release_frame FR' ST' (bv_unsigned sp). step. step.
    apply evt_done.
    eapply (CRYPTO_free_walkA) with (A := A) (n := 72) (lo := lo) (ras := ras) (OW := L') (LB := LB); try reflexivity.
    - exact HEAP'.
    - exact INQC'.
    - exact ST'.
    - exact CEIL.
    - unfold CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - SPT. lia.
    - exact SP16.
    - exact MI'.
    - exact CS'.
    - exact UW'.
    - exact (uk_ctx_tail _ _ _ (E_BN_CTX_free_2273e4 : uk_tail BN_CTX_FREE BnRepDefs.CRYPTO_FREE) CTX).
    - intros Σ7 ms7 PO. apply K. unfold gfree_postA.
      destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F7 & fc7 & m7 & -> & MI7 & ST7 & AG7 & CR7 & HEAP7).
      assert (EL7 : lb_remove qc (L' ++ LB) = lb_remove qc L' ++ LB) by (rewrite lb_remove_app, (lb_remove_notin qc LB QCLB); reflexivity).
      rewrite EL7 in AG7. rewrite <- EL.
      do 17 eexists. exists m7. split; [reflexivity|].
      split; [exact MI7|]. split; [exact ST7|].
      split. { eapply agree_on_trans; [| exact AG7].
               eapply agree_on_trans; [eapply agree_client_weaken; [exact AG1| clear; lia|]| eapply agree_client_weaken; [exact AG'| clear; lia| auto]].
               intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left; apply INCL; eapply lb_remove_incl; exact Hb| right; exact Hb]. }
      split; [rewrite CR7; exact CR'| exact HEAP7]. }

  assert (REST : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σ' : rts RT),
    let L0 := lb_remove_list (opt_ids oi) OW in
    mem_inv bgbsegs m' -> stk bgbsegs m' lo (bv_unsigned sp + -112) ->
    agree_on (aclient_addr (L0 ++ LB) (bv_unsigned sp + -112)) m1 m' -> rt_credit RT Σ' = rt_credit RT Σ -> AHEAP Σ' L0 LB m' -> BnRepDefs.crypto_statics m' ->
    implA (tfrees (item_ids items vals) (tfrees [qc] k)) Σ' Q
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 A)
               a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (A + 32)) (Z_to_bv 64 (Z.shiftr (A + 32) 3 + SHB)) s4 s5 (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F' (Z_to_bv 64 2258072) fc' None m' (seg_rom bgbsegs))).
  { intros until Σ'. intros L0 MI' ST' AG' CR' HEAP' CS'.
    assert (NQI : forall blk, In blk OW -> In (blk_id blk) (item_ids items vals ++ [qc]) -> In blk L0).
    { intros blk Hb Hi. unfold L0. apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_In; [exact Hb|]. intros Ho.
      eapply (OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_disj _ _ (blk_id blk) ND); [exact Ho| exact Hi]. }
    assert (INQC0 : In (qc, A, 72) L0) by (apply NQI; [exact INQC| apply in_or_app; right; left; reflexivity]).
    assert (INCL0 : forall b, In b L0 -> In b OW) by (intros b Hb; unfold L0 in Hb; eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_incl; exact Hb).
    assert (INQCL0 : In (qc, A, 72) (L0 ++ LB)) by (apply in_or_app; left; exact INQC0).
    apply (rw_cells_agree _ _ _ _ _ AG') in CX; [| intros x Hx; cbn in Hx; apply CLc; [exact INQCL0| clear - Hx; lia]].
    assert (FR' : rw_cells bgbsegs m' (bv_unsigned sp + -112) [CB 8 jfr; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_agree; [exact AG'| exact FR|]. intros x Hx. cbn in Hx. left. unfold USTACK_TOP. clear - Hx SPT. lia. }
    assert (PI0 : pitemsA m' L0 items Hs vals prev).
    { eapply pitemsA_transport; [exact PI1| exact AG'|]. intros blk Hb Hi.
      assert (Hb0 : In blk L0) by (apply NQI; [exact Hb| apply in_or_app; left; exact Hi]).
      split; [exact Hb0|]. intros x Hx. right. right. exists blk. split; [apply in_or_app; left; exact Hb0| exact Hx]. }
    assert (UW0 : uw_chain USTACK_TOP m' (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { apply (uw_chain_agree m1 m' _ _ _ UW1). eapply agree_on_mono; [exact AG'|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
    pose proof (AH_acc_in _ _ _ _ (qc, A, 72) A 72 HEAP' INQCL0 ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear; lia)) as ACC0.
    pose proof (AH_offsh _ _ _ _ (qc, A, 72) HEAP' INQCL0) as OFC. cbn [blk_addr blk_size fst snd] in OFC. unfold SHLO, SHHI in OFC.
    clear ACC MU WM OFF SHB1 SHB2 HEAP HEAP1 ST MI FR CS1 PI1 UW UW1 UWm1 AG1.
    pose proof (munch_refl [(A, A + 72)]%Z m') as MU'. pose proof (wmono_refl bgbsegs m') as WM'.
    assert (OFF' : offshW [(A, A + 72)]) by (cbn [offshW]; unfold SHLO, SHHI; clear - OFC; lia).
    apply implA_from_evt.
    shl_with ACC0 AL. chk0.
    step. step. step. shl_with ACC0 AL. chk0.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m'' end.
    assert (WB' : Forall (fun iv : Z * Z => blk_addr (qc, A, 72) <= fst iv /\ snd iv <= blk_addr (qc, A, 72) + blk_size (qc, A, 72)) [(A, A + 72)]).
    { constructor; [cbn; clear; lia| constructor]. }
    assert (HEAP'' : AHEAP Σ' L0 LB m'').
    { eapply (BnIfaceA.seg_heap Σ' L0 LB m' m'' _ lo (bv_unsigned sp + -112) HEAP' MU' WM'); [| exact CEIL | unfold USTACK_TOP; clear - SPT; lia].
      constructor; [right; exists (qc, A, 72); split; [exact INQC0| cbn; clear; lia] | constructor]. }
    assert (AGB : forall LL, (forall b, In b LL -> In b (L0 ++ LB) /\ blk_id b <> qc) -> agree_on (aclient_addr LL (bv_unsigned sp + -112)) m' m'').
    { intros LL HLL. eapply (block_munch_agree Σ' L0 LB m' m'' _ LL (bv_unsigned sp + -112) (qc, A, 72) HEAP' MU' INQCL0); [clear - CEIL LO'; lia| exact WB'| exact HLL]. }
    assert (INC0 : forall bb, In bb (lb_remove qc L0 ++ LB) -> In bb (L0 ++ LB) /\ blk_id bb <> qc).
    { intros bb Hbb. apply in_app_or in Hbb. destruct Hbb as [Hbb|Hbb].
      - apply lb_remove_In in Hbb. destruct Hbb as [Hbb Hne]. split; [apply in_or_app; left; exact Hbb| exact Hne].
      - split; [apply in_or_app; right; exact Hbb|]. intros E. apply QCLB. rewrite <- E. apply in_map. exact Hbb. }
    assert (CS'' : BnRepDefs.crypto_statics m'').
    { eapply BnRepA.crypto_statics_agree; [exact (AGB [] ltac:(intros b [])) | | exact CS']. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
    assert (PI'' : pitemsA m'' L0 items Hs vals prev).
    { eapply pitemsA_transport; [exact PI0| exact (AGB _ INC0)|].
      intros blk Hb Hi. split; [exact Hb|]. intros x Hx. right. right. exists blk. split; [| exact Hx].
      apply in_or_app. left. apply lb_remove_In. split; [exact Hb|]. intros E. apply NIQC. rewrite <- E. exact Hi. }
    assert (UW'' : uw_chain USTACK_TOP m'' (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { eapply uw_chain_munch_nw; [exact UW0 | exact MU' |]. constructor; [cbn; unfold BnHeapA.ACEIL in *; clear - CAC CEIL LO'; lia | constructor]. }
    assert (AG'' : agree_on (aclient_addr (lb_remove qc L0 ++ LB) (bv_unsigned sp + -112)) m1 m'').
    { eapply agree_on_trans; [| exact (AGB _ INC0)].
      eapply agree_client_weaken; [exact AG'| clear; lia|]. intros bb Hbb. exact (proj1 (INC0 bb Hbb)). }
    step. if_cases KB; zify_cond KB.
    -
      destruct items as [|q' items'].
      2: { destruct Hs as [|H' Hs']; cbn [pitemsA] in PI''; [contradiction|]. destruct PI'' as (INQ' & _). exfalso.
           pose proof (AH_range _ _ _ _ _ _ _ HEAP'' INQ') as (Q0 & _ & _ & QC' & _). cbn [hd] in KB.
           change 18446744073709551615 with (Z.ones 64) in KB. rewrite Z.land_ones in KB by (clear; lia).
           rewrite Z.mod_small in KB by (unfold BnHeapA.ACEIL in *; clear - Q0 QC' C1 C2 C3; lia). clear - KB Q0. lia. }
      cbn [item_ids OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.item_ids tfrees OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees
           OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list] in EXIT |- *.
      apply evt_done.
      eapply EXIT; [eassumption | eassumption | exact AG'' | exact CR' | exact HEAP'' | exact CS'' | exact INQC0 | exact INCL0 | reflexivity].
    -
      destruct items as [|q' items']; [destruct Hs; cbn [pitemsA] in PI''; [| contradiction]; exfalso; apply KB; reflexivity|].
      step. hide_ors. ub. unhide. do 4 step.
      rewrite ?(unsigned_lit (A + 8)) by (unfold BnHeapA.ACEIL in *; clear - CA0 CAC C1 C2 C3; lia). rewrite ?EA0.
      apply evt_done.
      eapply (items_loopA (q' :: items') Hs vals prev) with (qc := qc) (OW := L0) (LB := LB) (lo := lo) (ras := bv_unsigned ra :: ras) (EX := [qc]);
        [ exact PI'' | intros E; discriminate E | exact HEAP'' | exact INQC0
        | apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.NoDup_app_r in ND; exact ND | left; reflexivity
        | intros p0 Hp0; apply NLB; apply in_or_app; right; apply in_or_app; left; exact Hp0
        | unfold ctxf_cells, MallocRep.wz; eassumption | rewrite ESP; eassumption | exact CEIL
        | rewrite ESP; unfold BN_CLEAR_FREE_STACK, BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK; clear - LO'; lia
        | rewrite ESP; unfold USTACK_TOP; clear - SPT; lia | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia
        | eassumption | exact CS'' | rewrite ESP; exact UW'' | exact CTXB | exact CTXF | ].
      intros Σ3 ms3 PO. unfold il_postA, MallocRep.wz in PO. rewrite ?ESP in PO.
      destruct PO as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & F3 & fc3 & m3 & -> & MI3 & ST3 & AG3 & CR3 & HEAP3 & CS3 & CX3).
      eapply EXIT; [exact MI3 | exact ST3 | | rewrite CR3; exact CR' | exact HEAP3 | exact CS3 | | | reflexivity].
      + eapply agree_on_trans; [eapply agree_client_weaken; [exact AG''| clear; lia|]| exact AG3].
        intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left| right; exact Hb].
        pose proof (proj1 (lb_remove_In _ _ _) Hb) as [Hb3 Hne]. apply (proj2 (lb_remove_In _ _ _)).
        split; [eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_incl; exact Hb3| exact Hne].
      + apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_In; [exact INQC0| exact NIQC].
      + intros b Hb. apply INCL0. eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_incl. exact Hb. }

  apply evt_done.
  destruct oi as [qi|]; cbn [opt_ids OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.opt_ids tfrees OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees
                             OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list app] in REST, NLB |- *.
  - assert (QILB : ~ In qi (map blk_id LB)) by (apply NLB; left; reflexivity).
    eapply (CRYPTO_free_walkA) with (p := qi) (A := IX) (n := 128) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + exact IDX.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
    + rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact CS1.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_CTX_free_2272b0 : uk_call BN_CTX_FREE 0x227498 BnRepDefs.CRYPTO_FREE) CTX).
    + intros Σ2 ms2 PO.
      destruct PO as (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & F2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
      rewrite ?ESP in *. rewrite (ret_pc_even 2258072) by (clear; lia).
      assert (EL2 : lb_remove qi (OW ++ LB) = lb_remove qi OW ++ LB) by (rewrite lb_remove_app, (lb_remove_notin qi LB QILB); reflexivity).
      rewrite EL2 in AG2.
      eapply REST; [exact MI2 | exact ST2 | exact AG2 | exact CR2 | exact HEAP2 |].
      eapply BnRepA.crypto_statics_agree; [exact AG2 | | exact CS1]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx).
  - subst IX.
    eapply implA_step_same.
    { eapply (CRYPTO_free_null_cpsA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
      - exact HEAP1.
      - rewrite ESP. exact ST.
      - exact CEIL.
      - rewrite ESP. unfold CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
      - rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
      - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
      - exact MI.
      - exact CS1.
      - rewrite ESP. exact UW1.
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_CTX_free_2272b0 : uk_call BN_CTX_FREE 0x227498 BnRepDefs.CRYPTO_FREE) CTX). }
    intros ms2 (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & AG2).
    rewrite ?ESP in *. rewrite (ret_pc_even 2258072) by (clear; lia).
    eapply REST; [exact MI2 | exact ST2 | exact AG2 | reflexivity | exact HEAP2 |].
    eapply BnRepA.crypto_statics_agree; [exact AG2 | | exact CS1]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx).
Qed.

Lemma BN_CTX_free_treeA : forall (qc : bptr) (bs : bstate bptr), st_wf bs -> pool_fl0 bs = true ->
  BN_CTX_free (tree_ops bptr) qc bs
  = tfrees (ctx_free_ids (gx_indexes (st_ctx bs)) (gx_items (st_ctx bs)) (skipn NFIX (st_bns bs)) qc) (TRet (tt, st_ctx_freed bs)).
Proof.
  intros qc bs WF PF. pose proof WF as (EL & _).
  assert (HF : forall j, (j < BN_CTX_POOL_SIZE * length (gx_items (st_ctx bs)))%nat -> bn_flags (getbn (RPool j) bs) = 0).
  { intros j Hj. unfold pool_fl0 in PF. rewrite forallb_forall in PF. apply Z.eqb_eq. apply PF.
    unfold getbn, RPool. rewrite <- nth_skipn. apply nth_In. rewrite length_skipn. lia. }
  destruct (OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.pfin_tree (gx_items (st_ctx bs)) 0 bs) as (s' & E1 & (P1 & P2 & P3 & P4 & P5 & P6 & P7)).
  { cbn [Nat.add]. rewrite EL. lia. }
  { intros j Hj. apply HF. cbn [Nat.add] in Hj. lia. }
  unfold BN_CTX_free. unfold bbind at 1. unfold bgetctx at 1. cbn [bind ret tree_ops tbind fst snd].
  unfold bbind at 1. cbn [bind tree_ops]. unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.ctx_free_ids.
  rewrite !OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees_app.
  assert (EF : forall (K : unit * bstate bptr -> btree bptr (unit * bstate bptr)),
            tbind (bfree_opt (tree_ops bptr) (gx_indexes (st_ctx bs)) bs) K = tfrees (opt_ids (gx_indexes (st_ctx bs))) (K (tt, bs))).
  { intros K. destruct (gx_indexes (st_ctx bs)) as [qi|]; reflexivity. }
  rewrite EF. f_equal. cbn [fst snd].
  unfold bbind at 1. cbn [bind tree_ops]. rewrite E1. f_equal. replace (NFIX + BN_CTX_POOL_SIZE * 0)%nat with NFIX by (unfold BN_CTX_POOL_SIZE; lia).
  f_equal. unfold bbind, bfree, bgetst, bsetbns, bsetctx. cbn [bind ret lib_free tree_ops tbind fst snd OSSVerify.Proofs.openssl.bignum.lib.BgBnR.CtxFreeModel.tfrees].
  f_equal. f_equal. f_equal. unfold st_ctx_freed, set_ctx, set_bns. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift].
  rewrite P2, P3, P4, P5, P6. reflexivity.
Qed.

Lemma val_ids_blocks : forall (vs : list (bignum bptr)), val_ids vs = map fst (concat (map bn_blocks vs)).
Proof.
  induction vs as [|b vs IH]; [reflexivity|]. rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids_cons. cbn [map concat]. rewrite map_app, <- IH. f_equal.
  unfold bn_blocks. destruct (bn_d b); reflexivity.
Qed.

Lemma val_ids_app : forall (l1 l2 : list (bignum bptr)), val_ids (l1 ++ l2) = val_ids l1 ++ val_ids l2.
Proof. intros l1 l2. unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.val_ids. apply flat_map_app. Qed.

Lemma firstn_add_gen : forall {T} n k (l : list T), firstn (n + k) l = firstn n l ++ firstn k (skipn n l).
Proof.
  intros T n. induction n as [|n IH]; intros k l; [reflexivity|]. destruct l as [|x l]; cbn [Nat.add firstn skipn app].
  - rewrite firstn_nil. reflexivity.
  - f_equal. apply IH.
Qed.

Lemma item_ids_perm : forall items (vals : list (bignum bptr)),
  Permutation (item_ids items vals) (val_ids (firstn (16 * length items) vals) ++ items).
Proof.
  induction items as [|q items IH]; intros vals; [cbn; apply Permutation_refl|].
  rewrite OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.item_ids_cons. cbn [length].
  replace (16 * S (length items))%nat with (16 + 16 * length items)%nat by lia.
  rewrite firstn_add_gen, val_ids_app. rewrite <- app_assoc.
  apply Permutation_app_head. eapply Permutation_trans; [apply perm_skip; apply IH|]. apply Permutation_middle.
Qed.

Lemma ctx_free_ids_perm : forall (bs : bstate bptr) qc, length (st_bns bs) = (NFIX + 16 * length (gx_items (st_ctx bs)))%nat ->
  Permutation (ctx_free_ids (gx_indexes (st_ctx bs)) (gx_items (st_ctx bs)) (skipn NFIX (st_bns bs)) qc) (ctx_part_ids bs qc).
Proof.
  intros bs qc EL. unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.ctx_free_ids, ctx_part_ids.
  assert (E1 : opt_ids (gx_indexes (st_ctx bs)) = map fst (opt_block (gx_indexes (st_ctx bs)) (4 * Z.of_nat BN_CTX_START_FRAMES)))
    by (destruct (gx_indexes (st_ctx bs)); reflexivity).
  rewrite E1. rewrite <- val_ids_blocks.
  assert (E2 : firstn (16 * length (gx_items (st_ctx bs))) (skipn NFIX (st_bns bs)) = skipn NFIX (st_bns bs)) by (apply firstn_all2; rewrite length_skipn; lia).
  pose proof (item_ids_perm (gx_items (st_ctx bs)) (skipn NFIX (st_bns bs))) as P. rewrite E2 in P.
  set (ix := map fst (opt_block (gx_indexes (st_ctx bs)) (4 * Z.of_nat BN_CTX_START_FRAMES))) in *.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; exact P|].
  set (v := val_ids (skipn NFIX (st_bns bs))). set (it := gx_items (st_ctx bs)). clearbody ix v it.

  eapply Permutation_trans; [apply Permutation_app_comm|].
  eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_comm|].
  cbn [app]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

Lemma lb_remove_nodup : forall p (L : list block), List.NoDup (map blk_id L) -> List.NoDup (map blk_id (lb_remove p L)).
Proof.
  intros p L. induction L as [|b L IH]; intros ND; [exact ND|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [N1 N2].
  rewrite lb_remove_cons. destruct (bptr_eqb (blk_id b) p); [exact (IH N2)|]. cbn [map]. constructor; [| exact (IH N2)].
  intros Hi. apply N1. apply in_map_iff in Hi. destruct Hi as (c & Ec & Hc). apply in_map_iff. exists c. split; [exact Ec| eapply lb_remove_incl; exact Hc].
Qed.

Lemma lb_remove_list_length : forall ps (L : list block), List.NoDup (map blk_id L) -> List.NoDup ps -> (forall p, In p ps -> In p (map blk_id L)) ->
  (length (lb_remove_list ps L) + length ps = length L)%nat.
Proof.
  induction ps as [|p ps IH]; intros L ND NP HI; [cbn; lia|]. cbn [OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list length].
  apply NoDup_cons_iff in NP as [P1 P2].
  pose proof (lb_remove_length p L ND (HI p ltac:(left; reflexivity))) as E.
  rewrite Nat.add_succ_r, (IH (lb_remove p L) (lb_remove_nodup p L ND) P2); [exact E|].
  intros p' Hp'. pose proof (HI p' ltac:(right; exact Hp')) as Hin. apply in_map_iff in Hin. destruct Hin as (c & Ec & Hc).
  apply in_map_iff. exists c. split; [exact Ec|]. apply lb_remove_In. split; [exact Hc|]. rewrite Ec. intros ->. exact (P1 Hp').
Qed.

Definition RfreeA (m : mem) (L : list block) : bnR := fun a b _ => bn_rep_rw m L None a b /\ bg_ok b /\ bn_flags b = 0.

Lemma RfreeA_pbnA : forall m L a b r, RfreeA m L a b r -> pbnA m L a b.
Proof.
  intros m L a b r ((D & CE & ARR) & (OK1 & OK2 & OK3 & OK4) & FL). exists D. split; [exact CE|].
  unfold bn_arr in ARR. split; [| split; [unfold BG_DMAX in OK3; lia| exact FL]].
  destruct (bn_d b) as [p|]; [exact ARR| exact (proj1 ARR)].
Qed.

Lemma bns_gen_pbnsA : forall m L l a i, bns_gen (RfreeA m L) a l i -> pbnsA m L a l.
Proof.
  intros m L l. induction l as [|b l IH]; intros a i H; [exact I|]. cbn [bns_gen pbnsA] in *. destruct H as [H1 H2].
  split; [eapply RfreeA_pbnA; exact H1| eapply IH; exact H2].
Qed.

Lemma items_gen_pitemsA : forall m L items Hs vals k prev,
  items_gen (RfreeA m L) false m L items Hs vals k prev -> pitemsA m L items Hs vals prev.
Proof.
  intros m L items. induction items as [|q items IH]; intros Hs vals k prev HG; destruct Hs as [|H Hs]; cbn [items_gen pitemsA] in *;
    [exact I| exact HG| contradiction|].
  destruct HG as (Hin & H16 & Hb & HL & HG). split; [exact Hin|]. split; [exact H16|].
  split; [eapply bns_gen_pbnsA; exact Hb|]. split; [exact (HL eq_refl)| eapply IH; exact HG].
Qed.

Lemma BN_CTX_free_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_CTX_FREE_STACK 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CTX_FREE (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
  implA (BN_CTX_free_g (tree_ops bptr) qc ls) Σ
    (bn_postA_p ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA 0
                (fun _ ls' OW' PL' _ => PL' = pl_set_ctx PL None /\ ls' = st_ctx_freed ls /\ cnt_bal ls' OW' = cnt_bal ls OW - 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_FREE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until qc. intros PRE UW CTX -> E ->.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND. pose proof (AH_nodup _ _ _ _ HEAP) as NDL.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof WFS as (EL & OKS & _ & _). unfold BN_CTX_POOL_SIZE in EL.
  unfold BN_CTX_free_g. destruct (pool_fl0 ls) eqn:PF; [| apply implA_unr].
  rewrite (BN_CTX_free_treeA qc ls WFS PF).

  pose proof LS as (_ & _ & _ & (_ & _ & _ & (_ & _ & M3 & _))). rewrite E in M3.
  destruct M3 as [Hinc (Hs & Ia & LHs & HCX & HIT)]. destruct (HCX eq_refl) as [CX SREP]. clear HCX.
  set (c := st_ctx ls) in *. set (items := gx_items c) in *. set (vals := skipn NFIX (st_bns ls)) in *.
  assert (LV : length vals = (16 * length items)%nat) by (unfold vals; rewrite length_skipn; clear - EL; lia).

  assert (PIT : pitemsA m OW items Hs vals 0).
  { eapply items_gen_pitemsA.
    eapply (items_gen_impl_idx (holeR [] m OW PL) (RfreeA m OW)); [| exact HIT].
    intros k q0 H0 j Ek EH Hj [[]|(D & SC & ARR)]. rewrite pl_of_pool in SC, ARR. cbn [Nat.add] in *.
    assert (KL : (k < length items)%nat) by (apply nth_error_Some; rewrite Ek; discriminate).
    assert (IDX : (16 * k + j < length vals)%nat) by (unfold BN_CTX_POOL_SIZE in *; clear - LV KL Hj; lia).
    set (b0 := nth (BN_CTX_POOL_SIZE * k + j) vals (bn_nil 0)) in *.
    assert (EB : b0 = getbn (RPool (16 * k + j)) ls) by (unfold b0, getbn, RPool, vals, BN_CTX_POOL_SIZE; rewrite nth_skipn; reflexivity).
    split; [|split].
    - exists D. split; [exact SC| exact ARR].
    - rewrite EB. apply OKS; [unfold RPool; rewrite EL; clear - KL Hj; unfold BN_CTX_POOL_SIZE in Hj; lia| unfold RPool, ROne, NFIX; clear; lia].
    - unfold pool_fl0 in PF. rewrite forallb_forall in PF. apply Z.eqb_eq. apply PF. fold vals. unfold b0. apply nth_In. unfold BN_CTX_POOL_SIZE. exact IDX. }

  set (ids := ctx_free_ids (gx_indexes c) items vals qc).
  pose proof (ctx_free_ids_perm ls qc EL) as PERM. fold c items vals ids in PERM.
  destruct (lib_state_unplace_ctx [] ls m OW PL EA ac qc LS ltac:(intros i []) E) as (LSU & DISJ).
  assert (NDI : List.NoDup ids).
  { eapply Permutation_NoDup; [apply Permutation_sym; exact PERM|].
    pose proof (Permutation_NoDup (all_ids_ctx_split ls PL EA ac qc E) IDS) as N. eapply nodup_app_l. exact N. }
  assert (IDOW : forall p, In p ids -> In p (map blk_id OW)).
  { intros p Hp. eapply (all_ids_owned ls m OW PL EA p LS ND).
    eapply Permutation_in; [apply Permutation_sym; apply (all_ids_ctx_split ls PL EA ac qc E)|]. apply in_or_app. left.
    eapply Permutation_in; [exact PERM| exact Hp]. }
  assert (IDLB : forall p, In p ids -> ~ In p (map blk_id LB)).
  { intros p Hp H. rewrite map_app in NDL. exact (nodup_app_disj _ _ p NDL (IDOW p Hp) H). }
  assert (IDFRESH : forall p, In p ids -> ~ In p (all_ids (st_ctx_freed ls) (pl_set_ctx PL None) EA)).
  { intros p Hp. apply DISJ. eapply Permutation_in; [exact PERM| exact Hp]. }

  assert (LCNT : (length (blocks_of ls) + 1 = length ids + length (blocks_of (st_ctx_freed ls)))%nat).
  { pose proof (Permutation_length (all_ids_ctx_split ls PL EA ac qc E)) as PLn. pose proof (Permutation_length PERM) as PLi.
    unfold all_ids, pl_ids in PLn. rewrite pl_bn_ids_set_ctx in PLn. cbn [pl_ctx pl_mont pl_set_ctx] in PLn. rewrite E in PLn.
    set (xa := pl_bn_ids PL NFIX) in PLn. set (xb := OSSVerify.Proofs.openssl.bignum.lib.BgRepB.BgRepDefs.opt_ids (pl_mont PL)) in PLn. set (xc := ctx_part_ids ls qc) in PLn, PLi.
    set (xd := blocks_of ls) in *. set (xe := blocks_of (st_ctx_freed ls)) in *. clearbody xa xb xc xd xe.
    rewrite !length_app, !length_map in PLn. cbn [OSSVerify.Proofs.openssl.bignum.lib.BgRepB.BgRepDefs.opt_ids length] in PLn. rewrite <- PLi in PLn.
    clear - PLn. lia. }
  assert (FROK' : frames_ok (pl_set_ctx PL None) (bv_unsigned sp) USTACK_TOP) by (apply frames_ok_set_ctx; exact FROK).
  eapply (BN_CTX_free_cpsA) with (lo := lo) (A := ac) (IX := Ia) (Hs := Hs) (prev := 0) (ras := ras) (OW := OW) (LB := LB) (oi := gx_indexes c) (items := items) (vals := vals);
    [exact HEAP | exact Hinc | exact CX | | exact PIT | exact NDI | exact IDLB | exact ST | exact CEIL | exact LO | exact SPT | exact SP16
    | exact MI | reflexivity | exact (proj1 LS) | reflexivity | exact UW | exact CTX | ].
  { unfold stack_rep in SREP. destruct (gx_indexes c) as [qi|]; [exact (proj1 SREP)| exact (proj1 SREP)]. }
  intros Σ7 ms7 PO. unfold gfree_postA in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F7 & fc7 & m7 & -> & MI7 & ST7 & AG7 & CR7 & HEAP7).
  apply implA_ret.
  fold ids in AG7, HEAP7.
  set (OWF := lb_remove_list ids OW) in *.
  unfold bn_postA_p. do 17 eexists. exists m7, OWF, (pl_set_ctx PL None). split; [reflexivity|]. cbn [fst snd].
  split; [exact HEAP7|].
  split. { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ (bv_unsigned sp) (bv_unsigned sp) USTACK_TOP); [| exact FROK'| clear; lia| clear; lia| exact AG7|].
           - eapply lib_state_h_ow; [exact LSU|]. intros q0 A0 n0 Hq0 Hin0. apply OSSVerify.Proofs.openssl.bignum.lib.BgBnP2.W_ctxfree3.lb_remove_list_In; [exact Hin0|].
             cbn [blk_id fst]. intros Hid. exact (IDFRESH q0 Hid Hq0).
           - intros bk Hbk. apply in_or_app. left. exact Hbk. }
  split; [exact ST7|]. split; [exact MI7|].
  split. { eapply agree_on_mono; [exact AG7|]. intros x [_ [Hx|[Hx|(bk & Hbk & Hr)]]];
             [left; exact Hx | right; left; exact Hx | right; right; exists bk; split; [apply in_or_app; right; exact Hbk | exact Hr]]. }
  split; [rewrite CR7; clear; lia|].
  split; [reflexivity|]. split; [reflexivity|].
  unfold cnt_bal. pose proof (lb_remove_list_length ids OW ND NDI IDOW) as LL. fold OWF in LL. clear - LL LCNT. lia.
Qed.

End WithRT.
