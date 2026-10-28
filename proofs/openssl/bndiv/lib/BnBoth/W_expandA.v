(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2027096 => 1
  | 2027100 => 2
  | 2028012 => 2
  | 2028020 => 1
  | 2028024 => 2
  | 2028228 => 1
  | 2028232 => 1
  | 2028236 => 2
  | 2029404 => 2
  | 2029408 => 1
  | 2029412 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition BN_FREE_D : Z := 0x1eee48.
Definition BN_FREE_D_STACK : Z := 16 + CRYPTO_CLEAR_FREE_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Local Notation E_bfd_tail := (E_bn_free_d_1f3b14 : uk_tail BN_FREE_D CRYPTO_CLEAR_FREE).

Lemma cfree_postA_weaken : forall ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p lo m m1 Σ' ms',
  agree_on (aclient_addr (lb_remove p (OW ++ LB)) (bv_unsigned sp)) m m1 ->
  cfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p lo m1 Σ' ms' ->
  cfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p lo m Σ' ms'.
Proof.
  intros until ms'. intros AG (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & E & MI2 & ST2 & AG2 & Rest).
  do 17 eexists. exists m2. split; [exact E|]. split; [exact MI2|]. split; [exact ST2|].
  split; [eapply agree_on_trans; [exact AG | exact AG2] | exact Rest].
Qed.

(* [comment removed for export] *)
Lemma bn_free_d_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (p : bptr) (D n dm f a lo : Z) (tw nw : word) (bs : block) (ras : list Z)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> In (p, D, n) OW ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_FREE_D_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A -> crypto_statics m ->
  rw_cells bsegs m a [C8 (wz D); C4 tw; C4 (wz dm); C4 nw; C4 (wz f)] -> 0 <= f <= 1 -> 0 <= dm < 2^31 -> 8 * dm <= n ->
  In bs (OW ++ LB) -> blk_addr bs <= a -> a + 24 <= blk_addr bs + blk_size bs -> a mod 8 = 0 ->
  a0 = wz a -> a1 = wz 1 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FREE_D (bv_unsigned ra :: ras) ->
  (forall Σ' ms', cfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (TFree p k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_FREE_D) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HEAP IN ST CEIL LO SPT SP16 MI -> CS BN Hf Hdm Hn INS RS1 RS2 AL -> -> UW CTX K.
  unfold BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK, BN_FREE_D, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bs HEAP INS) as (S0 & _ & _ & SC & SI).
  pose proof (AH_acc_in _ _ _ _ bs a 24 HEAP INS RS1 RS2) as ACC.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  apply (flag_cell_split bsegs m a _ _ _ _ f Hf) in BN.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 16%nat ST. do 7 (ub; step).
  do 3 (ub; step). ub; shl. ub; chk0.
  assert (EL8 : Z.land f 8 = 0) by (assert (f = 0 \/ f = 1) as [-> | ->] by lia; reflexivity).
  ub; step. rewrite (zxb_small f) by lia. ub; step. rewrite (unsigned_lit f), EL8 by lia. ub; step. if_false.
  ub; step. if_false.
  do 2 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl. ub; step. ub; chk0.
  ub; step. rewrite (sx32_small dm) by lia.
  do 4 (ub; step). rewrite ?(unsigned_lit dm) by lia.
  replace (Z.shiftl dm 3) with (8 * dm) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  do 2 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  apply evt_done.
  eapply (CRYPTO_clear_free_walkA) with (n := n) (num := 8 * dm) (lo := lo) (ras := ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - exact IN.
  - exact ST.
  - exact CEIL.
  - unfold CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK. lia.
  - unfold USTACK_TOP. lia.
  - exact SP16.
  - exact MI.
  - eapply crypto_statics_agree; [exact AG1 | | exact CS]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx).
  - lia.
  - lia.
  - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor].
  - exact (uk_ctx_tail _ _ _ E_bfd_tail CTX).
  - intros Σ' ms' PO. apply (K Σ' ms'). eapply cfree_postA_weaken; [| exact PO].
    eapply agree_client_weaken; [exact AG1 | lia | intros b Hb; eapply lb_remove_incl; exact Hb].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BN_EXPAND2 : Z := 0x1ef1c0.
Definition BN_WEXPAND : Z := 0x1ef74c.
Definition BN_EXPAND2_STACK : Z := 80 + CRYPTO_CALLOC_STACK.     (* [comment removed for export] *)
Local Notation E_be_calloc := (E_bn_expand2_1f3e68 : uk_call BN_EXPAND2 0x1ef270 CRYPTO_CALLOC).
Local Notation E_be_freed := (E_bn_expand2_1f3edc : uk_call BN_EXPAND2 0x1ef2fc BN_FREE_D).

(* [comment removed for export] *)
Definition bn_expanded (b : bignum bptr) (pn : bptr) (words : nat) : bignum bptr :=
  mkBN (Some pn) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b).

Lemma bn_expanded_dmax : forall b pn words, (bn_top b <= bn_dmax b)%nat -> (bn_dmax b < words)%nat -> bn_dmax (bn_expanded b pn words) = words.
Proof. intros b pn words H1 H2. unfold bn_dmax, bn_expanded in *. cbn [bn_buf]. rewrite length_app, firstn_length_le, repeat_length by lia. lia. Qed.

(* [comment removed for export] *)
Lemma expand_close : forall ls mF OWF AD EA r a pn An (words : nat),
  lib_state_h [r] ls mF OWF AD EA -> List.NoDup (map blk_id OWF) -> ref_at ls OWF AD r a ->
  rw_cells bsegs mF a [C8 (wz An); C4 (wz (Z.of_nat (bn_top (getbn r ls)))); C4 (wz (Z.of_nat words));
                       C4 (wz (Z.b2z (bn_neg (getbn r ls)))); C4 (wz (bn_flags (getbn r ls)))] ->
  In (pn, An, Z.of_nat words * 8) OWF ->
  u64arr bsegs mF An (wlimbs (firstn (bn_top (getbn r ls)) (bn_buf (getbn r ls)) ++ repeat 0 (words - bn_top (getbn r ls)))) ->
  ~ In pn (all_ids ls AD EA) -> (bn_dmax (getbn r ls) < words)%nat -> Z.of_nat words <= BN_WORDS_MAX ->
  lib_state (setbn r (bn_expanded (getbn r ls) pn words) ls) mF OWF AD EA
  /\ (words <= bn_dmax (getbn r (setbn r (bn_expanded (getbn r ls) pn words) ls)))%nat.
Proof.
  intros ls mF OWF AD EA r a pn An words LSH ND HA BN HIN U FRESH HLT HMAX.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSH HA) as HV.
  destruct (lib_state_h_parts _ _ _ _ _ _ LSH) as (IDS & ADB & ERRB & SOK).
  pose proof (st_okm_getbn r ls SOK HV) as (OK1 & OK2 & OK3 & OK4).
  set (b := getbn r ls) in *.
  pose proof (bn_expanded_dmax b pn words OK2 HLT) as EDM.
  split.
  - unfold lib_state. eapply (lib_state_close [] ls mF OWF AD EA r a); [exact LSH| exact ND| exact HA| | |].
    + exists An. split.
      * unfold bn_cells. rewrite EDM. exact BN.
      * unfold bn_arr. cbn [bn_expanded bn_d]. rewrite EDM. split; [rewrite Z.mul_comm; exact HIN| exact U].
    + unfold bn_okm. rewrite EDM. cbn [bn_expanded bn_buf bn_top bn_flags].
      split; [apply limbs_app; [apply limbs_firstn; exact OK1| apply limbs_repeat; exact limb_0]|]. split; [lia|]. split; [exact HMAX| exact OK4].
    + eapply ids_ok_setbn_new; [exact IDS| exact HV| reflexivity| exact FRESH].
  - rewrite getbn_setbn_same_m by exact HV. rewrite EDM. lia.
Qed.

(* [comment removed for export] *)
Definition wexpand_res (r : bnref) (words : nat) (ls ls' : lstate bptr) : Prop :=
  ((words <= bn_dmax (getbn r ls))%nat /\ ls' = ls)
  \/ ((bn_dmax (getbn r ls) < words)%nat /\ exists pn, ls' = setbn r (bn_expanded (getbn r ls) pn words) ls).

Lemma bn_expand2_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (r : bnref) (a : Z) (words : nat),
  bn_preA Σ ls m OW LB AD EA sp lo BN_EXPAND2_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_EXPAND2 (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD r a -> a0 = wz a -> a1 = wz (Z.of_nat words) -> Z.of_nat words < 2^31 ->
  implA (bn_wexpand (tree_ops bptr) r words ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC
              (fun _ ls' OW' a0' => a0' = wz a /\ (words <= bn_dmax (getbn r ls'))%nat /\ wexpand_res r words ls ls'
                                  /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn r ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_EXPAND2) fc None m (seg_rom bsegs)).
Proof.
  intros until words. intros (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED) UW CTX -> HA -> -> HW.
  unfold BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BN_EXPAND2, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW AD EA r a LS ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qs & As & ns & Eqs & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & SA16 & _ & SAC & SAI).
  pose proof (ref_at_al8 _ _ _ _ _ _ _ _ HEAP ADB HA) as AL.
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & LENW & D0 & DC & DI & DSEP).
  specialize (DSEP r a HA).
  set (b := getbn r ls) in *.
  unfold bn_cells in BN. unfold BN_WORDS_MAX in OK3.
  assert (INS : In (qs, As, ns) (OW ++ LB)) by (apply in_or_app; left; exact Hins).
  pose proof (AH_acc_in _ _ _ _ (qs, As, ns) a 24 HEAP INS Ra1 Ra2) as ACC.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (a, a + 24)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp); (a, a + 24)]).
  { pose proof (AH_offsh _ _ _ _ (qs, As, ns) HEAP INS) as O. cbn [blk_addr blk_size fst snd] in O.
    cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
  unfold bn_wexpand, bbind, bget, bret, bunr, bmalloc, bfree_opt, bset, bfree.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold b.
  apply implA_from_evt.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 11 (ub; step). ub; step. ub; step. do 3 (ub; step). do 3 (ub; step). ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax b))) by lia.
  ub; step. if_cases K; zify_cond K; rewrite !signed_small in K by lia.
  - (* [comment removed for export] *)
    replace (words <=? bn_dmax b)%nat with true by (symmetry; apply Nat.leb_le; lia). cbv beta iota.
    do 10 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
    apply evt_done. apply implA_ret.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (a, a + 24)]).
    { constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists (qs, As, ns). cbn. auto. }
    unfold bn_postA. do 17 eexists. exists mF, OW. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split. { unfold lib_state. rewrite <- (setbn_getbn_id_m r ls). fold b.
             eapply (lib_state_close [] ls mF OW AD EA r a b); [| exact ND| exact HA| | | ].
             - eapply lib_state_frame; [exact HEAP| exact LSH| exact MU| exact WM|].
               constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [|constructor].
               eapply (w_struct OW LB ls AD EA false [r] _ r a); [left; reflexivity| exact HA| cbn; lia| cbn; lia].
             - exists D. split; [unfold bn_cells; exact BN|]. eapply bn_arr_of_u64arr; [exact ARR| exact U].
             - unfold b. apply st_okm_getbn; assumption.
             - apply ids_ok_setbn_same; [exact IDS| exact HV| reflexivity]. }
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|].
    split; [unfold MC; lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [reflexivity|]. split; [fold b; lia|]. split; [left; split; [fold b; lia| reflexivity]|]. intros q0 A0 n0 Hq0 _. exact Hq0.
  - (* [comment removed for export] *)
    replace (words <=? bn_dmax b)%nat with false by (symmetry; apply Nat.leb_gt; lia). cbv beta iota.
    ub; step. ub; step. if_cases K2; zify_cond K2; rewrite ?signed_small in K2 by lia.
    { (* [comment removed for export] *)
      replace (BN_WORDS_MAX <? Z.of_nat words) with true by (symmetry; apply Z.ltb_lt; unfold BN_WORDS_MAX; lia). cbv beta iota.
      apply evt_done. apply implA_unr. }
    replace (BN_WORDS_MAX <? Z.of_nat words) with false by (symmetry; apply Z.ltb_ge; unfold BN_WORDS_MAX; lia).
    assert (FLR : 0 <= bn_flags b <= 1) by (destruct OK4 as [E|E]; rewrite E; lia).
    assert (EL2 : Z.land (bn_flags b) 2 = 0) by (destruct OK4 as [E|E]; rewrite E; reflexivity).
    assert (EL8 : Z.land (bn_flags b) 8 = 0) by (destruct OK4 as [E|E]; rewrite E; reflexivity).
    unfold BN_FLG_STATIC_DATA, BN_FLG_SECURE. rewrite EL2, EL8. cbn [Z.eqb negb]. cbv beta iota.
    do 3 (ub; step). ub; shl. ub; chk0.
    ub; step. unfold MallocRep.wz at 1. rewrite (zx32_small (bn_flags b)) by lia.
    ub; step. rewrite (unsigned_lit (bn_flags b)), EL2 by lia. ub; step. if_false.
    ub; step. rewrite (unsigned_lit (bn_flags b)), EL8 by lia. ub; step. if_false.
    do 6 (ub; step).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (a, a + 24)]).
    { constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists (qs, As, ns). cbn. auto. }
    assert (HEAP1 : AHEAP Σ OW LB m1) by (exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))).
    assert (LSH1 : lib_state_h [r] ls m1 OW AD EA).
    { eapply lib_state_frame; [exact HEAP| exact LSH| exact MU| exact WM|].
      constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [|constructor].
      eapply (w_struct OW LB ls AD EA false [r] _ r a); [left; reflexivity| exact HA| cbn; lia| cbn; lia]. }
    assert (AXP1 : ax_pres LB (bv_unsigned sp) LIBW_A m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { apply (uw_push_frame m1 _ (bv_unsigned sp) 80 [CB 8 (take 8 junk); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
        [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
      - rewrite !Z_to_bv_bv_unsigned. exact FR.
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia |]. constructor; [|constructor].
        cbn. unfold BnHeapA.ACEIL in *. lia. }
    apply evt_done.
    replace (8 * Z.of_nat words) with (Z.of_nat words * 8) by lia.
    eapply (CRYPTO_calloc_walkA) with (num := Z.of_nat words) (size := 8) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. lia.
    + rewrite ESP. unfold USTACK_TOP. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact (proj1 LSH1).
    + lia.
    + lia.
    + pose proof (cnt_ok_live ls OW LB OW 0 SOK CNT ltac:(lia) ltac:(lia)) as HL. rewrite length_map in HL. exact HL.
    + exact CRED.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_be_calloc CTX).
    + intros pn Σ1 ms1 FRESH PO.
      unfold calloc_postA in PO. rewrite ?ESP in PO.
      destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F1 & fc1 & m3 & An & -> & MI3 & ST3 & AG3 & CR3 & BR & HEAP3 & ACCN & BLK).
      rewrite (ret_pc_even 2028144) by lia.
      (* [comment removed for export] *)
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG3) in BN; [| intros x Hx; right; right; exists (qs, As, ns); split; [exact INS| cbn in Hx |- *; lia]].
      assert (LSH3 : lib_state_h [r] ls m3 OW AD EA).
      { eapply lib_state_h_heap_pres; [exact LSH1| exact AG3|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (ARR3 : bn_arr m3 OW D b).
      { eapply bn_arr_of_u64arr; [exact ARR|]. eapply u64arr_agree; [exact AG3| exact U|]. intros x Hx.
        unfold bn_arr in ARR. destruct (bn_d b) as [pd|]; [|destruct ARR as [_ Eb]; rewrite Eb in Hx; cbn in Hx; lia].
        right; right. exists (pd, D, 8 * Z.of_nat (bn_dmax b)). split; [apply in_or_app; left; exact (proj1 ARR)|]. cbn [blk_addr blk_size fst snd]. lia. }
      clear U.
      assert (UW3 : uw_chain USTACK_TOP m3 (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { eapply uw_chain_agree; [exact UW1|]. eapply agree_on_mono; [exact AG3|]. intros x Hx. left. exact Hx. }
      assert (AXP3 : ax_pres LB (bv_unsigned sp) LIBW_A m m3).
      { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
          [left; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (EAn : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
      set (OW1 := (pn, An, Z.of_nat words * 8) :: OW) in *.
      assert (ND1 : List.NoDup (map blk_id OW1)) by (exact (AH_nodup_l _ _ _ _ HEAP3)).
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + Z.of_nat words * 8 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ Hins) as SEPs.
      assert (LSH3' : lib_state_h [r] ls m3 OW1 AD EA) by (eapply lib_state_h_ow; [exact LSH3|]; intros q A n _ Hq; right; exact Hq).
      assert (HA1 : ref_at ls OW1 AD r a).
      { destruct r as [| | | | |i]; cbn [ref_at] in HA |- *; try exact HA. destruct HA as (p0 & H0 & E0 & I0 & R0). exists p0, H0. split; [exact E0|]. split; [right; exact I0| exact R0]. }
      assert (FRESHA : ~ In pn (all_ids ls AD EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (HinN : In (pn, An, Z.of_nat words * 8) OW1) by (left; reflexivity).
      assert (HinS1 : In (qs, As, ns) OW1) by (right; exact Hins).
      assert (INS1 : In (qs, As, ns) (OW1 ++ LB)) by (apply in_or_app; left; exact HinS1).
      pose proof (AH_acc_in _ _ _ _ (qs, As, ns) a 24 HEAP3 INS1 Ra1 Ra2) as ACC3.
      clear ACC MU WM OFF.
      cbn [tbind fst snd].
      unfold bn_arr in ARR3. destruct (bn_d b) as [pd|] eqn:Ed.
      2:{ (* [comment removed for export] *)
        destruct ARR3 as [-> Eb]. assert (ED0 : bn_dmax b = 0%nat) by (unfold bn_dmax; rewrite Eb; reflexivity).
        assert (ET0 : bn_top b = 0%nat) by lia.
        pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (a, a + 24)]%Z m3) as MU3. pose proof (wmono_refl bsegs m3) as WM3.
        assert (OFF3 : offshW [(bv_unsigned sp + -80, bv_unsigned sp); (a, a + 24)]).
        { pose proof (AH_offsh _ _ _ _ (qs, As, ns) HEAP3 INS1) as O. cbn [blk_addr blk_size fst snd] in O.
          cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
        unfold bret. cbn [ret tree_ops tbind fst snd].
        unfold MallocRep.wz in *.
        apply implA_from_evt.
        do 2 (ub; step). ub; step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; lia|]. clear KA.
        do 3 (ub; step). ub; shl. ub; chk0.
        ub; step. replace (sx32 (Z_to_bv 64 (Z.of_nat (bn_top b)))) with (Z_to_bv 64 0) by (rewrite ET0; reflexivity).
        ub; step. ub; step. if_true.
        ub; step. ub; shl. ub; chk0. ub; step. ub; step. if_true.
        ub; shl. ub; chk0. ub; step. ub; shl. ub; chk0. ub; step.
        do 10 (ub; step). release_frame FR ST3 (bv_unsigned sp). ub; step. ub; step.
        apply evt_done. apply implA_ret.
        lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
        assert (HWL3 : Forall (w_lib OW1 lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (a, a + 24)]).
        { constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists (qs, As, ns). cbn. auto. }
        assert (LSHF : lib_state_h [r] ls mF OW1 AD EA).
        { eapply (lib_state_frame Σ1 LB); [exact HEAP3| exact LSH3'| exact MU3| exact WM3|].
          constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [|constructor].
          eapply (w_struct OW1 LB ls AD EA false [r] _ r a); [left; reflexivity| exact HA1| cbn; lia| cbn; lia]. }
        assert (UF : u64arr bsegs mF An (wlimbs (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)))).
        { rewrite ET0, Eb. cbn [firstn app]. rewrite Nat.sub_0_r. apply (CB_u64arr bsegs mF An (Z.to_nat (Z.of_nat words * 8))).
          unfold wlimbs. rewrite map_repeat, u64s_repeat0. replace (8 * words)%nat with (Z.to_nat (Z.of_nat words * 8)) by lia. exact BLK. }
        destruct (expand_close ls mF OW1 AD EA r a pn An words LSHF ND1 HA1) as [LSF RESF];
          [fold b; exact BN| exact HinN| fold b; exact UF| exact FRESHA| fold b; lia| unfold BN_WORDS_MAX; lia|].
        unfold bn_postA. do 17 eexists. exists mF, OW1. split; [reflexivity|]. cbn [fst snd].
        fold (bn_expanded b pn words). fold b in LSF, RESF.
        split; [exact (seg_heap Σ1 OW1 LB m3 mF _ lo _ HEAP3 MU3 WM3 HWL3 CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
        split; [exact ST3|]. split; [exact MI3|].
        split; [eapply ax_pres_trans; [exact AXP3|]; exact (seg_ax_pres' Σ1 OW1 LB m3 mF _ lo _ _ HEAP3 MU3 HWL3 CEIL ltac:(lia))|].
        split; [exact CR3|].
        split. { unfold cnt_eq. rewrite (cnt_bal_setbn r (bn_expanded b pn words) ls OW OW1 HV). fold b.
                 unfold bn_blocks. rewrite Ed. cbn [bn_expanded bn_d length]. unfold OW1. cbn [length]. lia. }
        split. { intros r' a' HA'. apply ref_at_setbn. destruct r' as [| | | | |i]; cbn [ref_at] in HA' |- *; try exact HA'.
                 destruct HA' as (p0 & H0 & E0 & I0 & R0). exists p0, H0. split; [exact E0|]. split; [right; exact I0| exact R0]. }
        split; [reflexivity|]. split; [exact RESF|]. split; [right; split; [fold b; lia|]; exists pn; reflexivity|].
        intros q0 A0 n0 Hq0 _. right. exact Hq0. }
      (* [comment removed for export] *)
      destruct ARR3 as [HinD U3].
      pose proof (AH_range _ _ _ _ _ _ _ HEAP HinD) as (DA0 & DA16 & _ & DAC & _).
      pose proof (NEWSEP _ _ _ HinD) as SEPd.
      set (newbuf := firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)).
      cbn [tbind fst snd].
      assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
      pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl bsegs m3) as WM3.
      assert (OFF3 : offshW [(bv_unsigned sp + -80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
      unfold MallocRep.wz in *.
      lazymatch goal with |- implA _ _ ?Q0 _ => set (QQ := Q0) end.
      (* [comment removed for export] *)
      assert (TAIL : forall (m4 : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F4 : bvmap 5 word) (fc4 : bv 32),
        AHEAP Σ1 OW1 LB m4 -> mem_inv bsegs m4 -> stk bsegs m4 lo (bv_unsigned sp + -80) ->
        rw_cells bsegs m4 (bv_unsigned sp + -80) [CB 8 (take 8 junk); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells bsegs m4 a [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (Z.of_nat (bn_top b))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax b)));
                             C4 (Z_to_bv 64 (Z.b2z (bn_neg b))); C4 (Z_to_bv 64 (bn_flags b))] ->
        u64arr bsegs m4 An (wlimbs newbuf) ->
        lib_state_h [r] ls m4 OW1 AD EA ->
        ax_pres LB (bv_unsigned sp) LIBW_A m m4 ->
        uw_chain USTACK_TOP m4 (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned ra :: ras) ->
        implA (TFree pd (TRet ((), setbn r {| bn_d := Some pn; bn_buf := newbuf; bn_top := bn_top b; bn_neg := bn_neg b; bn_flags := bn_flags b |} ls))) Σ1 QQ
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 a) x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 (Z.of_nat words)) (Z_to_bv 64 (a + 12)) (Z_to_bv 64 An)
                   (Z_to_bv 64 ((a + 12) ≫ 3 + SHB)) (Z_to_bv 64 SHB) (Z_to_bv 64 (a ≫ 3)) s8 s9 s10 s11 x28 x29 x30 x31)
              F4 (Z_to_bv 64 2028252) fc4 None m4 (seg_rom bsegs))).
      { intros m4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F4 fc4 HEAP4 MI4 ST4 FR4 BN4 UN4 LSH4 AXP4 UW4.
        clear MU3 WM3 OFF3 ACC3.
        pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)]%Z m4) as MU5. pose proof (wmono_refl bsegs m4) as WM5.
        assert (HinD1 : In (pd, D, 8 * Z.of_nat (bn_dmax b)) OW1) by (right; exact HinD).
        assert (LENN : Z.of_nat (length (wlimbs newbuf)) = Z.of_nat words).
        { subst newbuf. rewrite wlimbs_len, length_app, firstn_length_le, repeat_length by (unfold bn_dmax in *; lia). lia. }
        pose proof (AH_acc_in _ _ _ _ (qs, As, ns) a 24 HEAP4 INS1 Ra1 Ra2) as ACC4.
        assert (OFF5 : offshW [(bv_unsigned sp + -80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
        apply implA_from_evt.
        ub; step. ub; shl. ub; chk0. ub; step. clear ACC4 OFF5.
        ub; step. if_cases KD; zify_cond KD; [exfalso; rewrite ?ED in KD; lia|]. clear KD.
        do 3 (ub; step).
        apply evt_done.
        eapply (bn_free_d_walkA) with (n := 8 * Z.of_nat (bn_dmax b)) (dm := Z.of_nat (bn_dmax b)) (f := bn_flags b) (a := a) (lo := lo)
                                      (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB) (bs := (qs, As, ns)); try reflexivity.
        - exact HEAP4.
        - exact HinD1.
        - rewrite ESP. exact ST4.
        - exact CEIL.
        - rewrite ESP. unfold BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK. lia.
        - rewrite ESP. unfold USTACK_TOP. lia.
        - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
        - exact MI4.
        - exact (proj1 LSH4).
        - unfold MallocRep.wz. exact BN4.
        - exact FLR.
        - lia.
        - exact INS1.
        - exact Ra1.
        - exact Ra2.
        - exact AL.
        - rewrite ESP. exact UW4.
        - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_be_freed CTX).
        - intros Σ6 ms6 PO. unfold cfree_postA in PO. rewrite ?ESP in PO.
          destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & F6 & fc6 & m6
                          & -> & MI6 & ST6 & AG6 & CR6 & HEAP6).
          rewrite (ret_pc_even 2028284) by lia.
          pose proof (AH_nodup _ _ _ _ HEAP4) as NDL.
          assert (EL : lb_remove pd (OW1 ++ LB) = lb_remove pd OW1 ++ LB).
          { apply lb_remove_app_l; [exact NDL|]. apply (in_map blk_id) in HinD1. exact HinD1. }
          rewrite EL in AG6. set (OWF := lb_remove pd OW1) in *.
          assert (NEqs : qs <> pd).
          { pose proof (bn_in_m r ls pd HV Ed) as Hm. destruct (ref_sid_cases _ _ _ _ Eqs) as [[H5 _]|[Hh _]].
            - eapply ids_ad_m; eauto using in5_ad.
            - intros ->. eapply (ids_bn_head_neq r ls pd pd); eauto using ids_m_nodup. }
          assert (NEpn : pn <> pd).
          { intros ->. apply FRESH. rewrite map_app. apply in_or_app. left. apply (in_map blk_id) in HinD. exact HinD. }
          assert (HinNF : In (pn, An, Z.of_nat words * 8) OWF) by (apply lb_remove_In; split; [exact HinN| exact NEpn]).
          assert (HinSF : In (qs, As, ns) OWF) by (apply lb_remove_In; split; [exact HinS1| exact NEqs]).
          assert (NDF : List.NoDup (map blk_id OWF)) by (exact (AH_nodup_l _ _ _ _ HEAP6)).
          assert (LSH6 : lib_state_h [r] ls m6 OWF AD EA).
          { eapply (lib_state_h_free Σ1 LB [r] ls m4 m6 OW1 AD EA r pd D); [exact HEAP4| exact LSH4| left; reflexivity| exact HV| exact Ed| exact HinD1|].
            rewrite EL. exact AG6. }
          assert (HAF : ref_at ls OWF AD r a).
          { destruct r as [| | | | |i]; cbn [ref_at] in HA1 |- *; try exact HA1. destruct HA1 as (p0 & H0 & E0 & I0 & R0). exists p0, H0. split; [exact E0|].
            split; [|exact R0]. apply lb_remove_In. split; [exact I0|]. cbn [blk_id fst]. intros ->.
            eapply (ids_bn_head_neq (RPool i) ls pd pd); eauto using ids_m_nodup. }
          apply (rw_cells_agree _ _ _ _ _ AG6) in FR4; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; lia].
          apply (rw_cells_agree _ _ _ _ _ AG6) in BN4; [| intros x Hx; right; right; exists (qs, As, ns); split; [apply in_or_app; left; exact HinSF| cbn in Hx |- *; lia]].
          apply (u64arr_agree _ _ _ _ _ AG6) in UN4; [| intros x Hx; right; right; exists (pn, An, Z.of_nat words * 8); split; [apply in_or_app; left; exact HinNF| cbn [blk_addr blk_size fst snd]; lia]].
          assert (INSF : In (qs, As, ns) (OWF ++ LB)) by (apply in_or_app; left; exact HinSF).
          pose proof (AH_acc_in _ _ _ _ (qs, As, ns) a 24 HEAP6 INSF Ra1 Ra2) as ACC6.
          pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (a, a + 24)]%Z m6) as MU7. pose proof (wmono_refl bsegs m6) as WM7.
          assert (OFF7 : offshW [(bv_unsigned sp + -80, bv_unsigned sp); (a, a + 24)]).
          { pose proof (AH_offsh _ _ _ _ (qs, As, ns) HEAP6 INSF) as O. cbn [blk_addr blk_size fst snd] in O.
            cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
          clear MU5 WM5.
          unfold MallocRep.wz.
          apply implA_from_evt.
          ub; shl. ub; chk0. ub; step. ub; shl. ub; chk0. ub; step.
          do 10 (ub; step). release_frame FR4 ST6 (bv_unsigned sp). ub; step. ub; step.
          apply evt_done. apply implA_ret.
          lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
          assert (HWL7 : Forall (w_lib OWF lo (bv_unsigned sp)) [(bv_unsigned sp + -80, bv_unsigned sp); (a, a + 24)]).
          { constructor; [left; cbn; lia|]. constructor; [|constructor]. right. exists (qs, As, ns). cbn. auto. }
          assert (LSHF : lib_state_h [r] ls mF OWF AD EA).
          { eapply (lib_state_frame Σ6 LB); [exact HEAP6| exact LSH6| exact MU7| exact WM7|].
            constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [|constructor].
            eapply (w_struct OWF LB ls AD EA false [r] _ r a); [left; reflexivity| exact HAF| cbn; lia| cbn; lia]. }
          destruct (expand_close ls mF OWF AD EA r a pn An words LSHF NDF HAF) as [LSF RESF];
            [fold b; exact BN4| exact HinNF| fold b; exact UN4| exact FRESHA| fold b; lia| unfold BN_WORDS_MAX; lia|].
          unfold QQ, bn_postA. do 17 eexists. exists mF, OWF. split; [reflexivity|]. cbn [fst snd].
          fold (bn_expanded b pn words). fold b in LSF, RESF.
          split; [exact (seg_heap Σ6 OWF LB m6 mF _ lo _ HEAP6 MU7 WM7 HWL7 CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
          split; [exact ST6|]. split; [exact MI6|].
          split. { eapply ax_pres_trans; [exact AXP4|]. eapply ax_pres_trans.
                   - eapply agree_on_mono; [exact AG6|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
                       [left; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]].
                   - exact (seg_ax_pres' Σ6 OWF LB m6 mF _ lo _ _ HEAP6 MU7 HWL7 CEIL ltac:(lia)). }
          split; [rewrite CR6; exact CR3|].
          split. { unfold cnt_eq. rewrite (cnt_bal_setbn r (bn_expanded b pn words) ls OW OWF HV). fold b.
                   unfold bn_blocks. rewrite Ed. cbn [bn_expanded bn_d length].
                   pose proof (lb_remove_length pd OW1 ND1 ltac:(apply (in_map blk_id) in HinD1; exact HinD1)) as LL. fold OWF in LL.
                   unfold OW1 in LL. cbn [length] in LL. lia. }
          split. { intros r' a' HA'. apply ref_at_setbn. destruct r' as [| | | | |i]; cbn [ref_at] in HA' |- *; try exact HA'.
                   destruct HA' as (p0 & H0 & E0 & I0 & R0). exists p0, H0. split; [exact E0|]. split; [|exact R0].
                   apply lb_remove_In. split; [right; exact I0|]. cbn [blk_id fst]. intros ->.
                   eapply (ids_bn_head_neq r ls pd pd); eauto using ids_m_nodup. }
          split; [reflexivity|]. split; [exact RESF|]. split; [right; split; [fold b; lia|]; exists pn; reflexivity|].
          intros q0 A0 n0 Hq0 NE0. apply lb_remove_In. split; [right; exact Hq0|]. cbn [blk_id fst]. intros ->. apply NE0. reflexivity. }
      assert (LENN : Z.of_nat (length (wlimbs newbuf)) = Z.of_nat words).
      { subst newbuf. rewrite wlimbs_len, length_app, firstn_length_le, repeat_length by (unfold bn_dmax in *; lia). lia. }
      apply implA_from_evt.
      do 2 (ub; step). ub; step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; lia|]. clear KA.
      do 3 (ub; step). ub; shl. ub; chk0.
      ub; step. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia. ub; zstep. ub; step.
      if_cases KT; zify_cond KT.
      * (* [comment removed for export] *)
        assert (ET0 : bn_top b = 0%nat).
        { apply andb_false_iff in KT. destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia. }
        apply evt_done. eapply TAIL; [exact HEAP3 | exact MI3 | exact ST3 | exact FR | exact BN | | exact LSH3' | exact AXP3 | exact UW3].
        subst newbuf. rewrite ET0. cbn [firstn app]. rewrite Nat.sub_0_r. apply (CB_u64arr bsegs m3 An (Z.to_nat (Z.of_nat words * 8))).
        rewrite lbytes_repeat0. replace (8 * words)%nat with (Z.to_nat (Z.of_nat words * 8)) by lia. exact BLK.
      * (* [comment removed for export] *)
        assert (TOPP : (0 < bn_top b)%nat) by lia.
        ub; step. ub; shl. ub; chk0. ub; step.
        do 3 (ub; step).
        rewrite ?(unsigned_lit (Z.of_nat (bn_top b))) by lia.
        replace (Z.shiftl (Z.of_nat (bn_top b)) 3) with (Z.of_nat (bn_top b) * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
        set (cp := u64s (wlimbs (firstn (bn_top b) (bn_buf b)))).
        assert (LCP : Z.of_nat (length cp) = Z.of_nat (bn_top b) * 8).
        { subst cp. rewrite u64s_length, wlimbs_len, firstn_length_le by (unfold bn_dmax in *; lia). lia. }
        rewrite <- LCP.
        assert (SRC : bytes_at bsegs m3 D cp).
        { apply limbarr_bytes. apply (proj1 (limbarr_split bsegs m3 D (bn_buf b) (bn_top b) ltac:(unfold bn_dmax in *; lia))) in U3. exact (proj1 U3). }
        (* [comment removed for export] *)
        assert (ZSPLIT : u8arr bsegs m3 An (repeat (Z_to_bv 8 0) (8 * bn_top b) ++ repeat (Z_to_bv 8 0) (8 * (words - bn_top b)))).
        { rewrite <- repeat_app. replace (8 * bn_top b + 8 * (words - bn_top b))%nat with (Z.to_nat (Z.of_nat words * 8)) by lia.
          eapply u8arr_of_rw_cells. exact BLK. }
        apply u8arr_app in ZSPLIT. destruct ZSPLIT as [_ Z2]. rewrite repeat_length in Z2.
        assert (INN3 : In (pn, An, Z.of_nat words * 8) (OW1 ++ LB)) by (apply in_or_app; left; exact HinN).
        assert (IND3 : In (pd, D, 8 * Z.of_nat (bn_dmax b)) (OW1 ++ LB)) by (apply in_or_app; left; right; exact HinD).
        apply evt_done.
        eapply implA_step_same.
        -- eapply (asan_memcpy_cpsA) with (d := An) (s := D) (bs := cp) (bd := (pn, An, Z.of_nat words * 8))
                                          (bsrc := (pd, D, 8 * Z.of_nat (bn_dmax b))) (lo := lo) (OW := OW1) (LB := LB); try reflexivity.
           ++ exact HEAP3.
           ++ rewrite ESP. exact ST3.
           ++ exact CEIL.
           ++ rewrite ESP. unfold RT_STACK. lia.
           ++ rewrite ESP. unfold USTACK_TOP. lia.
           ++ rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
           ++ exact MI3.
           ++ exact INN3.
           ++ cbn [blk_addr blk_size fst snd]. lia.
           ++ exact IND3.
           ++ cbn [blk_addr blk_size fst snd]. lia.
           ++ exact SRC.
           ++ lia.
           ++ lia.
        -- intros ms5 PO. unfold icall_post in PO. rewrite ?ESP in PO.
           destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F5 & fc5 & m5 & -> & MI5 & ST5 & HEAP5 & WM5 & AG5 & BZ & WR5).
           rewrite (ret_pc_even 2028252) by lia. unfold MallocRep.wz.
           eapply TAIL; [exact HEAP5 | exact MI5 | exact ST5 | | | | | | ].
           ++ eapply (rw_cells_agree _ _ _ _ _ AG5); [exact FR|]. intros x Hx. cbn in Hx. split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia].
           ++ eapply (rw_cells_agree _ _ _ _ _ AG5); [exact BN|]. intros x Hx. cbn in Hx.
              split; [right; right; exists (qs, As, ns); split; [exact INS1 | cbn; lia] | lia].
           ++ apply u64arr_u8arr. subst newbuf. rewrite wlimbs_app, u64s_app. apply u8arr_app. fold cp. split.
              ** split; [exact BZ | exact WR5].
              ** rewrite lbytes_repeat0. replace (Z.of_nat (length cp)) with (Z.of_nat (8 * bn_top b)) by lia.
                 destruct Z2 as [ZB ZW]. rewrite repeat_length in ZW. split.
                 --- eapply (bytes_at_agree _ _ _ _ _ AG5); [exact ZB|]. intros x Hx. rewrite repeat_length in Hx.
                     split; [right; right; exists (pn, An, Z.of_nat words * 8); split; [exact INN3 | cbn; lia] | lia].
                 --- rewrite repeat_length. eapply (wr_at_agree _ _ _ _ _ AG5); [exact ZW|]. intros x Hx.
                     split; [right; right; exists (pn, An, Z.of_nat words * 8); split; [exact INN3 | cbn; lia] | lia].
           ++ eapply (lib_state_h_icall Σ1 LB false [r] ls m3 m5 OW1 AD EA _ An (Z.of_nat (length cp)) HEAP3 LSH3' AG5).
              eapply (w_foreign OW1 LB ls AD EA false [r] _ pn An (Z.of_nat words * 8)); [exact INN3 | exact FRESHA | cbn; lia | cbn; lia].
           ++ eapply ax_pres_trans; [exact AXP3|]. eapply agree_on_mono; [exact AG5|]. intros x [_ Hc]. split.
              ** destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]].
              ** intros HAr. destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]].
                 --- unfold BnHeapA.ACEIL in *. lia.
                 --- eapply (blk_not_static Σ1 OW1 LB m3 (pn, An, Z.of_nat words * 8) x HEAP3 HinN); [cbn; lia | exact Hc].
                 --- assert (NE : blk_id b0 <> pn).
                     { intros E. apply FRESH. rewrite <- E. apply in_map. apply in_or_app. right. exact Hb0. }
                     pose proof (AH_disjoint_gen _ _ _ _ b0 (pn, An, Z.of_nat words * 8) HEAP3 (in_or_app _ _ _ (or_intror Hb0)) INN3 NE) as DJ. cbn in DJ. lia.
           ++ eapply uw_chain_agree; [exact UW3|]. eapply agree_on_mono; [exact AG5|]. intros x Hx. cbv beta in Hx.
              split; [left; lia | unfold BnHeapA.ACEIL in *; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BN_WEXPAND_STACK : Z := 16 + BN_EXPAND2_STACK.
Local Notation E_bw_tail := (E_bn_wexpand_1f4334 : uk_tail BN_WEXPAND BN_EXPAND2).

Lemma bn_wexpand_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z) (r : bnref) (a : Z) (words : nat),
  bn_preA Σ ls m OW LB AD EA sp lo BN_WEXPAND_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_WEXPAND (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW AD r a -> a0 = wz a -> a1 = wz (Z.of_nat words) -> Z.of_nat words < 2^31 ->
  implA (bn_wexpand (tree_ops bptr) r words ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC
              (fun _ ls' OW' a0' => a0' = wz a /\ (words <= bn_dmax (getbn r ls'))%nat /\ wexpand_res r words ls ls'
                                  /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn r ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_WEXPAND) fc None m (seg_rom bsegs)).
Proof.
  intros until words. intros (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED) UW CTX -> HA -> -> HW.
  unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BN_WEXPAND, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls m OW AD EA r a LS ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  destruct (ref_at_inb _ _ _ _ _ ADB HA) as (qs & As & ns & Eqs & Hins & Ra1 & Ra2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hins) as (SA0 & SA16 & _ & SAC & SAI).
  pose proof (ref_at_al8 _ _ _ _ _ _ _ _ HEAP ADB HA) as AL.
  set (b := getbn r ls) in *.
  unfold bn_cells in BN. unfold BN_WORDS_MAX in OK3.
  assert (INS : In (qs, As, ns) (OW ++ LB)) by (apply in_or_app; left; exact Hins).
  pose proof (AH_acc_in _ _ _ _ (qs, As, ns) a 24 HEAP INS Ra1 Ra2) as ACC.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 16%nat ST. do 7 (ub; step). do 3 (ub; step). ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (bn_dmax b))) by lia.
  ub; step.
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp + -16, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  if_cases K; zify_cond K; rewrite !signed_small in K by lia.
  - (* [comment removed for export] *)
    do 2 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
    apply evt_done.
    unfold bn_wexpand, bbind, bget, bret. cbn [bind ret tree_ops tbind fst snd]. fold b.
    replace (words <=? bn_dmax b)%nat with true by (symmetry; apply Nat.leb_le; lia). cbv beta iota.
    apply implA_ret.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
    unfold bn_postA. do 17 eexists. exists mF, OW. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact (lib_state_frame Σ LB [] ls m mF OW AD EA _ HEAP LS MU WM WOK)|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|].
    split; [unfold MC; lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [reflexivity|]. split; [fold b; lia|]. split; [left; split; [fold b; lia| reflexivity]|]. intros q0 A0 n0 Hq0 _. exact Hq0.
  - (* [comment removed for export] *)
    do 2 (ub; step). release_frame FR ST (bv_unsigned sp). ub; step. ub; step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply evt_done.
    eapply implA_mono.
    { eapply (bn_expand2_walkA ra sp) with (lo := lo) (ras := ras) (r := r) (a := a) (words := words) (OW := OW) (LB := LB) (AD := AD) (EA := EA);
        [| | | reflexivity | exact HA | reflexivity | reflexivity | exact HW].
      - unfold bn_preA.
        split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
        split; [exact (lib_state_frame Σ LB [] ls m m1 OW AD EA _ HEAP LS MU WM WOK)|].
        split; [exact ST|]. split; [exact CEIL|].
        split; [unfold BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia|].
        split; [unfold USTACK_TOP; lia|]. split; [exact SP16|]. split; [exact MI|]. split; [exact CNT| exact CRED].
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor].
      - exact (uk_ctx_tail _ _ _ E_bw_tail CTX). }
    cbv beta. intros [u ls'] Σ' ms' PO. unfold bn_postA in *. cbn [fst snd] in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & OW' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    do 17 eexists. exists m', OW'. split; [reflexivity|].
    do 4 (split; [assumption|]). split; [|split; [assumption| split; [assumption| split; [assumption| exact P9]]]].
    eapply ax_pres_trans; [|exact P5]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia)).
Qed.

End WithRT.
