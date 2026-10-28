(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require W_alloc3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BgPlace BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_free_core.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_FREE : Z := 0xfdfd0.
Definition BN_FREE_STACK : Z := W_alloc3.BN_FREE_STACK.

Lemma free_post : forall {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (bs : bstate bptr) (OW LB : list block) (lo B : Z) (m : mem) (PL : placement) (EA : BnRep.err_addrs)
    (RES : A -> bstate bptr -> list block -> placement -> word -> Prop) (res : A)
    (bs' : bstate bptr) (PL' : placement) (OWF : list block) (s' : PState) (m' : mem) (errv' : word)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  lib_state bs' m OW PL' EA -> frames_ok PL' (bv_unsigned sp) B ->
  (forall q0 A0 n0, In q0 (all_ids bs' PL' EA) -> In (q0, A0, n0) OW -> In (q0, A0, n0) OWF) ->
  gx_items (st_ctx bs') = gx_items (st_ctx bs) ->
  RHEAP s' (OWF ++ LB) m' -> rheap_pres (OWF ++ LB) (bv_unsigned sp) m m' ->
  rauxv_ok m' B -> stk bgusegs m' lo (bv_unsigned sp) -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] -> mem_inv bgusegs m' ->
  ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
  RES res bs' OWF PL' a0 ->
  bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA RES (res, bs') s'
    (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom bgusegs)).
Proof.
  intros until t6. intros LSU FROK' KEEP EIT HEAP' HP AUX' ST' ERR' MI' FA SO HRES.
  unfold bn_post. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', OWF, PL', errv'. split; [reflexivity|]. cbn [fst snd].
  split; [exact HEAP'|].
  split. { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ _ (bv_unsigned sp) B); [| exact FROK'| | exact HP|]; [| lia| intros b0 Hb0; apply in_or_app; left; exact Hb0].
           eapply lib_state_h_ow; [exact LSU| exact KEEP]. }
  split; [exact AUX'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
  split. { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
  split; [exact FA|]. split; [exact SO|].
  split. { apply refs_stable_ow; [exact EIT|]. intros q0 H0 Hq Hin. apply (KEEP q0 H0 ITEM_SZ); [|exact Hin].
           unfold all_ids. apply in_or_app. right. apply in_or_app. right. apply item_in_m. rewrite EIT. exact Hq. }
  exact HRES.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_free_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (r : bnref) (a : Z) (q : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_FREE_STACK -> tp = wz RATP ->
    pl_bn PL r = Some (PHeap a q 0) -> a0 = wz a ->
    implM bgusegs (interp (embed (BN_free (tree_ops bptr) r (Some q) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ bs' OW' PL' _ => PL' = pl_set PL r None /\ bs' = setbn r (bn_nil 0) bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until q. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> E ->.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (LH_nodup _ _ _ HEAP) as NDL.
    pose proof LO as LO'. unfold BN_FREE_STACK, W_alloc3.BN_FREE_STACK, W_alloc3.BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK in LO'.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (pl_wf_stored PL r _ PWF E) as SR. pose proof SR as (RN & RO & RM).
    assert (EO : pl_of PL r = Some (PHeap a q 0)) by (rewrite pl_of_stored by exact SR; exact E).
    assert (HA : ref_at bs OW PL r a) by (apply ref_at_fixed; [exact RN|]; exists (PHeap a q 0); split; [exact EO| reflexivity]).
    pose proof (hpl_heap PL r a q 0 EO) as HP.
    destruct (proj1 PLB r _ RN EO) as (n & Hinq & _ & Hn). replace (a - 0) with a in Hinq by lia. unfold BN_STRUCT_SZ in Hn.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) RO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_unplace_bn false [] bs m OW PL EA r a q LSH ltac:(intros []) E) as (LSU & NQ & NP).
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HA HP) as (SA0 & SAC & SAI & _).
    assert (FROK' : frames_ok (pl_set PL r None) (bv_unsigned sp) B) by (apply frames_ok_set_none; exact FROK).
    set (b := getbn r bs) in *.
    assert (FLR : 0 <= bn_flags b < 256) by (destruct OK4 as [E4|E4]; rewrite E4; lia).
    assert (EL2 : Z.land (bn_flags b) 2 = 0) by (destruct OK4 as [E4|E4]; rewrite E4; reflexivity).
    assert (EL8 : Z.land (bn_flags b) 8 = 0) by (destruct OK4 as [E4|E4]; rewrite E4; reflexivity).
    assert (QL : In (q, a, n) (OW ++ LB)) by (apply in_or_app; left; exact Hinq).
    assert (QNLB : ~ In q (map blk_id LB)).
    { intros H. rewrite map_app in NDL. eapply (BnHeap.nodup_app_disj _ _ q NDL); [apply (in_map blk_id) in Hinq; exact Hinq| exact H]. }

    assert (DFACTS : forall pd, bn_d b = Some pd -> In (pd, D, 8 * Z.of_nat (bn_dmax b)) OW /\ pd <> q /\ ~ In pd (map blk_id LB)).
    { intros pd Ed. unfold bn_arr in ARR. rewrite Ed in ARR. destruct ARR as [HinD _]. split; [exact HinD|]. split.
      - intros ->. eapply (ids_pl_m bs PL EA q q IDS); [eapply in_pl_ids_bn; [exact RN| exact E]| eapply bn_in_m; [exact HV| exact Ed]| reflexivity].
      - intros H. rewrite map_app in NDL. eapply (BnHeap.nodup_app_disj _ _ pd NDL); [apply (in_map blk_id) in HinD; exact HinD| exact H]. }
    assert (DNULL : bn_d b = None -> D = 0).
    { intros Ed. exact (proj1 (bn_arr_null PL r m OW D b PWF (hpl_wref PL r HP) Ed ARR)). }
    unfold BN_free, bbind, bget, bset, bret, bfree_opt, bfree, bunr, has_flag, BN_FLG_STATIC_DATA, BN_FLG_MALLOCED.
    cbn [bind ret unreachable lib_free tree_ops tbind fst snd]. fold b. rewrite EL2. cbn [Z.eqb negb].
    destruct OK4 as [F0|F1].
    -
      rewrite F0. cbn [Z.land Z.eqb negb].
      lazymatch goal with |- implM _ (interp ?t) _ _ _ =>
        replace t with (lbind (lfree_opt (bn_d b)) (fun _ => LRet (tt, setbn r (bn_nil 0) bs))) by (destruct (bn_d b); reflexivity) end.
      eapply (W_alloc3.BN_free_walk_emb HF) with (B := B) (lo := lo) (errv := errv) (A := a) (D := D) (b := b);
        [exact HEAP | | exact DNULL | exact AUX | exact SPB | exact ST | exact CEIL | exact GLO | exact LO | exact ERR | exact MI | reflexivity
        | exact (proj1 LS) | exact BN | exact FLR | exact EL8 | exact EL2 | rewrite F0; reflexivity
        | left; unfold W_alloc3.BN_FREE_STACK, W_alloc3.BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, RFREE_STACK; clear - SAC CEIL LO'; lia
        | exact SA0 | exact (proj2 (block_ualign _ _ _ _ _ _ _ HEAP Hinq)) | reflexivity | ].
      { intros pd Ed. destruct (DFACTS pd Ed) as (HinD & NEQ & _). split; [apply in_or_app; left; exact HinD|].
        intros x Hx. right; right. exists (q, a, n). split; [apply lb_remove_In; split; [exact QL| cbn; intros E'; apply NEQ; symmetry; exact E']| cbn [blk_addr blk_size fst snd]; lia]. }
      intros s' ms' PO _. unfold W_alloc3.ofree_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MI' & ST' & ERR' & AUX' & HP' & FA & SO & HEAP').
      cbn [interp]. apply implM_ret. apply evt_done.
      assert (EL : W_alloc3.lb_remove_opt (bn_d b) (OW ++ LB) = W_alloc3.lb_remove_opt (bn_d b) OW ++ LB).
      { destruct (bn_d b) as [pd|] eqn:Ed; [|reflexivity]. cbn [W_alloc3.lb_remove_opt]. destruct (DFACTS pd eq_refl) as (_ & _ & NLB).
        rewrite lb_remove_app, (lb_remove_notin pd LB NLB). reflexivity. }
      rewrite EL in HP', HEAP'.
      eapply (free_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA _ tt (setbn r (bn_nil 0) bs) (pl_set PL r None)
                (W_alloc3.lb_remove_opt (bn_d b) OW) s' m' errv);
        [exact LSU | exact FROK' | | reflexivity | exact HEAP' | exact HP' | exact AUX' | exact ST' | exact ERR' | exact MI' | exact FA | exact SO | split; reflexivity].
      intros q0 A0 n0 Hq0 Hin0. destruct (bn_d b) as [pd|] eqn:Ed; [|exact Hin0]. cbn [W_alloc3.lb_remove_opt].
      apply lb_remove_In. split; [exact Hin0|]. cbn [blk_id fst]. intros ->. exact (NP pd eq_refl Hq0).
    -
      rewrite F1. cbn [Z.land Z.eqb negb].
      lazymatch goal with |- implM _ (interp ?t) _ _ _ =>
        replace t with (lbind (lfree_opt (bn_d b)) (fun _ => LFree q (LRet (tt, setbn r (bn_nil 0) bs)))) by (destruct (bn_d b); reflexivity) end.
      eapply (W_free_core.BN_free_walk_mal_n HF) with (B := B) (lo := lo) (errv := errv) (A := a) (D := D) (n := n) (b := b);
        [exact HEAP | exact QL | exact Hn | | exact DNULL | exact AUX | exact SPB | exact ST | exact CEIL | exact GLO | exact LO | exact ERR | exact MI | reflexivity
        | exact (proj1 LS) | exact BN | exact FLR | exact EL8 | exact EL2 | rewrite F1; reflexivity | reflexivity | ].
      { intros pd Ed. destruct (DFACTS pd Ed) as (HinD & NEQ & _). split; [apply in_or_app; left; exact HinD| exact NEQ]. }
      intros s' ms' PO. unfold cfree_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MI' & ST' & ERR' & AUX' & HP' & FA & SO & HEAP').
      cbn [interp]. apply implM_ret. apply evt_done.
      assert (EL : lb_remove q (W_alloc3.lb_remove_opt (bn_d b) (OW ++ LB)) = lb_remove q (W_alloc3.lb_remove_opt (bn_d b) OW) ++ LB).
      { destruct (bn_d b) as [pd|] eqn:Ed; cbn [W_alloc3.lb_remove_opt].
        - destruct (DFACTS pd eq_refl) as (_ & _ & NLB). rewrite !lb_remove_app, (lb_remove_notin pd LB NLB), (lb_remove_notin q LB QNLB). reflexivity.
        - rewrite lb_remove_app, (lb_remove_notin q LB QNLB). reflexivity. }
      rewrite EL in HP', HEAP'.
      eapply (free_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA _ tt (setbn r (bn_nil 0) bs) (pl_set PL r None)
                (lb_remove q (W_alloc3.lb_remove_opt (bn_d b) OW)) s' m' errv);
        [exact LSU | exact FROK' | | reflexivity | exact HEAP' | exact HP' | exact AUX' | exact ST' | exact ERR' | exact MI' | exact FA | exact SO | split; reflexivity].
      intros q0 A0 n0 Hq0 Hin0. apply lb_remove_In. split; [|cbn [blk_id fst]; intros ->; exact (NQ Hq0)].
      destruct (bn_d b) as [pd|] eqn:Ed; [|exact Hin0]. cbn [W_alloc3.lb_remove_opt].
      apply lb_remove_In. split; [exact Hin0|]. cbn [blk_id fst]. intros ->. exact (NP pd eq_refl Hq0).
  Qed.

End Proofs.
End WithCeiling0.
