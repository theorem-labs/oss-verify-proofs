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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require W_alloc3 W_ctx3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BgPlace.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_NEW : Z := 0xfe07c.
Definition BN_NEW_STACK : Z := W_alloc3.BN_NEW_STACK.
Definition BN_CTX_NEW : Z := 0x100a5c.
Definition BN_CTX_NEW_STACK : Z := W_ctx3.BN_CTX_NEW_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_new_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (r : bnref),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_NEW_STACK -> tp = wz RATP ->
    stored_ref r -> pl_bn PL r = None ->
    implM bgusegs (interp (embed (BN_new (tree_ops bptr) r bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun p bs' OW' PL' a0' => exists a, PL' = pl_set PL r (Some (PHeap a p 0)) /\ a0' = wz a /\ 0 < a < 2^63
                                         /\ OW' = (p, a, 24) :: OW /\ bs' = setbn r (bn_nil BN_FLG_MALLOCED) bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_NEW) fc None m (seg_rom bgusegs)).
  Proof.
    intros until r. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> SR E.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    unfold BN_new, bbind, bmalloc, bset, bret. cbn [bind ret unreachable lib_malloc tree_ops tbind fst snd embed].
    eapply (W_alloc3.BN_new_walk HM) with (B := B) (lo := lo) (errv := errv);
      [exact HEAP | exact AUX | exact SPB | exact ST | exact CEIL | exact GLO | exact LO | exact ERR | exact MI | reflexivity
      | exact (proj1 LS) | reflexivity |].
    intros p s' ms' PO. unfold calloc_post in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    cbn [tbind embed interp fst snd]. apply implM_ret. apply evt_done.
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (ND3 : List.NoDup (map blk_id ((p, A, 24) :: OW ++ LB))) by (eapply LH_nodup; exact HEAP3).
    assert (FRESH : ~ In p (map blk_id (OW ++ LB))) by (cbn [map] in ND3; apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
    assert (FRESHA : ~ In p (all_ids bs PL EA)).
    { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
    assert (LS3 : lib_state bs m3 OW PL EA).
    { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ _ (bv_unsigned sp) B); [exact LS| exact FROK| | exact HP|]; [lia|].
      intros b0 Hb0. apply in_or_app. left. exact Hb0. }
    set (OW1 := (p, A, 24) :: OW).
    assert (LS3' : lib_state bs m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LS3|]; intros q A0 n0 _ Hq; right; exact Hq).
    unfold bn_post. do 15 eexists. exists m3, OW1, (pl_set PL r (Some (PHeap A p 0))), errv2. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP3|].
    split. { eapply (lib_state_place_bn false [] bs m3 OW1 PL EA r A p 24); [exact LS3'| exact SR| exact E| left; reflexivity| unfold BN_STRUCT_SZ; lia| exact FRESHA| exact BLK]. }
    split; [exact AUX3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact MI3|].
    split. { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
    split; [exact FA|]. split; [exact SO|].
    split. { eapply refs_stable_trans; [|apply refs_stable_setbn]. apply refs_stable_ow; [reflexivity|]. intros q H _ Hq. right. exact Hq. }
    exists A. split; [reflexivity|]. split; [reflexivity|]. split; [clear - BA0 BAC; lia|]. split; reflexivity.
  Qed.

  Lemma BN_CTX_new_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_CTX_NEW_STACK -> tp = wz RATP ->
    pl_ctx PL = None ->
    implM bgusegs (interp (embed (BN_CTX_new (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun p bs' OW' PL' a0' => exists a, PL' = pl_set_ctx PL (Some (a, p)) /\ a0' = wz a /\ 0 < a < 2^63
                                         /\ OW' = (p, a, 72) :: OW /\ bs' = set_ctx gx_nil bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_NEW) fc None m (seg_rom bgusegs)).
  Proof.
    intros until errv. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> E.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    unfold BN_CTX_new, bbind, bmalloc, bsetctx, bret. cbn [bind ret unreachable lib_malloc tree_ops tbind fst snd embed].
    eapply (W_ctx3.BN_CTX_new_walk HM) with (B := B) (lo := lo) (errv := errv);
      [exact HEAP | exact AUX | exact SPB | exact ST | exact CEIL | exact GLO | exact LO | exact ERR | exact MI | reflexivity
      | exact (proj1 LS) | reflexivity |].
    intros p s' ms' PO. unfold calloc_post in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    cbn [tbind embed interp fst snd]. apply implM_ret. apply evt_done.
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (ND3 : List.NoDup (map blk_id ((p, A, 72) :: OW ++ LB))) by (eapply LH_nodup; exact HEAP3).
    assert (FRESH : ~ In p (map blk_id (OW ++ LB))) by (cbn [map] in ND3; apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
    assert (FRESHA : ~ In p (all_ids bs PL EA)).
    { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
    assert (LS3 : lib_state bs m3 OW PL EA).
    { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ _ (bv_unsigned sp) B); [exact LS| exact FROK| | exact HP|]; [lia|].
      intros b0 Hb0. apply in_or_app. left. exact Hb0. }
    set (OW1 := (p, A, 72) :: OW).
    assert (LS3' : lib_state bs m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LS3|]; intros q A0 n0 _ Hq; right; exact Hq).
    unfold bn_post. do 15 eexists. exists m3, OW1, (pl_set_ctx PL (Some (A, p))), errv2. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP3|].
    split. { eapply (lib_state_place_ctx [] bs m3 OW1 PL EA A p); [exact LS3'| exact E| left; reflexivity| exact FRESHA|].
             eapply bk_rw_cells_recast; [exact BLK| cbn; repeat split| reflexivity| reflexivity]. }
    split; [exact AUX3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact MI3|].
    split. { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
    split; [exact FA|]. split; [exact SO|].
    split. { apply refs_stable_ow; [|intros q H _ Hq; right; exact Hq]. cbn [st_ctx set_ctx gx_items gx_nil].
             destruct LS as (_ & _ & _ & (_ & _ & _ & (_ & _ & M3 & _))). rewrite E in M3. rewrite (proj1 M3). reflexivity. }
    exists A. split; [reflexivity|]. split; [reflexivity|]. split; [clear - BA0 BAC; lia|]. split; reflexivity.
  Qed.

End Proofs.
End WithCeiling0.
