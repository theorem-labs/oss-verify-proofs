(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnDivWords BnModel BnTree BnInv BnBridge BgState BgWords BgInv BgLib BgArith BgMont.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3 W_alloc3 W_ctx3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import PlaceRecp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma recp_free_tree : forall bs : bstate bptr,
  bn_flags (getbn RRecpN bs) = 0 -> bn_flags (getbn RRecpNr bs) = 0 ->
  embed (BN_RECP_CTX_free (tree_ops bptr) bs) =
  lbind (lfree_opt (bn_d (getbn RRecpN bs))) (fun _ => lbind (lfree_opt (bn_d (getbn RRecpNr bs))) (fun _ =>
    LRet (tt, set_recp 0 0 (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) bs))))).
Proof.
  intros bs F1 F2.
  assert (H1 : forall f, has_flag (getbn RRecpN bs) f = false) by (intros f; unfold has_flag; rewrite F1; reflexivity).
  assert (H2 : forall f, has_flag (getbn RRecpNr bs) f = false) by (intros f; unfold has_flag; rewrite F2; reflexivity).
  assert (H3 : forall b f, has_flag (getbn RRecpNr (setbn RRecpN b bs)) f = false)
    by (intros b f; rewrite getbn_setbn_other by (unfold RRecpN, RRecpNr; lia); apply H2).
  assert (D2' : forall b, bn_d (getbn RRecpNr (setbn RRecpN b bs)) = bn_d (getbn RRecpNr bs))
    by (intros b; rewrite getbn_setbn_other by (unfold RRecpN, RRecpNr; lia); reflexivity).
  unfold BN_RECP_CTX_free, BN_free, bbind, bget, bset, bret, bunr, bsetrecp. cbn [bind ret unreachable tree_ops tbind fst snd].
  rewrite !H1, !H2. cbn [orb]. cbv beta. rewrite !H1.
  destruct (bn_d (getbn RRecpN bs)) as [q1|];
    cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd lfree_opt lfree lbind embed];
    rewrite !H3, !D2'; cbv beta;
    (destruct (bn_d (getbn RRecpNr bs)) as [q2|];
     cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd lfree_opt lfree lbind embed]; reflexivity).
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem lib_state_h_setbn_hole : forall cxo hs (s : bstate bptr) m OW PL EA r a b',
  lib_state_hc cxo hs s m OW PL EA -> List.NoDup (map blk_id OW) -> ref_at s OW PL r a -> In r hs -> r <> ROne ->
  bg_ok b' -> ids_ok (setbn r b' s) PL EA ->
  lib_state_hc cxo hs (setbn r b' s) m OW PL EA.
Proof.
  intros cxo hs s m OW PL EA r a b' HS ND HA Hin NE HOK HIDS. pose proof (ref_at_valid _ _ _ _ _ _ _ _ HS HA) as HV.
  destruct HS as (HC & HE & HO & (S1 & S2 & S3 & HM)).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [apply st_wf_setbn; assumption|]. split; [exact S2|]. split; [exact HIDS|].
  eapply gen_set; [exact HM| exact ND| exact HA| exact HV| left; exact Hin].
Qed.

Lemma all_ids_setbn_nil : forall (s : bstate bptr) PL EA r q, vref r s ->
  In q (all_ids (setbn r (bn_nil 0) s) PL EA) -> In q (all_ids s PL EA).
Proof.
  intros s PL EA r q HV H. unfold all_ids in *. rewrite !in_app_iff in *. destruct H as [H|[H|H]]; [left; exact H| right; left; exact H|].
  right; right. destruct (blocks_setbn r s HV) as (R & P1 & P2). specialize (P2 (bn_nil 0)). cbn [bn_blocks bn_nil bn_d app] in P2.
  apply (Permutation_map fst) in P1. apply (Permutation_map fst) in P2.
  eapply Permutation_in; [apply Permutation_sym; exact P1|]. rewrite map_app. apply in_or_app. right.
  eapply Permutation_in; [exact P2| exact H].
Qed.

Lemma all_ids_without : forall (s : bstate bptr) PL EA r p, ids_ok s PL EA -> vref r s -> bn_d (getbn r s) = Some p ->
  ~ In p (all_ids (setbn r (bn_nil 0) s) PL EA).
Proof.
  intros s PL EA r p IDS HV Hd H. unfold all_ids in H. rewrite !in_app_iff in H. pose proof (bn_in_m r s p HV Hd) as Hm.
  destruct H as [H|[H|H]].
  - exact (ids_pl_m s PL EA p p IDS H Hm eq_refl).
  - exact (ids_ea_m s PL EA p p IDS H Hm eq_refl).
  - exact (ids_without r s p (ids_m_nodup _ _ _ IDS) HV Hd H).
Qed.

Lemma lb_remove_opt_In : forall o (L : list block) b, In b (lb_remove_opt o L) <-> In b L /\ (forall p, o = Some p -> blk_id b <> p).
Proof.
  intros [p|] L b; cbn [lb_remove_opt].
  - rewrite lb_remove_In. split; [intros [H N]; split; [exact H| intros p' E; injection E as <-; exact N]| intros [H N]; split; [exact H| apply N; reflexivity]].
  - split; [intros H; split; [exact H| intros p E; discriminate E]| intros [H _]; exact H].
Qed.

Lemma lb_remove_opt_app_l : forall o (OW LB : list block), List.NoDup (map blk_id (OW ++ LB)) -> (forall p, o = Some p -> In p (map blk_id OW)) ->
  lb_remove_opt o (OW ++ LB) = lb_remove_opt o OW ++ LB.
Proof. intros [p|] OW LB ND H; cbn [lb_remove_opt]; [apply lb_remove_app_l; [exact ND| apply H; reflexivity]| reflexivity]. Qed.

Section Proofs.
  Hypothesis HF : rfree_stmt.

  Lemma BN_RECP_CTX_free_lwalk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL0 : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (an : Z) (pad : word),
    bn_pre s bs m OW LB (pl_place_recp PL0 an) EA sp lo B errv BN_RECP_CTX_FREE_STACK -> tp = wz RATP ->
    pl_wf PL0 -> pl_bn PL0 RRecpN = None -> pl_bn PL0 RRecpNr = None -> pl_recp PL0 = None -> a0 = wz an ->
    rw_cells bgusegs m (an + 60) [C4 pad] ->
    implM bgusegs (interp (embed (BN_RECP_CTX_free (tree_ops bptr) bs))) s
      (fun r st' ms' =>
         bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m (pl_place_recp PL0 an) EA
                 (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (_ : word) => PL' = PL0) r st' ms'
         /\ exists rc, rw_cells bgusegs (ms_mem ms') an rc /\ cells_size rc = 60%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RECP_CTX_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until pad. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> PWF0 E1 E2 E3 -> PAD.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (recp_at_place PL0 an) as HRC.
    pose proof (recp_at_refN bs OW _ an HRC) as HAN. pose proof (recp_at_refNr bs OW _ an HRC) as HANr.
    assert (NRON : RRecpN <> ROne) by (unfold RRecpN, ROne; lia).
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAN NRON) as (_ & AN8).
    assert (NRONr : RRecpNr <> ROne) by (unfold RRecpNr, ROne; lia).
    assert (NENr : RRecpN <> RRecpNr) by (unfold RRecpN, RRecpNr; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAN) as HVN. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HANr) as HVNr.
    destruct (lib_state_open [] bs m OW _ EA RRecpN an LS ND HAN ltac:(intros []) NRON) as ((D1 & BN1 & ARR1) & (OK1a & OK1b & OK1c & OK1d) & LSH1).
    destruct (lib_state_open [RRecpN] bs m OW _ EA RRecpNr (an + 24) LSH1 ND HANr ltac:(intros [E|[]]; exact (NENr E)) NRONr)
      as ((D2 & BN2 & ARR2) & (OK2a & OK2b & OK2c & OK2d) & LSH2).
    pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS (proj2 (proj2 HRC))) as RC. unfold recp_cells in RC.

    destruct OK1d as [F1|F1].
    2: { unfold BN_RECP_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1.
         cbn [embed interp]. apply implM_interp_unr. }
    destruct OK2d as [F2|F2].
    2: { unfold BN_RECP_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1, F2.
         cbn [embed interp]. apply implM_interp_unr. }
    rewrite (recp_free_tree bs F1 F2).
    set (bsF := set_recp 0 0 (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) bs))).

    assert (SPA : bv_unsigned sp <= an /\ 0 < an).
    { destruct FROK as (PLF & CSP & _).
      destruct (PLF (an, an + BN_STRUCT_SZ)) as [X _]; [apply pl_frames_In; left; exists RRecpN; split; [unfold RRecpN, NFIX; lia| left; reflexivity]|].
      cbn [fst] in X. split; [exact X|]. clear - X CSP CEIL. lia. }
    destruct SPA as [SPA AN0].
    assert (SCL : rw_cells bgusegs m (an + 48) [C4 (wz (st_rbits bs)); C4 (wz (st_rshift bs)); C4 (wz 0); C4 pad]).
    { change [C4 (wz (st_rbits bs)); C4 (wz (st_rshift bs)); C4 (wz 0); C4 pad] with ([C4 (wz (st_rbits bs)); C4 (wz (st_rshift bs)); C4 (wz 0)] ++ [C4 pad]).
      apply bk_rw_cells_app. split; [exact RC|]. cbn [cells_size csize Nat.add]. replace (an + 48 + Z.of_nat 12) with (an + 60) by lia. exact PAD. }
    unfold bn_arr in ARR1, ARR2. rewrite pl_of_place_recp_N in ARR1. rewrite pl_of_place_recp_Nr in ARR2.
    pose proof (proj1 (proj2 (proj2 PARTS))) as IDS.
    set (bN := getbn RRecpN bs) in *. set (bNr := getbn RRecpNr bs) in *.
    assert (INS1 : forall pd, bn_d bN = Some pd -> In (pd, D1, 8 * Z.of_nat (bn_dmax bN)) OW) by (intros pd E; rewrite E in ARR1; exact (proj1 ARR1)).
    assert (NONE1 : bn_d bN = None -> D1 = 0) by (intros E; rewrite E in ARR1; exact (proj1 ARR1)).
    assert (INS2 : forall pd, bn_d bNr = Some pd -> In (pd, D2, 8 * Z.of_nat (bn_dmax bNr)) OW) by (intros pd E; rewrite E in ARR2; exact (proj1 ARR2)).
    assert (NONE2 : bn_d bNr = None -> D2 = 0) by (intros E; rewrite E in ARR2; exact (proj1 ARR2)).
    assert (NE12 : forall p1 p2, bn_d bN = Some p1 -> bn_d bNr = Some p2 -> p1 <> p2)
      by (intros p1 p2 H1 H2; exact (ids_bn_neq RRecpN RRecpNr bs p1 p2 (ids_m_nodup _ _ _ IDS) HVN HVNr NENr H1 H2)).
    clear ARR1 ARR2.
    eapply (BN_RECP_CTX_free_walk HF) with (L := OW ++ LB) (A := an) (D1 := D1) (D2 := D2) (bN := bN) (bNr := bNr)
        (nb := wz (st_rbits bs)) (sh := wz (st_rshift bs)) (pad := pad) (fl := 0) (lo := lo) (B := B) (errv := errv);
      [ exact HEAP
      | intros pd E; apply in_or_app; left; exact (INS1 pd E)
      | exact NONE1
      | intros pd E; apply lb_remove_opt_In; split; [apply in_or_app; left; exact (INS2 pd E)| intros p1 E1'; cbn [blk_id fst]; intros Epd; exact (NE12 p1 pd E1' E (eq_sym Epd))]
      | exact NONE2
      | intros a Ha; left; clear - Ha SPA; lia
      | exact AUX | exact SPB | exact ST | exact CEIL | exact GLO | exact LO | exact ERR | exact MI | reflexivity | exact (proj1 LS)
      | exact BN1 | rewrite F1; clear; lia | rewrite F1; reflexivity | rewrite F1; reflexivity | rewrite F1; reflexivity
      | exact BN2 | rewrite F2; clear; lia | rewrite F2; reflexivity | rewrite F2; reflexivity | rewrite F2; reflexivity
      | exact SCL | clear; lia | reflexivity | right; exact SPA | exact AN0 | exact AN8 | reflexivity | ].
    intros s' ms' GP C1 C2 C3.
    destruct GP as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MI' & ST' & ERR' & AUX' & HP & FA & SO & HEAP').
    change (rw_cells bgusegs m' an (bn_cells D1 bN)) in C1. change (rw_cells bgusegs m' (an + 24) (bn_cells D2 bNr)) in C2.
    change (rw_cells bgusegs m' (an + 48) [C4 (wz (st_rbits bs)); C4 (wz (st_rshift bs)); C4 (wz 0); C4 pad]) in C3.

    set (OW2 := lb_remove_opt (bn_d bNr) (lb_remove_opt (bn_d bN) OW)).
    assert (NDL : List.NoDup (map blk_id (OW ++ LB))) by (eapply LH_nodup; exact HEAP).
    assert (EL : lb_remove_opt (bn_d bNr) (lb_remove_opt (bn_d bN) (OW ++ LB)) = OW2 ++ LB).
    { unfold OW2. rewrite (lb_remove_opt_app_l (bn_d bN) OW LB NDL) by (intros p1 E; exact (in_map blk_id _ _ (INS1 p1 E))).
      destruct (bn_d bNr) as [p2|] eqn:Ed2; cbn [lb_remove_opt]; [|reflexivity].
      rewrite lb_remove_app. f_equal. apply lb_remove_notin. intros H.
      rewrite map_app in NDL. exact (nodup_app_disj _ _ p2 NDL (in_map blk_id _ _ (INS2 p2 eq_refl)) H). }
    rewrite EL in HP, HEAP'.
    assert (INC2 : forall b, In b OW2 -> In b OW).
    { intros b Hb. unfold OW2 in Hb. apply lb_remove_opt_In in Hb. destruct Hb as [Hb _]. apply lb_remove_opt_In in Hb. exact (proj1 Hb). }

    set (bs1 := setbn RRecpN (bn_nil 0) bs).
    set (bsN := setbn RRecpNr (bn_nil 0) bs1).
    assert (IDS1 : ids_ok bs1 (pl_place_recp PL0 an) EA) by (apply ids_ok_setbn_none; [exact IDS| exact HVN| reflexivity]).
    assert (LSa : lib_state_h [RRecpNr; RRecpN] bs1 m OW (pl_place_recp PL0 an) EA).
    { eapply (lib_state_h_setbn_hole false [RRecpNr; RRecpN] bs m OW _ EA RRecpN an); [exact LSH2| exact ND| exact HAN| right; left; reflexivity| exact NRON
        | apply bg_ok_nil; left; reflexivity| exact IDS1]. }
    assert (HVNr1 : vref RRecpNr bs1) by (unfold vref, bs1; rewrite length_setbn; exact HVNr).
    assert (IDSN : ids_ok bsN (pl_place_recp PL0 an) EA) by (apply ids_ok_setbn_none; [exact IDS1| exact HVNr1| reflexivity]).
    assert (LSb : lib_state_h [RRecpNr; RRecpN] bsN m OW (pl_place_recp PL0 an) EA).
    { eapply (lib_state_h_setbn_hole false [RRecpNr; RRecpN] bs1 m OW _ EA RRecpNr (an + 24)); [exact LSa| exact ND| exact (recp_at_refNr bs1 OW _ an HRC)| left; reflexivity| exact NRONr
        | apply bg_ok_nil; left; reflexivity| exact IDSN]. }

    assert (FOR1 : forall p1, bn_d bN = Some p1 -> ~ In p1 (all_ids bsN (pl_place_recp PL0 an) EA)).
    { intros p1 E H. apply (all_ids_setbn_nil bs1 _ EA RRecpNr p1 HVNr1) in H. exact (all_ids_without bs _ EA RRecpN p1 IDS HVN E H). }
    assert (FOR2 : forall p2, bn_d bNr = Some p2 -> ~ In p2 (all_ids bsN (pl_place_recp PL0 an) EA)).
    { intros p2 E. apply (all_ids_without bs1 _ EA RRecpNr p2 IDS1 HVNr1). unfold bs1. rewrite getbn_setbn_other by exact NENr. exact E. }
    assert (LSc : lib_state_h [RRecpNr; RRecpN] bsN m OW2 (pl_place_recp PL0 an) EA).
    { eapply lib_state_h_ow; [exact LSb|]. intros q A n Hq Hin. unfold OW2. apply lb_remove_opt_In. split.
      - apply lb_remove_opt_In. split; [exact Hin|]. intros p1 E. cbn [blk_id fst]. intros ->. exact (FOR1 p1 E Hq).
      - intros p2 E. cbn [blk_id fst]. intros ->. exact (FOR2 p2 E Hq). }
    assert (LSd : lib_state_h [RRecpNr; RRecpN] bsN m' OW2 (pl_place_recp PL0 an) EA).
    { eapply (lib_state_h_heap_pres [RRecpNr; RRecpN] bsN m m' OW2 _ EA (OW2 ++ LB) (bv_unsigned sp) (bv_unsigned sp) B);
        [exact LSc| exact FROK| clear; lia| exact HP| intros b Hb; apply in_or_app; left; exact Hb]. }
    assert (GN : getbn RRecpN bsN = bn_nil 0).
    { unfold bsN. rewrite getbn_setbn_other by (intros E; exact (NENr (eq_sym E))). unfold bs1. apply getbn_setbn_same. exact HVN. }
    assert (GNr : getbn RRecpNr bsN = bn_nil 0) by (unfold bsN; apply getbn_setbn_same; exact HVNr1).
    assert (LSF : lib_state bsF m' OW2 PL0 EA).
    { unfold lib_state, bsF. fold bs1. fold bsN.
      eapply (lib_state_unplace_recp false [RRecpNr; RRecpN] [] bsN m' OW2 PL0 EA an 0 0); [exact LSd| exact PWF0| exact E1| exact E2| exact E3| exact GN| exact GNr|].
      intros r [<-|[<-|[]]]; [right; left; reflexivity| left; reflexivity]. }
    cbn [interp]. apply implM_interp_ret. apply evt_done. split.
    - unfold bn_post. do 15 eexists. exists m', OW2, PL0, errv. split; [reflexivity|]. cbn [fst snd].
      split; [exact HEAP'|]. split; [exact LSF|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
      split. { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| clear; lia|]. intros b Hb. apply in_or_app. right. exact Hb. }
      split; [exact FA|]. split; [exact SO|].
      split; [|reflexivity].
      apply refs_stable_ow; [reflexivity|]. intros q H Hq HinH. unfold OW2. apply lb_remove_opt_In. split.
      + apply lb_remove_opt_In. split; [exact HinH|]. intros p1 E. cbn [blk_id fst]. intros ->.
        exact (ids_bn_item_neq RRecpN bs p1 p1 (ids_m_nodup _ _ _ IDS) HVN E Hq eq_refl).
      + intros p2 E. cbn [blk_id fst]. intros ->.
        exact (ids_bn_item_neq RRecpNr bs p2 p2 (ids_m_nodup _ _ _ IDS) HVNr E Hq eq_refl).
    - exists (bn_cells D1 bN ++ bn_cells D2 bNr ++ [C4 (wz (st_rbits bs)); C4 (wz (st_rshift bs)); C4 (wz 0)]). split; [|reflexivity].
      cbn [ms_mem].
      change [C4 (wz (st_rbits bs)); C4 (wz (st_rshift bs)); C4 (wz 0); C4 pad] with ([C4 (wz (st_rbits bs)); C4 (wz (st_rshift bs)); C4 (wz 0)] ++ [C4 pad]) in C3.
      apply bk_rw_cells_app in C3. destruct C3 as [C3 _].
      apply bk_rw_cells_app. split; [exact C1|]. change (Z.of_nat (cells_size (bn_cells D1 bN))) with 24.
      apply bk_rw_cells_app. split; [exact C2|]. change (Z.of_nat (cells_size (bn_cells D2 bNr))) with 24.
      replace (an + 24 + 24) with (an + 48) by (clear; lia). exact C3.
  Qed.

  Lemma BN_RECP_CTX_free_lwalk_cs : forall (CS : Z), BN_RECP_CTX_FREE_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL0 : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (an : Z) (pad : word),
    bn_pre s bs m OW LB (pl_place_recp PL0 an) EA sp lo B errv CS -> tp = wz RATP ->
    pl_wf PL0 -> pl_bn PL0 RRecpN = None -> pl_bn PL0 RRecpNr = None -> pl_recp PL0 = None -> a0 = wz an ->
    rw_cells bgusegs m (an + 60) [C4 pad] ->
    implM bgusegs (interp (embed (BN_RECP_CTX_free (tree_ops bptr) bs))) s
      (fun r st' ms' =>
         bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m (pl_place_recp PL0 an) EA
                 (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (_ : word) => PL' = PL0) r st' ms'
         /\ exists rc, rw_cells bgusegs (ms_mem ms') an rc /\ cells_size rc = 60%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RECP_CTX_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros CS HCS. intros until pad. intros (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
    eapply BN_RECP_CTX_free_lwalk. unfold bn_pre. repeat (split; [eassumption|]). split; [clear - P10 HCS; lia|]. split; eassumption.
  Qed.

End Proofs.
End WithCeiling0.
