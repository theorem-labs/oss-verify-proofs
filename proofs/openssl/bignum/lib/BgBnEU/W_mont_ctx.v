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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3 W_alloc3 W_ctx3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import W_recp_free PlaceMont.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma mont_free_tree : forall (bs : bstate bptr) (qm : bptr),
  bn_flags (getbn RMontRR bs) = 0 -> bn_flags (getbn RMontN bs) = 0 -> bn_flags (getbn RMontNi bs) = 0 ->
  embed (BN_MONT_CTX_free (tree_ops bptr) qm bs) =
  lbind (lfree_opt (bn_d (getbn RMontRR bs))) (fun _ => lbind (lfree_opt (bn_d (getbn RMontN bs))) (fun _ =>
  lbind (lfree_opt (bn_d (getbn RMontNi bs))) (fun _ =>
    LFree qm (LRet (tt, set_mont 0 0 (setbn RMontNi (bn_nil 0) (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) bs)))))))).
Proof.
  intros bs qm F1 F2 F3.
  assert (H1 : forall f, has_flag (getbn RMontRR bs) f = false) by (intros f; unfold has_flag; rewrite F1; reflexivity).
  assert (H2 : forall f, has_flag (getbn RMontN bs) f = false) by (intros f; unfold has_flag; rewrite F2; reflexivity).
  assert (H3 : forall f, has_flag (getbn RMontNi bs) f = false) by (intros f; unfold has_flag; rewrite F3; reflexivity).
  assert (G2 : forall b, getbn RMontN (setbn RMontRR b bs) = getbn RMontN bs)
    by (intros b; apply getbn_setbn_other; unfold RMontRR, RMontN; lia).
  assert (G3 : forall b b', getbn RMontNi (setbn RMontN b' (setbn RMontRR b bs)) = getbn RMontNi bs)
    by (intros b b'; rewrite !getbn_setbn_other by (unfold RMontRR, RMontN, RMontNi; lia); reflexivity).
  unfold BN_MONT_CTX_free, BN_clear_free, bbind, bget, bset, bret, bunr, bsetmont. cbn [bind ret unreachable tree_ops tbind fst snd].
  rewrite !H1, !H2, !H3. cbn [orb]. cbv beta. rewrite !H1.
  destruct (bn_d (getbn RMontRR bs)) as [q1|];
    cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd lfree_opt lfree lbind embed];
    rewrite !G2, !H2; cbv beta;
    (destruct (bn_d (getbn RMontN bs)) as [q2|];
     cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd lfree_opt lfree lbind embed];
     rewrite !G3, !H3; cbv beta;
     (destruct (bn_d (getbn RMontNi bs)) as [q3|];
      cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd lfree_opt lfree lbind embed]; reflexivity)).
Qed.

Lemma ref_at_mRR : forall st OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontRR am.
Proof. intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontRR, NFIX; lia|]. exists (PHeap am qm 0). unfold pl_of. rewrite E. cbn. split; reflexivity. Qed.
Lemma ref_at_mN : forall st OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontN (am + 24).
Proof. intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontN, NFIX; lia|]. exists (PHeap (am + 24) qm 24). unfold pl_of. rewrite E. cbn. split; reflexivity. Qed.
Lemma ref_at_mNi : forall st OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontNi (am + 48).
Proof. intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontNi, NFIX; lia|]. exists (PHeap (am + 48) qm 48). unfold pl_of. rewrite E. cbn. split; reflexivity. Qed.

Lemma all_ids_unset_mont : forall (s : bstate bptr) PL EA am qm x y q, pl_mont PL = Some (am, qm) ->
  In q (all_ids (set_mont x y s) (pl_set_mont PL None) EA) -> In q (all_ids s PL EA).
Proof.
  intros s PL EA am qm x y q E H. unfold all_ids in *. change (blocks_of (set_mont x y s)) with (blocks_of s) in H.
  rewrite in_app_iff in *. destruct H as [H|H]; [left| right; exact H].
  eapply Permutation_in; [apply Permutation_sym; exact (pl_ids_unset_mont PL am qm E)|]. right. exact H.
Qed.

Lemma lb_remove_opt_app_r : forall o (OW LB : list block), (forall p, o = Some p -> ~ In p (map blk_id LB)) ->
  lb_remove_opt o (OW ++ LB) = lb_remove_opt o OW ++ LB.
Proof.
  intros [p|] OW LB H; cbn [lb_remove_opt]; [|reflexivity].
  rewrite lb_remove_app. f_equal. apply lb_remove_notin. apply H. reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_MONT_CTX_new_lwalk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_MONT_CTX_NEW_STACK -> tp = wz RATP ->
    pl_mont PL = None ->
    implM bgusegs (interp (embed (BN_MONT_CTX_new (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun p bs' OW' PL' a0' => exists a, PL' = pl_set_mont PL (Some (a, p)) /\ a0' = wz a /\ 0 < a < 2^63
                                         /\ OW' = (p, a, 96) :: OW /\ bs' = st_mont_init bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_NEW) fc None m (seg_rom bgusegs)).
  Proof.
    intros until errv. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> E.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    unfold BN_MONT_CTX_new, bbind, bmalloc, bsetmont, bset, bret. cbn [bind ret unreachable lib_malloc tree_ops tbind fst snd embed].
    eapply (W_ctx3.BN_MONT_CTX_new_walk HM) with (B := B) (lo := lo) (errv := errv);
      [exact HEAP | exact AUX | exact SPB | exact ST | exact CEIL | exact GLO | exact LO | exact ERR | exact MI | reflexivity
      | exact (proj1 LS) | reflexivity |].
    intros p s' ms' PO. unfold calloc_post in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    cbn [tbind embed interp fst snd]. apply implM_ret. apply evt_done.
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (ND3 : List.NoDup (map blk_id ((p, A, 96) :: OW ++ LB))) by (eapply LH_nodup; exact HEAP3).
    assert (FRESH : ~ In p (map blk_id (OW ++ LB))) by (cbn [map] in ND3; apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
    assert (FRESHA : ~ In p (all_ids bs PL EA)).
    { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
    assert (LS3 : lib_state bs m3 OW PL EA).
    { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ _ (bv_unsigned sp) B); [exact LS| exact FROK| | exact HP|]; [lia|].
      intros b0 Hb0. apply in_or_app. left. exact Hb0. }
    set (OW1 := (p, A, 96) :: OW).
    assert (LS3' : lib_state bs m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LS3|]; intros q A0 n0 _ Hq; right; exact Hq).
    unfold mont_cells0 in BLK.
    apply bk_rw_cells_app in BLK. destruct BLK as [C1 BLK]. change (Z.of_nat (cells_size (bn_cells 0 (bn_nil 0)))) with 24 in BLK.
    apply bk_rw_cells_app in BLK. destruct BLK as [C2 BLK]. change (Z.of_nat (cells_size (bn_cells 0 (bn_nil 0)))) with 24 in BLK.
    apply bk_rw_cells_app in BLK. destruct BLK as [C3 C4]. change (Z.of_nat (cells_size (bn_cells 0 (bn_nil 0)))) with 24 in C4.
    replace (A + 24 + 24) with (A + 48) in C3, C4 by (clear; lia). replace (A + 48 + 24) with (A + 72) in C4 by (clear; lia).
    unfold bn_post. do 15 eexists. exists m3, OW1, (pl_set_mont PL (Some (A, p))), errv2. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP3|].
    split. { eapply (lib_state_place_mont false [] bs m3 OW1 PL EA A p); [exact LS3'| exact E| left; reflexivity| exact FRESHA| exact C1| exact C2| exact C3| exact C4]. }
    split; [exact AUX3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact MI3|].
    split. { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
    split; [exact FA|]. split; [exact SO|].
    split. { apply refs_stable_ow; [reflexivity|]. intros q H _ Hq. right. exact Hq. }
    exists A. split; [reflexivity|]. split; [reflexivity|]. split; [clear - BA0 BAC; lia|]. split; reflexivity.
  Qed.

  Lemma BN_MONT_CTX_free_lwalk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (am : Z) (qm : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_MONT_CTX_FREE_STACK -> tp = wz RATP ->
    pl_mont PL = Some (am, qm) -> a0 = wz am ->
    implM bgusegs (interp (embed (BN_MONT_CTX_free (tree_ops bptr) qm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (_ : word) => PL' = pl_set_mont PL None))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qm. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> E ->.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_mRR bs OW PL am qm E) as HA1. pose proof (ref_at_mN bs OW PL am qm E) as HA2. pose proof (ref_at_mNi bs OW PL am qm E) as HA3.
    assert (NRO1 : RMontRR <> ROne) by (unfold RMontRR, ROne; lia).
    assert (NRO2 : RMontN <> ROne) by (unfold RMontN, ROne; lia).
    assert (NRO3 : RMontNi <> ROne) by (unfold RMontNi, ROne; lia).
    assert (NE12 : RMontRR <> RMontN) by (unfold RMontRR, RMontN; lia).
    assert (NE13 : RMontRR <> RMontNi) by (unfold RMontRR, RMontNi; lia).
    assert (NE23 : RMontN <> RMontNi) by (unfold RMontN, RMontNi; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA1) as HV1. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA2) as HV2.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA3) as HV3.
    destruct (lib_state_open [] bs m OW _ EA RMontRR am LS ND HA1 ltac:(intros []) NRO1) as ((D1 & BN1 & ARR1) & (OK1a & OK1b & OK1c & OK1d) & LSH1).
    destruct (lib_state_open [RMontRR] bs m OW _ EA RMontN (am + 24) LSH1 ND HA2 ltac:(intros [X|[]]; exact (NE12 X)) NRO2)
      as ((D2 & BN2 & ARR2) & (OK2a & OK2b & OK2c & OK2d) & LSH2).
    destruct (lib_state_open [RMontN; RMontRR] bs m OW _ EA RMontNi (am + 48) LSH2 ND HA3 ltac:(intros [X|[X|[]]]; [exact (NE23 X)| exact (NE13 X)]) NRO3)
      as ((D3 & BN3 & ARR3) & (OK3a & OK3b & OK3c & OK3d) & LSH3).
    pose proof (lib_state_mont_cells _ _ _ _ _ _ _ _ _ LS E) as MC. unfold mont_cells in MC.
    assert (INQ : In (qm, am, 96) OW).
    { destruct LS as (_ & _ & _ & (_ & _ & _ & (_ & _ & _ & (M4 & _)))). rewrite E in M4. exact (proj1 M4). }

    destruct OK1d as [F1|F1].
    2: { unfold BN_MONT_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1.
         cbn [embed interp]. apply implM_interp_unr. }
    destruct OK2d as [F2|F2].
    2: { unfold BN_MONT_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1, F2.
         cbn [embed interp]. apply implM_interp_unr. }
    destruct OK3d as [F3|F3].
    2: { unfold BN_MONT_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1, F2, F3.
         cbn [embed interp]. apply implM_interp_unr. }
    rewrite (mont_free_tree bs qm F1 F2 F3).
    set (bsF := set_mont 0 0 (setbn RMontNi (bn_nil 0) (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) bs)))).
    unfold bn_arr in ARR1, ARR2, ARR3.
    replace (pl_of PL RMontRR) with (Some (PHeap am qm 0)) in ARR1 by (unfold pl_of; rewrite E; reflexivity).
    replace (pl_of PL RMontN) with (Some (PHeap (am + 24) qm 24)) in ARR2 by (unfold pl_of; rewrite E; reflexivity).
    replace (pl_of PL RMontNi) with (Some (PHeap (am + 48) qm 48)) in ARR3 by (unfold pl_of; rewrite E; reflexivity).
    pose proof (proj1 (proj2 (proj2 PARTS))) as IDS. pose proof (ids_m_nodup _ _ _ IDS) as NDM.
    set (b1 := getbn RMontRR bs) in *. set (b2 := getbn RMontN bs) in *. set (b3 := getbn RMontNi bs) in *.
    assert (INS1 : forall pd, bn_d b1 = Some pd -> In (pd, D1, 8 * Z.of_nat (bn_dmax b1)) OW /\ 0 < D1 /\ u64arr bgusegs m D1 (wlimbs (bn_buf b1))).
    { intros pd X. rewrite X in ARR1. destruct ARR1 as [I1 U1]. split; [exact I1|]. split; [|exact U1]. exact (proj1 (RH_range _ _ _ _ _ _ _ HEAP I1)). }
    assert (NONE1 : bn_d b1 = None -> D1 = 0) by (intros X; rewrite X in ARR1; exact (proj1 ARR1)).
    assert (INS2 : forall pd, bn_d b2 = Some pd -> In (pd, D2, 8 * Z.of_nat (bn_dmax b2)) OW /\ 0 < D2 /\ u64arr bgusegs m D2 (wlimbs (bn_buf b2))).
    { intros pd X. rewrite X in ARR2. destruct ARR2 as [I1 U1]. split; [exact I1|]. split; [|exact U1]. exact (proj1 (RH_range _ _ _ _ _ _ _ HEAP I1)). }
    assert (NONE2 : bn_d b2 = None -> D2 = 0) by (intros X; rewrite X in ARR2; exact (proj1 ARR2)).
    assert (INS3 : forall pd, bn_d b3 = Some pd -> In (pd, D3, 8 * Z.of_nat (bn_dmax b3)) OW /\ 0 < D3 /\ u64arr bgusegs m D3 (wlimbs (bn_buf b3))).
    { intros pd X. rewrite X in ARR3. destruct ARR3 as [I1 U1]. split; [exact I1|]. split; [|exact U1]. exact (proj1 (RH_range _ _ _ _ _ _ _ HEAP I1)). }
    assert (NONE3 : bn_d b3 = None -> D3 = 0) by (intros X; rewrite X in ARR3; exact (proj1 ARR3)).
    assert (N12 : forall p q, bn_d b1 = Some p -> bn_d b2 = Some q -> p <> q) by (intros p q X Y; exact (ids_bn_neq RMontRR RMontN bs p q NDM HV1 HV2 NE12 X Y)).
    assert (N13 : forall p q, bn_d b1 = Some p -> bn_d b3 = Some q -> p <> q) by (intros p q X Y; exact (ids_bn_neq RMontRR RMontNi bs p q NDM HV1 HV3 NE13 X Y)).
    assert (N23 : forall p q, bn_d b2 = Some p -> bn_d b3 = Some q -> p <> q) by (intros p q X Y; exact (ids_bn_neq RMontN RMontNi bs p q NDM HV2 HV3 NE23 X Y)).
    assert (NQ : forall r p, vref r bs -> bn_d (getbn r bs) = Some p -> qm <> p).
    { intros r p HV X. apply (ids_pl_m bs PL EA qm p IDS); [|exact (bn_in_m r bs p HV X)].
      unfold pl_ids. rewrite E. cbn [opt_ids]. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
    clear ARR1 ARR2 ARR3.
    unfold BG_DMAX in OK1c, OK2c, OK3c.
    eapply (BN_MONT_CTX_free_walk HF) with (L := OW ++ LB) (q := qm) (A := am) (D1 := D1) (D2 := D2) (D3 := D3) (bRR := b1) (bN := b2) (bNi := b3)
        (n0 := wz (st_n0 bs)) (n1 := wz 0) (ri := wz (st_ri bs)) (fl := BN_FLG_MALLOCED) (lo := lo) (B := B) (errv := errv);
      [ exact HEAP
      | intros pd X; destruct (INS1 pd X) as (I1 & I2 & I3); split; [apply in_or_app; left; exact I1| split; [exact I2| exact I3]]
      | exact NONE1
      | intros pd X; destruct (INS2 pd X) as (I1 & I2 & I3); split; [|split; [exact I2| exact I3]];
        apply lb_remove_opt_In; split; [apply in_or_app; left; exact I1| intros p1 X1; cbn [blk_id fst]; intros Y; exact (N12 p1 pd X1 X (eq_sym Y))]
      | exact NONE2
      | intros pd X; destruct (INS3 pd X) as (I1 & I2 & I3); split; [|split; [exact I2| exact I3]];
        apply lb_remove_opt_In; split;
        [apply lb_remove_opt_In; split; [apply in_or_app; left; exact I1| intros p1 X1; cbn [blk_id fst]; intros Y; exact (N13 p1 pd X1 X (eq_sym Y))]
        | intros p2 X2; cbn [blk_id fst]; intros Y; exact (N23 p2 pd X2 X (eq_sym Y))]
      | exact NONE3
      | apply lb_remove_opt_In; split;
        [apply lb_remove_opt_In; split;
         [apply lb_remove_opt_In; split; [apply in_or_app; left; exact INQ| intros p1 X1; cbn [blk_id fst]; exact (NQ RMontRR p1 HV1 X1)]
         | intros p2 X2; cbn [blk_id fst]; exact (NQ RMontN p2 HV2 X2)]
        | intros p3 X3; cbn [blk_id fst]; exact (NQ RMontNi p3 HV3 X3)]
      | exact AUX | exact SPB | exact ST | exact CEIL | exact GLO | exact LO | exact ERR | exact MI | reflexivity | exact (proj1 LS)
      | exact BN1 | rewrite F1; clear; lia | rewrite F1; reflexivity | rewrite F1; reflexivity | rewrite F1; reflexivity | clear - OK1c; lia
      | exact BN2 | rewrite F2; clear; lia | rewrite F2; reflexivity | rewrite F2; reflexivity | rewrite F2; reflexivity | clear - OK2c; lia
      | exact BN3 | rewrite F3; clear; lia | rewrite F3; reflexivity | rewrite F3; reflexivity | rewrite F3; reflexivity | clear - OK3c; lia
      | exact MC | unfold BN_FLG_MALLOCED; clear; lia | reflexivity | reflexivity | ].
    intros s' ms' GP.
    destruct GP as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MI' & ST' & ERR' & AUX' & HP & FA & SO & HEAP').

    set (OW4 := lb_remove qm (lb_remove_opt (bn_d b3) (lb_remove_opt (bn_d b2) (lb_remove_opt (bn_d b1) OW)))).
    assert (NDL : List.NoDup (map blk_id (OW ++ LB))) by (eapply LH_nodup; exact HEAP).
    assert (NLB : forall q A n, In (q, A, n) OW -> ~ In q (map blk_id LB)).
    { intros q A n Hq H. rewrite map_app in NDL. exact (nodup_app_disj _ _ q NDL (in_map blk_id _ _ Hq) H). }
    assert (EL : lb_remove qm (lb_remove_opt (bn_d b3) (lb_remove_opt (bn_d b2) (lb_remove_opt (bn_d b1) (OW ++ LB)))) = OW4 ++ LB).
    { unfold OW4.
      rewrite (lb_remove_opt_app_r (bn_d b1)) by (intros p1 X; exact (NLB _ _ _ (proj1 (INS1 p1 X)))).
      rewrite (lb_remove_opt_app_r (bn_d b2)) by (intros p2 X; exact (NLB _ _ _ (proj1 (INS2 p2 X)))).
      rewrite (lb_remove_opt_app_r (bn_d b3)) by (intros p3 X; exact (NLB _ _ _ (proj1 (INS3 p3 X)))).
      rewrite lb_remove_app. f_equal. apply lb_remove_notin. exact (NLB _ _ _ INQ). }
    rewrite EL in HP, HEAP'.

    set (bs1 := setbn RMontRR (bn_nil 0) bs).
    set (bs2 := setbn RMontN (bn_nil 0) bs1).
    set (bs3 := setbn RMontNi (bn_nil 0) bs2).
    assert (IDS1 : ids_ok bs1 PL EA) by (apply ids_ok_setbn_none; [exact IDS| exact HV1| reflexivity]).
    assert (LSa : lib_state_h [RMontNi; RMontN; RMontRR] bs1 m OW PL EA).
    { eapply (lib_state_h_setbn_hole false [RMontNi; RMontN; RMontRR] bs m OW PL EA RMontRR am); [exact LSH3| exact ND| exact HA1| right; right; left; reflexivity| exact NRO1
        | apply bg_ok_nil; left; reflexivity| exact IDS1]. }
    assert (HV2' : vref RMontN bs1) by (unfold vref, bs1; rewrite length_setbn; exact HV2).
    assert (IDS2 : ids_ok bs2 PL EA) by (apply ids_ok_setbn_none; [exact IDS1| exact HV2'| reflexivity]).
    assert (LSb : lib_state_h [RMontNi; RMontN; RMontRR] bs2 m OW PL EA).
    { eapply (lib_state_h_setbn_hole false [RMontNi; RMontN; RMontRR] bs1 m OW PL EA RMontN (am + 24)); [exact LSa| exact ND| exact (ref_at_mN bs1 OW PL am qm E)| right; left; reflexivity| exact NRO2
        | apply bg_ok_nil; left; reflexivity| exact IDS2]. }
    assert (HV3' : vref RMontNi bs2) by (unfold vref, bs2, bs1; rewrite !length_setbn; exact HV3).
    assert (IDS3 : ids_ok bs3 PL EA) by (apply ids_ok_setbn_none; [exact IDS2| exact HV3'| reflexivity]).
    assert (LSc : lib_state_h [RMontNi; RMontN; RMontRR] bs3 m OW PL EA).
    { eapply (lib_state_h_setbn_hole false [RMontNi; RMontN; RMontRR] bs2 m OW PL EA RMontNi (am + 48)); [exact LSb| exact ND| exact (ref_at_mNi bs2 OW PL am qm E)| left; reflexivity| exact NRO3
        | apply bg_ok_nil; left; reflexivity| exact IDS3]. }
    assert (G1 : getbn RMontRR bs3 = bn_nil 0).
    { unfold bs3, bs2. rewrite !getbn_setbn_other by (unfold RMontRR, RMontN, RMontNi; lia). unfold bs1. apply getbn_setbn_same. exact HV1. }
    assert (G2 : getbn RMontN bs3 = bn_nil 0).
    { unfold bs3. rewrite getbn_setbn_other by (unfold RMontN, RMontNi; lia). unfold bs2. apply getbn_setbn_same. exact HV2'. }
    assert (G3 : getbn RMontNi bs3 = bn_nil 0) by (unfold bs3; apply getbn_setbn_same; exact HV3').
    destruct (lib_state_unplace_mont false [RMontNi; RMontN; RMontRR] [] bs3 m OW PL EA am qm 0 0 LSc E G1 G2 G3) as [LSu NQF].
    { intros r [<-|[<-|[<-|[]]]]; left; reflexivity. }
    fold bsF in LSu, NQF.

    assert (FOR1 : forall p1, bn_d b1 = Some p1 -> ~ In p1 (all_ids bsF (pl_set_mont PL None) EA)).
    { intros p1 X H. apply (all_ids_unset_mont bs3 PL EA am qm 0 0 p1 E) in H.
      apply (all_ids_setbn_nil bs2 _ EA RMontNi p1 HV3') in H. apply (all_ids_setbn_nil bs1 _ EA RMontN p1 HV2') in H.
      exact (all_ids_without bs _ EA RMontRR p1 IDS HV1 X H). }
    assert (FOR2 : forall p2, bn_d b2 = Some p2 -> ~ In p2 (all_ids bsF (pl_set_mont PL None) EA)).
    { intros p2 X H. apply (all_ids_unset_mont bs3 PL EA am qm 0 0 p2 E) in H.
      apply (all_ids_setbn_nil bs2 _ EA RMontNi p2 HV3') in H.
      apply (all_ids_without bs1 _ EA RMontN p2 IDS1 HV2'); [|exact H]. unfold bs1. rewrite getbn_setbn_other by exact NE12. exact X. }
    assert (FOR3 : forall p3, bn_d b3 = Some p3 -> ~ In p3 (all_ids bsF (pl_set_mont PL None) EA)).
    { intros p3 X H. apply (all_ids_unset_mont bs3 PL EA am qm 0 0 p3 E) in H.
      apply (all_ids_without bs2 _ EA RMontNi p3 IDS2 HV3'); [|exact H]. unfold bs2, bs1. rewrite !getbn_setbn_other by (unfold RMontRR, RMontN, RMontNi; lia). exact X. }
    assert (KEEP : forall q A n, In q (all_ids bsF (pl_set_mont PL None) EA) -> In (q, A, n) OW -> In (q, A, n) OW4).
    { intros q A n Hq Hin. unfold OW4. apply lb_remove_In. split; [|cbn [blk_id fst]; intros ->; exact (NQF Hq)].
      apply lb_remove_opt_In. split; [|intros p3 X; cbn [blk_id fst]; intros ->; exact (FOR3 p3 X Hq)].
      apply lb_remove_opt_In. split; [|intros p2 X; cbn [blk_id fst]; intros ->; exact (FOR2 p2 X Hq)].
      apply lb_remove_opt_In. split; [exact Hin|]. intros p1 X. cbn [blk_id fst]. intros ->. exact (FOR1 p1 X Hq). }
    assert (LSv : lib_state bsF m OW4 (pl_set_mont PL None) EA) by (eapply lib_state_h_ow; [exact LSu| exact KEEP]).
    assert (LSF : lib_state bsF m' OW4 (pl_set_mont PL None) EA).
    { eapply (lib_state_h_heap_pres [] bsF m m' OW4 _ EA (OW4 ++ LB) (bv_unsigned sp) (bv_unsigned sp) B);
        [exact LSv| exact FROK| clear; lia| exact HP| intros b Hb; apply in_or_app; left; exact Hb]. }
    cbn [interp]. apply implM_interp_ret. apply evt_done.
    unfold bn_post. do 15 eexists. exists m', OW4, (pl_set_mont PL None), errv. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP'|]. split; [exact LSF|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
    split. { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| clear; lia|]. intros b Hb. apply in_or_app. right. exact Hb. }
    split; [exact FA|]. split; [exact SO|].
    split; [|reflexivity].
    apply refs_stable_ow; [reflexivity|]. intros q H Hq HinH. unfold OW4.
    apply lb_remove_In. split.
    2: { cbn [blk_id fst]. intros ->. apply (ids_pl_m bs PL EA qm qm IDS); [|exact (item_in_m bs qm Hq)| reflexivity].
         unfold pl_ids. rewrite E. cbn [opt_ids]. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
    apply lb_remove_opt_In. split; [|intros p3 X; cbn [blk_id fst]; intros ->; exact (ids_bn_item_neq RMontNi bs p3 p3 NDM HV3 X Hq eq_refl)].
    apply lb_remove_opt_In. split; [|intros p2 X; cbn [blk_id fst]; intros ->; exact (ids_bn_item_neq RMontN bs p2 p2 NDM HV2 X Hq eq_refl)].
    apply lb_remove_opt_In. split; [exact HinH|]. intros p1 X. cbn [blk_id fst]. intros ->. exact (ids_bn_item_neq RMontRR bs p1 p1 NDM HV1 X Hq eq_refl).
  Qed.

  Lemma bn_pre_le : forall s bs m OW LB PL EA sp lo B errv K K',
    bn_pre s bs m OW LB PL EA sp lo B errv K' -> K <= K' -> bn_pre s bs m OW LB PL EA sp lo B errv K.
  Proof.
    intros s bs m OW LB PL EA sp lo B errv K K' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12) H.
    unfold bn_pre. repeat (split; [assumption|]). split; [lia|]. split; assumption.
  Qed.

  Lemma BN_MONT_CTX_new_lwalk_cs : forall (CS : Z), BN_MONT_CTX_NEW_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    pl_mont PL = None ->
    implM bgusegs (interp (embed (BN_MONT_CTX_new (tree_ops bptr) bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun p bs' OW' PL' a0' => exists a, PL' = pl_set_mont PL (Some (a, p)) /\ a0' = wz a /\ 0 < a < 2^63
                                         /\ OW' = (p, a, 96) :: OW /\ bs' = st_mont_init bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_NEW) fc None m (seg_rom bgusegs)).
  Proof. intros CS HCS. intros until errv. intros PRE. eapply BN_MONT_CTX_new_lwalk. exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS). Qed.

  Lemma BN_MONT_CTX_free_lwalk_cs : forall (CS : Z), BN_MONT_CTX_FREE_STACK <= CS -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (am : Z) (qm : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    pl_mont PL = Some (am, qm) -> a0 = wz am ->
    implM bgusegs (interp (embed (BN_MONT_CTX_free (tree_ops bptr) qm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (_ : word) => PL' = pl_set_mont PL None))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MONT_CTX_FREE) fc None m (seg_rom bgusegs)).
  Proof. intros CS HCS. intros until qm. intros PRE. eapply BN_MONT_CTX_free_lwalk. exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE HCS). Qed.

End Proofs.
End WithCeiling0.
