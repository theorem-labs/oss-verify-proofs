(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_PmOwn LbB_PmCut LbB_PmCall LbB_PmXp LbB_PmVec LbB_PmVup LbB_PmVops LbB_WoGen LbB_ContStmt.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma pm_phi_blocks_cons : forall b bs, pm_phi_blocks (b :: bs) = 8 * (if ICM_LARGE <? snd b then snd b else 0) + pm_phi_blocks bs.
Proof. intros b bs. unfold pm_phi_blocks. cbn [fold_right]. lia. Qed.
Lemma pm_phi_blocks_app : forall l1 l2, pm_phi_blocks (l1 ++ l2) = pm_phi_blocks l1 + pm_phi_blocks l2.
Proof. induction l1 as [|b l1 IH]; intros l2; [reflexivity|]. cbn [app]. rewrite !pm_phi_blocks_cons, IH. lia. Qed.

Lemma phi_grow : forall (esz cap b b' : Z) (PRE POST : list (Z * Z)),
  0 <= cap -> 1 <= esz -> (b = 0 -> cap = 0) ->
  pm_phi_blocks (PRE ++ [(b', esz * vgrow cap)] ++ POST)
    >= pm_phi_blocks (PRE ++ (if b =? 0 then [] else [(b, esz * cap)]) ++ POST) + ICM (esz * vgrow cap).
Proof.
  intros esz cap b b' PRE POST Hc He Hb.
  assert (VG : vgrow cap >= 2 * cap /\ vgrow cap >= cap + 1) by (unfold vgrow; lia).
  assert (K0 : 0 <= esz * cap) by nia.
  assert (K2 : 2 * (esz * cap) <= esz * vgrow cap) by nia.
  set (k := esz * vgrow cap) in *. set (j := esz * cap) in *. clearbody k j.
  rewrite !pm_phi_blocks_app. rewrite !pm_phi_blocks_cons. cbn [snd]. change (pm_phi_blocks []) with 0.
  destruct (Z.eqb_spec b 0) as [E|E].
  - change (pm_phi_blocks []) with 0. unfold ICM, ICM_LARGE.
    destruct (Z.ltb_spec 64512 k); destruct (Z.leb_spec k 64512); lia.
  - rewrite pm_phi_blocks_cons. cbn [snd]. change (pm_phi_blocks []) with 0. unfold ICM, ICM_LARGE.
    destruct (Z.ltb_spec 64512 k); destruct (Z.leb_spec k 64512); destruct (Z.ltb_spec 64512 j); lia.
Qed.

Section LBR.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma lbr_app_notin : forall p l1 l2, ~ In p (map blk_id l1) -> as_lb_remove H p (l1 ++ l2) = l1 ++ as_lb_remove H p l2.
  Proof.
    intros p l1 l2 NI. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction l1 as [|b l1 IH]; [reflexivity|]. cbn [app map] in *.
    rewrite (L2 p b (l1 ++ l2)) by (intros E; apply NI; left; exact E). rewrite IH by (intros K; apply NI; right; exact K). reflexivity.
  Qed.

  Lemma lbr_head : forall p A n l, ~ In p (map blk_id l) -> as_lb_remove H p ((p, A, n) :: l) = l.
  Proof. intros p A n l NI. pose proof (ah_lb_remove H HH) as (L1 & _). exact (L1 p A n l NI). Qed.

  Lemma lbr_split : forall p A n l1 l2, List.NoDup (map blk_id (l1 ++ (p, A, n) :: l2)) ->
    as_lb_remove H p (l1 ++ (p, A, n) :: l2) = l1 ++ l2.
  Proof.
    intros p A n l1 l2 ND. rewrite map_app in ND. cbn [map blk_id fst] in ND.
    assert (N1 : ~ In p (map blk_id l1)) by (intros K; exact (nodup_app_disj _ _ p p ND K (or_introl eq_refl) eq_refl)).
    apply nodup_app_r in ND. inversion ND as [|? ? N2 _]; subst.
    rewrite (lbr_app_notin p l1 _ N1). rewrite (lbr_head p A n l2 N2). reflexivity.
  Qed.

  Lemma own_grow : forall (LB LB0 LBs TB : list block) (pid pid' : bptr) (b n b' n' : Z),
    List.NoDup (map blk_id LB) -> Permutation LB (LB0 ++ LBs ++ TB) -> In (pid, b, n) LBs ->
    Permutation ((pid', b', n') :: as_lb_remove H pid LB) (LB0 ++ ((pid', b', n') :: as_lb_remove H pid LBs) ++ TB).
  Proof.
    intros LB LB0 LBs TB pid pid' b n b' n' ND P IN.
    apply (Permutation_trans (l' := (pid', b', n') :: LB0 ++ (as_lb_remove H pid LBs ++ TB))); [| apply Permutation_middle].
    apply Permutation_cons; [reflexivity|].
    assert (INL : In (pid, b, n) LB).
    { eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_or_app; right. apply in_or_app; left. exact IN. }
    assert (ND2 : List.NoDup (map blk_id (LB0 ++ LBs ++ TB))) by (eapply Permutation_NoDup; [apply Permutation_map; exact P | exact ND]).
    assert (NDs : List.NoDup (map blk_id LBs)).
    { rewrite !map_app in ND2. apply nodup_app_r in ND2. exact (nodup_app_l _ _ ND2). }
    pose proof (LbB_WoGen.lb_remove_perm H HH pid b n LB ND INL) as P1.
    pose proof (LbB_WoGen.lb_remove_perm H HH pid b n LBs NDs IN) as P2.
    apply (Permutation_cons_inv (a := (pid, b, n))).
    apply (Permutation_trans (l' := LB)); [apply Permutation_sym; exact P1|].
    apply (Permutation_trans (l' := LB0 ++ LBs ++ TB)); [exact P|].
    apply (Permutation_trans (l' := LB0 ++ ((pid, b, n) :: as_lb_remove H pid LBs) ++ TB)).
    - apply Permutation_app_head. apply Permutation_app_tail. exact P2.
    - apply Permutation_sym. apply (Permutation_middle LB0 (as_lb_remove H pid LBs ++ TB) (pid, b, n)).
  Qed.

  Lemma own_grow0 : forall (LB LB0 LBs TB : list block) (pid' : bptr) (b' n' : Z),
    Permutation LB (LB0 ++ LBs ++ TB) -> Permutation ((pid', b', n') :: LB) (LB0 ++ ((pid', b', n') :: LBs) ++ TB).
  Proof.
    intros LB LB0 LBs TB pid' b' n' P.
    apply (Permutation_trans (l' := (pid', b', n') :: LB0 ++ (LBs ++ TB))); [| apply Permutation_middle].
    apply Permutation_cons; [reflexivity | exact P].
  Qed.

  Lemma cblocks_grow : forall (LBs : list block) (PRE POST : list (Z * Z)) (pid pid' : bptr) (b n b' n' : Z),
    List.NoDup (map blk_id LBs) ->
    Permutation (lbl LBs) (PRE ++ (if b =? 0 then [] else [(b, n)]) ++ POST) ->
    (b <> 0 -> In (pid, b, n) LBs) ->
    Permutation (lbl ((pid', b', n') :: (if b =? 0 then LBs else as_lb_remove H pid LBs))) (PRE ++ [(b', n')] ++ POST).
  Proof.
    intros LBs PRE POST pid pid' b n b' n' ND P IN.
    unfold lbl in *. cbn [map fst snd]. fold (lbl LBs) in P.
    apply (Permutation_trans (l' := (b', n') :: PRE ++ POST)); [| apply Permutation_middle]. apply Permutation_cons; [reflexivity|].
    destruct (Z.eqb_spec b 0) as [E|E].
    - cbn [app] in P. fold (lbl LBs). exact P.
    - fold (lbl (as_lb_remove H pid LBs)).
      pose proof (LbB_WoGen.lb_remove_perm H HH pid b n LBs ND (IN E)) as P1.
      apply (Permutation_map (fun bb : block => (snd (fst bb), snd bb))) in P1. change (map _ LBs) with (lbl LBs) in P1.
      cbn [map fst snd] in P1. fold (lbl (as_lb_remove H pid LBs)) in P1.
      apply (@Permutation_cons_app_inv _ (lbl (as_lb_remove H pid LBs)) PRE POST (b, n)).
      etransitivity; [apply Permutation_sym; exact P1|]. cbn [app] in P. exact P.
  Qed.
End LBR.

Lemma cblocks_set_v2 : forall c b' xs' cap',
  c_blocks (set_v2A c (b', xs', cap')) =
    (umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ++ umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
     ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ++ vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c)))
    ++ (if b' =? 0 then [] else [(b', 4 * cap')])
    ++ ((if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]) ++ c_tr c).
Proof. intros c b' xs' cap'. unfold c_blocks, set_v2A. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd]. rewrite <- !app_assoc. reflexivity. Qed.
Lemma cblocks_v2 : forall c,
  c_blocks c =
    (umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ++ umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
     ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ++ vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c)))
    ++ (if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))])
    ++ ((if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]) ++ c_tr c).
Proof. intros c. unfold c_blocks. rewrite <- !app_assoc. reflexivity. Qed.

Lemma cblocks_set_v3 : forall c b' xs' cap',
  c_blocks (set_v3A c (b', xs', cap')) =
    (umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ++ umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
     ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ++ vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))
     ++ (if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))]))
    ++ (if b' =? 0 then [] else [(b', 4 * cap')])
    ++ c_tr c.
Proof. intros c b' xs' cap'. unfold c_blocks, set_v3A. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd]. rewrite <- !app_assoc. reflexivity. Qed.
Lemma cblocks_v3 : forall c,
  c_blocks c =
    (umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ++ umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
     ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ++ vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))
     ++ (if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))]))
    ++ (if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))])
    ++ c_tr c.
Proof. intros c. unfold c_blocks. rewrite <- !app_assoc. reflexivity. Qed.

Lemma cblocks_set_v1 : forall c b' n' cap',
  c_blocks (set_v1A c (b', n', cap')) =
    (umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ++ umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
     ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)))
    ++ vec_opnd_blocks b' cap'
    ++ ((if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))])
        ++ (if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]) ++ c_tr c).
Proof. intros c b' n' cap'. unfold c_blocks, set_v1A. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd]. rewrite <- !app_assoc. reflexivity. Qed.
Lemma cblocks_v1 : forall c,
  c_blocks c =
    (umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ++ umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
     ++ umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)))
    ++ vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))
    ++ ((if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))])
        ++ (if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]) ++ c_tr c).
Proof. intros c. unfold c_blocks. rewrite <- !app_assoc. reflexivity. Qed.

Lemma phi_grow_v2 : forall c b' xs' cap, t3c (c_v2 c) = cap -> 0 <= cap -> (t3a (c_v2 c) = 0 -> cap = 0) -> b' <> 0 ->
  pm_phi (set_v2A c (b', xs', vgrow cap)) >= pm_phi c + ICM (4 * vgrow cap).
Proof.
  intros c b' xs' cap Hc Hcap Hb Hb'. apply pm_phi_ge_blocks; [reflexivity|]. rewrite cblocks_set_v2, (cblocks_v2 c).
  replace (b' =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb'). rewrite <- Hc.
  apply (phi_grow 4 (t3c (c_v2 c)) (t3a (c_v2 c)) b'); [lia | lia | rewrite Hc; exact Hb].
Qed.
Lemma phi_grow_v3 : forall c b' xs' cap, t3c (c_v3 c) = cap -> 0 <= cap -> (t3a (c_v3 c) = 0 -> cap = 0) -> b' <> 0 ->
  pm_phi (set_v3A c (b', xs', vgrow cap)) >= pm_phi c + ICM (4 * vgrow cap).
Proof.
  intros c b' xs' cap Hc Hcap Hb Hb'. apply pm_phi_ge_blocks; [reflexivity|]. rewrite cblocks_set_v3, (cblocks_v3 c).
  replace (b' =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb'). rewrite <- Hc.
  apply (phi_grow 4 (t3c (c_v3 c)) (t3a (c_v3 c)) b'); [lia | lia | rewrite Hc; exact Hb].
Qed.
Lemma phi_grow_v1 : forall c b' n' cap, t3c (c_v1 c) = cap -> 0 <= cap -> (t3a (c_v1 c) = 0 -> cap = 0) -> b' <> 0 ->
  pm_phi (set_v1A c (b', n', vgrow cap)) >= pm_phi c + ICM (OPND_SZ * vgrow cap).
Proof.
  intros c b' n' cap Hc Hcap Hb Hb'. apply pm_phi_ge_blocks; [reflexivity|]. rewrite cblocks_set_v1, (cblocks_v1 c). unfold vec_opnd_blocks.
  replace (b' =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb'). rewrite <- Hc.
  apply (phi_grow OPND_SZ (t3c (c_v1 c)) (t3a (c_v1 c)) b'); [lia | unfold OPND_SZ; lia | rewrite Hc; exact Hb].
Qed.

Lemma pm_phi_blocks_one : forall b n, pm_phi_blocks [(b, n)] = lg n.
Proof. intros b n. rewrite pm_phi_blocks_cons. cbn [snd]. change (pm_phi_blocks []) with 0. unfold lg, ICM_LARGE. destruct (64512 <? n); lia. Qed.
Lemma phi_set_v3_eq : forall c b' xs' cap', (t3a (c_v3 c) = 0 -> t3c (c_v3 c) = 0) -> b' <> 0 ->
  pm_phi (set_v3A c (b', xs', cap')) = pm_phi c + closs (t3c (c_v3 c)) cap'.
Proof.
  intros c b' xs' cap' Hb Hb'. apply pm_phi_eq_blocks; [reflexivity|]. unfold closs. rewrite cblocks_set_v3, (cblocks_v3 c).
  replace (b' =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb').
  rewrite !pm_phi_blocks_app, pm_phi_blocks_one.
  destruct (Z.eqb_spec (t3a (c_v3 c)) 0) as [E|E].
  - rewrite (Hb E). change (pm_phi_blocks []) with 0. replace (lg (4 * 0)) with 0 by reflexivity. lia.
  - rewrite pm_phi_blocks_one. lia.
Qed.

Section PW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma pw_sh_add : forall a n, a mod 8 = 0 -> n mod 8 = 0 -> sh a + nsh n = sh (a + n).
  Proof. intros a n Ha Hn. unfold sh, nsh. Z.div_mod_to_equations. lia. Qed.

  Lemma pwin_aclient : forall (w : pmwA H) LB SP a n, pmw_okA H w ->
    wa_p w <= a -> a + n <= wa_p w + PARSER_SIZE -> 0 <= n -> a mod 8 = 0 -> n mod 8 = 0 ->
    aclient_range H LB SP a n /\ aclient_range H LB SP (sh a) (nsh n).
  Proof.
    intros w LB SP a n OK H1 H2 Hn Ha8 Hn8.
    destruct (p_frame H HH w OK) as (f & Hf & P1 & P2 & P3 & P4).
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    unfold AFS_HDR in *. split.
    - right; right; right; right; left. lia.
    - right; right; right; right; right; left. split.
      + apply sh_mono. lia.
      + rewrite (pw_sh_add a n Ha8 Hn8). apply sh_mono. lia.
  Qed.

  Lemma pwin_write : forall (w : pmwA H) LB a n, pmw_okA H w ->
    wa_p w <= a -> a + n <= wa_p w + PARSER_SIZE -> 0 <= n ->
    aclient_write_ok H LB (a, a + n) /\ afs_write_ok H (PMLF H w) (a, a + n) /\ aconst_ok (a, a + n).
  Proof.
    intros w LB a n OK H1 H2 Hn.
    destruct (p_frame H HH w OK) as (f & Hf & P1 & P2 & P3 & P4).
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). unfold AFS_HDR in *.
    split; [| split].
    - right; right; right; right; left. cbn [fst snd]. lia.
    - right. exists f. split; [right; exact Hf|]. cbn [fst snd]. lia.
    - pose proof (wk_papp H w OK) as ([(Q1 & Q2)|(Q1 & Q2)] & _ & _).
      + apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
          AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
          replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity;
          unfold AIMG_TOP, ALOWSH_LO, PARSER_SIZE in *; lia.
      + apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
          AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
          replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity;
          unfold AHI_LO, PARSER_SIZE in *; lia.
  Qed.

  Lemma pwin_band : forall (w : pmwA H) a n, pmw_okA H w ->
    wa_p w <= a -> a + n <= wa_p w + PARSER_SIZE -> 0 <= n ->
    ((0x6e8000 <= a /\ a + n <= 0x7fff7000) \/ (0x10007fff8000 <= a /\ a + n <= 2 ^ 47)) /\ a + n <= wa_lo w.
  Proof.
    intros w a n OK H1 H2 Hn. pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (p_range H w OK) as [PR1 PR2].
    split; [| lia].
    pose proof (wk_papp H w OK) as ([(Q1 & Q2)|(Q1 & Q2)] & _ & _).
    - left. unfold AIMG_TOP, ALOWSH_LO in *. lia.
    - right. unfold AHI_LO in *. lia.
  Qed.

  Lemma pwin_obj : forall (w : pmwA H) LB ho, pmw_okA H w ->
    0 <= ho -> ho + 24 <= PARSER_SIZE -> ho mod 8 = 0 ->
    obj_win H LB (PMLF H w) (wa_s1 w) (wa_lo w) (wa_p w + ho) 24.
  Proof.
    intros w LB ho OK H0 H1 H8. pose proof (wk_papp H w OK) as (_ & _ & P16).
    assert (A8 : (wa_p w + ho) mod 8 = 0) by (clear - P16 H8; Z.div_mod_to_equations; lia).
    destruct (pwin_aclient w LB (wa_s1 w) (wa_p w + ho) 24 OK ltac:(lia) ltac:(lia) ltac:(lia) A8 eq_refl) as [A1 A2].
    destruct (pwin_write w LB (wa_p w + ho) 24 OK ltac:(lia) ltac:(lia) ltac:(lia)) as (A3 & A4 & A5).
    destruct (pwin_band w (wa_p w + ho) 24 OK ltac:(lia) ltac:(lia) ltac:(lia)) as [_ A6].
    unfold obj_win. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. left. exact A6.
  Qed.

  Lemma wr_at_of_mdef : forall m a n k l, mdef m a n -> 0 <= a -> a + n <= 2 ^ 64 -> 0 <= k -> 0 <= l -> k + l <= n -> wr_at asegs m (a + k) l.
  Proof.
    intros m a n k l D Ha Han Hk Hl Hkl. split; [lia|]. split; [lia|]. intros i Hi. unfold wview, wa.
    replace (a + k + i) with (a + (k + i)) by lia. pose proof (D (k + i) ltac:(lia)) as Di.
    destruct (m (Z_to_bv 64 (a + (k + i)))); [discriminate | contradiction].
  Qed.

  Lemma pw_addr_sub8 : forall m A n o k, addressable m A n -> n mod 8 = 0 -> o mod 8 = 0 -> k mod 8 = 0 ->
    0 <= o -> 0 <= k -> o + k <= n -> addressable m (A + o) k.
  Proof.
    intros m A n o k AD Hn Ho Hk H1 H2 H3.
    destruct (addressable_split8 m A n o AD Hn Ho ltac:(lia)) as [_ AD2].
    destruct (addressable_split8 m (A + o) (n - o) k AD2 ltac:(rewrite Zminus_mod, Hn, Ho; reflexivity) Hk ltac:(lia)) as [AD3 _]. exact AD3.
  Qed.

  Variable LINV : mem -> Prop.

  Lemma ff_src4_keep : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal so x,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    obj_sh_ok ins so 4 = true -> 24 <= so -> so + 4 <= 16376 ->
    rw_cells asegs m (wa_ff w + so) [C4 (Z_to_bv 64 x)] -> 0 <= x < 2 ^ 32 ->
    src4_keep H LB (wa_s1 w) m (wa_ff w + so) x.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal so x OK X Hok Hso1 Hso2 RW Hx m' AC' MI' AP.
    pose proof (pmw_frame_facts H w OK) as (E1 & E2 & E3 & _). change (fsz PM_FCLASS) with 16384 in *.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). unfold AIMG_TOP, AFS_HDR in E1.
    pose proof (xpres_of_apres H LB (wa_s1 w) [] m m' AP) as XP.
    assert (XRf : forall k n, 0 <= k -> 0 <= n -> k + n <= 16384 -> xclient_range H LB (wa_s1 w) [] (wa_ff w + k) n).
    { intros k n Hk Hn Hkn. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia | apply Forall_nil]. }
    assert (XRfsh : xclient_range H LB (wa_s1 w) [] (sh (wa_ff w)) PM_NSH).
    { apply (xr_fssh H w); [exact OK | apply sh_mono; unfold AFS_HDR in *; lia | | apply Forall_nil].
      assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
      assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia).
      unfold PM_NSH. lia. }
    pose proof (xpres_SHAD H LB (wa_s1 w) [] m m' (wa_ff w) (pm_fsh ins) XP (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
                  ltac:(unfold pm_fsh; rewrite length_map, pm_fsh_len; exact XRfsh)) as FSH'.
    split.
    - pose proof (xpres_rw_cells H LB (wa_s1 w) [] m m' (wa_ff w + so) _ XP RW ltac:(cbn [cells_size csize Nat.add]; apply XRf; lia)) as RW'.
      pose proof (fld_of_cell4 m' (wa_ff w + so) (Z_to_bv 64 x) RW' ltac:(lia)) as FL4. rewrite HLib.u64_of_Z in FL4 by lia. exact FL4.
    - apply (addressable_accessible m' (wa_ff w + so) 4 (wa_ff w + so) 4); [| lia | lia | unfold AAPP_HI in *; lia].
      exact (ff_addressable m' (wa_ff w) ins so 4 FSH' Hok).
  Qed.

  Lemma blksh_apart_ff : forall (w : pmwA H) s LB m (pid : bptr) b n, pmw_okA H w -> as_RHEAP H s LB m -> In (pid, b, n) LB ->
    (wa_ff w + 16384 <= sh b \/ sh b + nsh n <= wa_ff w) /\ (sh (wa_ff w) + PM_NSH <= sh b \/ sh b + nsh n <= sh (wa_ff w)).
  Proof.
    intros w s LB m pid b n OK RH INb. pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (blk_apart_ff H HH w s LB m _ OK RH INb) as AP. cbn [blk_addr blk_size fst snd] in AP.
    pose proof (ah_blocks H HH _ _ _ _ RH INb) as (R0 & R16 & Rn & RI & RC & RFb & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RFb, RAPP.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof (pmw_frame_facts H w OK) as (_ & _ & E3 & _).
    split.
    - destruct RAPP as [(L1 & L2)|(L1 & L2)]; destruct FA as [(N1 & N2)|(N1 & N2)]; unfold aapp_lo, aapp_hi in *.
      + left. unfold sh, ASHADOW_BASE, ALOWSH_LO, AIMG_TOP in *. Z.div_mod_to_equations. lia.
      + right. assert (sh (b + n) <= sh ALOWSH_LO) by (apply sh_mono; lia).
        assert (sh b + nsh n <= sh (b + n) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
        replace (sh ALOWSH_LO) with 0x8fff6e00 in * by reflexivity. unfold AHI_LO in *. lia.
      + left. assert (sh AHI_LO <= sh b) by (apply sh_mono; lia).
        replace (sh AHI_LO) with 0x2008fff7000 in * by reflexivity. unfold ALOWSH_LO in *. lia.
      + right. assert (sh b + nsh n <= sh (b + n) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
        assert (sh (b + n) <= sh aceil) by (apply sh_mono; lia).
        assert (sh aceil + 1 <= AHI_LO) by (unfold sh, ASHADOW_BASE, AHI_LO; Z.div_mod_to_equations; lia). lia.
    - destruct AP as [AP|AP].
      + right. unfold sh, nsh. Z.div_mod_to_equations. lia.
      + left. unfold sh, PM_NSH. Z.div_mod_to_equations. lia.
  Qed.

  Lemma ff_src4_keep_x : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal so x X,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    obj_sh_ok ins so 4 = true -> 24 <= so -> so + 4 <= 16376 ->
    rw_cells asegs m (wa_ff w + so) [C4 (Z_to_bv 64 x)] -> 0 <= x < 2 ^ 32 ->
    Forall (fun iv : Z * Z => exists (pid : bptr) b n, In (pid, b, n) LB /\ fst iv = sh b /\ snd iv = sh b + nsh n) X ->
    src4_keep_x H LB (wa_s1 w) X m (wa_ff w + so) x.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal so x X OK XA Hok Hso1 Hso2 RW Hx FX m' AC' MI' XP.
    pose proof (pmw_frame_facts H w OK) as (E1 & E2 & E3 & _). change (fsz PM_FCLASS) with 16384 in *.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). unfold AIMG_TOP, AFS_HDR in E1.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA) as RH.
    assert (AX1 : forall k n, 0 <= k -> 0 <= n -> k + n <= 16384 -> Forall (fun iv : Z * Z => wa_ff w + k + n <= fst iv \/ snd iv <= wa_ff w + k) X).
    { intros k n Hk Hn Hkn. eapply Forall_impl; [| exact FX]. intros iv (pid & b & nb & INb & -> & ->).
      pose proof (proj1 (blksh_apart_ff w s LB m pid b nb OK RH INb)). lia. }
    assert (AX2 : Forall (fun iv : Z * Z => sh (wa_ff w) + PM_NSH <= fst iv \/ snd iv <= sh (wa_ff w)) X).
    { eapply Forall_impl; [| exact FX]. intros iv (pid & b & nb & INb & -> & ->). exact (proj2 (blksh_apart_ff w s LB m pid b nb OK RH INb)). }
    assert (XRf : forall k n, 0 <= k -> 0 <= n -> k + n <= 16384 -> xclient_range H LB (wa_s1 w) X (wa_ff w + k) n).
    { intros k n Hk Hn Hkn. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia | exact (AX1 k n Hk Hn Hkn)]. }
    assert (XRfsh : xclient_range H LB (wa_s1 w) X (sh (wa_ff w)) PM_NSH).
    { apply (xr_fssh H w); [exact OK | apply sh_mono; unfold AFS_HDR in *; lia | | exact AX2].
      assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
      assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia).
      unfold PM_NSH. lia. }
    pose proof (xpres_SHAD H LB (wa_s1 w) X m m' (wa_ff w) (pm_fsh ins) XP (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA)
                  ltac:(unfold pm_fsh; rewrite length_map, pm_fsh_len; exact XRfsh)) as FSH'.
    split.
    - pose proof (xpres_rw_cells H LB (wa_s1 w) X m m' (wa_ff w + so) _ XP RW ltac:(cbn [cells_size csize Nat.add]; apply XRf; lia)) as RW'.
      pose proof (fld_of_cell4 m' (wa_ff w + so) (Z_to_bv 64 x) RW' ltac:(lia)) as FL4. rewrite HLib.u64_of_Z in FL4 by lia. exact FL4.
    - apply (addressable_accessible m' (wa_ff w + so) 4 (wa_ff w + so) 4); [| lia | lia | unfold AAPP_HI in *; lia].
      exact (ff_addressable m' (wa_ff w) ins so 4 FSH' Hok).
  Qed.

  Lemma ff_srcb_keep : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal so cs,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    obj_sh_ok ins so (Z.of_nat (cells_size cs)) = true -> 24 <= so -> so + Z.of_nat (cells_size cs) <= 11584 ->
    rw_cells asegs m (wa_ff w + so) cs ->
    srcb_keep H LB (wa_s1 w) m (wa_ff w + so) (cells_bytes cs).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal so cs OK X Hok Hso1 Hso2 RW m' AC' MI' AP.
    pose proof (pmw_frame_facts H w OK) as (E1 & E2 & E3 & _). change (fsz PM_FCLASS) with 16384 in *.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). unfold AIMG_TOP, AFS_HDR in E1.
    pose proof (xpres_of_apres H LB (wa_s1 w) [] m m' AP) as XP.
    assert (XRf : forall k n, 0 <= k -> 0 <= n -> k + n <= 16384 -> xclient_range H LB (wa_s1 w) [] (wa_ff w + k) n).
    { intros k n Hk Hn Hkn. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia | apply Forall_nil]. }
    assert (XRfsh : xclient_range H LB (wa_s1 w) [] (sh (wa_ff w)) PM_NSH).
    { apply (xr_fssh H w); [exact OK | apply sh_mono; unfold AFS_HDR in *; lia | | apply Forall_nil].
      assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
      assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia).
      unfold PM_NSH. lia. }
    pose proof (xpres_SHAD H LB (wa_s1 w) [] m m' (wa_ff w) (pm_fsh ins) XP (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
                  ltac:(unfold pm_fsh; rewrite length_map, pm_fsh_len; exact XRfsh)) as FSH'.
    pose proof (xpres_rw_cells H LB (wa_s1 w) [] m m' (wa_ff w + so) _ XP RW ltac:(apply XRf; lia)) as RW'.
    pose proof RW' as [[Hwf HB] _]. rewrite (cells_bytes_length cs Hwf).
    split; [exact HB|]. split.
    - apply (addressable_accessible m' (wa_ff w + so) (Z.of_nat (cells_size cs)) (wa_ff w + so) (Z.of_nat (cells_size cs))); [| lia | lia | unfold AAPP_HI in *; lia].
      exact (ff_addressable m' (wa_ff w) ins so _ FSH' Hok).
    - apply (ff_shvis m' (wa_ff w) ins so (Z.of_nat (cells_size cs)) FSH'); unfold AAPP_HI in *; lia.
  Qed.

  Lemma ff_obj_keep : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal so cs X XS m',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    obj_sh_ok ins so (Z.of_nat (cells_size cs)) = true -> 24 <= so -> so + Z.of_nat (cells_size cs) <= 11584 ->
    rw_cells asegs m (wa_ff w + so) cs ->
    Forall (fun iv : Z * Z => (wa_ff w + 16384 <= fst iv \/ snd iv <= wa_ff w) /\ (sh (wa_ff w) + PM_NSH <= fst iv \/ snd iv <= sh (wa_ff w))) X ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LB (wa_s1 w) (X ++ XS) m m' ->
    rw_cells asegs m' (wa_ff w + so) cs /\ accessible m' (wa_ff w + so) (Z.of_nat (cells_size cs))
    /\ shvis m' (wa_ff w + so) (wa_ff w + so + Z.of_nat (cells_size cs)) /\ SHAD m' (wa_ff w) (pm_fsh ins).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal so cs X XS m' OK XA Hok Hso1 Hso2 RW FX FXS XP.
    pose proof (pmw_frame_facts H w OK) as (E1 & E2 & E3 & _). change (fsz PM_FCLASS) with 16384 in *.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). unfold AIMG_TOP, AFS_HDR in E1.
    assert (FOf : fsobj H (PMLF H w) (wa_ff w) 16384)
      by (right; exists (PM_FCLASS, wa_ff w, wa_fp w); split; [left; reflexivity | unfold ff_addr, ff_class; cbn [fst snd]; change (fsz PM_FCLASS) with 16384; lia]).
    pose proof (xp_scr_obj H HH w m XS (wa_ff w) 16384 OK (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA) FXS FOf ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) FA) as [SXf SXfs].
    assert (XRf : forall k n, 0 <= k -> 0 <= n -> k + n <= 16384 -> xclient_range H LB (wa_s1 w) (X ++ XS) (wa_ff w + k) n).
    { intros k n Hk Hn Hkn. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |]. apply Forall_app. split.
      - eapply Forall_impl; [| exact FX]. intros iv [Hiv _]. cbn beta. lia.
      - eapply Forall_impl; [| exact SXf]. intros iv Hiv. cbn beta in *. lia. }
    assert (XRfsh : xclient_range H LB (wa_s1 w) (X ++ XS) (sh (wa_ff w)) PM_NSH).
    { apply (xr_fssh H w); [exact OK | apply sh_mono; unfold AFS_HDR in *; lia | |].
      - assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
        assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia). unfold PM_NSH. lia.
      - apply Forall_app. split.
        + eapply Forall_impl; [| exact FX]. intros iv [_ Hiv]. exact Hiv.
        + eapply Forall_impl; [| exact SXfs]. intros iv Hiv. cbn beta in *. unfold PM_NSH, nsh in *. change ((16384 + 7) / 8) with 2048 in Hiv. lia. }
    pose proof (xpres_SHAD H LB (wa_s1 w) (X ++ XS) m m' (wa_ff w) (pm_fsh ins) XP (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA)
                  ltac:(unfold pm_fsh; rewrite length_map, pm_fsh_len; exact XRfsh)) as FSH'.
    pose proof (xpres_rw_cells H LB (wa_s1 w) (X ++ XS) m m' (wa_ff w + so) _ XP RW ltac:(apply XRf; lia)) as RW'.
    split; [exact RW'|]. split; [| split; [| exact FSH']].
    - apply (addressable_accessible m' (wa_ff w + so) (Z.of_nat (cells_size cs)) (wa_ff w + so) (Z.of_nat (cells_size cs))); [| lia | lia | unfold AAPP_HI in *; lia].
      exact (ff_addressable m' (wa_ff w) ins so _ FSH' Hok).
    - apply (ff_shvis m' (wa_ff w) ins so (Z.of_nat (cells_size cs)) FSH'); unfold AAPP_HI in *; lia.
  Qed.
End PW.
