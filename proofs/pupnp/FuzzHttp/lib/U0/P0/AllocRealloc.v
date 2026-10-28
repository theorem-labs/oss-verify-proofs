(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame ITree Nodes Decode Tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KStepK KStepC.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocHINV MallocFacts_A Malloc_iface MallocTree MallocFacts_inv2 F_malloc_entry.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import AllocLink. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import AllocInst F_memcpy RF_realloc_A RF_realloc_D RF_realloc_ip RF_realloc_spec.

Import ListNotations.
Import ITree.Exc.

Local Ltac arith_atom T := lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq N _ _ => idtac | @eq positive _ _ => idtac
  | le _ _ => idtac | lt _ _ => idtac | ge _ _ => idtac | gt _ _ => idtac | N.le _ _ => idtac | N.lt _ _ => idtac
  | True => idtac | False => idtac end.
Local Ltac arith_prop T := lazymatch T with
  | ?A \/ ?B => arith_prop A; arith_prop B | ?A /\ ?B => arith_prop A; arith_prop B | not ?A => arith_prop A
  | ?A <-> ?B => arith_prop A; arith_prop B | ?A -> ?B => arith_prop A; arith_prop B | _ => arith_atom T end.
Local Ltac arith_goal := lazymatch goal with |- ?G => arith_prop G end.
Local Ltac clear_props := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => clear H end end.

Local Open Scope Z_scope.

Lemma heap_pres_weaken {HGW : HasGuard} {HCEIL : HasCeiling} : forall (LB LB' : list block) SP SP' m m',
  heap_pres AI_P0 LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> heap_pres AI_P0 LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma heap_pres_bytes_at {HGW : HasGuard} {HCEIL : HasCeiling} : forall (LB : list block) SP m m' A bs,
  heap_pres AI_P0 LB SP m m' -> bytes_at rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> client_addr AI_P0 LB SP a) ->
  bytes_at rsegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma heap_pres_rw_cells {HGW : HasGuard} {HCEIL : HasCeiling} : forall (LB : list block) SP m m' A cs,
  heap_pres AI_P0 LB SP m m' -> rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> client_addr AI_P0 LB SP a) ->
  rw_cells rsegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] (W0 & W1 & HW)] HR. split; [split; [exact Hwf|]|].
  - eapply heap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.

Lemma heap_pres_of_munch {HGW : HasGuard} {HCEIL : HasCeiling} : forall (LB : list block) SP m m' W,
  munch W m m' -> wmono rsegs m m' -> (forall a, 0 <= a < 2^64 -> client_addr AI_P0 LB SP a -> outside W a) ->
  heap_pres AI_P0 LB SP m m'.
Proof.
  intros LB SP m m' W MU WM HO a Ha Hc. split.
  - apply MU. rewrite wa_unsigned by lia. apply HO; assumption.
  - intros Hw. apply WM. exact Hw.
Qed.

Lemma rw_cells_CB_merge m A n1 n2 bs1 bs2 :
  rw_cells rsegs m A [CB n1 bs1; CB n2 bs2] -> rw_cells rsegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite !app_nil_r, app_length, !Nat.add_0_r.
  intros [[W B] R]. split; [split; [| exact B]| exact R]. cbn in W |- *. split; [lia| exact I].
Qed.

Lemma rw_cells_CB_split m A n1 n2 bs1 bs2 :
  rw_cells rsegs m A [CB (n1 + n2) (bs1 ++ bs2)] -> length bs1 = n1 -> rw_cells rsegs m A [CB n1 bs1; CB n2 bs2].
Proof.
  unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite !app_nil_r, app_length, !Nat.add_0_r.
  intros [[W B] R] L. split; [split; [| exact B]| exact R]. cbn in W |- *. repeat split; lia.
Qed.

Lemma rw_cells_CB2_split m A n1 n2 bs1 bs2 :
  rw_cells rsegs m A [CB n1 bs1; CB n2 bs2] -> rw_cells rsegs m A [CB n1 bs1] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 bs2].
Proof.
  unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize]. rewrite !app_nil_r, !Nat.add_0_r.
  intros [[(L1 & L2 & _) B] W]. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite L1 in B2.
  pose proof W as (W0 & W1 & _).
  split; (split; [split; [cbn; LiaTuning.ctauto| assumption]|]); eapply (F_malloc_free.wr_at_sub rsegs m A _ _ _ W); lia.
Qed.

Lemma rw_cells_CB2_join m A n1 n2 bs1 bs2 :
  rw_cells rsegs m A [CB n1 bs1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 bs2] -> rw_cells rsegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize]. rewrite !app_nil_r, !Nat.add_0_r.
  intros [[[L1 _] B1] (W0 & W1 & W)] [[[L2 _] B2] (V0 & V1 & V)]. split; [split; [cbn; rewrite app_length; split; [lia| exact I]|]|].
  - apply bytes_at_app. split; [exact B1|]. rewrite L1. exact B2.
  - split; [exact W0|]. split; [lia|]. intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat n1)); [apply W; lia|].
    replace (A + i) with (A + Z.of_nat n1 + (i - Z.of_nat n1)) by lia. apply V. lia.
Qed.

Lemma P0_malloc_sreach {HGW : HasGuard} {HCEIL : HasCeiling} : forall pc, rmalloc_stmt_at pc ->
  forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m -> rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells rsegs m RERRNO [C4 errv] -> mem_inv rsegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  SREACH AI_P0 (malloc_post AI_P0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB n lo B m)
    (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)) s LB.
Proof.
  intros pc SPEC ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
         HR HE HB ST CLO LOLE ERR MI Ha0 Hn.
  intros mo HL. cbn [LINK AI_P0] in HL.
  assert (ERR' : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 RATP) + -164) [C4 errv]) by (rewrite errno_addr_RATP; exact ERR).
  pose proof (SPEC ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m s LB n lo B errv HR HE HB ST ltac:(idtac; exact CLO) LOLE ERR' MI eq_refl Ha0 Hn) as IMPL.
  pose proof (raw_malloc_spec_c (map blk_id LB) G0 n frame_ok_G0 ltac:(lia)) as MSP.
  pose proof HL as [(L & _ & HK & _) _].
  pose proof (implM_mspec_safe_reach rsegs (raw_malloc n) s _ mo _ _ _ IMPL MSP HL (raw_malloc_mm n s) (kl_halt _ _ _ HK) (kl_minv _ _ _ HK)) as SR.
  eapply sr_mono; [exact SR|]. intros [ms' mo'] (r & s' & HQm & HQs & HF & HM). cbn [cfg_ms cfg_model] in HQm, HQs, HF, HM.
  unfold rmalloc_post in HQm.
  destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & -> & MI' & ST' & ERR2 & AUX' & HP' & KFA & KSO & RES).
  unfold linked. cbn [cfg_ms cfg_model LINK AI_P0 ai_keep ai_mrel].
  assert (FRAME : alloc_frame AI_P0 sp lo B m m' LB).
  { split; [exact MI'|]. split; [exact ST'|]. split; [exact AUX'|]. split; [exists errv'; cbn [ai_L AI_P0 P0L al_errno]; rewrite <- errno_addr_RATP; exact ERR2|].
    apply heap_pres_of_rheap_pres. exact HP'. }
  destruct r as [p|].
  - destruct RES as (A & junk & -> & BR & HR' & CELLS & _). destruct HQs as [OWN' _].
    exists s', ((p, A, n) :: LB). split; [exact OWN'|]. split; [split; assumption|]. split; [exact HM|].
    unfold malloc_post. do 15 eexists. exists m'. split; [reflexivity|]. split; [exact FRAME|].
    right. exists p, A, junk. split; [reflexivity|]. split; [reflexivity|]. split; [|split; [exact HR'| exact CELLS]].
    destruct BR as (B1 & B2 & B3 & B4 & B5 & B6). unfold block_range. cbn [ai_L AI_P0 P0L al_img].
    ceil_facts. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    split; [first [exact B4 | unfold alloc_ceiling; cbn; lia]|].
    constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
  - destruct RES as [-> HR']. exists s', LB. split; [exact HQs|]. split; [split; assumption|]. split; [exact HM|].
    unfold malloc_post. do 15 eexists. exists m'. split; [reflexivity|]. split; [exact FRAME|].
    left. auto.
Qed.

Lemma P0_free_sreach {HGW : HasGuard} {HCEIL : HasCeiling} : forall pc, rfree_stmt_at pc ->
  forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (k : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (k, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells rsegs m RERRNO [C4 errv] -> mem_inv rsegs m ->
  a0 = Z_to_bv 64 A ->
  SREACH AI_P0 (free_post AI_P0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (lb_remove k LB) lo B m)
    (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)) s LB.
Proof.
  intros pc SPEC ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB k A n lo B errv
         HR HIN HE HB ST CLO LOLE ERR MI Ha0.
  intros mo HL. cbn [LINK AI_P0] in HL.
  assert (ERR' : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 RATP) + -164) [C4 errv]) by (rewrite errno_addr_RATP; exact ERR).
  pose proof (SPEC ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m s LB k A n lo B errv HR HIN HE HB ST ltac:(idtac; exact CLO) LOLE ERR' MI eq_refl Ha0) as IMPL.
  pose proof (raw_free_spec_c (map blk_id (lb_remove k LB)) G0 k frame_ok_G0) as MSP.
  pose proof HL as [(L & _ & HK & _) _].
  assert (HL' : OWN (k :: map blk_id (lb_remove k LB)) G0 s mo).
  { eapply OWN_perm; [| exact HL]. eapply lb_remove_perm; [exact (RHEAP_blocks_nodup_proof _ _ _ HR)| exact HIN]. }
  pose proof (implM_mspec_safe_reach rsegs (raw_free k) s _ mo _ _ _ IMPL MSP HL' (raw_free_mm k s) (kl_halt _ _ _ HK) (kl_minv _ _ _ HK)) as SR.
  eapply sr_mono; [exact SR|]. intros [ms' mo'] (r & s' & HQm & HQs & HF & HM). cbn [cfg_ms cfg_model] in HQm, HQs, HF, HM.
  unfold rfree_post in HQm.
  destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & -> & MI' & ST' & ERR2 & AUX' & HP' & KFA & KSO & HR').
  unfold linked. cbn [cfg_ms cfg_model LINK AI_P0 ai_keep ai_mrel].
  exists s', (lb_remove k LB). split; [exact HQs|]. split; [split; assumption|]. split; [exact HM|].
  unfold free_post. do 15 eexists. exists m'. split; [reflexivity|].
  split; [| split; [reflexivity| exact HR']].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact AUX'|]. split; [exists errv; cbn [ai_L AI_P0 P0L al_errno]; rewrite <- errno_addr_RATP; exact ERR2|].
  apply heap_pres_of_rheap_pres. exact HP'.
Qed.

Lemma lb_remove_cons_other : forall (LB : list block) k k' A n,
  k' <> k -> lb_remove k ((k', A, n) :: LB) = (k', A, n) :: lb_remove k LB.
Proof.
  intros LB k k' A n NE. unfold lb_remove. rewrite filter_cons. destruct (decide _) as [D|D]; [reflexivity|].
  exfalso. apply D. cbn [blk_id fst]. destruct (bptr_eqb k' k) eqn:E; [| exact I]. apply bptr_eqb_eq in E. exact (NE E).
Qed.

Lemma lb_remove_sub : forall (LB : list block) k b, In b (lb_remove k LB) -> In b LB.
Proof.
  induction LB as [|b0 LB IH]; intros k b H; [exact H|]. unfold lb_remove in *. rewrite filter_cons in H.
  destruct (decide _); [destruct H as [->|H]; [left; reflexivity| right; eapply IH; exact H]| right; eapply IH; exact H].
Qed.

Theorem P0_realloc_contract_basic {HGW : HasGuard} {HCEIL : HasCeiling} :
  forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (k : bptr) (A sz n lo B : Z)
         (old : list byte) (errv : word),
  RHEAP s LB m -> In (k, A, sz) LB ->
  rw_cells rsegs m A [CB (Z.to_nat sz) old] ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells rsegs m RERRNO [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  n < MMAP_THRESHOLD ->
  SREACH AI_P0 (realloc_post AI_P0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB k A sz n lo B old m)
    (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1995c) fc None m (seg_rom rsegs)) s LB.
Proof.
  intros until errv. intros HR HIN CELLS HE HB ST CLO LOLE ERR MI Ha0 Ha1 Hn NT.
  cbn [ai_L AI_P0 P0L al_realloc_pc al_tp al_stack al_errno RHEAP RENV LINK ai_PS ai_K ai_K_eqb ai_keep ai_mrel] in *.
  pose proof CLO as CLO'. idtac.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HR) as ND.
  eapply sreach_evt.
  { eapply (rrealloc_walk_spec ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB k A sz n lo old
              HR HIN CELLS ST CLO' ltac:(lia) MI Ha0 Ha1 ltac:(lia)). }
  intros ms' [IP|GEN].
  -
    destruct IP as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & junk & -> & MI' & ST' & AUX & ERRP & HP' & HR' & BR & CELLS').
    intros mo HL. apply sr_done. unfold linked. cbn [cfg_ms cfg_model LINK AI_P0 ai_keep ai_mrel].
    exists s, ((k, A, n) :: lb_remove k LB). split; [| split; [apply P0_keep_refl| split; [apply P0_mrel_refl|]]].
    { cbn [LINK AI_P0] in HL. unfold P0_LINK in *. cbn [map blk_id fst]. eapply OWN_perm; [| exact HL]. eapply lb_remove_perm; [exact ND| exact HIN]. }
    unfold realloc_post. do 15 eexists. exists m'. split; [reflexivity|].
    right. exists k, A, junk. split; [reflexivity|]. split; [reflexivity|]. split; [| split; [| split; [exact HR'| exact CELLS']]].
    + destruct BR as (B1 & B2 & B3 & B4 & B5 & B6). unfold block_range. cbn [ai_L AI_P0 P0L al_img].
      ceil_facts. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
      split; [first [exact B4 | unfold alloc_ceiling; cbn; lia]|].
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    + split; [exact MI'|]. split; [exact ST'|]. split; [exact (AUX B HE HB)|]. split; [exists errv; exact (ERRP errv ERR)|].
      apply heap_pres_of_rheap_pres. exact HP'.
  -
    destruct GEN as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & -> & FR1 & ST1 & MU1 & WM1 & MI1).
    pose proof (P0_block_range _ _ _ _ HR HIN) as (A1' & _ & SZ0 & ATOP & AIMG). cbn [blk_addr blk_size fst snd ai_L AI_P0 P0L al_img] in A1', SZ0, ATOP, AIMG.
    apply Forall_cons_iff in AIMG as [AI1 AIMG]. apply Forall_cons_iff in AIMG as [AI2 _]. cbn [fst snd] in AI1, AI2.
    ceil_facts.

    assert (HPm1 : heap_pres AI_P0 LB (bv_unsigned sp) m m1).
    { eapply heap_pres_of_munch; [exact MU1| exact WM1|]. intros a Ha Hc. cbn. split; [| exact I].
      destruct Hc as [Hc|[(lo' & hi' & CS & Hlo)|(b & Hb & Hab)]]; [lia| |].
      - cbn [ai_L AI_P0 P0L al_client_static] in CS. unfold p0_client_static in CS. lia.
      - pose proof (P0_block_range _ _ _ _ HR Hb) as (_ & _ & _ & BT & _). idtac. ceil_facts.
        unfold AllocIF.blk_addr, AllocIF.blk_size, blk_addr, blk_size in BT, Hab.
        cbn [ai_K AI_P0] in Hab. clear -BT Hab CLO LOLE. lia. }
    assert (HRm1 : RHEAP s LB m1).
    { eapply P0_heap_frame; [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. idtac. ceil_facts. lia. }
    assert (HEm1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (ERRm1 : rw_cells rsegs m1 RERRNO [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold RERRNO, RATP. lia. }
    assert (OLDm1 : rw_cells rsegs m1 A [CB (Z.to_nat sz) old]).
    { eapply rw_cells_transport; [exact CELLS| exact MU1| exact WM1|]. cbn. lia. }

    eapply sreach_bind.
    { eapply (P0_malloc_sreach rmalloc_entry rmalloc_entry_spec);
        [exact HRm1| exact HEm1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| idtac; ceil_facts; lia
        | rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| exact ERRm1| exact MI1| reflexivity| lia]. }
    intros s' LB' ms' POSTm.
    destruct POSTm as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & FRAMEm & RES).
    destruct FRAMEm as (MI' & ST' & HE' & [errv' ERR'] & HP'). cbn [ai_L AI_P0 P0L al_errno] in ERR'.
    rewrite unsigned_lit in ST', HP' by lia.
    replace (ret_pc (Z_to_bv 64 0x19cf8)) with (Z_to_bv 64 0x19cf8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR' : rw_cells rsegs m' (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply heap_pres_rw_cells; [exact HP'| exact FR1|]. cbn. intros a Ha. left. lia. }
    destruct RES as [(-> & -> & HRf)|(k' & A' & junk & -> & -> & BR' & HR'' & NEW)].
    +
      eapply sreach_evt.
      { eapply (rrgen_fail _ sp gp (Z_to_bv 64 RATP)); [exact FR'| exact ST'| lia| exact MI']. }
      intros ms'' [-> ST''].
      apply sreach_ret. unfold realloc_post. do 15 eexists. exists m'. split; [reflexivity|].
      left. split; [reflexivity|]. split; [reflexivity|]. split; [| exact HRf].
      split; [exact MI'|]. split; [exact ST''|]. split; [exact HE'|]. split; [exists errv'; exact ERR'|].
      eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPm1| lia| auto]|]. eapply heap_pres_weaken; [exact HP'| lia| auto].
    +
      pose proof (RHEAP_blocks_nodup_proof _ _ _ HR'') as ND'. cbn [map blk_id fst] in ND'.
      inversion ND' as [|x l NIk ND0]; subst x l.
      assert (INk : In k (map blk_id LB)) by (change k with (blk_id (k, A, sz)); apply in_map; exact HIN).
      assert (NEk : k' <> k) by (intros ->; exact (NIk INk)).
      destruct BR' as (BA1 & BA2 & _ & BA4 & BAI). cbn [ai_L AI_P0 P0L al_img] in BAI. ceil_facts.
      apply Forall_cons_iff in BAI as [BI1 BAI]. apply Forall_cons_iff in BAI as [BI2 _]. cbn [fst snd] in BI1, BI2.
      assert (DISJ : A + sz <= A' \/ A' + n <= A).
      { destruct (P0_blocks_disjoint s' ((k', A', n) :: LB) m' (k', A', n) (k, A, sz) HR'' ltac:(left; reflexivity) ltac:(right; exact HIN)
                   ltac:(intros E; inversion E; subst; exact (NEk eq_refl))) as [D|D]; cbn [blk_addr blk_size fst snd] in D; lia. }
      assert (OLDm' : rw_cells rsegs m' A [CB (Z.to_nat sz) old]).
      { eapply heap_pres_rw_cells; [exact HP'| exact OLDm1|]. cbn [cells_size csize Nat.add]. intros a Ha. right. right.
        exists (k, A, sz). split; [exact HIN|]. cbn [AllocIF.blk_addr AllocIF.blk_size fst snd]. lia. }
      assert (LENold : length old = Z.to_nat sz) by (destruct OLDm' as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
      set (mn := Z.to_nat (Z.min n sz)) in *.
      assert (LENjunk : length junk = Z.to_nat n) by (destruct NEW as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
      assert (NEW2 : rw_cells rsegs m' A' [CB mn (firstn mn junk); CB (Z.to_nat n - mn) (skipn mn junk)]).
      { apply rw_cells_CB_split; [| rewrite firstn_length; lia]. rewrite firstn_skipn. replace (mn + (Z.to_nat n - mn))%nat with (Z.to_nat n) by lia. exact NEW. }
      apply rw_cells_CB2_split in NEW2 as [DST REST].

      eapply sreach_evt.
      { eapply (rrgen_tocpy _ (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m' A' A n (A + sz)); lia. }
      intros ms2 ->. replace (A + sz - A) with sz by lia.

      eapply sreach_evt.
      { eapply (memcpy_spec _ _ gp (Z_to_bv 64 RATP) _ _ _ _ _ (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 (Z.min n sz)) _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m'
                  (firstn mn old) (firstn mn junk)); rewrite ?unsigned_lit by lia.
        - destruct OLDm' as [[_ BO] _]. cbn [cells_bytes cbytes] in BO. rewrite app_nil_r in BO. apply bytes_at_firstn. exact BO.
        - rewrite firstn_length. lia.
        - fold mn. exact DST.
        - lia.
        - exact MI'. }
      intros ms3 POSTc. unfold memcpy_post in POSTc.
      destruct POSTc as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m'' & -> & MU2 & WM2 & MI2 & CPY & _).
      rewrite ?unsigned_lit in MU2, CPY by lia. fold mn in CPY.
      replace (ret_pc (Z_to_bv 64 0x19d18)) with (Z_to_bv 64 0x19d18) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (MN : 0 <= Z.min n sz <= n) by lia.
      assert (FR2 : rw_cells rsegs m'' (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
      { eapply rw_cells_transport; [exact FR'| exact MU2| exact WM2|]. cbn. lia. }
      assert (ST2 : stk rsegs m'' lo (bv_unsigned sp + -64)).
      { eapply stk_transport_disjoint; [exact ST'| exact MU2| exact WM2|]. cbn. lia. }
      assert (HR2 : RHEAP s' ((k', A', n) :: LB) m'').
      { eapply P0_heap_frame; [exact HR''| exact MU2| exact WM2|]. constructor; [| constructor]. right. right. right.
        exists (k', A', n). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
      assert (HE2 : rauxv_ok m'' B).
      { eapply rauxv_ok_frame; [exact HE'| exact MU2| exact WM2|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
      assert (ERR2 : rw_cells rsegs m'' RERRNO [C4 errv']).
      { eapply rw_cells_transport; [exact ERR'| exact MU2| exact WM2|]. cbn. unfold RERRNO, RATP. lia. }
      assert (REST2 : rw_cells rsegs m'' (A' + Z.of_nat mn) [CB (Z.to_nat n - mn) (skipn mn junk)]).
      { eapply rw_cells_transport; [exact REST| exact MU2| exact WM2|]. cbn. lia. }
      pose proof (rw_cells_CB2_join _ _ _ _ _ _ CPY REST2) as NEW3.
      replace (mn + (Z.to_nat n - mn))%nat with (Z.to_nat n) in NEW3 by lia.
      assert (HPc : heap_pres AI_P0 (lb_remove k LB) (bv_unsigned sp) m' m'').
      { eapply heap_pres_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc. cbn. split; [| exact I].
        destruct Hc as [Hc|[(lo' & hi' & CS & Hlo)|(b & Hb & Hab)]]; [lia| |].
        - cbn [ai_L AI_P0 P0L al_client_static] in CS. unfold p0_client_static in CS. (first [solve [clear - BI2 CS Hlo; lia] | lia]).
        - cbn [ai_K AI_P0] in Hab. pose proof (lb_remove_sub _ _ _ Hb) as HbL.
          assert (NEb : (k', A', n) <> b).
          { intros <-. apply NIk. change k' with (blk_id (k', A', n)). apply in_map. exact HbL. }
          destruct (P0_blocks_disjoint s' ((k', A', n) :: LB) m' (k', A', n) b HR'' ltac:(left; reflexivity) ltac:(right; exact HbL) NEb) as [D|D];
            cbn [blk_addr blk_size fst snd] in D; unfold blk_addr, blk_size in D; unfold AllocIF.blk_addr, AllocIF.blk_size in Hab; lia. }

      eapply sreach_evt; [apply rrgen_tofree|]. intros ms4 ->.

      eapply sreach_bind.
      { eapply (P0_free_sreach rfree_entry rfree_entry_spec);
          [exact HR2| right; exact HIN| exact HE2| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST2
          | idtac; ceil_facts; lia| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia| exact ERR2| exact MI2| reflexivity]. }
      intros s'' LB'' ms5 POSTf.
      destruct POSTf as (z0 & z1 & z2 & ra1 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & FRAMEf & -> & HR3).
      destruct FRAMEf as (MI3 & ST3 & HE3 & [errv3 ERR3] & HP3). cbn [ai_L AI_P0 P0L al_errno] in ERR3.
      rewrite unsigned_lit in ST3, HP3 by lia.
      replace (ret_pc (Z_to_bv 64 0x19d20)) with (Z_to_bv 64 0x19d20) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite (lb_remove_cons_other LB k k' A' n NEk) in HR3, HP3 |- *.
      assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
      { eapply heap_pres_rw_cells; [exact HP3| exact FR2|]. cbn. intros a Ha. left. lia. }

      eapply sreach_evt.
      { eapply (rrgen_end _ sp gp (Z_to_bv 64 RATP)); [exact FR3| exact ST3| lia| exact MI3]. }
      intros ms6 [-> ST6].
      apply sreach_ret. unfold realloc_post. do 15 eexists. exists m3. split; [reflexivity|].
      right. exists k', A', (skipn mn junk). split; [reflexivity|]. split; [reflexivity|].
      split; [| split; [| split; [exact HR3|]]].
      * unfold block_range. cbn [ai_L AI_P0 P0L al_img]. ceil_facts.
        split; [exact BA1|]. split; [exact BA2|]. split; [lia|]. split; [exact BA4|].
        constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
      * split; [exact MI3|]. split; [exact ST6|]. split; [exact HE3|]. split; [exists errv3; exact ERR3|].
        eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPm1| lia| intros b Hb; exact (lb_remove_sub _ _ _ Hb)]|].
        eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HP'| lia| intros b Hb; exact (lb_remove_sub _ _ _ Hb)]|].
        eapply heap_pres_trans; [exact HPc|].
        eapply heap_pres_weaken; [exact HP3| lia|]. intros b Hb. right. exact Hb.
      * eapply heap_pres_rw_cells; [exact HP3| exact NEW3|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. intros a Ha. right. right.
        exists (k', A', n). split; [left; reflexivity|]. cbn [AllocIF.blk_addr AllocIF.blk_size fst snd]. lia.
Qed.
