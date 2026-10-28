(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame ITree Nodes Decode.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KStepK KStepC.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocHINV MallocFacts_A Malloc_iface MallocTree MallocFacts_inv2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import AllocLink.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

Definition p0_client_static (lo hi : Z) : Prop :=
  0x2a000 <= lo /\ hi <= 0x5d000
  /\ (hi <= RLIBC \/ RCTX + 928 <= lo) /\ (hi <= RERRNO \/ RERRNO + 4 <= lo)
  /\ (hi <= RSSP_GUARD \/ RSSP_GUARD + 8 <= lo) /\ (hi <= RGOT_SSP \/ RGOT_SSP + 8 <= lo)
  /\ (hi <= RVMLOCK \/ RVMLOCK + 8 <= lo).

Definition P0L : alloc_layout :=
  mkAL RATP RERRNO RMALLOC_SYM RFREE_SYM 0x1995c 8192 [(0x10000, 0x2a000); (0x2a000, 0x5d000)] p0_client_static.

Definition G0 : PState -> Model -> Prop := fun _ _ => True.
Lemma frame_ok_G0 : frame_ok G0.
Proof. intros s s' mo mo' _ _ _ _. exact I. Qed.

Definition P0_LINK (s : PState) (LB : list block) (mo : Model) : Prop := OWN (map blk_id LB) G0 s mo.

Lemma bptr_eqb_eq : forall a b : bptr, bptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold bptr_eqb. cbn [fst snd]. rewrite andb_true_iff, MI_Kit.aptr_eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma nodup_map_eq {A B} (f : A -> B) : forall l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|? ? Hni ND']; subst.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply Hni. rewrite E. apply in_map. exact Hy.
  - exfalso. apply Hni. rewrite <- E. apply in_map. exact Hx.
  - apply IH; auto.
Qed.

Lemma P0_link_frame : forall s LB mo, P0_LINK s LB mo -> m_halted mo = None /\ m_vm_lazy mo = [].
Proof.
  intros s LB mo [(L & _ & HK & _) _]. split; [exact (kl_halt _ _ _ HK)| apply minv_nolazy; exact (kl_minv _ _ _ HK)].
Qed.

Lemma P0_block_range {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m b, RHEAP s LB m -> In b LB ->
  0 < blk_addr b /\ blk_addr b mod 16 = 0 /\ 0 <= blk_size b
  /\ blk_addr b + blk_size b <= alloc_ceiling
  /\ Forall (fun w => blk_addr b + blk_size b <= fst w \/ snd w <= blk_addr b) (al_img P0L).
Proof.
  intros s LB m b HR HIN. pose proof (RHEAP_block_range_proof s LB m b HR HIN) as (R1 & R2 & R3 & R4 & R5 & R6).
  idtac. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
Qed.

Lemma P0_blocks_disjoint {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m b1 b2, RHEAP s LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros s LB m b1 b2 HR H1 H2 NE. apply (RHEAP_blocks_disjoint_proof s LB m b1 b2 HR H1 H2).
  intros E. apply NE. exact (nodup_map_eq blk_id LB b1 b2 (RHEAP_blocks_nodup_proof _ _ _ HR) H1 H2 E).
Qed.

Lemma P0_block_ge_4096 {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m b, RHEAP s LB m -> In b LB -> 4096 <= blk_addr b.
Proof.
  intros s LB m b (st & LB0 & HP & _ & MR & [_ AR]) HIN.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1 & RI2). lia.
Qed.

Lemma P0_block_img {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m b, RHEAP s LB m -> In b LB -> blk_addr b + blk_size b <= 0x2a000 \/ 0x5d000 <= blk_addr b.
Proof.
  intros s LB m b HR HIN. pose proof (RHEAP_block_range_proof s LB m b HR HIN) as (R1 & R2 & R3 & R4 & R5 & R6). exact R6.
Qed.

Lemma round_up8_le : forall x e, x <= e -> e mod 8 = 0 -> round_up8 x <= e.
Proof. intros x e Hx He. unfold round_up8. Z.div_mod_to_equations. lia. Qed.
Lemma round_up8_ge : forall x, x <= round_up8 x.
Proof. intros x. unfold round_up8. Z.div_mod_to_equations. lia. Qed.

Lemma P0_block_slack {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m b a, RHEAP s LB m -> In b LB ->
  blk_addr b <= a < round_up8 (blk_addr b + blk_size b) ->
  exists v, mrd rsegs m (wa a) = Some v.
Proof.
  intros s LB m b a (st & LB0 & HP & _ & MR & [_ AR]) HIN Ha.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1 & RI2).
  pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH _ r Hr Hk) as [HWr _].
  pose proof WF as (_ & _ & WR & _). destruct (WR _ r Hr) as (RB0 & RBAL & _).
  assert (E8 : (r_base r + round_up_pg (r_len r)) mod 8 = 0).
  { rewrite round_up_pg_eq. unfold page_round_up_Z, page_size. clear -RBAL. Z.div_mod_to_equations. nia. }
  pose proof (round_up8_le _ _ HIB E8) as UP. ceil_facts.
  destruct HWr as (W0 & W1 & W). specialize (W (a - r_base r) ltac:(lia)). replace (r_base r + (a - r_base r)) with a in W by lia.
  rewrite p0_wview_overlay2 in W by (rewrite wa_unsigned by lia; lia).
  rewrite p0_mrd_overlay2 by (rewrite wa_unsigned by lia; lia).
  destruct (m (wa a)) as [v|]; [exists v; reflexivity| exfalso; apply W; reflexivity].
Qed.

Lemma P0_heap_frame {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv => alloc_ceiling <= fst iv
                    \/ (exists lo hi, al_client_static P0L lo hi /\ lo <= fst iv /\ snd iv <= hi)
                    \/ (al_errno P0L <= fst iv /\ snd iv <= al_errno P0L + 4)
                    \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
  RHEAP s LB m'.
Proof.
  intros s LB m m' W HR MU WM FW. eapply RHEAP_frame_proof; [exact HR| exact MU| exact WM|].
  eapply Forall_impl; [|exact FW]. intros [lo hi] H. cbn [fst snd al_errno al_client_static P0L] in H. unfold rclient_write_ok. cbn [fst snd].
  idtac.
  destruct H as [H|[(lo' & hi' & CS & H1 & H2)|[H|H]]].
  - left. exact H.
  - right. left. unfold p0_client_static in CS. lia.
  - right. left. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
  - right. right. exact H.
Qed.

Lemma P0_env_frame {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m m' W B,
  RHEAP s LB m -> rauxv_ok m B -> munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= B)
                    \/ (exists lo hi, al_client_static P0L lo hi /\ lo <= fst iv /\ snd iv <= hi)
                    \/ (al_errno P0L <= fst iv /\ snd iv <= al_errno P0L + 4)
                    \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
  rauxv_ok m' B.
Proof.
  intros s LB m m' W B HR AUX MU WM FW.
  pose proof AUX as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & AB & _).
  eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
  eapply Forall_impl; [|exact FW]. intros [lo hi] H. cbn [fst snd al_errno al_client_static P0L] in H. cbn [fst snd].
  idtac. ceil_facts. unfold RAUXV_CELL, RERRNO in *.
  destruct H as [H|[(lo' & hi' & CS & H1 & H2)|[H|(b & Hb & H1 & H2)]]].
  - lia.
  - unfold p0_client_static, RLIBC, RCTX in CS. lia.
  - lia.
  - pose proof (RHEAP_block_range_proof s LB m b HR Hb) as (R1 & R2 & R3 & R4 & R5 & R6). ceil_facts. lia.
Qed.

Lemma P0_blocks_nodup {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m, RHEAP s LB m -> base.NoDup (map blk_id LB).
Proof. intros s LB m HR. apply NoDup_ListNoDup. exact (RHEAP_blocks_nodup_proof s LB m HR). Qed.

Definition P0_keep (s s' : PState) : Prop := ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.
Lemma P0_keep_refl : forall s, P0_keep s s. Proof. intros; split; reflexivity. Qed.
Lemma P0_keep_trans : forall s1 s2 s3, P0_keep s1 s2 -> P0_keep s2 s3 -> P0_keep s1 s3.
Proof. intros s1 s2 s3 [A B] [C D]. split; congruence. Qed.

Lemma P0_link_perm : forall s LB LB' mo, P0_LINK s LB mo -> Permutation LB LB' -> P0_LINK s LB' mo.
Proof. intros s LB LB' mo H HP. unfold P0_LINK in *. eapply OWN_perm; [apply Permutation_map; exact HP| exact H]. Qed.

Definition AI_P0 {HGW : HasGuard} {HCEIL : HasCeiling} : alloc_if rsegs :=
  mkAI rsegs P0L bptr bptr_eqb bptr_eqb_eq PState
       RHEAP rauxv_ok P0_LINK
       P0_link_frame P0_keep P0_keep_refl P0_keep_trans
       P0_mrel P0_mrel_refl P0_mrel_trans P0_mrel_fs
       P0_block_range P0_blocks_disjoint P0_blocks_nodup P0_block_slack
       P0_heap_frame P0_env_frame RHEAP_perm P0_link_perm.

Lemma heap_pres_of_rheap_pres {HGW : HasGuard} {HCEIL : HasCeiling} : forall LB SP m m',
  rheap_pres LB SP m m' -> heap_pres AI_P0 LB SP m m'.
Proof.
  intros LB SP m m' H a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[(lo & hi & CS & Hlo)|Hc]]; [left; exact Hc| right; left| right; right; exact Hc].
  cbn [ai_L AI_P0 P0L al_client_static] in CS. unfold p0_client_static in CS. unfold ralloc_static.
  unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
Qed.

Lemma errno_addr_RATP : bv_unsigned (Z_to_bv 64 RATP) + -164 = RERRNO.
Proof. unfold RATP, RERRNO. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma P0_malloc_contract_gen {HGW : HasGuard} {HCEIL : HasCeiling} : forall pc, rmalloc_stmt_at pc -> malloc_contract_at AI_P0 pc.
Proof.
  intros pc SPEC ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
         HR HE HB ST CLO LOLE ERR MI Ha0 Hn.
  cbn [ai_L AI_P0 P0L al_malloc_pc al_tp al_stack al_errno RHEAP RENV ai_PS ai_K] in *.
  intros mo HL. cbn [LINK AI_P0] in HL.
  assert (ERR' : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 RATP) + -164) [C4 errv]) by (rewrite errno_addr_RATP; exact ERR).
  pose proof (SPEC ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m s LB n lo B errv HR HE HB ST ltac:(idtac; exact CLO) ltac:(unfold RMALLOC_STACK; lia) ERR' MI eq_refl Ha0 Hn) as IMPL.
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

Theorem P0_malloc_contract {HGW : HasGuard} {HCEIL : HasCeiling} : malloc_contract_at AI_P0 (al_malloc_pc (ai_L rsegs AI_P0)).
Proof. exact (P0_malloc_contract_gen RMALLOC_SYM rmalloc_spec). Qed.

Lemma lb_remove_notin : forall (LB : list block) k,
  ~ In k (map blk_id LB) -> lb_remove k LB = LB.
Proof.
  induction LB as [|b LB IH]; intros k Hni; [reflexivity|]. cbn in Hni. unfold lb_remove in *.
  rewrite filter_cons. destruct (decide _) as [D|D].
  - f_equal. apply IH. LiaTuning.ctauto.
  - exfalso. apply D. apply Is_true_true_2. destruct (bptr_eqb (blk_id b) k) eqn:E; [|reflexivity].
    exfalso. apply Hni. left. apply bptr_eqb_eq. exact E.
Qed.
Lemma lb_remove_perm : forall (LB : list block) k A n,
  List.NoDup (map blk_id LB) -> In (k, A, n) LB ->
  Permutation (map blk_id LB) (k :: map blk_id (lb_remove k LB)).
Proof.
  induction LB as [|b LB IH]; intros k A n ND HIN; [destruct HIN|].
  cbn in ND. inversion ND as [|? ? Hni ND']; subst.
  unfold lb_remove in *. rewrite filter_cons. destruct (decide _) as [D|D].
  - destruct HIN as [->|HIN].
    { exfalso. cbn in D. rewrite (proj2 (bptr_eqb_eq k k) eq_refl) in D. exact D. }
    cbn [map]. eapply Permutation_trans; [apply perm_skip; apply (IH k A n ND' HIN)|]. apply perm_swap.
  - assert (Eb : blk_id b = k).
    { apply bptr_eqb_eq. destruct (bptr_eqb (blk_id b) k) eqn:E; [reflexivity|]. exfalso. apply D. exact I. }
    cbn [map]. rewrite Eb. constructor. fold (lb_remove k LB). rewrite lb_remove_notin; [apply Permutation_refl|]. rewrite <- Eb. exact Hni.
Qed.

Lemma P0_free_contract_gen {HGW : HasGuard} {HCEIL : HasCeiling} : forall pc, rfree_stmt_at pc -> free_contract_at AI_P0 pc.
Proof.
  intros pc SPEC ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB k A n lo B errv
         HR HIN HE HB ST CLO LOLE ERR MI Ha0.
  cbn [ai_L AI_P0 P0L al_free_pc al_tp al_stack al_errno RHEAP RENV ai_PS ai_K ai_K_eqb] in *.
  intros mo HL. cbn [LINK AI_P0] in HL.
  assert (ERR' : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 RATP) + -164) [C4 errv]) by (rewrite errno_addr_RATP; exact ERR).
  pose proof (SPEC ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m s LB k A n lo B errv HR HIN HE HB ST ltac:(idtac; exact CLO) ltac:(unfold RFREE_STACK; lia) ERR' MI eq_refl Ha0) as IMPL.
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

Theorem P0_free_contract {HGW : HasGuard} {HCEIL : HasCeiling} : free_contract_at AI_P0 (al_free_pc (ai_L rsegs AI_P0)).
Proof. exact (P0_free_contract_gen RFREE_SYM rfree_spec_proof). Qed.

Theorem P0_free_null_contract {HGW : HasGuard} {HCEIL : HasCeiling} : free_null_contract_at rsegs (al_free_pc (ai_L rsegs AI_P0)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Ha0.
  cbn [ai_L AI_P0 P0L al_free_pc].
  eapply evt_mono; [apply (rfree_null_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Ha0)|].
  intros ms' ->. do 15 eexists. reflexivity.
Qed.

Theorem P0_realloc_null_contract {HGW : HasGuard} {HCEIL : HasCeiling} : realloc_null_contract_at AI_P0 (al_realloc_pc (ai_L rsegs AI_P0)).
Proof.
  intros ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
         HR HE HB ST CLO LOLE ERR MI Ha0 Ha1 Hn.
  cbn [ai_L AI_P0 P0L al_realloc_pc al_tp].
  eapply (sreach_evt rsegs AI_P0 (fun ms' => ms' = MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                    F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
  { subst a0. step. step. if_true. step. step. apply evt_done. reflexivity. }
  intros ms' ->.
  eapply (P0_malloc_contract_gen rmalloc_entry rmalloc_entry_spec); eauto.
Qed.
