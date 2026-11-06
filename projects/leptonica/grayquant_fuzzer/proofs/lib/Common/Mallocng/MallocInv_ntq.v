(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_steps MallocInv_repw MallocInv_getmeta MallocInv_tryavail MallocInv_ntpieces.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma meta_facts : forall A x mt, WF A -> a_meta A x = Some mt ->
  0x1000 <= x /\ x + 40 <= alloc_ceiling /\ (x + 40 <= IMG_LO \/ IMG_HI <= x) /\ x mod 8 = 0 /\
  (forall j, 0 <= j < 40 -> dom A (x + j)).
Proof.
  intros A x mt HW Hx.
  destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpg & Hk & ->).
  destruct (wf_areas_al A HW pg Hpg) as [Hal Hph]. unfold heap_range in Hph. unfold page_aligned in Hal.
  pose proof (meta_addr_range pg k Hk) as Hmr.
  split; [llia|]. split; [llia|]. split; [llia|]. split.
  - unfold meta_addr. pose proof (Z.div_mod pg 4096 ltac:(llia)) as E.
    replace (pg + 24 + 40 * k) with ((512 * (pg / 4096) + 3 + 5 * k) * 8) by llia. apply Z_mod_mult.
  - intros j Hj. left. exists pg. split; [exact Hpg | llia].
Qed.

Lemma meta_u64 : forall A x mt, WF A -> a_meta A x = Some mt -> 0 <= x < 2^64.
Proof. intros A x mt HW Hx. pose proof (meta_facts A x mt HW Hx) as (H1 & H2 & _). ceil. llia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma addr_active : forall sc, 0 <= sc < 64 ->
  at_ (v_add A_CTX (v_slli (Z_to_bv 64 sc) 3)) 80 = Z_to_bv 64 (caddr (KActive sc)).
Proof.
  intros sc Hsc. rewrite v_slli_Z by llia. rewrite A_CTX_eq, v_add_Z, at_Z. f_equal. cbn. unfold C_SECRET, C_ACTIVE. llia.
Qed.

Lemma addr_usage : forall sc, 0 <= sc < 64 ->
  at_ (v_add A_CTX (v_slli (Z_to_bv 64 sc) 3)) 464 = Z_to_bv 64 (caddr (KUsage sc)).
Proof.
  intros sc Hsc. rewrite v_slli_Z by llia. rewrite A_CTX_eq, v_add_Z, at_Z. f_equal. cbn. unfold C_SECRET, C_USAGE. llia.
Qed.

Lemma addr_bounce : forall d, at_ (v_add A_CTX (Z_to_bv 64 d)) 880 = Z_to_bv 64 (caddr (KBounce d)).
Proof. intros d. rewrite A_CTX_eq, v_add_Z, at_Z. f_equal. cbn. unfold C_SECRET, C_BOUNCE. llia. Qed.

Lemma addr_useq : forall d, at_ (v_add A_CTX (Z_to_bv 64 d)) 848 = Z_to_bv 64 (caddr (KUseq d)).
Proof. intros d. rewrite A_CTX_eq, v_add_Z, at_Z. f_equal. cbn. unfold C_SECRET, C_USEQ. llia. Qed.

Lemma addr_seq : at_ A_CTX 912 = Z_to_bv 64 (caddr KSeq).
Proof. rewrite A_CTX_eq, at_Z. f_equal. cbn. unfold C_SECRET, C_SEQ. llia. Qed.

Lemma addr_fmh : at_ A_CTX 16 = Z_to_bv 64 (caddr KFmh).
Proof. rewrite A_CTX_eq, at_Z. f_equal. cbn. unfold C_SECRET, C_FMH. llia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wsc_eq : forall mt, 0 <= mt_w32 mt < 2^64 ->
  v_srli (v_slli (Z_to_bv 64 (mt_w32 mt)) 52) 58 = Z_to_bv 64 (mt_sc mt).
Proof.
  intros mt Hw. rewrite v_slli_Z by llia. rewrite <- (ZZ_mod (mt_w32 mt * 2^52)).
  rewrite v_srli_Z by (pose proof (Z.mod_pos_bound (mt_w32 mt * 2^52) (2^64)); llia).
  f_equal. unfold mt_sc. apply (proj1 (proj2 (w32_fields (mt_w32 mt) ltac:(llia)))).
Qed.

Lemma wlast_eq : forall mt, 0 <= mt_w32 mt < 2^64 -> v_andi (Z_to_bv 64 (mt_w32 mt)) 31 = Z_to_bv 64 (mt_last mt).
Proof. intros mt Hw. rewrite v_andi_Z by llia. f_equal. unfold mt_last. apply (proj1 (w32_fields (mt_w32 mt) ltac:(llia))). Qed.

Lemma wmaplen_eq : forall mt, 0 <= mt_w32 mt < 2^64 -> v_srli (Z_to_bv 64 (mt_w32 mt)) 12 = Z_to_bv 64 (mt_maplen mt).
Proof. intros mt Hw. rewrite v_srli_Z by llia. reflexivity. Qed.

Lemma wall_eq : forall mt, 0 <= mt_w32 mt < 2^64 ->
  v_addiw (v_sllw (wlit 2) (Z_to_bv 64 (mt_w32 mt))) (-1) = w32 (2 ^ mt_cnt mt - 1).
Proof.
  intros mt Hw. rewrite v_sllw_2 by llia. rewrite v_addiw_w32. reflexivity.
Qed.

Lemma maplen_nonneg : forall mt, 0 <= mt_w32 mt -> 0 <= mt_maplen mt.
Proof. intros mt H. unfold mt_maplen, w_maplen. apply Z.div_pos; llia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StoreW.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop) (ws : list fct).

  Lemma ts_st_domW : forall s (m0 : word -> option byte) ws n a v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> (0 < n)%nat ->
    (forall j, 0 <= j < Z.of_nat n -> dom A (a + j)) ->
    (forall m', RepW A m0 (FCT a (Z.of_nat n) (bv_unsigned v) :: ws) m' -> tsafe (k tt (upd s m' (ms_vm s))) P) ->
    tsafe ((x <- m_st n (Z_to_bv 64 a) v ;; k x) s) P.
  Proof.
    intros s m0 ws n a v k P RW HWIN Hn Hd Hk.
    eapply (ts_st_domw A HW); [exact RW | exact HWIN | exact Hn | exact Hd |].
    apply Hk. apply (repw_st_dom A HW); [exact RW | exact Hn | exact Hd].
  Qed.

  Lemma ts_sd_metaW : forall s (m0 : word -> option byte) ws x mt d v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> a_meta A x = Some mt -> 0 <= d -> d + 8 <= 40 ->
    (forall m', RepW A m0 (FCT (x + d) 8 (bv_unsigned v) :: ws) m' -> tsafe (k tt (upd s m' (ms_vm s))) P) ->
    tsafe ((y <- m_sd (Z_to_bv 64 (x + d)) v ;; k y) s) P.
  Proof.
    intros s m0 ws x mt d v k P RW HWIN Hx Hd0 Hd8 Hk. unfold m_sd.
    pose proof (meta_facts A x mt HW Hx) as (_ & _ & _ & _ & Hdom).
    apply (ts_st_domW s m0 ws 8 (x + d) v k P RW HWIN ltac:(lia)).
    - intros j Hj. rewrite <- Z.add_assoc. apply Hdom. llia.
    - exact Hk.
  Qed.

  Lemma ts_st_ctxW : forall s (m0 : word -> option byte) ws ck v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> cvalid ck ->
    (forall m', RepW A m0 (FCT (caddr ck) (clen ck) (bv_unsigned v) :: ws) m' -> tsafe (k tt (upd s m' (ms_vm s))) P) ->
    tsafe ((x <- m_st (Z.to_nat (clen ck)) (Z_to_bv 64 (caddr ck)) v ;; k x) s) P.
  Proof.
    intros s m0 ws ck v k P RW HWIN Hck Hk.
    eapply (ts_st_ctxw A s m0 ws ck); [exact RW | exact HWIN | exact Hck |].
    apply Hk. apply (repw_st_ctx A s m0 ws ck v RW Hck).
  Qed.

  Lemma ts_sd_ctxW : forall s (m0 : word -> option byte) ws ck v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 8 ->
    (forall m', RepW A m0 (FCT (caddr ck) 8 (bv_unsigned v) :: ws) m' -> tsafe (k tt (upd s m' (ms_vm s))) P) ->
    tsafe ((x <- m_sd (Z_to_bv 64 (caddr ck)) v ;; k x) s) P.
  Proof.
    intros s m0 ws ck v k P RW HWIN Hck Hlen Hk. unfold m_sd.
    replace 8%nat with (Z.to_nat (clen ck)) by (rewrite Hlen; reflexivity).
    apply (ts_st_ctxW s m0 ws ck v k P RW HWIN Hck). rewrite Hlen. exact Hk.
  Qed.

  Lemma ts_sb_ctxW : forall s (m0 : word -> option byte) ws ck v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 1 ->
    (forall m', RepW A m0 (FCT (caddr ck) 1 (bv_unsigned v) :: ws) m' -> tsafe (k tt (upd s m' (ms_vm s))) P) ->
    tsafe ((x <- m_sb (Z_to_bv 64 (caddr ck)) v ;; k x) s) P.
  Proof.
    intros s m0 ws ck v k P RW HWIN Hck Hlen Hk. unfold m_sb.
    replace 1%nat with (Z.to_nat (clen ck)) by (rewrite Hlen; reflexivity).
    apply (ts_st_ctxW s m0 ws ck v k P RW HWIN Hck). rewrite Hlen. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_ld_metaW : forall s (m0 : word -> option byte) ws x mt fl (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> a_meta A x = Some mt -> mlen fl = 8 -> wfree_range ws (x + moff fl) 8 ->
    0 <= mt_f mt fl ->
    tsafe (k (Z_to_bv 64 (mt_f mt fl)) s) P ->
    tsafe ((y <- m_ld (Z_to_bv 64 (x + moff fl)) ;; k y) s) P.
  Proof.
    intros s m0 ws x mt fl k P RW HWIN Hx Hlen Hfree Hv Hk.
    eapply (ts_ld_factw A HW); [exact RW | exact HWIN | | exact Hfree | exact Hv | exact Hk].
    right; right; left. exists x, mt, fl. rewrite <- Hlen. auto.
  Qed.

  Lemma ts_lw_metaW : forall s (m0 : word -> option byte) ws x mt fl (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> a_meta A x = Some mt -> mlen fl = 4 -> wfree_range ws (x + moff fl) 4 ->
    0 <= mt_f mt fl < 2^32 ->
    tsafe (k (w32 (mt_f mt fl)) s) P ->
    tsafe ((y <- m_lw (Z_to_bv 64 (x + moff fl)) ;; k y) s) P.
  Proof.
    intros s m0 ws x mt fl k P RW HWIN Hx Hlen Hfree Hv Hk.
    eapply (ts_lw_factw A HW); [exact RW | exact HWIN | | exact Hfree | exact Hv | exact Hk].
    right; right; left. exists x, mt, fl. rewrite <- Hlen. auto.
  Qed.

  Lemma ts_ld_ctxfW : forall s (m0 : word -> option byte) ws ck (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 8 -> wfree_range ws (caddr ck) 8 ->
    tsafe (k (Z_to_bv 64 (a_ctx A ck)) s) P ->
    tsafe ((y <- m_ld (Z_to_bv 64 (caddr ck)) ;; k y) s) P.
  Proof.
    intros s m0 ws ck k P RW HWIN Hck Hlen Hfree Hk.
    eapply (ts_ld_factw A HW); [exact RW | exact HWIN | | exact Hfree | apply (wf_ctx_nonneg A HW) | exact Hk].
    left. exists ck. rewrite <- Hlen. auto.
  Qed.
End StoreW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section QueueCPS.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop) (ws : list fct).

  (* [comment removed for export] *)
  Theorem ts_nt_queue : forall s (m0 : word -> option byte) ws ck (g act t : Z) (mtg : meta_rec) (K : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 8 ->
    a_meta A g = Some mtg -> 0 <= act ->
    (act <> 0 -> exists mta mtt, a_meta A act = Some mta /\ mt_prev mta = t /\ a_meta A t = Some mtt /\
                 wfree_range ws act 8 /\ act <> g /\ t <> g) ->
    (act = 0 -> forall m', RepW A m0 (FCT (caddr ck) 8 g :: FCT (g + 8) 8 g :: FCT g 8 g :: ws) m' ->
                tsafe (K tt (upd s m' (ms_vm s))) P) ->
    (act <> 0 -> forall m', RepW A m0 (FCT act 8 g :: FCT (t + 8) 8 g :: FCT g 8 t :: FCT (g + 8) 8 act :: ws) m' ->
                 tsafe (K tt (upd s m' (ms_vm s))) P) ->
    tsafe ((x <- nt_queue (Z_to_bv 64 (caddr ck)) (Z_to_bv 64 g) (Z_to_bv 64 act) ;; K x) s) P.
  Proof.
    intros s m0 ws ck g act t mtg K P RW HWIN Hck Hlen Hg Hact0 Hne K0 K1.
    pose proof (meta_facts A g mtg HW Hg) as (G1 & G2 & G3 & G4 & Gdom). ceil.
    assert (Hg64 : 0 <= g < 2^64) by llia.
    unfold nt_queue. destruct (Z.eq_dec act 0) as [-> | Hnz].
    - rewrite is0_Z by llia. cbn [Z.eqb].
      reassoc. replace (Z_to_bv 64 g) with (Z_to_bv 64 (g + 0)) at 1 by (f_equal; lia).
      eapply (ts_sd_metaW A HW); [exact RW | exact HWIN | exact Hg | lia | lia |]. intros m1 RW1. rewrite uZ in RW1 by llia.
      reassoc. rewrite ?at_Z.
      eapply (ts_sd_metaW A HW); [exact RW1 | exact HWIN | exact Hg | lia | lia |]. intros m2 RW2. rewrite uZ in RW2 by llia.
      eapply (ts_sd_ctxW A); [exact RW2 | exact HWIN | exact Hck | exact Hlen |]. intros m3 RW3. rewrite uZ in RW3 by llia.
      apply (K0 eq_refl m3). rewrite Z.add_0_r in RW3. exact RW3.
    - destruct (Hne Hnz) as (mta & mtt & Ha & Hpa & Ht & Hfree & Hag & Htg).
      pose proof (meta_facts A act mta HW Ha) as (A1 & A2 & A3 & A4 & Adom).
      pose proof (meta_facts A t mtt HW Ht) as (T1 & T2 & T3 & T4 & Tdom).
      pose proof (metas_apart A act mta g mtg HW Ha Hg Hag) as Dag.
      pose proof (metas_apart A t mtt g mtg HW Ht Hg Htg) as Dtg.
      rewrite is0_Z by llia. replace (act =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
      reassoc. rewrite ?at_Z.
      eapply (ts_sd_metaW A HW); [exact RW | exact HWIN | exact Hg | lia | lia |]. intros m1 RW1. rewrite uZ in RW1 by llia.
      (* [comment removed for export] *)
      reassoc. replace (Z_to_bv 64 act) with (Z_to_bv 64 (act + moff FPrev)) at 1 by (f_equal; cbn; lia).
      eapply (ts_ld_metaW A HW); [exact RW1 | exact HWIN | exact Ha | reflexivity | | unfold mt_prev in Hpa; rewrite Hpa; llia |].
      { cbn [moff]. rewrite Z.add_0_r. apply wfree_range_cons; [cbn; llia | exact Hfree]. }
      change (mt_f mta FPrev) with (mt_prev mta). rewrite Hpa.
      reassoc. replace (Z_to_bv 64 g) with (Z_to_bv 64 (g + 0)) at 1 by (f_equal; lia).
      eapply (ts_sd_metaW A HW); [exact RW1 | exact HWIN | exact Hg | lia | lia |]. intros m2 RW2. rewrite uZ, Z.add_0_r in RW2 by llia.
      reassoc. rewrite ?at_Z.
      eapply (ts_sd_metaW A HW); [exact RW2 | exact HWIN | exact Ht | lia | lia |]. intros m3 RW3. rewrite uZ in RW3 by llia.
      (* [comment removed for export] *)
      reassoc. rewrite ?at_Z.
      eapply (ts_ld_wrw A _ m0 _ (g + 8) act); [exact RW3 | exact HWIN | llia | llia | llia | |].
      { intros j Hj. rewrite wlook_skip by (cbn; llia). rewrite wlook_skip by (cbn; llia). rewrite wlook_hit by (cbn; llia).
        cbn [f_v f_a]. f_equal. f_equal. lia. }
      replace (Z_to_bv 64 act) with (Z_to_bv 64 (act + 0)) at 1 by (f_equal; lia).
      eapply (ts_sd_metaW A HW); [exact RW3 | exact HWIN | exact Ha | lia | lia |]. intros m4 RW4. rewrite uZ, Z.add_0_r in RW4 by llia.
      exact (K1 Hnz m4 RW4).
  Qed.
End QueueCPS.

End WithLayout.
