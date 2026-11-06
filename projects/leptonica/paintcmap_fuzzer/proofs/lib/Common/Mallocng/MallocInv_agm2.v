(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf4 MallocInv_wf6 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_sc MallocInv_sc2 MallocInv_sc3
  MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_aspieces MallocInv_agrp_iface MallocInv_tav2.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record hrel (A A' : astate) : Prop := {
  hr_live : a_live A' = a_live A;
  hr_areas : a_areas A' = a_areas A;
  hr_pages : a_pages A' = a_pages A;
  hr_mblocks : a_mblocks A' = a_mblocks A;
  hr_xmaps : a_xmaps A' = a_xmaps A;
  hr_fl : a_freelist A' = a_freelist A;
  hr_active : a_active A' = a_active A;
  hr_brk_lo : a_brk_lo A' = a_brk_lo A;
  hr_meta : forall x, a_meta A' x = a_meta A x;
  hr_ctx : forall k, cvalid k -> ~ ctx_heur k -> a_ctx A' k = a_ctx A k;
  hr_dom : forall x, dom A' x <-> dom A x
}.

Lemma hrel_refl : forall A, hrel A A.
Proof. intros A. constructor; auto; tauto. Qed.

Lemma hrel_trans : forall A B C, hrel A B -> hrel B C -> hrel A C.
Proof.
  intros A B C [L1 Ar1 Pg1 Mb1 Xm1 F1 Ac1 Bk1 M1 C1 D1] [L2 Ar2 Pg2 Mb2 Xm2 F2 Ac2 Bk2 M2 C2 D2].
  constructor; first [ intros x; rewrite (D2 x); apply D1
                     | intros k Hv Hh; rewrite (C2 k Hv Hh); apply C1; assumption
                     | intros x; rewrite (M2 x); apply M1
                     | congruence ].
Qed.

Lemma hrel_set_ctx : forall A c', (forall k, ctx_heur k \/ c' k = a_ctx A k) -> hrel A (set_ctx A c').
Proof.
  intros A c' Hc. constructor; try reflexivity; try tauto.
  intros k _ Hh. cbn. destruct (Hc k) as [H | H]; [exfalso; exact (Hh H) | exact H].
Qed.

Lemma hrel_owned : forall A B x, hrel A B -> owned_of B x -> owned_of A x.
Proof. intros A B x HR [Hc | Hd]; [left; exact Hc | right]. apply (proj1 (hr_dom A B HR x)). exact Hd. Qed.

Lemma hrel_chain : forall A B s s1 s2, ntframe A s s1 -> hrel A B -> ntframe B s1 s2 -> ntframe A s s2.
Proof.
  intros A B s s1 s2 NF1 HR NF2. apply (ntframe_trans A B s s1 s2 NF1 NF2); [intros x; apply (hrel_owned A B x HR) | exact (hr_live A B HR)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hslot1 (k : cslot) : Prop := match k with KBounce _ | KUseq _ | KSeq => True | _ => False end.

Lemma hslot1_heur : forall k, hslot1 k -> ctx_heur k.
Proof. intros k. destruct k; cbn; tauto. Qed.
Lemma hslot1_clen : forall k, hslot1 k -> clen k = 1.
Proof. intros k. destruct k; cbn; tauto. Qed.

(* [comment removed for export] *)
Definition c_w (A : astate) (ws : list fct) : ctx_rec := fun k =>
  match k with
  | KBounce _ | KUseq _ | KSeq => match wlook ws (caddr k) with Some b => b | None => a_ctx A k end
  | _ => a_ctx A k
  end.

Section HeurCommit.
  Variables (A : astate) (m0 : word -> option byte) (ws : list fct) (m : word -> option byte).
  Hypothesis HW : WF A.
  Hypothesis RW : RepW A m0 ws m.
  (* [comment removed for export] *)
  Hypothesis HB : forall w x, In w ws -> f_a w <= x < f_a w + f_n w -> exists k, cvalid k /\ hslot1 k /\ x = caddr k.

  Lemma c_w_heur : forall k, ctx_heur k \/ c_w A ws k = a_ctx A k.
  Proof. intros k. destruct k; cbn; auto. Qed.

  Lemma wlook_byte : forall x b, wlook ws x = Some b -> 0 <= b < 256.
  Proof.
    intros x b Hw. pose proof (rw_wr A m0 ws m RW x b Hw) as Hm. unfold mbyte in Hm.
    destruct (rdn ml_segs m (Z_to_bv 64 x) 1) as [[|b0 [|]]|]; try discriminate Hm. injection Hm as <-. apply u8_range.
  Qed.

  Lemma c_w_nonneg : forall k, 0 <= c_w A ws k.
  Proof.
    intros k. pose proof (wf_ctx_nonneg A HW k) as H0. unfold c_w.
    destruct k; try exact H0; destruct (wlook ws _) as [b|] eqn:E; try exact H0; exact (proj1 (wlook_byte _ _ E)).
  Qed.

  Lemma c_w_slot : forall k, hslot1 k -> c_w A ws k = match wlook ws (caddr k) with Some b => b | None => a_ctx A k end.
  Proof. intros k Hk. destruct k; cbn in Hk; try contradiction; reflexivity. Qed.

  Lemma WF_c_w : WF (set_ctx A (c_w A ws)).
  Proof. exact (WF_ctx_heur A HW (c_w A ws) c_w_heur c_w_nonneg). Qed.

  Lemma Rep_c_w : Rep (set_ctx A (c_w A ws)) m.
  Proof.
    apply (commit_heur A (c_w A ws) m0 ws m HW c_w_heur c_w_nonneg RW).
    - intros x b Hw. destruct (wlook_some_cov ws x b Hw) as (w & Hin & Hx). destruct (HB w x Hin Hx) as (k & Hk & Hs & ->).
      exists k. split; [exact Hk|]. rewrite (hslot1_clen k Hs). split; [lia|]. rewrite (c_w_slot k Hs), Hw.
      rewrite Z.sub_diag, byte_of_0. symmetry. apply Z.mod_small. exact (wlook_byte _ _ Hw).
    - intros k Hk Hne x Hx.
      assert (Hs : hslot1 k) by (destruct k; cbn in Hne |- *; auto).
      rewrite (c_w_slot k Hs) in Hne. rewrite (hslot1_clen k Hs) in Hx. replace x with (caddr k) by lia.
      destruct (wlook ws (caddr k)); [discriminate | exfalso; exact (Hne eq_refl)].
  Qed.

  Lemma writes_ok_c_w : writes_ok A ws.
  Proof.
    apply (writes_ok_ctxr A ws HW). intros w x Hin Hx. destruct (HB w x Hin Hx) as (k & Hk & Hs & ->).
    exists k. split; [exact Hk|]. rewrite (hslot1_clen k Hs). lia.
  Qed.
End HeurCommit.

Theorem heur_commit : forall sp0 argv envp cb D A s ws m,
  II sp0 argv envp cb D A s -> RepW A (ms_mem s) ws m ->
  (forall w x, In w ws -> f_a w <= x < f_a w + f_n w -> exists k, cvalid k /\ hslot1 k /\ x = caddr k) ->
  II sp0 argv envp cb D (set_ctx A (c_w A ws)) (upd s m (ms_vm s)) /\ ntframe A s (upd s m (ms_vm s)) /\ hrel A (set_ctx A (c_w A ws)).
Proof.
  intros sp0 argv envp cb D A s ws m HII RW HB. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
  pose proof (WF_c_w A (ms_mem s) ws m HW RW) as HW'. pose proof (Rep_c_w A (ms_mem s) ws m HW RW HB) as HR'.
  pose proof (writes_ok_c_w A ws HW HB) as WO. pose proof (c_w_heur A ws) as Hc.
  split; [| split; [exact (ntframe_commit A s ws m HW RW WO) | exact (hrel_set_ctx A _ Hc)]].
  apply II_intro.
  - exact (IS_commit sp0 argv envp cb A _ s ws m HI RW WO HW' HR').
  - cbn [ms_vm upd]. apply (VMok_ctx_heur A (c_w A ws) Hc). exact (ii_vm HII).
  - apply (AvOK_transfer A _ (ii_av HII)); try reflexivity. intros x mt' Hx Hrl; exists mt'; auto.
  - apply (UsOK_transfer A _ (ii_us HII)); try reflexivity; intros; reflexivity.
  - apply (deads_transfer A _ D (ii_dd HII)). intros x. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ag_bounce (sc : word) : M (bool * option word)%type :=
  let d := v_addiw sc (-7) in
  if c_ltu (wlit 31) d then mret (false, None)
  else let a5 := v_add A_LOCK d in
       b <- m_lbu (at_ a5 888) ;;
       us <- m_lbu (at_ a5 856) ;;
       let nosmall := negb (c_ltu b (wlit 100)) in
       (if is0 us then mret tt
        else sq <- m_lbu (at_ A_LOCK 920) ;;
             if c_lts (wlit 9) (v_sub sq us) then mret tt
             else if c_ltu b (wlit 99) then m_sb (at_ a5 888) (v_addi b 1)
             else m_sb (at_ a5 888) (wlit 150)) ;;
       mret (nosmall, Some a5).

(* [comment removed for export] *)
Definition ag_seq (sq : word) : M word :=
  if c_eq sq (wlit 255)
  then m_sd (at_ A_LOCK 856) w0 ;; m_sd (at_ A_LOCK 864) w0 ;;
       m_sd (at_ A_LOCK 872) w0 ;; m_sd (at_ A_LOCK 880) w0 ;; mret (wlit 1)
  else mret (v_addi sq 1).

(* [comment removed for export] *)
Definition ag_usage2 (sc usage s7 : word) : M word :=
  if c_lts (wlit 31) sc then mret usage
  else if negb (is0 (v_andi sc 1)) then mret usage
  else u1 <- m_ld (at_ s7 480) ;; mret (v_add u1 usage).

(* [comment removed for export] *)
Definition ag_fail (m : word) : M word := m_free_meta_ag (at_ A_LOCK 24) m ;; mret wm1.

(* [comment removed for export] *)
Definition ag_ok (sc m p needed3 cnt3 size s7 pm : word) : M word :=
  wm <- m_ld (at_ m 32) ;;
  let aimax := v_divu (wlit 4080) size in
  ctr <- m_lw (at_ A_LOCK 20) ;;
  m_sd (at_ m 32) (v_or (v_srli (v_slli wm 52) 52) (v_and needed3 PAGEMASK)) ;;
  m_sw (at_ A_LOCK 20) (v_addi ctr 1) ;;
  let a2 := if c_ltu cnt3 aimax then cnt3 else aimax in
  let aidx := v_and (v_addi (v_sltu a2 (v_addi a2 (-1))) (-1)) (v_addi a2 (-1)) in
  as_tail sc m p aidx cnt3 s7 pm.

Lemma as_mmap_eq : forall sc req m usage pg size cnt1 a4 s7 pm,
  as_mmap sc req m usage pg size cnt1 a4 s7 pm =
  (bn <- ag_bounce sc ;;
   let '(nosmall, _) := bn in
   sq <- m_lbu (at_ A_LOCK 920) ;;
   sq' <- ag_seq sq ;;
   m_sb (at_ A_LOCK 920) sq' ;;
   usage2 <- ag_usage2 sc usage s7 ;;
   let cnt2 := cnt2w sc usage2 pg a4 cnt1 nosmall in
   let needed0 := v_mul size cnt2 in
   let needed := v_addi (v_add needed0 (v_and (v_sub (wlit (2^64 - 16)) needed0) (v_addi pg (-1)))) 16 in
   let '(cnt3, needed3) := cn3w nosmall cnt2 needed req pg size usage2 in
   p <- sys_mmap MMrw needed3 ;;
   if c_eq p wm1 then ag_fail m else ag_ok sc m p needed3 cnt3 size s7 pm).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma addr_lock : forall d, at_ A_LOCK d = Z_to_bv 64 (LOCKA + d).
Proof. intros d. rewrite A_LOCK_eq, at_Z. reflexivity. Qed.

Lemma addr_useq_lock : forall d, 0 <= d < 2^64 -> at_ (v_add A_LOCK (Z_to_bv 64 d)) 856 = Z_to_bv 64 (caddr (KUseq d)).
Proof. intros d Hd. rewrite A_LOCK_eq, v_add_Z, at_Z. f_equal. cbn. unfold C_USEQ. lia. Qed.

Lemma caddr_KSeq_lock : caddr KSeq = LOCKA + 920. Proof. cbn. unfold C_SEQ. lia. Qed.
Lemma caddr_KCtr_lock : caddr KCtr = LOCKA + 20. Proof. cbn. unfold C_CTR. lia. Qed.
Lemma caddr_KUseq_lock : forall j, caddr (KUseq j) = LOCKA + 856 + j. Proof. intros j. cbn. unfold C_USEQ. lia. Qed.
Lemma caddr_KUsage_lock : forall c, caddr (KUsage c) = LOCKA + 472 + 8 * c. Proof. intros c. cbn. unfold C_USAGE. lia. Qed.
Lemma CTX_lock : CTX = LOCKA + 8. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bounce.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variable sc : Z.
  Hypothesis Hsc : 0 <= sc < 48.
  Implicit Types (P : R -> mstate -> Prop).

  Theorem ag_bounce_ok : forall (K : bool * option word -> M R) P,
    (forall s1 A1 (ns : bool) (o : option word), II sp0 argv envp cb D A1 s1 -> ntframe A s s1 -> hrel A A1 ->
       ((sc < 7 \/ 38 < sc) -> ns = false) ->
       tsafe (K (ns, o) s1) P) ->
    tsafe ((bn <- ag_bounce (Z_to_bv 64 sc) ;; K bn) s) P.
  Proof.
    intros K P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    unfold ag_bounce. cbv zeta.
    destruct (bounce_d_word sc Hsc) as [Dlo Dhi].
    destruct (Z.lt_ge_cases sc 7) as [H7 | H7].
    { rewrite (Dlo H7). apply ts_bind_ret. exact (HK s A false None HII (ntframe_refl A s) (hrel_refl A) (fun _ => eq_refl)). }
    rewrite (Dhi H7). unfold wlit at 1. rewrite c_ltu_Z by lia.
    destruct (Z.ltb_spec 31 (sc - 7)) as [H38 | H38].
    { apply ts_bind_ret. exact (HK s A false None HII (ntframe_refl A s) (hrel_refl A) (fun _ => eq_refl)). }
    assert (Hmid : (sc < 7 \/ 38 < sc) -> False) by lia.
    set (i := sc - 7) in *. assert (Hi : cvalid (KBounce i)) by (cbn; lia). assert (Hiu : cvalid (KUseq i)) by (cbn; lia).
    apply ts_assoc. rewrite (addr_bounce_lock i) by lia.
    eapply (ts_lbu_ctxW_m A HW s (ms_mem s) [] (KBounce i)); [exact RW0 | exact HWIN | exact Hi | reflexivity | apply wfree_range_nil |].
    apply ts_assoc. rewrite (addr_useq_lock i) by lia.
    eapply (ts_lbu_ctxW_m A HW s (ms_mem s) [] (KUseq i)); [exact RW0 | exact HWIN | exact Hiu | reflexivity | apply wfree_range_nil |].
    pose proof (Z.mod_pos_bound (a_ctx A (KBounce i)) 256 ltac:(lia)) as Hb. set (b := a_ctx A (KBounce i) mod 256) in *.
    pose proof (Z.mod_pos_bound (a_ctx A (KUseq i)) 256 ltac:(lia)) as Hus. set (us := a_ctx A (KUseq i) mod 256) in *.
    apply ts_assoc.
    (* [comment removed for export] *)
    assert (STORE : forall (v : word) (K' : unit -> M R),
      (forall s1 A1, II sp0 argv envp cb D A1 s1 -> ntframe A s s1 -> hrel A A1 -> tsafe (K' tt s1) P) ->
      tsafe ((x <- m_sb (Z_to_bv 64 (caddr (KBounce i))) v ;; K' x) s) P).
    { intros v K' HK'. eapply (ts_sb_ctxW A s (ms_mem s) [] (KBounce i)); [exact RW0 | exact HWIN | exact Hi | reflexivity |].
      intros m1 RW1.
      destruct (heur_commit sp0 argv envp cb D A s _ m1 HII RW1) as (HII1 & NF1 & HR1).
      { intros w x [<- | []] Hx. cbn [f_a f_n] in Hx. exists (KBounce i). split; [exact Hi|]. split; [exact I | lia]. }
      exact (HK' _ _ HII1 NF1 HR1). }
    rewrite is0_Z by lia. destruct (Z.eqb_spec us 0) as [Eus | Nus].
    - apply ts_bind_ret. apply ts_bind_ret. exact (HK s A _ _ HII (ntframe_refl A s) (hrel_refl A) (fun Hc => False_ind _ (Hmid Hc))).
    - apply ts_assoc. rewrite (addr_lock 920), <- caddr_KSeq_lock.
      eapply (ts_lbu_ctxW_m A HW s (ms_mem s) [] KSeq); [exact RW0 | exact HWIN | exact I | reflexivity | apply wfree_range_nil |].
      destruct (c_lts (wlit 9) (v_sub (Z_to_bv 64 (a_ctx A KSeq mod 256)) (Z_to_bv 64 us))).
      + apply ts_bind_ret. apply ts_bind_ret. exact (HK s A _ _ HII (ntframe_refl A s) (hrel_refl A) (fun Hc => False_ind _ (Hmid Hc))).
      + destruct (c_ltu (Z_to_bv 64 b) (wlit 99)).
        * apply STORE. intros s1 A1 HII1 NF1 HR1. apply ts_bind_ret. exact (HK s1 A1 _ _ HII1 NF1 HR1 (fun Hc => False_ind _ (Hmid Hc))).
        * apply STORE. intros s1 A1 HII1 NF1 HR1. apply ts_bind_ret. exact (HK s1 A1 _ _ HII1 NF1 HR1 (fun Hc => False_ind _ (Hmid Hc))).
  Qed.
End Bounce.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Seq.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Theorem ag_seq_ok : forall s (m0 : word -> option byte) ws (sqv : Z) (K : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> 0 <= sqv < 256 ->
    (forall s1 (sq' : Z) (reset : bool), 1 <= sq' <= 256 ->
       RepW A m0 (reset_writes reset ++ ws) (ms_mem s1) -> WIN s1 -> ms_vm s1 = ms_vm s -> ms_lo s1 = ms_lo s -> ms_hi s1 = ms_hi s ->
       tsafe (K (Z_to_bv 64 sq') s1) P) ->
    tsafe ((x <- ag_seq (Z_to_bv 64 sqv) ;; K x) s) P.
  Proof.
    intros s m0 ws sqv K P RW HWIN Hsq HK. pose proof layout_nums as LN. ceil.
    unfold ag_seq. unfold wlit. rewrite c_eq_Z by lia.
    destruct (Z.eqb_spec sqv 255) as [E255 | N255].
    - apply ts_assoc. rewrite (addr_lock 856). replace (LOCKA + 856) with (CTX + 848) by (rewrite CTX_lock; lia). unfold m_sd at 1.
      eapply (ts_st_ctxrW A s m0 ws 8 (CTX + 848)); [exact RW | exact HWIN | rewrite CTX_lock; lia | unfold CTX_END; rewrite CTX_lock; cbn; lia |].
      intros m1 RW1. change (bv_unsigned w0) with 0 in RW1.
      apply ts_assoc. rewrite (addr_lock 864). replace (LOCKA + 864) with (CTX + 856) by (rewrite CTX_lock; lia). unfold m_sd at 1.
      eapply (ts_st_ctxrW A _ m0 _ 8 (CTX + 856)); [exact RW1 | exact HWIN | rewrite CTX_lock; lia | unfold CTX_END; rewrite CTX_lock; cbn; lia |].
      intros m2 RW2. change (bv_unsigned w0) with 0 in RW2.
      apply ts_assoc. rewrite (addr_lock 872). replace (LOCKA + 872) with (CTX + 864) by (rewrite CTX_lock; lia). unfold m_sd at 1.
      eapply (ts_st_ctxrW A _ m0 _ 8 (CTX + 864)); [exact RW2 | exact HWIN | rewrite CTX_lock; lia | unfold CTX_END; rewrite CTX_lock; cbn; lia |].
      intros m3 RW3. change (bv_unsigned w0) with 0 in RW3.
      apply ts_assoc. rewrite (addr_lock 880). replace (LOCKA + 880) with (CTX + 872) by (rewrite CTX_lock; lia). unfold m_sd at 1.
      eapply (ts_st_ctxrW A _ m0 _ 8 (CTX + 872)); [exact RW3 | exact HWIN | rewrite CTX_lock; lia | unfold CTX_END; rewrite CTX_lock; cbn; lia |].
      intros m4 RW4. change (bv_unsigned w0) with 0 in RW4. change (Z.of_nat 8) with 8 in RW4.
      apply ts_bind_ret.
      apply (HK (upd s m4 (ms_vm s)) 1 true ltac:(lia)); [exact RW4 | exact HWIN | reflexivity | reflexivity | reflexivity].
    - apply ts_bind_ret. rewrite v_addi_Z.
      apply (HK s (sqv + 1) false ltac:(lia)); [exact RW | exact HWIN | reflexivity | reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma seq_writes_slots : forall (sq' : Z) (reset : bool) w x,
    In w (FCT (caddr KSeq) 1 sq' :: reset_writes reset) -> f_a w <= x < f_a w + f_n w ->
    exists k, cvalid k /\ hslot1 k /\ x = caddr k.
  Proof.
    intros sq' reset w x [<- | Hin] Hx.
    - cbn [f_a f_n] in Hx. exists KSeq. split; [exact I|]. split; [exact I | lia].
    - unfold reset_writes in Hin. destruct reset; [| destruct Hin].
      assert (Hr : CTX + 848 <= x < CTX + 880).
      { destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [f_a f_n] in Hx; lia. }
      exists (KUseq (x - (CTX + 848))). rewrite caddr_KUseq. split; [unfold cvalid; lia|]. split; [exact I | lia].
  Qed.
End Seq.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Usage2.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Theorem ag_usage2_ok : forall s (sc usage : Z) (K : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> 0 <= sc < 48 -> 0 <= usage < 2^64 ->
    (forall c, 0 <= c < 48 -> 0 <= a_ctx A (KUsage c) < 2^64) ->
    (forall uv, 0 <= uv < 2^64 -> (31 < sc -> uv = usage) -> tsafe (K (Z_to_bv 64 uv) s) P) ->
    tsafe ((x <- ag_usage2 (Z_to_bv 64 sc) (Z_to_bv 64 usage) (Z_to_bv 64 (LOCKA + 8 * sc)) ;; K x) s) P.
  Proof.
    intros s sc usage K P HR HWIN Hsc Hus Hcu HK.
    unfold ag_usage2. unfold wlit. rewrite c_lts_Z by lia.
    destruct (Z.ltb_spec 31 sc) as [H31 | H31]; [apply ts_bind_ret; apply HK; lia|].
    rewrite v_andi_Z by lia. change 1 with (2^1 - 1) at 1. rewrite land_ones_low by lia. change (2^1) with 2.
    pose proof (Z.mod_pos_bound sc 2 ltac:(lia)). rewrite is0_Z by lia.
    destruct (Z.eqb_spec (sc mod 2) 0) as [Ev | Od]; cbn [negb]; [| apply ts_bind_ret; apply HK; lia].
    apply ts_assoc. rewrite at_Z. replace (LOCKA + 8 * sc + 480) with (caddr (KUsage (sc + 1))) by (rewrite caddr_KUsage_lock; lia).
    pose proof (Hcu (sc + 1) ltac:(lia)) as Hc1.
    eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KUsage (sc + 1))); [apply repw_init; [exact HW | exact HR] | exact HWIN | cbn; lia | reflexivity | apply wfree_range_nil |].
    apply ts_bind_ret. rewrite v_add_Z. rewrite <- ZZ_mod. apply HK; [apply Z.mod_pos_bound; lia | intros H31x; lia].
  Qed.
End Usage2.

End WithLayout.
