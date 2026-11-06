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
  MallocInv_wf4 MallocInv_wf6 MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_vmops MallocInv_coh MallocInv_usage MallocInv_ops MallocInv_sc MallocInv_sc2 MallocInv_sc3
  MallocInv_ameta_iface MallocInv_ameta5 MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_ntfm MallocInv_aspieces MallocInv_agrp_iface MallocInv_tav2 MallocInv_agm2 MallocSureCap.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma upd_eq : forall s1 s2 m h, ms_lo s2 = ms_lo s1 -> ms_hi s2 = ms_hi s1 -> upd s2 m h = upd s1 m h.
Proof. intros [m1 h1 lo1 hi1] [m2 h2 lo2 hi2] m h; cbn; intros -> ->; reflexivity. Qed.

Lemma FR_of_ntframe : forall A A' s s', ntframe A s s' -> (forall x, owned_of A x -> owned_of A' x) -> a_live A' = a_live A ->
  FR A s A' s'.
Proof.
  intros A A' s s' [L1 H1 V1 M1 P1 Q1] Ho Hl. constructor.
  - exact L1.
  - exact H1.
  - exact Ho.
  - intros a Hno _. apply M1. intros Hox. exact (Hno (Ho _ Hox)).
  - intros p n Hp. rewrite Hl. exact Hp.
  - exact P1.
  - exact Q1.
  - rewrite V1. reflexivity.
Qed.

(* [comment removed for export] *)
Definition chk_small7 : bool := forallb (fun sc => size_class sc <=? 7) (Zseq 0 7).
Lemma chk_small7_ok : chk_small7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma size_class_small7 : forall sc, 0 <= sc < 7 -> size_class sc <= 7.
Proof.
  intros sc Hsc. pose proof (proj1 (forallb_forall _ _) chk_small7_ok sc (Zseq_In 7 0 sc ltac:(llia))) as H.
  apply Z.leb_le in H. exact H.
Qed.

Lemma size_class_small7' : forall sc, 0 <= sc < 48 -> sc < 7 -> size_class sc <= 7.
Proof. intros sc Hsc H7. apply size_class_small7. lia. Qed.

(* [comment removed for export] *)
Lemma ts_lw_fact4 : forall {R : Type} A s a v (k : word -> M R) (P : R -> mstate -> Prop),
  WF A -> Rep A (ms_mem s) -> WIN s -> has A (FCT a 4 v) -> 0 <= v ->
  tsafe (k (w32 v) s) P ->
  tsafe ((x <- m_lw (Z_to_bv 64 a) ;; k x) s) P.
Proof.
  intros R A s a v k P HW HR HWIN Hf Hv Hk.
  destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
  destruct (rdn_of_mbytes (ms_mem s) 4 a (fun k => byte_of v k) ltac:(lia) ltac:(cbn; lia)) as (bs & Hbs & Hlen & Hnth).
  { intros j Hj. apply (rep_facts A (ms_mem s) HR). exists (FCT a 4 v). split; [exact Hf|]. unfold fbyte. cbn [f_a f_n f_v]. split; [lia|]. f_equal. lia. }
  eapply ts_lw; [apply acc_ok_heap; [exact HWIN | llia | llia | llia] | exact Hbs |].
  assert (Hval : bytes_le_to_Z bs = v mod 2 ^ 32).
  { replace (2 ^ 32) with (2 ^ (8 * Z.of_nat (length bs))) by (rewrite Hlen; reflexivity).
    apply bytes_le_to_Z_of_bytes; [exact Hv|]. intros j Hj. rewrite Hnth by lia. reflexivity. }
  rewrite (le_val_Z bs (v mod 2^32) Hval). rewrite v_lw_w32 by (pose proof (Z.mod_pos_bound v (2^32)); lia). rewrite w32_mod. exact Hk.
Qed.

(* [comment removed for export] *)
Definition zhide (z : Z) : Z := z.

(* [comment removed for export] *)
Lemma c_eq_u : forall (a : word) z, 0 <= z < 2^64 -> c_eq a (Z_to_bv 64 z) = (bv_unsigned a =? z).
Proof. intros a z Hz. rewrite <- (Z_to_bv_bv_unsigned 64 a) at 1. apply c_eq_Z; [apply u64_range | exact Hz]. Qed.

(* [comment removed for export] *)
Lemma ag_tail_facts : forall sc req cnt1 c2 c3 n2 n3 q,
  0 <= sc < 48 -> 1 <= size_class sc <= 8191 -> (sc < 7 -> size_class sc <= 7) ->
  0 <= req -> req + 4 <= 16 * size_class sc -> 1 <= cnt1 <= 32 -> 16 * size_class sc * cnt1 < 2^20 ->
  (cnt1 = 1 -> page_round_up_Z (16 * size_class sc + 16) = 16 * size_class sc + 16) ->
  1 <= c2 <= 32 -> 16 * size_class sc * c2 < 2^20 -> (c2 = 1 -> cnt1 = 1) ->
  n2 = page_round_up_Z (16 * size_class sc * c2 + 16) ->
  (c3 = c2 /\ n3 = n2 \/ c3 = 1 /\ n3 = page_round_up_Z (req + 20) /\ (n3 < 16 * size_class sc + 16 \/ 4 * 4096 <= n3)) ->
  q = 4080 / (16 * size_class sc) ->
  let aidx := Z.max (Z.min c3 q - 1) 0 in
  1 <= c3 <= 32 /\ 16 * size_class sc * c3 < 2^20 /\ (1 < c3 -> 16 * size_class sc * c3 + 16 <= n3) /\ (c3 = 1 -> req + 20 <= n3) /\
  0 <= aidx <= c3 - 1 /\ (c3 = 1 -> 256 <= size_class sc \/ n3 - 16 <= 16 * size_class sc) /\ (c3 = 1 -> n3 < 2^20 + 16) /\
  (aidx < c3 - 1 -> 7 <= sc) /\ 20 <= n3 < 2^21 /\ n3 mod 4096 = 0 /\ 0 <= q < 2^62.
Proof.
  intros sc req cnt1 c2 c3 n2 n3 q Hsc Hszc Hs7 Hreq Hreq4 Hc1 Hspan Hone Hc2 Hspan2 Hc21 En2 Hcase Eq aidx.
  assert (Hpos : 0 < 16 * size_class sc) by (clear - Hszc; lia).
  assert (Hq : 0 <= q < 2^62).
  { rewrite Eq. split; [apply Z.div_pos; [clear; lia | exact Hpos] | apply Z.div_lt_upper_bound; [exact Hpos | clear - Hszc; lia]]. }
  assert (Hq32 : size_class sc <= 7 -> 32 <= q).
  { intros H7. rewrite Eq. apply Z.div_le_lower_bound; [exact Hpos | clear - H7 Hszc; lia]. }
  clear Eq.
  destruct (page_round_up_Z_spec (16 * size_class sc * c2 + 16) ltac:(clear - Hszc Hc2; lia)) as [Hn2 Hn2m]. rewrite <- En2 in Hn2, Hn2m.
  destruct (page_round_up_Z_spec (req + 20) ltac:(clear - Hreq; lia)) as [Hr20 Hr20m].
  assert (Hn3m : n3 mod 4096 = 0) by (destruct Hcase as [(_ & ->) | (_ & -> & _)]; assumption).
  clear Hn2m Hr20m.
  assert (En2' : c2 = 1 -> n2 = 16 * size_class sc + 16).
  { intros E. rewrite En2, E, Z.mul_1_r. apply Hone. apply Hc21. exact E. }
  clear En2 Hone. set (r := page_round_up_Z (req + 20)) in *. clearbody r.
  assert (Hc3 : 1 <= c3 <= c2) by (destruct Hcase as [(-> & _) | (-> & _)]; clear - Hc2; lia).
  assert (Hsp3 : 16 * size_class sc * c3 < 2^20).
  { apply (Z.le_lt_trans _ (16 * size_class sc * c2)); [apply Z.mul_le_mono_nonneg_l; clear - Hc3 Hszc; lia | exact Hspan2]. }
  assert (Haidx : 0 <= aidx <= c3 - 1 /\ (aidx < c3 - 1 -> q < c3)) by (subst aidx; clear - Hc3 Hc2 Hq; lia).
  split; [clear - Hc3 Hc2; lia|]. split; [exact Hsp3|].
  split. { intros Hgt. destruct Hcase as [(-> & ->) | (E1 & _)]; [clear - Hn2; lia | clear - E1 Hgt; lia]. }
  split. { intros E1. destruct Hcase as [(Ec & ->) | (_ & -> & _)]; [rewrite (En2' ltac:(clear - Ec E1; lia)); clear - Hreq4; lia | exact (proj1 Hr20)]. }
  split; [exact (proj1 Haidx)|].
  split. { intros E1. destruct Hcase as [(Ec & ->) | (_ & -> & [Hlt | Hge])];
           [right; rewrite (En2' ltac:(clear - Ec E1; lia)); clear; lia | right; clear - Hlt; lia | left; clear - Hge Hr20 Hreq4 Hszc; lia]. }
  split. { intros E1. destruct Hcase as [(Ec & ->) | (_ & -> & _)]; [rewrite (En2' ltac:(clear - Ec E1; lia)); clear - Hszc; lia | clear - Hr20 Hreq4 Hszc; lia]. }
  split. { intros Hlt. destruct (Z.lt_ge_cases sc 7) as [H7 | H7]; [exfalso | exact H7].
           pose proof (Hq32 (Hs7 H7)) as Hq'. pose proof (proj2 Haidx Hlt) as Hqc. clear - Hq' Hqc Hc3 Hc2. lia. }
  split; [| split; [exact Hn3m | exact Hq]].
  destruct Hcase as [(_ & ->) | (_ & -> & _)]; [clear - Hn2 Hspan2 Hszc Hc2; lia | clear - Hr20 Hreq Hreq4 Hszc; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Hand.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (B : astate) (s1 : mstate).
  Variables (m : Z) (md : meta_rec) (L cv : Z).
  Hypothesis HII : II sp0 argv envp cb D B s1.
  Hypothesis Hm : a_meta B m = Some md.
  Hypothesis Hr : mt_role md = RDead.
  Hypothesis HL : 0 <= L.
  Hypothesis Hcv : 0 <= cv.

  Definition hd_ctx : ctx_rec := cupd (a_ctx B) KCtr cv.
  Definition hdA : astate := set_ctx (deadupd B m md FW32 L) hd_ctx.
  Definition hd_ws : list fct := [FCT (caddr KCtr) 4 cv; FCT (m + 32) 8 L].

  Lemma HWB : WF B. Proof. exact (is_wf _ _ _ _ _ _ (ii_is HII)). Qed.

  Lemma hd_ctx_heur : forall k, ctx_heur k \/ hd_ctx k = a_ctx (deadupd B m md FW32 L) k.
  Proof. intros k. unfold hd_ctx, cupd. destruct (cslot_eq_dec k KCtr) as [-> | Hne]; [left; exact I | right; reflexivity]. Qed.

  Lemma hd_ctx_nonneg : forall k, 0 <= hd_ctx k.
  Proof. intros k. unfold hd_ctx, cupd. destruct (cslot_eq_dec k KCtr); [lia | apply (wf_ctx_nonneg B HWB)]. Qed.

  Lemma WF_hdA : WF hdA.
  Proof. unfold hdA. apply WF_ctx_heur; [apply WF_deadupd; [exact HWB | exact Hm | exact Hr] | exact hd_ctx_heur | exact hd_ctx_nonneg]. Qed.

  Lemma hdA_meta_m : a_meta hdA m = Some (mupd md FW32 L).
  Proof. unfold hdA. cbn. apply du_meta_m. Qed.
  Lemma hdA_meta_other : forall x, x <> m -> a_meta hdA x = a_meta B x.
  Proof. intros x Hx. unfold hdA. cbn. apply du_meta_other. exact Hx. Qed.
  Lemma mupd_f : forall fl, mt_f (mupd md FW32 L) fl = if mfield_eq_dec fl FW32 then L else mt_f md fl.
  Proof. intros fl. unfold mupd. rewrite mt_f_MT. reflexivity. Qed.
  Lemma hdA_ctx : forall k, a_ctx hdA k = if cslot_eq_dec k KCtr then cv else a_ctx B k.
  Proof. intros k. reflexivity. Qed.
  Lemma dom_hdA : forall x, dom hdA x <-> dom B x.
  Proof. intros x. unfold hdA. rewrite (dom_set_ctx _ _ x). apply dom_deadupd; [exact Hm | exact Hr]. Qed.

  Lemma writes_ok_hd : writes_ok B hd_ws.
  Proof.
    unfold hd_ws. apply (writes_ok_ctx B _ KCtr cv HWB); [| exact I].
    apply (writes_ok_meta B [] m md 32 8 L HWB (writes_ok_nil B) Hm); lia.
  Qed.

  Lemma Rep_hdA : forall mm, RepW B (ms_mem s1) hd_ws mm -> Rep hdA mm.
  Proof.
    intros mm RW. pose proof HWB as HW. pose proof WF_hdA as HW'.
    pose proof (ctx_slot_range KCtr I) as (C1 & C2 & C3). cbn [clen] in C2, C3.
    pose proof (meta_facts B m md HW Hm) as (M1 & M2 & M3 & M4 & Mdom).
    pose proof ctx_block_rw as [CB1 CB2]. pose proof layout_nums as LN. unfold CTX_END in C2, CB2.
    assert (APART : m + 40 <= caddr KCtr \/ caddr KCtr + 4 <= m) by lia.
    apply (repw_commit2 B hdA (ms_mem s1) hd_ws mm HW' RW).
    - intros f Hf. unfold hdA in Hf.
      destruct (has_set_ctx (deadupd B m md FW32 L) hd_ctx f Hf) as [(k & Hk & ->) | [[Har _] | [(pg & Hpg & ->) | [Hmf | Hg]]]].
      + unfold hd_ctx, cupd. destruct (cslot_eq_dec k KCtr) as [-> | Hne].
        * right. cbn [f_a f_n clen]. intros x Hx. apply (wlook_cov_some hd_ws (FCT (caddr KCtr) 4 cv) x); [left; reflexivity | cbn [f_a f_n]; lia].
        * left. left. exists k. auto.
      + left. right; left. exact Har.
      + left. right; left. exists pg. unfold hd_ctx. rewrite cupd_other by discriminate. auto.
      + destruct Hmf as (x & mtx & fl & Hx & ->). cbn [a_meta deadupd ameta_upd set_meta] in Hx.
        destruct (Z.eq_dec x m) as [-> | Hne].
        * rewrite aupd_same in Hx. injection Hx as <-. rewrite mupd_f.
          destruct (mfield_eq_dec fl FW32) as [-> | Hnf].
          -- right. cbn [moff mlen f_a f_n]. intros y Hy. apply (wlook_cov_some hd_ws (FCT (m + 32) 8 L) y); [right; left; reflexivity | cbn [f_a f_n]; lia].
          -- left. right; right; left. exists m, md, fl. auto.
        * rewrite aupd_other in Hx by exact Hne. left. right; right; left. exists x, mtx, fl. auto.
      + left. right; right; right. destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & Hin). cbn [a_meta deadupd ameta_upd set_meta] in Hx.
        destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite aupd_same in Hx; injection Hx as <-; rewrite mupd_role, Hr in Hrx; discriminate|].
        rewrite aupd_other in Hx by exact Hne. exists x, mtx, aibx, slx. auto.
    - intros x b Hw. unfold hd_ws in Hw. destruct (wlook_some_cov _ _ _ Hw) as (w & [<- | [<- | []]] & Hxw); cbn [f_a f_n] in Hxw.
      + rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia). injection Hw as <-. cbn [f_v f_a].
        right; left. exists KCtr. split; [exact I|]. cbn [clen]. split; [lia|]. rewrite hdA_ctx. destruct (cslot_eq_dec KCtr KCtr); [reflexivity | contradiction].
      + rewrite wlook_skip in Hw by (cbn [f_a f_n]; lia). rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia). injection Hw as <-. cbn [f_v f_a].
        left. exists m, (mupd md FW32 L), FW32. split; [exact hdA_meta_m|]. cbn [moff mlen]. split; [lia|]. rewrite mupd_f.
        destruct (mfield_eq_dec FW32 FW32); [reflexivity | contradiction].
    - intros x Hx. exact (proj1 (dom_hdA x) Hx).
  Qed.

  Theorem hand_commit : forall mm, RepW B (ms_mem s1) hd_ws mm ->
    II sp0 argv envp cb D hdA (upd s1 mm (ms_vm s1)) /\ ntframe B s1 (upd s1 mm (ms_vm s1)).
  Proof.
    intros mm RW. pose proof HWB as HW. pose proof (ii_is HII) as HI.
    split; [| exact (ntframe_commit B s1 hd_ws mm HW RW writes_ok_hd)].
    apply II_intro.
    - exact (IS_commit sp0 argv envp cb B hdA s1 hd_ws mm HI RW writes_ok_hd WF_hdA (Rep_hdA mm RW)).
    - cbn [ms_vm upd]. unfold hdA. apply (VMok_ctx_heur _ hd_ctx hd_ctx_heur). apply VMok_deadupd; [exact Hm | exact Hr | exact (ii_vm HII)].
    - apply (AvOK_transfer B hdA (ii_av HII)); [reflexivity | reflexivity |].
      intros x mt' Hx Hrl. destruct (Z.eq_dec x m) as [-> | Hne].
      + rewrite hdA_meta_m in Hx. injection Hx as <-. rewrite mupd_role, Hr in Hrl. discriminate.
      + rewrite (hdA_meta_other x Hne) in Hx. exists mt'. auto.
    - apply (UsOK_transfer B hdA (ii_us HII)); [reflexivity | intros; reflexivity |].
      intros c x. unfold hdA. etransitivity; [| apply (meta_usage_deadupd B m md FW32 L Hm Hr c x)]. reflexivity.
    - apply (deads_transfer B hdA D (ii_dd HII)). intros x. destruct (Z.eq_dec x m) as [-> | Hne].
      + rewrite hdA_meta_m, Hm. split; intros _; [exists md; auto | exists (mupd md FW32 L); rewrite mupd_role; auto].
      + rewrite (hdA_meta_other x Hne). tauto.
  Qed.
End Hand.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ag_mmap_ok : ag_mmap_spec.
Proof.
  intros W R sp0 argv envp cb D A s sc req m usage size cnt1 md K P HII Hmd Hrd Hz HmD Hsc Hact0 -> Hreq Hreq4 Hus Hc1 Hspan Hbig Hone HKF HKO.
  pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG]. ceil.
  pose proof (size_class_bound sc Hsc) as Hszc. pose proof layout_nums as LN.
  assert (Hone' : cnt1 = 1 -> page_round_up_Z (16 * size_class sc + 16) = 16 * size_class sc + 16).
  { intros E. apply page_round_up_Z_aligned; [clear - Hszc; lia | exact (proj2 (Hone E))]. }
  clear Hone.
  rewrite as_mmap_eq.
  (* [comment removed for export] *)
  apply tsall_assoc.
  eapply (tw_lift W (ag_bounce (Z_to_bv 64 sc)) s
            (fun bn s1 => exists A1 (ns : bool) (o : option word), bn = (ns, o) /\ II sp0 argv envp cb (m :: D) A1 s1 /\ ntframe A s s1 /\ hrel A A1 /\
                                                            ((sc < 7 \/ 38 < sc) -> ns = false))).
  { intros K' P' HK'. apply (ag_bounce_ok sp0 argv envp cb (m :: D) A s HII sc Hsc). intros s1 A1 ns o HII1 NF1 HR1 Hns. apply HK'. exists A1, ns, o. auto. }
  intros bn s1 (A1 & ns & o & -> & HII1 & NF1 & HR1 & Hns). cbv beta iota.
  pose proof (ii_is HII1) as HI1. pose proof HI1 as [HW1 HRp1 _ HWIN1 _ _]. pose proof (repw_init A1 (ms_mem s1) HW1 HRp1) as RW1.
  (* [comment removed for export] *)
  apply tsall_assoc. rewrite (addr_lock 920), <- caddr_KSeq_lock.
  eapply (tw_det W _ s1 _ P (Z_to_bv 64 (a_ctx A1 KSeq mod 256)) s1).
  { intros K' P' HK'. eapply (ts_lbu_ctxW_m A1 HW1 s1 (ms_mem s1) [] KSeq); [exact RW1 | exact HWIN1 | exact I | reflexivity | apply wfree_range_nil | exact HK']. }
  pose proof (Z.mod_pos_bound (a_ctx A1 KSeq) 256 ltac:(clear; lia)) as Hsqv. set (sqv := a_ctx A1 KSeq mod 256) in *. clearbody sqv.
  apply tsall_assoc.
  eapply (tw_lift W (ag_seq (Z_to_bv 64 sqv)) s1
            (fun sq' s2 => exists (sqn : Z) (reset : bool), sq' = Z_to_bv 64 sqn /\ 1 <= sqn <= 256 /\
               RepW A1 (ms_mem s1) (reset_writes reset) (ms_mem s2) /\ WIN s2 /\ ms_vm s2 = ms_vm s1 /\ ms_lo s2 = ms_lo s1 /\ ms_hi s2 = ms_hi s1)).
  { intros K' P' HK'. apply (ag_seq_ok A1 s1 (ms_mem s1) [] sqv K' P' RW1 HWIN1 ltac:(clear - Hsqv; lia)).
    intros s2 sq' reset Hsq RW2 HWIN2 Hvm2 Hlo2 Hhi2. apply HK'. exists sq', reset. rewrite app_nil_r in RW2. auto 10. }
  intros sq' s2 (sqn & reset & -> & Hsqn & RW2 & HWIN2 & Hvm2 & Hlo2 & Hhi2).
  apply tsall_assoc.
  eapply (tw_lift W (m_sb (Z_to_bv 64 (caddr KSeq)) (Z_to_bv 64 sqn)) s2
            (fun _ s3 => exists A2, II sp0 argv envp cb (m :: D) A2 s3 /\ ntframe A s s3 /\ hrel A A2)).
  { intros K' P' HK'. eapply (ts_sb_ctxW A1 s2 (ms_mem s1) (reset_writes reset) KSeq); [exact RW2 | exact HWIN2 | exact I | reflexivity |].
    intros m3 RW3. rewrite uZ in RW3 by (clear - Hsqn; lia).
    destruct (heur_commit sp0 argv envp cb (m :: D) A1 s1 _ m3 HII1 RW3 (seq_writes_slots sqn reset)) as (HII2 & NF2 & HR2).
    rewrite (upd_eq s1 s2 m3 (ms_vm s2) Hlo2 Hhi2), Hvm2. apply HK'. eexists. split; [exact HII2|]. split; [exact (hrel_chain A A1 s s1 _ NF1 HR1 NF2) | exact (hrel_trans A A1 _ HR1 HR2)]. }
  intros x3 s3 (A2 & HII2 & NF2 & HR2). clear x3.
  pose proof (ii_is HII2) as HI2. pose proof HI2 as [HW2 HRp2 _ HWIN2' _ _].
  (* [comment removed for export] *)
  apply tsall_assoc.
  eapply (tw_lift W (ag_usage2 (Z_to_bv 64 sc) (Z_to_bv 64 usage) (Z_to_bv 64 (LOCKA + 8 * sc))) s3
            (fun x s4 => s4 = s3 /\ exists uv, 0 <= uv < 2^64 /\ (31 < sc -> uv = usage) /\ x = Z_to_bv 64 uv)).
  { intros K' P' HK'. apply (ag_usage2_ok A2 HW2 s3 sc usage K' P' HRp2 HWIN2' Hsc Hus).
    - intros c Hc. rewrite (ii_us HII2 c Hc). pose proof (usage_of_range A2 c HW2) as HU. clear - HU. lia.
    - intros uv Huv Huv31. apply HK'. eauto 6. }
  intros x4 s4 (-> & uv & Huv & Huv31 & ->).
  (* [comment removed for export] *)
  cbv zeta.
  destruct (cnt2_word sc (size_class sc) cnt1 (Z_to_bv 64 uv) ns Hsc Hszc Hc1) as (c2 & Hrel2 & E2). rewrite E2.
  assert (Hc2 : 1 <= c2 <= 32 /\ 16 * size_class sc * c2 < 2^20 /\ (c2 = 1 -> cnt1 = 1)).
  { clear - Hrel2 Hc1 Hspan Hszc. destruct Hrel2 as [-> | [(_ & _ & ->) | [(_ & _ & ->) | [(_ & _ & ->) | (_ & _ & ->)]]]]; lia. }
  destruct Hc2 as (Hc2 & Hspan2 & Hc21).
  rewrite v_mul_Z. rewrite (roundup_word16 (16 * size_class sc * c2)) by (clear - Hspan2 Hszc Hc2; lia).
  destruct (page_round_up_Z_spec (16 * size_class sc * c2 + 16) ltac:(clear - Hszc Hc2; lia)) as [Hn2 _]. set (n2 := page_round_up_Z (16 * size_class sc * c2 + 16)) in *.
  destruct (cn3_word ns c2 n2 req (size_class sc) (Z_to_bv 64 uv) Hc2 ltac:(clear - Hn2 Hspan2 Hszc Hc2; lia) ltac:(clear - Hreq Hreq4 Hszc; lia) Hszc) as (c3 & n3 & E3 & Hcn3). rewrite E3. cbv beta iota.
  remember (4080 / (16 * size_class sc)) as q eqn:Eq.
  destruct (ag_tail_facts sc req cnt1 c2 c3 n2 n3 q Hsc Hszc (size_class_small7' sc Hsc) Hreq Hreq4 Hc1 Hspan
              Hone' Hc2 Hspan2 Hc21 eq_refl Hcn3 Eq)
    as (Hc3 & Hsp3 & Tmulti & Tone & Taidx & Tsingle & Tlen & Tpartial & Hn3r & Hn3m & Hq).
  cbv zeta in Taidx, Tpartial.
  (* [comment removed for export] *)
  assert (Hcap : n3 <= grp_cap sc).
  { apply (ag_len_grp_cap sc req c2 n3 Hszc Hreq Hreq4 Hc2 Hspan2).
    destruct Hcn3 as [(_ & ->) | (_ & -> & _)]; [left; reflexivity | right; reflexivity]. }
  (* [comment removed for export] *)
  assert (Hlen : n3 <= 16 * size_class sc * c3 + 4111).
  { destruct (page_round_up_Z_spec (req + 20) ltac:(clear - Hreq; lia)) as [Hr20 _].
    destruct Hcn3 as [(-> & ->) | (-> & -> & _)]; [clear - Hn2; lia | clear - Hr20 Hreq4 Hszc; lia]. }
  clear Hcn3. change (page_aligned n3) in Hn3m. change (q = zhide (4080 / (16 * size_class sc))) in Eq.
  assert (HLu : u (Z_to_bv 64 n3) = n3) by (apply uZ; clear - Hn3r; lia).
  assert (HprZ : page_round_up_Z n3 = n3) by (apply page_round_up_Z_aligned; [clear - Hn3r; lia | unfold page_size; exact Hn3m]).
  assert (Hpr : page_round_up (Z_to_bv 64 n3) = Z_to_bv 64 n3) by (unfold page_round_up; rewrite HLu, HprZ; reflexivity).
  assert (Hvm3 : ms_vm s3 = ms_vm s) by exact (nf_vm A s s3 NF2).
  apply tsall_assoc.
  eapply tw_sys_mmap04; [rewrite HLu; clear - Hn3r; lia | rewrite HLu; clear - Hn3r; lia | |].
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    intros Hnone. assert (HWf : W <> WOk \/ forall a0, mmap_grant_ok MMrw (ms_vm s3) a0 (mm_len (Z_to_bv 64 n3)) = false) by (right; exact Hnone).
    eapply tw_set_errno; [exact HWIN2'|]. cbv beta.
    unfold MAP_FAILED at 1. rewrite wm1_eq, c_eq_Z by (clear; lia). rewrite Z.eqb_refl. cbv iota.
    set (se := upd s3 (errno_mem (ms_mem s3) ENOMEM) (ms_vm s3)).
    pose proof (II_errno sp0 argv envp cb (m :: D) A2 s3 ENOMEM HII2) as HIIe. fold se in HIIe.
    assert (Hm2 : a_meta A2 m = Some md) by (rewrite (hr_meta A A2 HR2 m); exact Hmd).
    unfold ag_fail. apply tsall_assoc.
    set (fl := a_freelist A2). set (Bf := fmA A2 m fl (hd m fl) (last fl m)).
    eapply (tw_lift W (m_free_meta_ag (at_ A_LOCK 24) (Z_to_bv 64 m)) se
              (fun _ s' => II sp0 argv envp cb D Bf s' /\ ntframe A2 se s')).
    { intros K' P' HK'. apply (ts_free_meta_ag sp0 argv envp cb D A2 se m md HIIe HmD Hm2 Hrd K' P'). intros s' HII' NF'. apply HK'. auto. }
    intros x5 s' [HII' NF']. clear x5. apply tw_bind_ret.
    pose proof (fmrel sp0 argv envp cb D A2 se m md HIIe Hm2 Hrd) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10). fold fl Bf in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10.
    pose proof (ii_is HII') as [HWf' _ _ _ _ _].
    apply (HKF s' Bf HII').
    + (* [comment removed for export] *)
      apply (FR_trans A s A2 s3); [| apply (FR_trans A2 s3 A2 se); [apply FR_errno; exact HW2 |]].
      * apply (FR_of_ntframe A A2 s s3 NF2); [| exact (hr_live A A2 HR2)]. intros x [Hc | Hd]; [left; exact Hc | right; apply (proj2 (hr_dom A A2 HR2 x)); exact Hd].
      * apply (FR_of_ntframe A2 Bf se s' NF'); [| exact F1]. intros x [Hc | Hd]; [left; exact Hc | right; apply (proj2 (F10 x)); exact Hd].
    + rewrite (nf_vm A2 se s' NF'). unfold se. cbn [ms_vm upd]. exact Hvm3.
    + (* [comment removed for export] *)
      pose proof HR2 as [L1 Ar1 Pg1 Mb1 Xm1 Fl1 Ac1 Bk1 M1 C1 D1].
      constructor; try congruence.
      * unfold Bf, fmA, MallocInv_wf3.A'. cbn. exact Bk1.
      * intros k Hk Hkf Hh. rewrite <- (C1 k Hk Hh).
        destruct k; try (apply F7; [exact Hkf | intros c; discriminate]).
        cbn in Hk. rewrite (wf_act_head Bf HWf' i Hk), (wf_act_head A2 HW2 i Hk), F6. reflexivity.
      * intros x mtx aibx slx Hx Hrx. rewrite <- (M1 x). exact (F9 x mtx aibx slx Hx Hrx).
      * intros x mt0 aib0 sl0 Hx Hrx. apply (F8 x mt0 aib0 sl0); [rewrite (M1 x); exact Hx | exact Hrx].
      * exists (fm_mt (hd m fl) (last fl m)). split; [apply (fmA_meta_g A2 m fl) | reflexivity].
      * intros x. rewrite (F10 x). apply D1.
      * intros x mt0 Hx Hr0 Hne. unfold Bf. rewrite (fmA_meta_other A2 m fl (hd m fl) (last fl m) x Hne). rewrite (M1 x), Hx. cbn [option_map].
        f_equal. apply (rl_nonfree A2 HW2 m fl (hd m fl) (last fl m) eq_refl eq_refl eq_refl x mt0); [rewrite (M1 x); exact Hx | rewrite Hr0; discriminate | exact Hne].
      * unfold Bf. rewrite (fmA_freelist A2 m fl (hd m fl) (last fl m)). unfold fl. rewrite Fl1. reflexivity.
    + (* [comment removed for export] *)
      intros HWk. destruct HWf as [HWf | Hall]; [exfalso; exact (HWf HWk)|].
      exists n3. split; [clear - Hn3r; lia|]. intros a. specialize (Hall a). unfold mm_len in Hall. rewrite HLu, HprZ, Hvm3 in Hall. exact Hall.
    + (* [comment removed for export] *)
      intros _. exists n3. split; [clear - Hn3r Hcap; lia|]. split; [exact Hn3m|].
      intros a. specialize (Hnone a). unfold mm_len in Hnone. rewrite HLu, HprZ, Hvm3 in Hnone. exact Hnone.
  - (* [comment removed for export] *)
    intros HWs a Hg. cbn [mmap_grant_ok] in Hg. unfold mm_len in Hg. rewrite HLu in Hg.
    pose proof (VMok_core A2 _ (ii_vm HII2)) as HVc2.
    destruct (mmap_grant_facts sp0 argv envp cb A2 s3 a (Z_to_bv 64 n3) HI2 HVc2 ltac:(rewrite HLu; clear - Hn3r; lia) ltac:(rewrite HLu; clear - Hn3r; lia) ltac:(rewrite HLu; exact Hg))
      as (EnZ & _ & G1 & Glo & Gce & Gimg & Gm & Gna & Gdom & Gdisj & _).
    destruct (mmap_rw_ok sp0 argv envp cb A2 s3 a (Z_to_bv 64 n3) HI2 (ii_vm HII2) ltac:(rewrite HLu; clear - Hn3r; lia) ltac:(rewrite HLu; clear - Hn3r; lia) ltac:(rewrite HLu; exact Hg)) as [HI3 HV3].
    rewrite HLu, HprZ in *. rewrite Hpr in *.
    pose proof (u64_range a) as Ha. set (p := u a) in *. change (page_aligned p) in G1.
    set (A3 := xadd A2 p n3) in *. set (sg := upd s3 (zfill a (Z_to_bv 64 n3) (ms_mem s3)) (vm_mmap a (Z_to_bv 64 n3) (ms_vm s3))) in *.
    assert (HII3 : II sp0 argv envp cb (m :: D) A3 sg).
    { apply II_intro; [exact HI3 | exact HV3 | | |].
      - apply (AvOK_transfer A2 A3 (ii_av HII2)); [reflexivity | reflexivity | intros x mt' Hx Hrl; exists mt'; split; [exact Hx | exact Hrl]].
      - apply (UsOK_transfer A2 A3 (ii_us HII2)); [reflexivity | intros; reflexivity | intros; reflexivity].
      - apply (deads_transfer A2 A3 (m :: D) (ii_dd HII2)). intros x. unfold A3, xadd, set_xmaps. cbn [a_meta]. tauto. }
    pose proof (ii_is HII3) as HI3'. pose proof HI3' as [HW3 HRp3 _ HWIN3 _ _]. pose proof (repw_init A3 (ms_mem sg) HW3 HRp3) as RW30.
    assert (Hm3 : a_meta A3 m = Some md) by (unfold A3, xadd, set_xmaps; cbn [a_meta]; rewrite (hr_meta A A2 HR2 m); exact Hmd).
    assert (Hdom3 : forall x, dom A3 x <-> dom A x) by (intros x; unfold A3, xadd, set_xmaps, dom; cbn [a_areas a_meta a_pages]; apply (hr_dom A A2 HR2 x)).
    assert (Hown3 : forall x, owned_of A3 x <-> owned_of A x) by (intros x; unfold owned_of; rewrite (Hdom3 x); tauto).
    assert (NOWN : forall x, p <= x < p + n3 -> ~ owned_of A3 x).
    { intros x Hx [Hc | Hd]; [pose proof ctx_block_rw as CB; clear - CB Hc Hx Gimg LN; unfold CTX_END in *; lia | exact (proj1 (Gdom x Hx) Hd)]. }
    cbv beta. rewrite wm1_eq, (c_eq_u a (2^64 - 1)) by (clear; lia). fold p.
    replace (p =? 2^64 - 1) with false by (symmetry; apply Z.eqb_neq; clear - Gce Hn3r LN; lia). cbv iota.
    unfold ag_ok. cbv zeta.
    (* [comment removed for export] *)
    apply tsall_assoc. rewrite at_Z. change (m + 32) with (m + moff FW32).
    eapply (tw_det W _ sg _ P (Z_to_bv 64 (mt_f md FW32)) sg).
    { intros K' P' HK'. eapply (ts_ld_metaW A3 HW3 sg (ms_mem sg) [] m md FW32); [exact RW30 | exact HWIN3 | exact Hm3 | reflexivity | apply wfree_range_nil | rewrite (Hz FW32); clear; lia | exact HK']. }
    rewrite (Hz FW32).
    (* [comment removed for export] *)
    apply tsall_assoc. rewrite (addr_lock 20), <- caddr_KCtr_lock.
    pose proof (wf_ctx_nonneg A3 HW3 KCtr) as Hctr0. set (cv0 := a_ctx A3 KCtr) in *.
    eapply (tw_det W _ sg _ P (w32 cv0) sg).
    { intros K' P' HK'. apply (ts_lw_fact4 A3 sg (caddr KCtr) cv0 K' P' HW3 HRp3 HWIN3); [left; exists KCtr; split; [exact I | reflexivity] | exact Hctr0 | exact HK']. }
    (* [comment removed for export] *)
    apply tsall_assoc. rewrite (maplen_word n3 ltac:(clear - Hn3r; lia) Hn3m).
    eapply (tw_lift W (m_sd (Z_to_bv 64 (m + moff FW32)) (Z_to_bv 64 n3)) sg (fun _ s5 => exists m5, s5 = upd sg m5 (ms_vm sg) /\ RepW A3 (ms_mem sg) [FCT (m + 32) 8 n3] m5)).
    { intros K' P' HK'. eapply (ts_sd_metaW A3 HW3 sg (ms_mem sg) [] m md (moff FW32)); [exact RW30 | exact HWIN3 | exact Hm3 | cbn; clear; lia | cbn; clear; lia |].
      intros m5 RW5. rewrite uZ in RW5 by (clear - Hn3r; lia). apply HK'. exists m5. auto. }
    intros x6 s5 (m5 & -> & RW5). clear x6.
    (* [comment removed for export] *)
    apply tsall_assoc. unfold m_sw at 1.
    set (cvw := v_addi (w32 cv0) 1). pose proof (u64_range cvw) as Hcvw.
    eapply (tw_lift W (m_st 4 (Z_to_bv 64 (caddr KCtr)) cvw) (upd sg m5 (ms_vm sg)) (fun _ s6 => exists m6, s6 = upd sg m6 (ms_vm sg) /\ RepW A3 (ms_mem sg) (hd_ws m n3 (u cvw)) m6)).
    { intros K' P' HK'. eapply (ts_st_ctxrW A3 _ (ms_mem sg) _ 4 (caddr KCtr)); [exact RW5 | apply WIN_upd; exact HWIN3 | rewrite caddr_KCtr_lock, CTX_lock; clear; lia | rewrite caddr_KCtr_lock; unfold CTX_END; cbn; clear; lia |].
      intros m6 RW6. apply HK'. exists m6. split; [reflexivity|]. exact RW6. }
    intros x7 s6 (m6 & -> & RW6). clear x7.
    (* [comment removed for export] *)
    destruct (hand_commit sp0 argv envp cb (m :: D) A3 sg m md n3 (u cvw) HII3 Hm3 Hrd (proj1 Hcvw) m6 RW6) as [HII4 NF4].
    set (A4 := hdA A3 m md n3 (u cvw)) in *. set (st := upd sg m6 (ms_vm sg)) in *.
    (* [comment removed for export] *)
    unfold zhide in Eq. rewrite (aimax_word (size_class sc) Hszc), <- Eq. clear Eq.
    pose proof (aidx_word c3 q ltac:(clear - Hc3; lia) Hq) as Haidx. cbv zeta in Haidx. rewrite Haidx.
    set (aidx := Z.max (Z.min c3 q - 1) 0) in *.
    replace a with (Z_to_bv 64 p) by (subst p; apply Z_to_bv_bv_unsigned).
    assert (Ea : a = Z_to_bv 64 p) by (subst p; symmetry; apply Z_to_bv_bv_unsigned).
    (* [comment removed for export] *)
    assert (MEMst : forall a0 : word, ~ owned_of A3 (u a0) -> ms_mem st a0 = zfill a (Z_to_bv 64 n3) (ms_mem s3) a0).
    { intros a0 Ha0. rewrite (nf_mem A3 sg st NF4 a0 Ha0). unfold sg. cbn [ms_mem upd]. reflexivity. }
    assert (ZOUT : forall a0 : word, ~ (p <= u a0 < p + n3) -> zfill a (Z_to_bv 64 n3) (ms_mem s3) a0 = ms_mem s3 a0).
    { intros a0 Ha0. apply zfill_out. rewrite HLu. fold p.
      destruct (Z.lt_ge_cases (u a0) p) as [H1 | H1]; [left; exact H1 | right].
      destruct (Z.lt_ge_cases (u a0) (p + n3)) as [H2 | H2]; [exfalso; apply Ha0; split; assumption | exact H2]. }
    assert (ZIN : forall a0 : word, p <= u a0 < p + n3 -> zfill a (Z_to_bv 64 n3) (ms_mem s3) a0 = Some (Z_to_bv 8 0)).
    { intros a0 Ha0. apply zfill_in. rewrite HLu. exact Ha0. }
    assert (LIVEOUT : forall q0 n (a0 : word), a_live A q0 = Some n -> q0 <= u a0 < q0 + n -> ~ (p <= u a0 < p + n3)).
    { intros q0 n a0 Hq0 Hin Hx. exact (proj1 (Gdom (u a0) Hx) (proj2 (hr_dom A A2 HR2 (u a0)) (live_dom A q0 n (u a0) HW Hq0 Hin))). }
    pose proof HR2 as [L1 Ar1 Pg1 Mb1 Xm1 Fl1 Ac1 Bk1 M1 C1 D1].
    (* [comment removed for export] *)
    apply (HKO st A4 p n3 c3 aidx HII4).
    + (* [comment removed for export] *) constructor.
      * unfold st, sg. cbn [ms_lo upd]. exact (nf_lo A s s3 NF2).
      * unfold st, sg. cbn [ms_hi upd]. exact (nf_hi A s s3 NF2).
      * unfold st, sg. cbn [ms_vm upd]. rewrite Ea, Hvm3. reflexivity.
      * intros a0 Hno Hout. rewrite (MEMst a0) by (intros Ho; exact (Hno (proj1 (Hown3 _) Ho))).
        rewrite (ZOUT a0 Hout). exact (nf_mem A s s3 NF2 a0 Hno).
      * intros q0 n a0 Hq0 Hin.
        rewrite (nf_live A3 sg st NF4 q0 n a0); [| unfold A3, xadd, set_xmaps; cbn [a_live]; rewrite L1; exact Hq0 | exact Hin].
        unfold sg. cbn [ms_mem upd]. rewrite (ZOUT a0 (LIVEOUT q0 n a0 Hq0 Hin)). exact (nf_live A s s3 NF2 q0 n a0 Hq0 Hin).
      * intros a0 Ha0. apply (nf_mapped A3 sg st NF4 a0). unfold sg. cbn [ms_mem upd].
        destruct (Z.lt_ge_cases (u a0) p) as [H1 | H1]; [rewrite ZOUT by (intros [X _]; clear - X H1; lia); exact (nf_mapped A s s3 NF2 a0 Ha0)|].
        destruct (Z.lt_ge_cases (u a0) (p + n3)) as [H2 | H2]; [rewrite ZIN by (split; assumption); discriminate|].
        rewrite ZOUT by (intros [_ X]; clear - X H2; lia). exact (nf_mapped A s s3 NF2 a0 Ha0).
    + (* [comment removed for export] *)
      constructor.
      * unfold A4, hdA, A3, xadd. cbn [a_live set_ctx deadupd ameta_upd set_meta set_xmaps]. exact L1.
      * unfold A4, hdA, A3, xadd. cbn [a_areas set_ctx deadupd ameta_upd set_meta set_xmaps]. exact Ar1.
      * unfold A4, hdA, A3, xadd. cbn [a_pages set_ctx deadupd ameta_upd set_meta set_xmaps]. exact Pg1.
      * unfold A4, hdA, A3, xadd. cbn [a_mblocks set_ctx deadupd ameta_upd set_meta set_xmaps]. exact Mb1.
      * unfold A4, hdA, A3, xadd. cbn [a_freelist set_ctx deadupd ameta_upd set_meta set_xmaps]. exact Fl1.
      * unfold A4, hdA, A3, xadd. cbn [a_active set_ctx deadupd ameta_upd set_meta set_xmaps]. exact Ac1.
      * unfold A4, hdA, A3, xadd. cbn [a_brk_lo set_ctx deadupd ameta_upd set_meta set_xmaps]. exact Bk1.
      * unfold A4, hdA, A3, xadd. cbn [a_xmaps set_ctx deadupd ameta_upd set_meta set_xmaps]. rewrite Xm1. reflexivity.
      * intros k Hk Hh. unfold A4. rewrite (hdA_ctx A3 m md n3 (u cvw) k). destruct (cslot_eq_dec k KCtr) as [-> | Hne]; [exfalso; exact (Hh I)|].
        unfold A3, xadd. cbn [a_ctx set_xmaps]. exact (C1 k Hk Hh).
      * intros x Hx. unfold A4. rewrite (hdA_meta_other A3 m md n3 (u cvw) x Hx). unfold A3, xadd. cbn [a_meta set_xmaps]. apply M1.
      * exists (mupd md FW32 n3). unfold A4. rewrite (hdA_meta_m A3 m md n3 (u cvw)). split; [reflexivity|]. split; [rewrite mupd_role; exact Hrd|].
        rewrite !(mupd_f md n3). split; [destruct (mfield_eq_dec FW32 FW32); [reflexivity | contradiction]|].
        intros fl Hfl. rewrite (mupd_f md n3). destruct (mfield_eq_dec fl FW32) as [-> | _]; [exfalso; exact (Hfl eq_refl) | apply Hz].
      * intros x. rewrite <- (Hdom3 x). unfold A4. apply (dom_hdA A3 m md n3 (u cvw) Hm3 Hrd).
    + exact G1.
    + unfold heap_range. fold p in Glo, Gce, Gimg. repeat split; [exact Glo | clear - Hn3r; lia | exact Gce | exact Gimg].
    + clear - Hn3r; lia.
    + exact Hn3m.
    + unfold st, sg. cbn [ms_vm upd vm_maps vm_mmap]. left. rewrite Ea. reflexivity.
    + unfold st, sg. cbn [ms_vm upd vm_noaccess vm_mmap]. rewrite <- Ea. exact Gna.
    + intros x Hx Hd. apply (proj1 (Gdom x Hx)). apply (proj2 (hr_dom A A2 HR2 x)). apply (proj1 (Hdom3 x)). exact (proj1 (dom_hdA A3 m md n3 (u cvw) Hm3 Hrd x) Hd).
    + intros a0 Ha0. rewrite (MEMst a0) by (apply NOWN; exact Ha0). exact (ZIN a0 Ha0).
    + clear - Hc3; lia.
    + exact Hsp3.
    + exact Tmulti.
    + exact Tone.
    + exact Taidx.
    + exact Tsingle.
    + exact Tlen.
    + exact Tpartial.
    + intros HWf. exact (HWs HWf).
    + intros a0 Ha0. rewrite <- (nf_mem A s s3 NF2 a0) by (intros Ho; exact (NOWN (u a0) Ha0 (proj2 (Hown3 _) Ho))).
      rewrite <- (Z_to_bv_bv_unsigned 64 a0). exact (proj2 (Gdom (u a0) Ha0)).
    + exists ns, uv, c2. split; [exact Hns|]. split; [exact Huv31|]. split; [exact Huv|]. split; [exact Hc2|]. split; [exact E2 | exact E3].
    + (* [comment removed for export] *) clear - Hn3r; lia.
    + (* [comment removed for export] *) exact Hcap.
    + (* [comment removed for export] *) exact Hlen.
Qed.


End WithLayout.
