(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_wf6 MallocInv_wf7 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm
  MallocInv_coh MallocInv_ops MallocInv_usage MallocInv_free MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_ntq
  MallocInv_nt1 MallocInv_aspieces MallocInv_agtail.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.
Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wlook_free_inv : forall ws x, wlook ws x = None -> wfree ws x.
Proof using Type. pu_keep tt.
  induction ws as [|w ws IH]; intros x H; [apply wfree_nil|].
  cbn [wlook] in H. destruct (wcov w x) eqn:E; [discriminate H|].
  apply wfree_cons; [exact (wcov_false w x E) | exact (IH x H)].
Qed.

(* [comment removed for export] *)
Lemma fact_at_hdr : forall A, WF A -> forall f ma mt aib slots hf x,
  has A f -> a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  In hf (grp_hdr_fields ma mt aib) ->
  f_a f <= x < f_a f + f_n f -> f_a hf <= x < f_a hf + f_n hf -> f = hf.
Proof using MLok. pu_keep (MLok).
  intros A HW f ma mt aib slots hf x Hf Hma Hr Hhf Hx Hhx.
  pose proof (wf_grp A HW ma mt aib slots Hma Hr) as (Hw & _ & Hsc & Hlen & _).
  pose proof (stride_ge16 mt ltac:(lia) Hsc) as S16. pose proof (w_last_range (mt_w32 mt)) as WL.
  assert (Hhdr : forall g, In g (grp_hdr_fields ma mt aib) -> (g = FCT (mt_mem mt) 8 ma \/ g = FCT (mt_mem mt + 8) 1 aib)).
  { intros g Hg. cbn in Hg. destruct Hg as [<- | [<- | []]]; auto. }
  assert (Hext : gext_lo mt = mt_mem mt /\ mt_mem mt + 28 <= gext_hi mt).
  { unfold gext_lo, gext_hi, mt_cnt, mt_last in *. split; [reflexivity|]. assert (16 <= (w_last (mt_w32 mt) + 1) * mt_stride mt) by nia. lia. }
  destruct Hext as [Elo Ehi].
  assert (Hx9 : mt_mem mt <= x < mt_mem mt + 9) by (destruct (Hhdr hf Hhf) as [-> | ->]; cbn in Hhx; lia).
  destruct (fact_locate A HW ma mt aib slots Hma Hr f Hf) as [(fl & ->) | [Hin | [(j & st & Hj & Hin) | [(j & ch & Hj & Hlo & Hhi) | [Hmeta Hclear]]]]].
  - exfalso. cbn in Hx. pose proof (mfield_range fl). pose proof (meta_clear_of_gext A HW ma mt aib slots Hma Hr). unfold gext_lo, gext_hi in *. lia.
  - destruct (Hhdr f Hin) as [-> | ->]; destruct (Hhdr hf Hhf) as [-> | ->]; try reflexivity; cbn in Hx, Hhx; lia.
  - exfalso. pose proof (slot_fields_where A HW ma mt aib slots j st f Hma Hr Hj Hin) as [W1 W2].
    assert (Hjc : Z.of_nat j + 1 <= mt_cnt mt) by (pose proof (proj1 (nth_error_Some slots j) ltac:(rewrite Hj; discriminate)); lia).
    destruct (slot_in_ext mt (Z.of_nat j) ltac:(lia) Hjc ltac:(lia)) as [E1 E2]. unfold gext_lo in E1. lia.
  - exfalso. assert (Hjc : Z.of_nat j + 1 <= mt_cnt mt) by (pose proof (proj1 (nth_error_Some slots j) ltac:(rewrite Hj; discriminate)); lia).
    destruct (slot_in_ext mt (Z.of_nat j) ltac:(lia) Hjc ltac:(lia)) as [E1 E2]. unfold gext_lo in E1. lia.
  - exfalso. rewrite Elo in Hclear. lia.
Qed.

(* [comment removed for export] *)
Lemma repw_commit3 : forall A A' m0 ws m,
  WF A' -> RepW A m0 ws m ->
  (forall f, has A' f ->
     has A f \/ (forall x, f_a f <= x < f_a f + f_n f -> wlook ws x <> None) \/
     (forall x, f_a f <= x < f_a f + f_n f -> wlook ws x = None /\ mbyte m0 x = Some (byte_of (f_v f) (x - f_a f)))) ->
  (forall x b, wlook ws x = Some b ->
      (exists y mt fl, a_meta A' y = Some mt /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mt fl) (x - (y + moff fl))) \/
      (exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (a_ctx A' k) (x - caddr k)) \/
      (exists y mt aib sl hf, a_meta A' y = Some mt /\ mt_role mt = RGroup aib sl /\ In hf (grp_hdr_fields y mt aib) /\
          f_a hf <= x < f_a hf + f_n hf /\ b = byte_of (f_v hf) (x - f_a hf)) \/
      (forall f, has A' f -> ~ (f_a f <= x < f_a f + f_n f))) ->
  (forall x, dom A' x -> dom A x \/ (0 <= x < 2^64 /\ m0 (Z_to_bv 64 x) <> None)) ->
  Rep A' m.
Proof using MLok. pu_keep (MLok).
  intros A A' m0 ws m HW' RW Hf Hw Hd. constructor.
  - intros x b (f & Hfa & [Hx ->]). destruct (wlook ws x) as [b'|] eqn:E.
    + replace (byte_of (f_v f) (x - f_a f)) with b'; [exact (rw_wr A m0 ws m RW x b' E)|].
      destruct (Hw x b' E) as [(y & mt & fl & Hy & Hr & ->) | [(k & Hk & Hr & ->) | [(y & mt & aib & sl & hf & Hy & Hry & Hhf & Hr & ->) | Hno]]].
      * rewrite (fact_at_meta A' HW' f y mt fl x Hfa Hy Hx Hr). reflexivity.
      * rewrite (fact_at_ctx A' HW' f k x Hfa Hk Hx Hr). reflexivity.
      * rewrite (fact_at_hdr A' HW' f y mt aib sl hf x Hfa Hy Hry Hhf Hx Hr). reflexivity.
      * exfalso. exact (Hno f Hfa Hx).
    + destruct (Hf f Hfa) as [Ho | [Hc | Hz]].
      * apply (rw_fact A m0 ws m RW x _ E). exists f. split; [exact Ho | split; [exact Hx | reflexivity]].
      * exfalso. exact (Hc x Hx E).
      * destruct (Hz x Hx) as [_ Hb]. rewrite <- Hb. apply mbyte_ext. apply (rw_frame A m0 ws m RW).
        pose proof (facts_addr64 A' HW' x (byte_of (f_v f) (x - f_a f)) ltac:(exists f; split; [exact Hfa | split; [exact Hx | reflexivity]])) as Hx64.
        rewrite uZ by lia. exact (wlook_free_inv ws x E).
  - intros x Hx. destruct (Hd x Hx) as [Ho | [Hr Hm0]]; [exact (rw_dom A m0 ws m RW x Ho)|].
    apply (rw_mapped A m0 ws m RW). exact Hm0.
Qed.

(* [comment removed for export] *)
Lemma wlook_some_of_in : forall ws w x, In w ws -> f_a w <= x < f_a w + f_n w -> wlook ws x <> None.
Proof using Type. pu_keep tt.
  intros ws. induction ws as [|w0 ws IH]; intros w x Hin Hx; [destruct Hin|].
  cbn [wlook]. destruct (wcov w0 x) eqn:E; [discriminate|].
  destruct Hin as [<- | Hin]; [apply wcov_spec in Hx; rewrite Hx in E; discriminate E|]. exact (IH w x Hin Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RootTail.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A1 : astate) (s1 : mstate).
  Variables (sc req m : Z) (md : meta_rec) (p L cnt aidx : Z) (xs : list (Z * Z)).
  Hypothesis HII : II sp0 argv envp cb (m :: D) A1 s1.
  Hypothesis Hm : a_meta A1 m = Some md.
  Hypothesis Hr : mt_role md = RDead.
  Hypothesis HmdW : mt_f md FW32 = L.
  Hypothesis Hmd0 : forall fl, fl <> FW32 -> mt_f md fl = 0.
  Hypothesis HmD : ~ In m D.
  Hypothesis Hxm : a_xmaps A1 = (p, L) :: xs.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A1 sc = [].
  Hypothesis Hpal : page_aligned p.
  Hypothesis Hhr : heap_range p (p + L).
  Hypothesis HL : 0 < L.
  Hypothesis HLm : L mod 4096 = 0.
  Hypothesis Hin : In (Z_to_bv 64 p, Z_to_bv 64 L) (vm_maps (ms_vm s1)).
  Hypothesis Hrf : region_free (vm_noaccess (ms_vm s1)) (Z_to_bv 64 p) (Z_to_bv 64 L) = true.
  Hypothesis Hnodom : forall x, p <= x < p + L -> ~ dom A1 x.
  Hypothesis Hzero : forall a : word, p <= u a < p + L -> ms_mem s1 a = Some (Z_to_bv 8 0).
  Hypothesis Hcnt : 1 <= cnt <= 32.
  Hypothesis Hspan : 16 * size_class sc * cnt < 2^20.
  Hypothesis Hfit : 1 < cnt -> 16 * size_class sc * cnt + 16 <= L.
  Hypothesis Hreq : cnt = 1 -> req + 20 <= L.
  Hypothesis Hreq0 : 0 <= req.
  Hypothesis Haidx : 0 <= aidx <= cnt - 1.
  Hypothesis Hsingle : cnt = 1 -> 256 <= size_class sc \/ L - 16 <= 16 * size_class sc.
  Hypothesis Hs20 : cnt = 1 -> L < 2^20 + 16.
  Hypothesis Hpsc : aidx < cnt - 1 -> 7 <= sc.

  Let HW1 : WF A1 := is_wf _ _ _ _ _ _ (ii_is HII).

  (* [comment removed for export] *)
  Definition rc2 : ctx_rec := cupd (a_ctx A1) (KUsage sc) (a_ctx A1 (KUsage sc) + cnt).
  Definition rA2 : astate := set_ctx A1 rc2.
  (* [comment removed for export] *)
  Definition rmd3 : meta_rec := MT (ir_f p L cnt aidx sc) RDead.
  Definition rA3 : astate := ameta_upd rA2 m rmd3.
  (* [comment removed for export] *)
  Definition rA4 (ab : Z) : astate := instR rA3 m p L cnt aidx sc ab xs.
  Definition rootA (ab : Z) : astate := queA (rA4 ab) sc m [] m m.

  Lemma L47 : L < 2^47. Proof using Hcnt Hhr Hs20 Hsc MLok. pu_keep (Hcnt, Hhr, Hs20, Hsc, MLok). unfold heap_range in Hhr. pose proof layout_small. lia. Qed.
  Lemma usage_now : a_ctx A1 (KUsage sc) = usage_of A1 sc /\ 0 <= usage_of A1 sc < 2^47.
  Proof using HW1 Hsc. pu_keep (HW1, Hsc). split; [exact (ii_us HII sc Hsc) | exact (usage_of_range A1 sc HW1)]. Qed.
  Lemma act0 : a_ctx A1 (KActive sc) = 0.
  Proof using HW1 Hact Hsc. pu_keep (HW1, Hact, Hsc). rewrite (wf_act_head A1 HW1 sc Hsc), Hact. reflexivity. Qed.
  Lemma p_m_apart : p + L <= m \/ m + 40 <= p.
  Proof using HL HW1 Hcnt Hm Hnodom Hsc. pu_keep (HL, HW1, Hcnt, Hm, Hnodom, Hsc).
    pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3 & M4 & Mdom).
    destruct (Z.lt_ge_cases m (p + L)) as [H1 | H1]; [| left; lia]. destruct (Z.lt_ge_cases p (m + 40)) as [H2|H2]; [| right; lia]. exfalso.
    destruct (Z.lt_ge_cases m p) as [H3 | H3].
    - apply (Hnodom p ltac:(lia)). replace p with (m + (p - m)) by lia. apply Mdom. lia.
    - apply (Hnodom m ltac:(lia)). replace m with (m + 0) by lia. apply Mdom. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rc2_heur : forall k, ctx_heur k \/ rc2 k = a_ctx A1 k.
  Proof using Type. pu_keep tt. intros k. unfold rc2, cupd. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hne]; [left; exact I | right; reflexivity]. Qed.
  Lemma rc2_nn : forall k, 0 <= rc2 k.
  Proof using HL HW1 Haidx Hcnt Hsc. pu_keep (HL, HW1, Haidx, Hcnt, Hsc). intros k. unfold rc2, cupd. pose proof (wf_ctx_nonneg A1 HW1 k). pose proof (wf_ctx_nonneg A1 HW1 (KUsage sc)). destruct (cslot_eq_dec k (KUsage sc)); lia. Qed.
  Lemma WF2 : WF rA2. Proof using HL HW1 Haidx Hcnt Hsc. pu_keep (HL, HW1, Haidx, Hcnt, Hsc). exact (WF_ctx_heur A1 HW1 rc2 rc2_heur rc2_nn). Qed.
  Lemma VMok2 : forall h, VMok A1 h -> VMok rA2 h. Proof using Type. pu_keep tt. intros h Hv. exact (VMok_ctx_heur A1 rc2 rc2_heur h Hv). Qed.
  Lemma rA2_meta : a_meta rA2 = a_meta A1. Proof using Type. pu_keep tt. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rA3_meta : forall x, a_meta rA3 x = if Z.eq_dec x m then Some rmd3 else a_meta A1 x.
  Proof using Type. pu_keep tt. intros x. reflexivity. Qed.
  Lemma rA3_m : a_meta rA3 m = Some rmd3.
  Proof using Type. pu_keep tt. rewrite rA3_meta. destruct (Z.eq_dec m m); [reflexivity | contradiction]. Qed.
  Lemma rA3_other : forall x, x <> m -> a_meta rA3 x = a_meta rA2 x.
  Proof using Type. pu_keep tt. intros x Hx. rewrite rA3_meta, rA2_meta. destruct (Z.eq_dec x m); [contradiction | reflexivity]. Qed.
  Lemma rmd3_f : forall fl, mt_f rmd3 fl = ir_f p L cnt aidx sc fl. Proof using Type. pu_keep tt. intros fl. unfold rmd3. apply mt_f_MT. Qed.
  Lemma WF3 : WF rA3.
  Proof using HL HW1 Haidx Hcnt Hm Hr Hsc. pu_keep (HL, HW1, Haidx, Hcnt, Hm, Hr, Hsc). apply (WF_dead_local rA2 rA3 m md rmd3 WF2); try reflexivity; [exact Hm | exact Hr | exact rA3_m | exact rA3_other]. Qed.
  Lemma VMok3 : forall h, VMok A1 h -> VMok rA3 h.
  Proof using Hm Hr. pu_keep (Hm, Hr). intros h Hv. apply (VMok_dead_local rA2 rA3 m md rmd3); try reflexivity; [exact Hm | exact Hr | exact rA3_m | exact rA3_other | exact (VMok2 h Hv)]. Qed.
  Lemma Hnodom3 : forall x, p <= x < p + L -> ~ dom rA3 x.
  Proof using Hm Hnodom Hr. pu_keep (Hm, Hnodom, Hr).
    intros x Hx Hd. apply (Hnodom x Hx). apply (proj1 (dom_set_ctx A1 rc2 x)).
    apply (proj1 (dom_dead_local rA2 rA3 m md rmd3 Hm Hr rA3_m eq_refl rA3_other eq_refl eq_refl x)). exact Hd.
  Qed.

  (* [comment removed for export] *)
  Section Ab.
    Variable ab : Z.
    Hypothesis Hab : 0 <= ab < 256.

    Lemma WF4 : WF (rA4 ab).
    Proof using HL HLm HW1 Hab Haidx Hcnt Hfit Hhr Hm Hnodom Hpal Hpsc Hr Hs20 Hsc Hsingle Hspan MLok. pu_keep (HL, HLm, HW1, Hab, Haidx, Hcnt, Hfit, Hhr, Hm, Hnodom, Hpal, Hpsc, Hr, Hs20, Hsc, Hsingle, Hspan, MLok).
      unfold rA4. apply (WF_instR rA3 m rmd3 p L cnt aidx sc ab xs WF3 rA3_m eq_refl).
      all: first [assumption | exact (or_introl Hsc) | exact L47 | exact Hnodom3
                 | (intros E H48; exact (Hsingle E)) | (intros E H48; exact (Hs20 E)) | (intros Hgt; exact Hspan)].
    Qed.
    Lemma rA4_m : a_meta (rA4 ab) m = Some (ir_mt p L cnt aidx sc ab).
    Proof using Type. pu_keep tt. unfold rA4. apply ir_meta_m. Qed.
    Lemma rA4_other : forall x, x <> m -> a_meta (rA4 ab) x = a_meta A1 x.
    Proof using Type. pu_keep tt. intros x Hx. unfold rA4. rewrite (ir_meta_other rA3 m p L cnt aidx sc ab xs x Hx). rewrite (rA3_other x Hx). reflexivity. Qed.
    Lemma rA4_active : a_active (rA4 ab) = a_active A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rA4_ctx : a_ctx (rA4 ab) = rc2. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma ir_sc' : mt_sc (ir_mt p L cnt aidx sc ab) = sc.
    Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). apply ir_sc; [exact (or_introl Hsc) | exact Hcnt | exact Hab | exact HL | exact HLm]. Qed.
    Lemma ir_last' : mt_last (ir_mt p L cnt aidx sc ab) = cnt - 1.
    Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). apply ir_last; [exact (or_introl Hsc) | exact Hcnt | exact Hab | exact HL | exact HLm]. Qed.

    Lemma WF5 : WF (rootA ab).
    Proof using HL HLm HW1 Hab Hact Haidx Hcnt Hfit Hhr Hm Hnodom Hpal Hpsc Hr Hs20 Hsc Hsingle Hspan MLok. pu_keep (HL, HLm, HW1, Hab, Hact, Haidx, Hcnt, Hfit, Hhr, Hm, Hnodom, Hpal, Hpsc, Hr, Hs20, Hsc, Hsingle, Hspan, MLok).
      unfold rootA. apply (WF_queA (rA4 ab) WF4 sc m (ir_mt p L cnt aidx sc ab) (ir_aib aidx ab) (ir_slots cnt) [] m m Hsc rA4_m eq_refl ir_sc').
      - rewrite rA4_active. exact Hact.
      - reflexivity.
      - reflexivity.
      - intros [].
      - intros H; exfalso; exact (H eq_refl).
      - intros H; exfalso; exact (H eq_refl).
      - intros H; exfalso; exact (H eq_refl).
    Qed.

    Definition rmt5 : meta_rec := MallocInv_wf3.relink (qP m m m) (qN m m m) m (ir_mt p L cnt aidx sc ab).
    Lemma rootA_m : a_meta (rootA ab) m = Some rmt5.
    Proof using Type. pu_keep tt. unfold rootA. rewrite (queA_meta (rA4 ab) sc m [] m m m), rA4_m. reflexivity. Qed.
    Lemma rmt5_role : mt_role rmt5 = RGroup (ir_aib aidx ab) (ir_slots cnt). Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rmt5_f : forall fl, mt_f rmt5 fl = match fl with FPrev => m | FNext => m | _ => ir_f p L cnt aidx sc fl end.
    Proof using Type. pu_keep tt.
      intros fl. unfold rmt5, MallocInv_wf3.relink. rewrite mt_f_MT. unfold qP, qN. rewrite Z.eqb_refl.
      destruct fl; reflexivity.
    Qed.
    Lemma rmt5_w32 : mt_w32 rmt5 = iw32 L sc cnt. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rmt5_mem : mt_mem rmt5 = p. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rmt5_stride : mt_stride rmt5 = mt_stride (ir_mt p L cnt aidx sc ab). Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rmt5_sc : mt_sc rmt5 = sc. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). exact ir_sc'. Qed.
    Lemma rmt5_last : mt_last rmt5 = cnt - 1. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). exact ir_last'. Qed.
    Lemma rmt5_maplen : mt_maplen rmt5 = L / 4096. Proof using HL HLm Hab Hcnt Hsc. pu_keep (HL, HLm, Hab, Hcnt, Hsc). apply ir_maplen; [exact (or_introl Hsc) | exact Hcnt | exact Hab | exact HL | exact HLm]. Qed.

    Lemma rA4_act_sc : a_active (rA4 ab) sc = []. Proof using Hact. pu_keep (Hact). rewrite rA4_active. exact Hact. Qed.
    Lemma rootA_other : forall x, x <> m -> a_meta (rootA ab) x = a_meta A1 x.
    Proof using Hact. pu_keep (Hact).
      intros x Hx. unfold rootA.
      rewrite (queA_meta_other (rA4 ab) sc m (ir_mt p L cnt aidx sc ab) (ir_aib aidx ab) [] m m rA4_act_sc eq_refl eq_refl ltac:(intros [])
                 ltac:(intros H; exfalso; exact (H eq_refl)) ltac:(intros H; exfalso; exact (H eq_refl)) ltac:(intros H; exfalso; exact (H eq_refl)) x Hx ltac:(intros [])).
      apply rA4_other. exact Hx.
    Qed.
    Lemma rootA_meta_inv : forall x mtx, a_meta (rootA ab) x = Some mtx -> (x = m /\ mtx = rmt5) \/ (x <> m /\ a_meta A1 x = Some mtx).
    Proof using Hact. pu_keep (Hact).
      intros x mtx Hx. destruct (Z.eq_dec x m) as [-> | Hne]; [left; rewrite rootA_m in Hx; injection Hx as <-; auto | right].
      rewrite (rootA_other x Hne) in Hx. auto.
    Qed.
    Lemma rootA_active_sc : a_active (rootA ab) sc = [m].
    Proof using Type. pu_keep tt. unfold rootA. rewrite (queA_active_sc (rA4 ab) sc m [] m m). reflexivity. Qed.
    Lemma rootA_active_other : forall c, c <> sc -> a_active (rootA ab) c = a_active A1 c.
    Proof using Type. pu_keep tt. intros c Hc. unfold rootA. rewrite (queA_active_other (rA4 ab) sc m [] m m c Hc). reflexivity. Qed.
    Lemma rootA_ctx : forall k, cvalid k -> a_ctx (rootA ab) k =
      if cslot_eq_dec k (KActive sc) then m else if cslot_eq_dec k (KUsage sc) then a_ctx A1 (KUsage sc) + cnt else a_ctx A1 k.
    Proof using HL HLm HW1 Hab Haidx Hcnt Hfit Hhr Hm Hnodom Hpal Hpsc Hr Hs20 Hsc Hsingle Hspan MLok. pu_keep (HL, HLm, HW1, Hab, Haidx, Hcnt, Hfit, Hhr, Hm, Hnodom, Hpal, Hpsc, Hr, Hs20, Hsc, Hsingle, Hspan, MLok). intros k Hk. unfold rootA. rewrite (queA_ctx_valid (rA4 ab) WF4 sc m [] m m Hsc eq_refl k Hk). rewrite rA4_ctx. reflexivity. Qed.
    Lemma rootA_areas : a_areas (rootA ab) = a_areas A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rootA_freelist : a_freelist (rootA ab) = a_freelist A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rootA_live : a_live (rootA ab) = a_live A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rootA_xmaps : a_xmaps (rootA ab) = xs. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rootA_pages : a_pages (rootA ab) = a_pages A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma rootA_mblocks : a_mblocks (rootA ab) = a_mblocks A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma dom_rootA : forall x, dom (rootA ab) x <-> dom A1 x \/ p <= x < p + L.
    Proof using HL HLm Hab Haidx Hcnt Hm Hr Hsc. pu_keep (HL, HLm, Hab, Haidx, Hcnt, Hm, Hr, Hsc).
      intros x. unfold rootA. rewrite (dom_queA (rA4 ab) sc m [] m m x). unfold rA4.
      rewrite (dom_instR rA3 m rmd3 p L cnt aidx sc ab xs rA3_m eq_refl (or_introl Hsc) Hcnt Hab HL HLm x).
      rewrite (dom_dead_local rA2 rA3 m md rmd3 Hm Hr rA3_m eq_refl rA3_other eq_refl eq_refl x). rewrite (dom_set_ctx A1 rc2 x). tauto.
    Qed.
    Lemma VMok5 : VMok (rootA ab) (ms_vm s1).
    Proof using HII HL HLm Hab Hcnt Hhr Hin Hm Hr Hrf Hs20 Hsc Hxm MLok. pu_keep (HII, HL, HLm, Hab, Hcnt, Hhr, Hin, Hm, Hr, Hrf, Hs20, Hsc, Hxm, MLok).
      unfold rootA. apply (VMok_queA (rA4 ab) sc m [] m m). unfold rA4.
      apply (VMok_instR rA3 m rmd3 p L cnt aidx sc ab xs rA3_m eq_refl Hxm (or_introl Hsc) Hcnt Hab Hhr HL HLm L47); [| exact Hin | exact Hrf].
      apply VMok3. exact (ii_vm HII).
    Qed.
    Lemma meta_usage_rootA : forall c x, meta_usage (rootA ab) c x = meta_usage A1 c x + (if Z.eq_dec x m then (if sc =? c then cnt else 0) else 0).
    Proof using HL HLm Hab Hact Hcnt Hm Hr Hsc. pu_keep (HL, HLm, Hab, Hact, Hcnt, Hm, Hr, Hsc).
      intros c x. unfold meta_usage at 1. destruct (Z.eq_dec x m) as [-> | Hne].
      - rewrite rootA_m. unfold rmt5, MallocInv_wf3.relink. rewrite mt_role_MT. cbn [mt_role ir_mt]. unfold ir_mt. rewrite mt_role_MT.
        fold (ir_mt p L cnt aidx sc ab).
        replace (mt_sc (MT _ (RGroup (ir_aib aidx ab) (ir_slots cnt)))) with (mt_sc rmt5) by reflexivity.
        replace (mt_cnt (MT _ (RGroup (ir_aib aidx ab) (ir_slots cnt)))) with (mt_cnt rmt5) by reflexivity.
        rewrite rmt5_sc. unfold mt_cnt. rewrite rmt5_last. unfold meta_usage. rewrite Hm, Hr. destruct (sc =? c); lia.
      - rewrite (rootA_other x Hne). unfold meta_usage. lia.
    Qed.
    Lemma UsOK5 : UsOK (rootA ab).
    Proof using HL HLm HW1 Hab Hact Haidx Hcnt Hfit Hhr Hm Hnodom Hpal Hpsc Hr Hs20 Hsc Hsingle Hspan MLok. pu_keep (HL, HLm, HW1, Hab, Hact, Haidx, Hcnt, Hfit, Hhr, Hm, Hnodom, Hpal, Hpsc, Hr, Hs20, Hsc, Hsingle, Hspan, MLok).
      intros c Hc. rewrite (rootA_ctx (KUsage c) ltac:(cbn; lia)).
      destruct (cslot_eq_dec (KUsage c) (KActive sc)) as [E | _]; [discriminate E|].
      destruct (proj1 (wf_meta_dom A1 HW1 m) ltac:(rewrite Hm; discriminate)) as (pg & k & Hpg & Hk & Em).
      rewrite (usage_of_point A1 (rootA ab) c m pg k (- (if sc =? c then cnt else 0)) HW1 eq_refl Hpg Hk Em).
      - destruct (cslot_eq_dec (KUsage c) (KUsage sc)) as [E | Hne].
        + injection E as ->. rewrite Z.eqb_refl. rewrite (ii_us HII sc Hsc). lia.
        + replace (sc =? c) with false by (symmetry; apply Z.eqb_neq; intros ->; exact (Hne eq_refl)). rewrite (ii_us HII c Hc). lia.
      - intros x Hx. rewrite meta_usage_rootA. destruct (Z.eq_dec x m); [contradiction | lia].
      - rewrite meta_usage_rootA. destruct (Z.eq_dec m m); [lia | contradiction].
    Qed.
    Lemma AvOK5 : AvOK (rootA ab).
    Proof using HL HLm HW1 Hab Hact Haidx Hcnt Hfit Hhr Hm Hnodom Hpal Hpsc Hr Hs20 Hsc Hsingle Hspan MLok. pu_keep (HL, HLm, HW1, Hab, Hact, Haidx, Hcnt, Hfit, Hhr, Hm, Hnodom, Hpal, Hpsc, Hr, Hs20, Hsc, Hsingle, Hspan, MLok).
      apply (AvOK_transfer A1 (rootA ab) (ii_av HII)); [reflexivity | |].
      - rewrite (rootA_ctx KAmc I). reflexivity.
      - intros x mt' Hx Hrx. destruct (rootA_meta_inv x mt' Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | eauto].
    Qed.
    Lemma deads5 : deads (rootA ab) D.
    Proof using HII Hact Hm HmD. pu_keep (HII, Hact, Hm, HmD).
      intros x. split.
      - intros (mtx & Hx & Hrx). destruct (rootA_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx|].
        destruct (proj1 (ii_dd HII x) (ex_intro _ mtx (conj H Hrx))) as [-> | Hin']; [contradiction | exact Hin'].
      - intros Hin'. assert (Hne : x <> m) by (intros ->; exact (HmD Hin')).
        destruct (proj2 (ii_dd HII x) (or_intror Hin')) as (mtx & Hx & Hrx). exists mtx. rewrite (rootA_other x Hne). auto.
    Qed.

    (* [comment removed for export] *)
    Lemma ir_slot_zero_range : forall i, (i < Z.to_nat cnt)%nat ->
      p + 12 <= slot_start (ir_mt p L cnt aidx sc ab) (Z.of_nat i) - 4 /\ slot_end (ir_mt p L cnt aidx sc ab) (Z.of_nat i) + 1 <= p + L.
    Proof using HL HLm Hab Hcnt Hfit Hs20 Hsc Hsingle. pu_keep (HL, HLm, Hab, Hcnt, Hfit, Hs20, Hsc, Hsingle).
      intros i Hi. pose proof (ir_stride_ge p L cnt aidx sc ab (or_introl Hsc) Hcnt Hab HL HLm Hfit (fun E _ => Hsingle E) (fun E _ => Hs20 E)) as [S1 S2].
      unfold slot_start, slot_end, slot_start_g, slot_end_g. rewrite (ir_mem p L cnt aidx sc ab).
      set (sd := mt_stride (ir_mt p L cnt aidx sc ab)) in *.
      assert (0 <= Z.of_nat i * sd) by (apply Z.mul_nonneg_nonneg; lia).
      assert ((Z.of_nat i + 1) * sd <= cnt * sd) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    Qed.

    (* [comment removed for export] *)
    Lemma root_commit : forall m' av1 fr av2,
      av1 mod 2^32 = 2^(aidx + 1) - 1 -> fr mod 2^32 = ifr cnt aidx -> av2 mod 2^32 = iav cnt aidx -> 0 <= av1 -> 0 <= fr -> 0 <= av2 ->
      RepW A1 (ms_mem s1) (tail_ws A1 m sc cnt aidx p L ab av1 fr av2) m' ->
      Rep (rootA ab) m'.
    Proof using HL HLm HW1 Hab Hact Haidx Hcnt Hfit Hhr Hm Hnodom Hpal Hpsc Hr Hreq Hreq0 Hs20 Hsc Hsingle Hspan Hzero MLok. pu_keep (HL, HLm, HW1, Hab, Hact, Haidx, Hcnt, Hfit, Hhr, Hm, Hnodom, Hpal, Hpsc, Hr, Hreq, Hreq0, Hs20, Hsc, Hsingle, Hspan, Hzero, MLok).
      intros m' av1 fr av2 Hav1 Hfr Hav2 P1 P2 P3 RW.
      pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3 & M4 & Mdom). ceil. pose proof layout_small as LS.
      pose proof (ctx_slot_range (KUsage sc) ltac:(cbn; lia)) as (U1 & U2 & U3). cbn [clen] in U2, U3.
      pose proof (ctx_slot_range (KActive sc) ltac:(cbn; lia)) as (C1 & C2 & C3). cbn [clen] in C2, C3. unfold CTX_END in U2, C2.
      pose proof (caddr_usage sc) as CU. pose proof (caddr_active sc) as CA. pose proof Hhr as HR'. unfold heap_range in HR'.
      pose proof p_m_apart as Hpm. pose proof act0 as Hact0.
      pose proof (masks_facts cnt aidx Hcnt Haidx) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). pose proof (iav_eq cnt aidx Hcnt Haidx) as Eiav.
      set (TW := tail_ws A1 m sc cnt aidx p L ab av1 fr av2) in RW.
      (* [comment removed for export] *)
      assert (INW : forall w, In w TW ->
        w = FCT (caddr (KActive sc)) 8 m \/ w = FCT (m + 8) 8 m \/ w = FCT m 8 m \/ w = FCT (m + 24) 4 av2 \/
        w = FCT (m + 32) 8 (iw32 L sc cnt) \/ w = FCT (p + 8) 1 (Z.lor aidx (Z.land ab 224)) \/ w = FCT p 8 m \/
        w = FCT (m + 16) 8 p \/ w = FCT (m + 28) 4 fr \/ w = FCT (m + 24) 4 av1 \/ w = FCT (caddr (KUsage sc)) 8 (a_ctx A1 (KUsage sc) + cnt)).
      { intros w Hw. unfold TW, tail_ws in Hw. cbn [In] in Hw. intuition auto. }
      apply (repw_commit3 A1 (rootA ab) (ms_mem s1) TW m' WF5 RW).
      - (* [comment removed for export] *)
        intros f Hf. unfold rootA in Hf.
        destruct (has_queA_inv (rA4 ab) WF4 sc m [] m m Hsc eq_refl f Hf) as [Hf4 | [-> | (x0 & mt0 & fl & Hx0 & Hfl & Hx0m & ->)]].
        + unfold rA4 in Hf4. destruct (has_instR rA3 m rmd3 p L cnt aidx sc ab xs rA3_m (or_introl Hsc) Hcnt Haidx Hab HL rmd3_f f Hf4) as [Hf3 | [-> | [-> | (i & Hi & Hfi)]]].
          * destruct (has_dead_local rA2 rA3 m md rmd3 rA3_m eq_refl rA3_other eq_refl eq_refl f Hf3) as [[Hf2 Hnot] | [(fl & ->) | Hf2]].
            -- destruct (has_set_ctx A1 rc2 f Hf2) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | [Hmf | Hg]]]].
               ++ unfold rc2, cupd. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hku].
                  ** right; left. cbn [f_a f_n clen]. intros x Hx. unfold TW, tail_ws.
                     do 10 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
                  ** destruct (cslot_eq_dec k (KActive sc)) as [-> | Hka].
                     { right; left. cbn [f_a f_n clen]. intros x Hx. unfold TW, tail_ws. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate. }
                     left. left. exists k. auto.
               ++ left. right; left. exact Har.
               ++ left. right; left. exists pg. auto.
               ++ (* [comment removed for export] *)
                  destruct Hmf as (x & mtx & fl & Hx0 & ->). assert (Hx : a_meta A1 x = Some mtx) by exact Hx0. clear Hx0.
                  destruct (Z.eq_dec x m) as [-> | Hne]; [exfalso; rewrite Hm in Hx; injection Hx as <-; exact (Hnot fl eq_refl)|].
                  left. right; right; left. exists x, mtx, fl. auto.
               ++ left. right; right; right. exact Hg.
            -- (* [comment removed for export] *)
               right; left. rewrite rmd3_f. pose proof (mfield_range fl) as Hflr. intros x Hx. cbn [f_a f_n] in Hx. unfold TW, tail_ws.
               destruct fl; cbn [moff mlen] in Hx;
                 repeat (first [rewrite wlook_skip by (cbn [f_a f_n]; lia) | rewrite wlook_hit by (cbn [f_a f_n]; lia)]); discriminate.
            -- (* [comment removed for export] *)
               destruct (has_set_ctx A1 rc2 f Hf2) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | [Hmf | Hg]]]].
               ++ unfold rc2, cupd. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hku].
                  ** right; left. cbn [f_a f_n clen]. intros x Hx. unfold TW, tail_ws.
                     do 10 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
                  ** destruct (cslot_eq_dec k (KActive sc)) as [-> | Hka].
                     { right; left. cbn [f_a f_n clen]. intros x Hx. unfold TW, tail_ws. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate. }
                     left. left. exists k. auto.
               ++ left. right; left. exact Har.
               ++ left. right; left. exists pg. auto.
               ++ destruct Hmf as (x & mtx & fl & Hx0 & ->). assert (Hx : a_meta A1 x = Some mtx) by exact Hx0. clear Hx0.
                  destruct (Z.eq_dec x m) as [-> | Hne].
                  ** rewrite Hm in Hx. injection Hx as <-. right; left. pose proof (mfield_range fl) as Hflr. intros y Hy. cbn [f_a f_n] in Hy. unfold TW, tail_ws.
                     destruct fl; cbn [moff mlen] in Hy;
                       repeat (first [rewrite wlook_skip by (cbn [f_a f_n]; lia) | rewrite wlook_hit by (cbn [f_a f_n]; lia)]); discriminate.
                  ** left. right; right; left. exists x, mtx, fl. auto.
               ++ left. right; right; right. exact Hg.
          * (* [comment removed for export] *) right; left. cbn [f_a f_n]. intros x Hx. unfold TW, tail_ws.
            do 6 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
          * (* [comment removed for export] *) right; left. cbn [f_a f_n]. intros x Hx. unfold TW, tail_ws.
            do 5 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
          * (* [comment removed for export] *)
            right; right. destruct (ir_slot_zero_range i Hi) as [Z1 Z2].
            assert (Hfz : f_v f = 0 /\ f_n f = 1 /\ p + 12 <= f_a f /\ f_a f + 1 <= p + L).
            { pose proof (ir_stride_ge p L cnt aidx sc ab (or_introl Hsc) Hcnt Hab HL HLm Hfit (fun E _ => Hsingle E) (fun E _ => Hs20 E)) as [S1 S2]. unfold slot_end, slot_start, slot_end_g, slot_start_g in *.
              destruct Hfi as [-> | ->]; cbn [f_a f_n f_v]; (split; [reflexivity | split; [reflexivity | lia]]). }
            destruct Hfz as (Ev & En & Z3 & Z4). rewrite Ev, En. intros x Hx. split.
            -- unfold TW, tail_ws. repeat (rewrite wlook_skip by (cbn [f_a f_n]; lia)). reflexivity.
            -- rewrite byte_of_zero. apply (mbyte_overlay (ms_mem s1) x (Z_to_bv 8 0)); [lia|]. apply Hzero. rewrite uZ by lia. lia.
        + (* [comment removed for export] *) right; left. cbn [f_a f_n]. intros x Hx. unfold TW, tail_ws. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
        + (* [comment removed for export] *) assert (x0 = m) by tauto. subst x0. right; left. intros x Hx. cbn [f_a f_n] in Hx. unfold TW, tail_ws.
          destruct Hfl as [-> | ->]; cbn [moff mlen] in Hx.
          * rewrite wlook_skip by (cbn [f_a f_n]; lia). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
          * do 2 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
      - (* [comment removed for export] *)
        intros x b Hw. destruct (wlook_some_cov TW x b Hw) as (w & Hwin & Hwx).
        destruct (INW w Hwin) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]; cbn [f_a f_n] in Hwx; unfold TW, tail_ws in Hw;
          repeat (first [rewrite wlook_skip in Hw by (cbn [f_a f_n]; lia) | rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia)]); cbn [f_a f_v] in Hw; injection Hw as <-.
        + right; left. exists (KActive sc). split; [cbn; lia|]. cbn [clen]. split; [lia|]. rewrite (rootA_ctx (KActive sc) ltac:(cbn; lia)).
          destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction].
        + left. exists m, rmt5, FNext. split; [exact rootA_m|]. cbn [moff mlen]. split; [lia|]. rewrite rmt5_f. reflexivity.
        + left. exists m, rmt5, FPrev. split; [exact rootA_m|]. cbn [moff mlen]. split; [lia|]. rewrite rmt5_f. f_equal. lia.
        + left. exists m, rmt5, FAvail. split; [exact rootA_m|]. cbn [moff mlen]. split; [lia|]. rewrite rmt5_f. cbn [ir_f].
          apply byte_of_mod32; [lia|]. rewrite Hav2, Eiav. rewrite Z.mod_small by lia. reflexivity.
        + left. exists m, rmt5, FW32. split; [exact rootA_m|]. cbn [moff mlen]. split; [lia|]. rewrite rmt5_f. reflexivity.
        + right; right; left. exists m, rmt5, (ir_aib aidx ab), (ir_slots cnt), (FCT (p + 8) 1 (ir_aib aidx ab)).
          split; [exact rootA_m|]. split; [reflexivity|]. split; [cbn; right; left; reflexivity|]. cbn [f_a f_n f_v]. split; [lia|].
          unfold ir_aib. rewrite Z.lor_comm. reflexivity.
        + right; right; left. exists m, rmt5, (ir_aib aidx ab), (ir_slots cnt), (FCT p 8 m).
          split; [exact rootA_m|]. split; [reflexivity|]. split; [cbn; left; reflexivity|]. cbn [f_a f_n f_v]. split; [lia | reflexivity].
        + left. exists m, rmt5, FMem. split; [exact rootA_m|]. cbn [moff mlen]. split; [lia|]. rewrite rmt5_f. reflexivity.
        + left. exists m, rmt5, FFreed. split; [exact rootA_m|]. cbn [moff mlen]. split; [lia|]. rewrite rmt5_f. cbn [ir_f].
          apply byte_of_mod32; [lia|]. rewrite Hfr. rewrite Z.mod_small by lia. reflexivity.
        + (* [comment removed for export] *)
          left. exists m, rmt5, FAvail. split; [exact rootA_m|]. cbn [moff mlen]. split; [lia|]. rewrite rmt5_f. cbn [ir_f].
          apply byte_of_mod32; [lia|]. rewrite Hav2, Eiav. rewrite Z.mod_small by lia. reflexivity.
        + right; left. exists (KUsage sc). split; [cbn; lia|]. cbn [clen]. split; [lia|]. rewrite (rootA_ctx (KUsage sc) ltac:(cbn; lia)).
          destruct (cslot_eq_dec (KUsage sc) (KActive sc)) as [E|_]; [discriminate E|]. destruct (cslot_eq_dec (KUsage sc) (KUsage sc)); [reflexivity | contradiction].
      - intros x Hx. apply dom_rootA in Hx. destruct Hx as [Hx | Hx]; [left; exact Hx | right]. split; [lia|].
        rewrite (Hzero (Z_to_bv 64 x)); [discriminate | rewrite uZ by lia; lia].
    Qed.
  End Ab.

  (* [comment removed for export] *)
  Theorem ts_root_tail : forall (K : word -> M R) P,
    (forall ab m', 0 <= ab < 256 ->
       let s' := upd s1 m' (ms_vm s1) in
       II sp0 argv envp cb D (rootA ab) s' -> FR A1 s1 (rootA ab) s' ->
       (* [comment removed for export] *)
       (forall a : word, p + 16 <= u a < p + L -> m' a = ms_mem s1 a) ->
       tsafe (K (Z_to_bv 64 0) s') P) ->
    tsafe ((r <- as_tail (Z_to_bv 64 sc) (Z_to_bv 64 m) (Z_to_bv 64 p) (Z_to_bv 64 aidx) (Z_to_bv 64 cnt)
                        (Z_to_bv 64 (LOCKA + 8 * sc)) (Z_to_bv 64 (caddr (KActive sc))) ;; K r) s1) P.
  Proof using HL HLm HW1 Hact Haidx Hcnt Hfit Hhr Hin Hm HmD Hmd0 HmdW Hnodom Hpal Hpsc Hr Hreq Hreq0 Hrf Hs20 Hsc Hsingle Hspan Hxm Hzero MLok. pu_keep (HL, HLm, HW1, Hact, Haidx, Hcnt, Hfit, Hhr, Hin, Hm, HmD, Hmd0, HmdW, Hnodom, Hpal, Hpsc, Hr, Hreq, Hreq0, Hrf, Hs20, Hsc, Hsingle, Hspan, Hxm, Hzero, MLok).
    intros K P HK. pose proof (ii_is HII) as HIS. pose proof HIS as [HW HRp HC HWIN HE HG].
    pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3 & M4 & Mdom). ceil. pose proof layout_small as LS.
    pose proof Hhr as HR'. unfold heap_range in HR'. pose proof p_m_apart as Hpm. pose proof usage_now as [EU HU].
    eapply (ts_as_tail A1 m md sc cnt aidx p L HW1 Hm (Hmd0 FPrev ltac:(discriminate)) (Hmd0 FNext ltac:(discriminate)) HmdW
              ltac:(pose proof L47; lia) HLm Hsc act0 Hcnt Haidx ltac:(lia) ltac:(split; [| split]; lia) ltac:(lia)
              s1 (ms_mem s1) []); [apply repw_init; [exact HW1 | exact HRp] | exact HWIN | | apply wfree_range_nil | apply wfree_range_nil | apply wfree_range_nil | apply wfree_range_nil |].
    { intros j Hj. rewrite (Hzero (Z_to_bv 64 (p + j))); [discriminate | rewrite uZ by lia; lia]. }
    intros m' ab av1 fr av2 Hab Hav1 Hfr Hav2 P1 P2 P3 RW. rewrite app_nil_r in RW.
    pose proof (root_commit ab Hab m' av1 fr av2 Hav1 Hfr Hav2 P1 P2 P3 RW) as HR5.
    pose proof (ctx_slot_range (KUsage sc) ltac:(cbn; lia)) as (U1 & U2 & U3). pose proof (ctx_slot_range (KActive sc) ltac:(cbn; lia)) as (C1 & C2 & C3).
    cbn [clen] in U2, U3, C2, C3. unfold CTX_END in U2, C2.
    assert (WCASE : forall w x, In w (tail_ws A1 m sc cnt aidx p L ab av1 fr av2) -> f_a w <= x < f_a w + f_n w ->
      (LOCKA + 8 <= x < LOCKA + 936) \/ (m <= x < m + 40) \/ (p <= x < p + 9)).
    { intros w x Hw Hx. unfold tail_ws in Hw. cbn [In] in Hw.
      destruct Hw as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]]]; cbn [f_a f_n] in Hx; lia. }
    assert (ZONE : forall a : word, m' a = ms_mem s1 a \/ mzone (u a)).
    { intros a. destruct (wfree_dec (tail_ws A1 m sc cnt aidx p L ab av1 fr av2) (u a)) as [Hf | (w & Hw & Hx)]; [left; exact (rw_frame A1 _ _ m' RW a Hf) | right].
      unfold mzone, CTX, CTX_END. destruct (WCASE w (u a) Hw Hx) as [H | [H | H]]; lia. }
    assert (MAPPED : forall a : word, m' a <> None -> ms_mem s1 a <> None \/ (IMG_LO <= u a < IMG_HI) \/ mcov (vm_maps (ms_vm s1)) (u a) 1).
    { intros a Ha. destruct (wfree_dec (tail_ws A1 m sc cnt aidx p L ab av1 fr av2) (u a)) as [Hf | (w & Hw & Hx)]; [left; rewrite <- (rw_frame A1 _ _ m' RW a Hf); exact Ha|].
      destruct (WCASE w (u a) Hw Hx) as [H | [H | H]].
      - right; left. lia.
      - left. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (rep_dom A1 (ms_mem s1) HRp). replace (u a) with (m + (u a - m)) by lia. apply Mdom. lia.
      - left. rewrite (Hzero a); [discriminate | lia]. }
    apply (HK ab m' Hab).
    - apply II_intro.
      + apply (IS_mem sp0 argv envp cb A1 (rootA ab) s1 m' HIS ltac:(first [exact (WF5 ab Hab) | exact (WF5 ab)]) HR5 ZONE MAPPED).
      + cbn [ms_vm upd]. first [exact (VMok5 ab Hab) | exact (VMok5 ab)].
      + first [exact (AvOK5 ab Hab) | exact (AvOK5 ab)].
      + first [exact (UsOK5 ab Hab) | exact (UsOK5 ab)].
      + first [exact (deads5 ab Hab) | exact (deads5 ab)].
    - constructor; cbn [ms_lo ms_hi ms_vm ms_mem upd]; try reflexivity.
      + intros x Ho. unfold owned_of in *. first [rewrite (dom_rootA ab Hab x) | rewrite (dom_rootA ab x)]. tauto.
      + intros a Ho _. destruct (wfree_dec (tail_ws A1 m sc cnt aidx p L ab av1 fr av2) (u a)) as [Hf | (w & Hw & Hx)]; [exact (rw_frame A1 _ _ m' RW a Hf)|].
        exfalso. apply Ho. unfold owned_of. first [rewrite (dom_rootA ab Hab (u a)) | rewrite (dom_rootA ab (u a))]. unfold CTX_END.
        destruct (WCASE w (u a) Hw Hx) as [H | [H | H]]; [left; lia | | right; right; lia].
        right; left. replace (u a) with (m + (u a - m)) by lia. apply Mdom. lia.
      + intros q n Hq. rewrite (rootA_live ab). exact Hq.
      + intros q n a Hq Ha. destruct (wfree_dec (tail_ws A1 m sc cnt aidx p L ab av1 fr av2) (u a)) as [Hf | (w & Hw & Hx)]; [exact (rw_frame A1 _ _ m' RW a Hf)|].
        exfalso. pose proof (live_dom A1 q n (u a) HW1 Hq Ha) as Hd.
        pose proof (dom_heap A1 (u a) HW1 Hd) as (lo & hi & Hh & Hlh). unfold heap_range in Hh.
        destruct (WCASE w (u a) Hw Hx) as [H | [H | H]].
        * lia.
        * exact (proj2 (meta_dom_nolive A1 m md (u a) HW1 Hm ltac:(lia)) q n Hq Ha).
        * apply (Hnodom (u a)); [lia | exact Hd].
      + intros a Ha. exact (rw_mapped A1 _ _ m' RW a Ha).
    - intros a Ha. apply (rw_frame A1 _ _ m' RW a).
      destruct (wfree_dec (tail_ws A1 m sc cnt aidx p L ab av1 fr av2) (u a)) as [Hf | (w & Hw & Hx)]; [exact Hf | exfalso].
      destruct (WCASE w (u a) Hw Hx) as [H | [H | H]]; lia.
  Qed.
End RootTail.

End WithLayout.
