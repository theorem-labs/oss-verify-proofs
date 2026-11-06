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
  MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_wf6 MallocInv_wf7 MallocInv_wf8 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm
  MallocInv_coh MallocInv_ops MallocInv_usage MallocInv_live MallocInv_free MallocInv_freetop MallocInv_enframe MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_ntq
  MallocInv_nt1 MallocInv_aspieces MallocInv_agtail MallocInv_agroot.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.
Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zl (size : word) : nat -> word -> M unit :=
  fix zl (k : nat) (a2 : word) : M unit :=
    match k with O => mret tt | S k' => m_sb a2 w0 ;; zl k' (v_add a2 size) end.

(* [comment removed for export] *)
Definition nest_rest (sc size m cnt1 s7 pm j' idx : word) : M word :=
  szj <- m_lhu (v_add A_SIZE_CLASSES (v_slli j' 1)) ;;
  gj <- m_ld (at_ (v_add A_LOCK (v_slli j' 3)) 88) ;;
  ctr <- m_lw (at_ A_LOCK 20) ;;
  p <- m_enframe gj idx (v_addi (v_slli szj 4) (-4)) ctr ;;
  wm <- m_ld (at_ m 32) ;;
  m_sd (at_ m 32) (v_srli (v_slli wm 52) 52) ;;
  c3 <- m_lbu (at_ p (-3)) ;;
  m_sb (at_ p (-3)) (v_addi (v_andi c3 31) 192) ;;
  zl size (S (Z.to_nat (bv_unsigned cnt1))) (at_ p 12) ;;
  let aidx := v_addi cnt1 (-1) in
  as_tail sc m p aidx cnt1 s7 pm.

Lemma as_nested_unfold : forall rec (sp sc size m cnt1 a4 s7 pm : word),
  as_nested rec sp sc size m cnt1 a4 s7 pm =
  (j <- (if c_ltu (v_addi a4 12) (wlit 157) then mret (v_srli a4 4)
         else m_size_to_class_big A_SIZE_CLASSES (v_srli a4 4)) ;;
   idx <- rec (at_ sp (-144)) (v_addiw j 0) (v_addi a4 12) ;;
   if c_lts idx w0 then m_free_meta_ag (at_ A_LOCK 24) m ;; mret wm1
   else nest_rest sc size m cnt1 s7 pm (v_addiw j 0) idx).
Proof using Type. pu_keep tt. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma repw_commit4 : forall A A' m0 ws m,
  WF A' -> RepW A m0 ws m ->
  (forall f, has A' f ->
     has A f \/ (forall x, f_a f <= x < f_a f + f_n f -> wlook ws x <> None) \/
     (forall x, f_a f <= x < f_a f + f_n f -> wlook ws x = None /\ mbyte m0 x = Some (byte_of (f_v f) (x - f_a f)))) ->
  (forall x b, wlook ws x = Some b ->
      (exists y mt fl, a_meta A' y = Some mt /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mt fl) (x - (y + moff fl))) \/
      (exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (a_ctx A' k) (x - caddr k)) \/
      (exists y mt aib sl hf, a_meta A' y = Some mt /\ mt_role mt = RGroup aib sl /\ In hf (grp_hdr_fields y mt aib) /\
          f_a hf <= x < f_a hf + f_n hf /\ b = byte_of (f_v hf) (x - f_a hf)) \/
      (forall f, has A' f -> f_a f <= x < f_a f + f_n f -> byte_of (f_v f) (x - f_a f) = b)) ->
  (forall x, dom A' x -> dom A x \/ (0 <= x < 2^64 /\ m0 (Z_to_bv 64 x) <> None)) ->
  Rep A' m.
Proof using MLok. pu_keep (MLok).
  intros A A' m0 ws m HW' RW Hf Hw Hd. constructor.
  - intros x b (f & Hfa & [Hx ->]). destruct (wlook ws x) as [b'|] eqn:E.
    + replace (byte_of (f_v f) (x - f_a f)) with b'; [exact (rw_wr A m0 ws m RW x b' E)|].
      destruct (Hw x b' E) as [(y & mt & fl & Hy & Hr & ->) | [(k & Hk & Hr & ->) | [(y & mt & aib & sl & hf & Hy & Hry & Hhf & Hr & ->) | Hsem]]].
      * rewrite (fact_at_meta A' HW' f y mt fl x Hfa Hy Hx Hr). reflexivity.
      * rewrite (fact_at_ctx A' HW' f k x Hfa Hk Hx Hr). reflexivity.
      * rewrite (fact_at_hdr A' HW' f y mt aib sl hf x Hfa Hy Hry Hhf Hx Hr). reflexivity.
      * symmetry. exact (Hsem f Hfa Hx).
    + destruct (Hf f Hfa) as [Ho | [Hc | Hz]].
      * apply (rw_fact A m0 ws m RW x _ E). exists f. split; [exact Ho | split; [exact Hx | reflexivity]].
      * exfalso. exact (Hc x Hx E).
      * destruct (Hz x Hx) as [_ Hb]. rewrite <- Hb. apply mbyte_ext. apply (rw_frame A m0 ws m RW).
        pose proof (facts_addr64 A' HW' x (byte_of (f_v f) (x - f_a f)) ltac:(exists f; split; [exact Hfa | split; [exact Hx | reflexivity]])) as Hx64.
        rewrite uZ by lia. exact (wlook_free_inv ws x E).
  - intros x Hx. destruct (Hd x Hx) as [Ho | [Hr Hm0]]; [exact (rw_dom A m0 ws m RW x Ho)|].
    apply (rw_mapped A m0 ws m RW). exact Hm0.
Qed.

Lemma wlook_app_hit : forall ws1 ws2 x b, wlook ws1 x = Some b -> wlook (ws1 ++ ws2) x = Some b.
Proof using Type. pu_keep tt.
  induction ws1 as [|w ws1 IH]; intros ws2 x b H; [discriminate H|].
  cbn [wlook app] in *. destruct (wcov w x); [exact H | exact (IH ws2 x b H)].
Qed.
Lemma wlook_app_skip : forall ws1 ws2 x, wlook ws1 x = None -> wlook (ws1 ++ ws2) x = wlook ws2 x.
Proof using Type. pu_keep tt.
  induction ws1 as [|w ws1 IH]; intros ws2 x H; [reflexivity|].
  cbn [wlook app] in *. destruct (wcov w x); [discriminate H | exact (IH ws2 x H)].
Qed.

Section StepsN.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop) (ws : list fct).

  (* [comment removed for export] *)
  Lemma ts_lbu_m0w : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> 0x1000 <= a -> a + 1 <= alloc_ceiling -> wfree ws a -> mbyte m0 a = Some v ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 a) ;; k x) s) P.
  Proof using Type. pu_keep tt.
    intros s m0 ws a v k P RW HWIN Ha Hc Hf Hm0 Hk. ceil.
    assert (Hm : mbyte (ms_mem s) a = Some v).
    { rewrite <- Hm0. apply mbyte_ext. apply (rw_frame A m0 ws (ms_mem s) RW). rewrite uZ by lia. exact Hf. }
    eapply ts_lbu_mbyte; [exact HWIN | exact Hm | lia | exact Hk].
  Qed.
End StepsN.

(* [comment removed for export] *)
Lemma taken_not_live : forall A ma mt aib slots i, WF A ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 <= i -> nth_error slots (Z.to_nat i) = Some STaken ->
  a_live A (slot_start mt i) = None.
Proof using Type. pu_keep tt.
  intros A ma mt aib slots i HW Hma Hr Hi0 Hi.
  destruct (a_live A (slot_start mt i)) as [k|] eqn:E; [| reflexivity]. exfalso.
  apply (proj1 (wf_live_map A HW _ _)) in E. destruct E as (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Eq).
  pose proof (wf_grp A HW ma mt aib slots Hma Hr) as (Hw & _ & Hsc & _). pose proof (stride_ge16 mt ltac:(lia) Hsc) as S16.
  destruct (live_in_span_unique A x mtx aibx slx j off k ma mt aib slots i STaken HW Hx Hrx Hj0 Hj Hma Hr Hi0 Hi ltac:(intros ch E'; discriminate E')) as [-> Eji].
  { rewrite <- Eq. unfold slot_end, slot_start, slot_end_g, slot_start_g in *. lia. }
  subst j. rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-. rewrite Hi in Hj. discriminate Hj.
Qed.

(* [comment removed for export] *)
Lemma slots_apart' : forall mt j j', 0 <= j -> 0 <= j' -> j <> j' -> 0 <= mt_stride mt ->
  slot_end mt j + 4 <= slot_start mt j' \/ slot_end mt j' + 4 <= slot_start mt j.
Proof using Type. pu_keep tt.
  intros mt j j' Hj Hj' Hne Hsd. unfold slot_end, slot_start, slot_end_g, slot_start_g.
  destruct (Z.lt_ge_cases j j') as [Hlt | Hge].
  - left. assert ((j + 1) * mt_stride mt <= j' * mt_stride mt) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - right. assert ((j' + 1) * mt_stride mt <= j * mt_stride mt) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

Lemma slot_cnt_of_nth : forall A ma mt aib slots j st, WF A -> a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  nth_error slots (Z.to_nat j) = Some st -> 0 <= j -> j + 1 <= mt_cnt mt /\ 16 <= mt_stride mt.
Proof using Type. pu_keep tt.
  intros A ma mt aib slots j st HW Hma Hr Hj Hj0.
  pose proof (wf_grp A HW ma mt aib slots Hma Hr) as (Hw & _ & Hsc & Hlen & _). pose proof (stride_ge16 mt ltac:(lia) Hsc).
  pose proof (proj1 (nth_error_Some slots (Z.to_nat j)) ltac:(rewrite Hj; discriminate)). lia.
Qed.

(* [comment removed for export] *)
Lemma taken_span_nolive : forall A ma mt aib slots i, WF A ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 <= i -> nth_error slots (Z.to_nat i) = Some STaken ->
  forall x q n, slot_start mt i - 4 <= x <= slot_end mt i -> a_live A q = Some n -> ~ (q <= x < q + n).
Proof using Type. pu_keep tt.
  intros A ma mt aib slots i HW Hma Hr Hi0 Hi x q n Hx Hq Hin.
  apply (proj1 (wf_live_map A HW _ _)) in Hq. destruct Hq as (y & mty & aiby & sly & j & off & Hy & Hry & Hj0 & Hj & Eq).
  pose proof (live_geom A HW y mty aiby sly j off n Hy Hry Hj0 Hj) as (qq & Hqq & Hn & Hoff & Hfit & _).
  destruct (slot_cnt_of_nth A ma mt aib slots i STaken HW Hma Hr Hi Hi0) as [Ci Si].
  destruct (slot_cnt_of_nth A y mty aiby sly j (SLive off n) HW Hy Hry Hj Hj0) as [Cj Sj].
  destruct (slot_in_ext mt i Hi0 Ci ltac:(lia)) as [Ei1 Ei2]. destruct (slot_in_ext mty j Hj0 Cj ltac:(lia)) as [Ej1 Ej2].
  assert (Hpay : slot_start mty j <= q /\ q + n <= slot_end mty j).
  { rewrite Eq. unfold slot_end, slot_start, slot_end_g, slot_start_g in *. lia. }
  destruct Hpay as [P1 P2].
  destruct (Z.eq_dec y ma) as [-> | Hne].
  - rewrite Hma in Hy. injection Hy as Emt. subst mty. rewrite Hr in Hry. injection Hry as Ea Es. subst aiby sly.
    destruct (Z.eq_dec j i) as [-> | Hji]; [rewrite Hi in Hj; discriminate Hj|].
    destruct (slots_apart' mt j i Hj0 Hi0 Hji ltac:(lia)); lia.
  - destruct (wf_laminar A HW ma mt aib slots y mty aiby sly Hma Hr Hy Hry ltac:(intros E; exact (Hne (eq_sym E)))) as [D | [D | [D | D]]].
    + unfold gext_lo in *. lia.
    + unfold gext_lo in *. lia.
    + destruct D as (j2 & ch & Hj20 & Hj2 & Dlo & Dhi).
      assert (Hj2i : j2 <> i) by (intros ->; rewrite Hi in Hj2; discriminate Hj2).
      destruct (slots_apart' mt j2 i Hj20 Hi0 Hj2i ltac:(lia)); unfold gext_lo in *; lia.
    + destruct D as (j2 & ch & Hj20 & Hj2 & Dlo & Dhi).
      assert (Hj2j : j2 <> j) by (intros ->; rewrite Hj in Hj2; discriminate Hj2).
      destruct (slots_apart' mty j2 j Hj20 Hj0 Hj2j ltac:(lia)); unfold gext_lo in *; lia.
Qed.

(* [comment removed for export] *)
Lemma meta_grp_apart : forall A m mdm g mtg aibg slg x, WF A -> a_meta A m = Some mdm ->
  a_meta A g = Some mtg -> mt_role mtg = RGroup aibg slg -> gext_lo mtg <= x < gext_hi mtg + 4 ->
  m + 40 <= x \/ x + 1 <= m.
Proof using Type. pu_keep tt.
  intros A m mdm g mtg aibg slg x HW Hm Hg Hrg Hx.
  destruct (proj1 (wf_meta_dom A HW m) ltac:(rewrite Hm; discriminate)) as (pg & k & Hpg & Hk & ->).
  pose proof (meta_addr_range pg k Hk) as MR.
  destruct (wf_grp_root A HW g mtg aibg slg Hg Hrg) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Rlo & Rhi & _).
  destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpg Hmr Hrr Hml); unfold meta_addr in *; lia.
Qed.

(* [comment removed for export] *)
Lemma rep_consistent : forall A m f f' x, Rep A m -> has A f -> has A f' ->
  f_a f <= x < f_a f + f_n f -> f_a f' <= x < f_a f' + f_n f' ->
  byte_of (f_v f) (x - f_a f) = byte_of (f_v f') (x - f_a f').
Proof using Type. pu_keep tt.
  intros A m f f' x HR Hf Hf' Hx Hx'.
  pose proof (rep_facts A m HR x _ (ex_intro _ f (conj Hf (conj Hx eq_refl)))) as E1.
  pose proof (rep_facts A m HR x _ (ex_intro _ f' (conj Hf' (conj Hx' eq_refl)))) as E2.
  rewrite E1 in E2. injection E2 as E. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NestRest.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A1 : astate) (s1 : mstate).
  (* [comment removed for export] *)
  Variables (sc m : Z) (md : meta_rec) (j gj : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (idx cnt1 : Z).
  Hypothesis HII : II sp0 argv envp cb (m :: D) A1 s1.
  Hypothesis Hm : a_meta A1 m = Some md.
  Hypothesis Hr : mt_role md = RDead.
  Hypothesis Hmd0 : forall fl, mt_f md fl = 0.
  Hypothesis HmD : ~ In m D.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A1 sc = [].
  Hypothesis Hj : 0 <= j < 48.
  Hypothesis Hgj : a_ctx A1 (KActive j) = gj.
  Hypothesis Hmt : a_meta A1 gj = Some mt.
  Hypothesis Hrl : mt_role mt = RGroup aib slots.
  Hypothesis Hscj : mt_sc mt = j.
  Hypothesis Hidx : 0 <= idx <= mt_last mt.
  Hypothesis Hslot : nth_error slots (Z.to_nat idx) = Some STaken.
  Hypothesis Hstride : mt_stride mt = 16 * size_class j.
  Hypothesis Hcnt1 : 2 <= cnt1 <= 32.
  Hypothesis Hfitj : 16 * size_class sc * cnt1 + 16 <= 16 * size_class j.
  Hypothesis Hsmall : 16 * size_class sc * cnt1 + 16 <= 2048.

  Let HW1 : WF A1 := is_wf _ _ _ _ _ _ (ii_is HII).
  Definition nsize : Z := 16 * size_class sc.
  Definition nn : Z := 16 * size_class j - 4.
  Definition p0 : Z := slot_start mt idx.
  Definition ne : Z := slot_end mt idx.

  Lemma gj_ne_m : gj <> m.
  Proof using Hidx Hm Hmt Hr Hrl Hscj Hstride. pu_keep (Hidx, Hm, Hmt, Hr, Hrl, Hscj, Hstride). intros E. rewrite E, Hm in Hmt. injection Hmt as <-. rewrite Hr in Hrl. discriminate Hrl. Qed.
  Lemma szj_rng : 1 <= size_class j <= 8191. Proof using Hj. pu_keep (Hj). exact (size_class_range j Hj). Qed.
  Lemma szc_rng : 1 <= size_class sc <= 8191. Proof using Hsc. pu_keep (Hsc). exact (size_class_range sc Hsc). Qed.
  Lemma ne_eq : ne = p0 + 16 * size_class j - 4.
  Proof using Hj Hsc Hstride. pu_keep (Hj, Hsc, Hstride). unfold ne, p0, slot_end, slot_start, slot_end_g, slot_start_g. rewrite Hstride. lia. Qed.
  Lemma idx_facts : idx + 1 <= mt_cnt mt /\ 16 <= mt_stride mt /\ idx < 32.
  Proof using HW1 Hidx Hj Hmt Hrl Hsc Hslot. pu_keep (HW1, Hidx, Hj, Hmt, Hrl, Hsc, Hslot).
    destruct (slot_cnt_of_nth A1 gj mt aib slots idx STaken HW1 Hmt Hrl Hslot ltac:(lia)) as [C S].
    pose proof (w_last_range (mt_w32 mt)). unfold mt_cnt, mt_last in *. lia.
  Qed.
  Lemma span_dom : forall x, p0 - 4 <= x < ne + 1 -> dom A1 x.
  Proof using HW1 Hidx Hj Hmt Hrl Hsc Hslot. pu_keep (HW1, Hidx, Hj, Hmt, Hrl, Hsc, Hslot).
    intros x Hx. pose proof idx_facts as (C & S16g & _). destruct (slot_in_ext mt idx ltac:(lia) C ltac:(lia)) as [E1 E2].
    apply (grp_dom A1 gj mt aib slots x HW1 Hmt Hrl). unfold p0, ne, gext_lo in *. lia.
  Qed.
  Lemma span_heap : 0x1000 <= p0 - 4 /\ ne + 4 <= alloc_ceiling /\ (ne + 4 <= IMG_LO \/ IMG_HI <= p0 - 4).
  Proof using HW1 Hidx Hj Hmt Hrl Hsc Hslot. pu_keep (HW1, Hidx, Hj, Hmt, Hrl, Hsc, Hslot).
    pose proof idx_facts as (C & S16g & _). destruct (slot_in_ext mt idx ltac:(lia) C ltac:(lia)) as [E1 E2].
    pose proof (grp_heap A1 gj mt aib slots HW1 Hmt Hrl) as (G1 & G2 & G3). unfold p0, ne, gext_lo in *. lia.
  Qed.
  Lemma p0_m_apart : p0 + 16 <= m \/ m + 40 <= p0.
  Proof using HW1 Hidx Hj Hm Hmt Hrl Hsc Hslot Hstride. pu_keep (HW1, Hidx, Hj, Hm, Hmt, Hrl, Hsc, Hslot, Hstride).
    pose proof idx_facts as (C & S16g & _). destruct (slot_in_ext mt idx ltac:(lia) C ltac:(lia)) as [E1 E2].
    destruct (meta_grp_apart A1 m md gj mt aib slots p0 HW1 Hm Hmt Hrl ltac:(unfold p0, gext_lo in *; pose proof ne_eq; unfold ne, p0 in *; lia)) as [H|H]; [| left].
    - destruct (meta_grp_apart A1 m md gj mt aib slots (p0 + 15) HW1 Hm Hmt Hrl ltac:(unfold p0, gext_lo in *; pose proof ne_eq; pose proof szj_rng; unfold ne, p0 in *; lia)) as [H'|H']; [| lia].
      (* [comment removed for export] *) right. lia.
    - pose proof szj_rng. pose proof ne_eq. unfold ne, p0 in *.
      destruct (meta_grp_apart A1 m md gj mt aib slots (slot_start mt idx + 15) HW1 Hm Hmt Hrl ltac:(unfold gext_lo in *; lia)); lia.
  Qed.

  (* [comment removed for export] *)
  Definition nL2 : Z -> option Z := lupd (a_live A1) p0 (Some nn).
  Definition mt2 : meta_rec := MT (mt_f mt) (RGroup aib (list_set slots (Z.to_nat idx) (SLive 0 nn))).
  Definition nA2 : astate := set_live (ameta_upd A1 gj mt2) nL2.
  Definition slots3 : list slot_st := list_set (list_set slots (Z.to_nat idx) (SLive 0 nn)) (Z.to_nat idx) STaken.
  Definition mt3 : meta_rec := MT (mt_f mt) (RGroup aib slots3).
  Definition nA3 : astate := set_live (ameta_upd nA2 gj mt3) (a_live A1).
  Lemma nA2_eq : slot_set A1 gj idx (SLive 0 nn) nL2 = nA2.
  Proof using Hmt Hrl. pu_keep (Hmt, Hrl). exact (MallocInv_wf.A'_eq A1 gj mt aib slots idx (SLive 0 nn) Hmt Hrl nL2). Qed.

  Lemma nA2_gj : a_meta nA2 gj = Some mt2.
  Proof using Type. pu_keep tt. unfold nA2, set_live, ameta_upd, set_meta. cbn. apply aupd_same. Qed.
  Lemma nA2_other : forall x, x <> gj -> a_meta nA2 x = a_meta A1 x.
  Proof using Type. pu_keep tt. intros x Hx. unfold nA2, set_live, ameta_upd, set_meta. cbn. apply aupd_other. exact Hx. Qed.
  Lemma mt2_role : mt_role mt2 = RGroup aib (list_set slots (Z.to_nat idx) (SLive 0 nn)). Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma idx_lt : (Z.to_nat idx < length slots)%nat.
  Proof using Hslot. pu_keep (Hslot). apply (proj1 (nth_error_Some slots (Z.to_nat idx))). rewrite Hslot. discriminate. Qed.
  Lemma slots2_idx : nth_error (list_set slots (Z.to_nat idx) (SLive 0 nn)) (Z.to_nat idx) = Some (SLive 0 nn).
  Proof using Hslot. pu_keep (Hslot). apply list_set_nth_same. exact idx_lt. Qed.
  Lemma nA3_eq : slot_set nA2 gj idx STaken (a_live A1) = nA3.
  Proof using Type. pu_keep tt. rewrite (MallocInv_wf.A'_eq nA2 gj mt2 aib _ idx STaken nA2_gj mt2_role (a_live A1)). reflexivity. Qed.
  Lemma nA3_gj : a_meta nA3 gj = Some mt3.
  Proof using Type. pu_keep tt. unfold nA3, set_live, ameta_upd, set_meta. cbn. apply aupd_same. Qed.
  Lemma nA3_other : forall x, x <> gj -> a_meta nA3 x = a_meta A1 x.
  Proof using Type. pu_keep tt. intros x Hx. unfold nA3, set_live, ameta_upd, set_meta. cbn. rewrite aupd_other by exact Hx. apply nA2_other. exact Hx. Qed.
  Lemma nA3_m : a_meta nA3 m = Some md. Proof using Hidx Hm Hmt Hr Hrl Hscj Hstride. pu_keep (Hidx, Hm, Hmt, Hr, Hrl, Hscj, Hstride). rewrite (nA3_other m (not_eq_sym gj_ne_m)). exact Hm. Qed.
  Lemma slots3_idx : nth_error slots3 (Z.to_nat idx) = Some STaken.
  Proof using Hslot. pu_keep (Hslot). unfold slots3. apply list_set_nth_same. rewrite list_set_length. exact idx_lt. Qed.
  Lemma slots3_other : forall k, k <> Z.to_nat idx -> nth_error slots3 k = nth_error slots k.
  Proof using Type. pu_keep tt. intros k Hk. unfold slots3. rewrite !list_set_nth_other by (intros E; apply Hk; symmetry; exact E). reflexivity. Qed.
  Lemma slots3_nth : forall k, nth_error slots3 k = nth_error slots k.
  Proof using Hslot. pu_keep (Hslot). intros k. destruct (Nat.eq_dec k (Z.to_nat idx)) as [-> | Hk]; [rewrite slots3_idx, Hslot; reflexivity | apply slots3_other; exact Hk]. Qed.
  Lemma slots3_len : length slots3 = length slots. Proof using Type. pu_keep tt. unfold slots3. rewrite !list_set_length. reflexivity. Qed.
  Lemma mt3_role : mt_role mt3 = RGroup aib slots3. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma mt3_f : forall fl, mt_f mt3 fl = mt_f mt fl. Proof using Type. pu_keep tt. intros fl. unfold mt3. apply mt_f_MT. Qed.
  Lemma mt3_mem : mt_mem mt3 = mt_mem mt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma mt3_w32 : mt_w32 mt3 = mt_w32 mt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma mt3_stride : mt_stride mt3 = mt_stride mt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma mt3_maplen : mt_maplen mt3 = mt_maplen mt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma mt3_sc : mt_sc mt3 = mt_sc mt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma mt3_cnt : mt_cnt mt3 = mt_cnt mt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma mt3_last : mt_last mt3 = mt_last mt. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma nA3_ctx : a_ctx nA3 = a_ctx A1. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma nA3_areas : a_areas nA3 = a_areas A1. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma nA3_active : a_active nA3 = a_active A1. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma nA3_freelist : a_freelist nA3 = a_freelist A1. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma nA3_live : a_live nA3 = a_live A1. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma nA3_xmaps : a_xmaps nA3 = a_xmaps A1. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma nA3_pages : a_pages nA3 = a_pages A1. Proof using Type. pu_keep tt. reflexivity. Qed.
  Lemma nA3_mblocks : a_mblocks nA3 = a_mblocks A1. Proof using Type. pu_keep tt. reflexivity. Qed.

  Lemma nn_facts : 0 <= nn /\ nn + 4 <= mt_stride mt /\ mt_stride mt - nn < 2^20 /\ (mt_stride mt - nn - 4) / 16 = 0.
  Proof using Hj Hsc Hstride. pu_keep (Hj, Hsc, Hstride). unfold nn. rewrite Hstride. pose proof szj_rng. split; [lia|]. split; [lia|]. split; [lia|]. replace (16 * size_class j - (16 * size_class j - 4) - 4) with 0 by lia. reflexivity. Qed.

  Lemma WF_nA2 : WF nA2.
  Proof using HW1 Hidx Hj Hmt Hrl Hsc Hslot Hstride. pu_keep (HW1, Hidx, Hj, Hmt, Hrl, Hsc, Hslot, Hstride).
    pose proof nn_facts as (N1 & N2 & N3 & N4). pose proof idx_facts as (C & S16g & I32).
    rewrite <- nA2_eq. apply (WF_slot_set A1 HW1 gj mt aib slots idx STaken (SLive 0 nn) Hmt Hrl Hslot ltac:(lia)).
    - left. reflexivity.
    - right. exists 0, nn. reflexivity.
    - intros off n E. injection E as <- <-. lia.
    - intros q k. unfold nL2, lupd. unfold p0. destruct (Z.eq_dec q (slot_start mt idx)) as [-> | Hne].
      + split; [intros E; injection E as <-; left; exists 0; split; [reflexivity | lia] |].
        intros [(off & E & _) | (Hl & _)]; [injection E as <- <-; reflexivity |].
        exfalso. rewrite (taken_not_live A1 gj mt aib slots idx HW1 Hmt Hrl ltac:(lia) Hslot) in Hl. discriminate Hl.
      + split; [intros Hl; right; split; [exact Hl | intros off n E; discriminate E] |].
        intros [(off & E & Eq) | (Hl & _)]; [| exact Hl]. injection E as <- <-. exfalso. apply Hne. lia.
  Qed.
  Lemma WF_nA3 : WF nA3.
  Proof using HW1 Hidx Hj Hmt Hrl Hsc Hslot Hstride. pu_keep (HW1, Hidx, Hj, Hmt, Hrl, Hsc, Hslot, Hstride).
    pose proof nn_facts as (N1 & N2 & N3 & N4).
    rewrite <- nA3_eq. apply (WF_slot_set nA2 WF_nA2 gj mt2 aib _ idx (SLive 0 nn) STaken nA2_gj mt2_role slots2_idx ltac:(lia)).
    - right. exists 0, nn. reflexivity.
    - left. reflexivity.
    - intros off n E. discriminate E.
    - intros q k. split.
      + intros Hl. right. split.
        * change (a_live nA2 q) with (nL2 q). unfold nL2, lupd. destruct (Z.eq_dec q p0) as [-> | Hne]; [| exact Hl].
          exfalso. unfold p0 in Hl. rewrite (taken_not_live A1 gj mt aib slots idx HW1 Hmt Hrl ltac:(lia) Hslot) in Hl. discriminate Hl.
        * intros off n E. injection E as <- <-. intros ->. change (slot_start mt2 idx) with (slot_start mt idx) in Hl.
          rewrite Z.mul_0_r, Z.add_0_r in Hl. rewrite (taken_not_live A1 gj mt aib slots idx HW1 Hmt Hrl ltac:(lia) Hslot) in Hl. discriminate Hl.
      + intros [(off & E & _) | (Hl & Hne)]; [discriminate E|]. change (a_live nA2 q) with (nL2 q) in Hl. unfold nL2, lupd in Hl.
        destruct (Z.eq_dec q p0) as [-> | Hq]; [| exact Hl]. exfalso. apply (Hne 0 nn eq_refl). unfold p0. change (slot_start mt2 idx) with (slot_start mt idx). lia.
  Qed.
  Lemma dom_nA3 : forall x, dom nA3 x <-> dom A1 x.
  Proof using Hmt Hrl. pu_keep (Hmt, Hrl).
    intros x. split.
    - intros Hd. pose proof (dom_slot_set A1 gj mt aib slots idx (SLive 0 nn) Hmt Hrl nL2 x) as D1. rewrite nA2_eq in D1. apply D1.
      pose proof (dom_slot_set nA2 gj mt2 aib _ idx STaken nA2_gj mt2_role (a_live A1) x) as D2. rewrite nA3_eq in D2. apply D2. exact Hd.
    - intros [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & Rx) | Hp]]; [left; exact Ha | | right; right; exact Hp].
      right; left. destruct (Z.eq_dec y gj) as [-> | Hne].
      + rewrite Hmt in Hy. injection Hy as <-. exists gj, mt3, aib, slots3. split; [exact nA3_gj|]. split; [reflexivity|]. auto.
      + exists y, mty, aiby, sly. rewrite (nA3_other y Hne). auto.
  Qed.
  Lemma VMok_nA3 : forall h, VMok A1 h -> VMok nA3 h.
  Proof using Hmt Hrl. pu_keep (Hmt, Hrl).
    intros h Hv. apply (VMok_transfer A1 nA3 h Hv); try reflexivity.
    - intros x mtx aibx slx Hx Hrx Hml. destruct (Z.eq_dec x gj) as [-> | Hne].
      + rewrite nA3_gj in Hx. injection Hx as <-. exists mt, aib, slots. auto.
      + rewrite (nA3_other x Hne) in Hx. exists mtx, aibx, slx. auto.
    - intros x mt0 aib0 sl0 Hx Hrx Hml. destruct (Z.eq_dec x gj) as [-> | Hne].
      + rewrite Hmt in Hx. injection Hx as <-. exists mt3, aib, slots3. split; [exact nA3_gj | auto].
      + exists mt0, aib0, sl0. rewrite (nA3_other x Hne). auto.
  Qed.
  Lemma meta_usage_nA3 : forall c x, meta_usage nA3 c x = meta_usage A1 c x.
  Proof using Hmt Hrl. pu_keep (Hmt, Hrl).
    intros c x. unfold meta_usage. destruct (Z.eq_dec x gj) as [-> | Hne].
    - rewrite nA3_gj, Hmt, Hrl. unfold mt3. rewrite mt_role_MT. reflexivity.
    - rewrite (nA3_other x Hne). reflexivity.
  Qed.
  Lemma nA3_meta_inv : forall x mtx, a_meta nA3 x = Some mtx -> (x = gj /\ mtx = mt3) \/ (x <> gj /\ a_meta A1 x = Some mtx).
  Proof using Type. pu_keep tt.
    intros x mtx Hx. destruct (Z.eq_dec x gj) as [-> | Hne]; [left; rewrite nA3_gj in Hx; injection Hx as <-; auto | right].
    rewrite (nA3_other x Hne) in Hx. auto.
  Qed.
  (* [comment removed for export] *)
  Lemma nA3_grp_fwd : forall x mtx aibx slx, a_meta A1 x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    exists mtx' slx', a_meta nA3 x = Some mtx' /\ mt_role mtx' = RGroup aibx slx' /\ (forall fl, mt_f mtx' fl = mt_f mtx fl) /\
      (forall k, nth_error slx' k = nth_error slx k) /\ length slx' = length slx.
  Proof using Hmt Hrl Hslot. pu_keep (Hmt, Hrl, Hslot).
    intros x mtx aibx slx Hx Hrx. destruct (Z.eq_dec x gj) as [-> | Hne].
    - rewrite Hmt in Hx. injection Hx as <-. rewrite Hrl in Hrx. injection Hrx as <- <-.
      exists mt3, slots3. split; [exact nA3_gj|]. split; [reflexivity|]. split; [exact mt3_f|]. split; [exact slots3_nth | exact slots3_len].
    - exists mtx, slx. rewrite (nA3_other x Hne). auto.
  Qed.
  Lemma nA3_grp_back : forall x mtx' aibx slx', a_meta nA3 x = Some mtx' -> mt_role mtx' = RGroup aibx slx' ->
    exists mtx slx, a_meta A1 x = Some mtx /\ mt_role mtx = RGroup aibx slx /\ (forall fl, mt_f mtx' fl = mt_f mtx fl) /\
      (forall k, nth_error slx' k = nth_error slx k) /\ length slx' = length slx.
  Proof using Hmt Hrl Hslot. pu_keep (Hmt, Hrl, Hslot).
    intros x mtx' aibx slx' Hx Hrx. destruct (nA3_meta_inv x mtx' Hx) as [(-> & ->) | (Hne & H)].
    - cbn in Hrx. injection Hrx as <- <-. exists mt, slots. split; [exact Hmt|]. split; [exact Hrl|]. split; [exact mt3_f|]. split; [exact slots3_nth | exact slots3_len].
    - exists mtx', slx'. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma II_nA3 : forall s, IS sp0 argv envp cb nA3 s -> VMok A1 (ms_vm s) -> II sp0 argv envp cb (m :: D) nA3 s.
  Proof using HII Hmt Hrl. pu_keep (HII, Hmt, Hrl).
    intros s HIS Hvm. apply II_intro; [exact HIS | apply VMok_nA3; exact Hvm | | |].
    - apply (AvOK_transfer A1 nA3 (ii_av HII)); [reflexivity | reflexivity |].
      intros x mtx Hx Hrx. destruct (nA3_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | eauto].
    - apply (UsOK_transfer A1 nA3 (ii_us HII)); [reflexivity | intros; reflexivity | exact meta_usage_nA3].
    - apply (deads_transfer A1 nA3 (m :: D) (ii_dd HII)). intros x. split.
      + intros (mtx & Hx & Hrx). destruct (nA3_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | eauto].
      + intros (mtx & Hx & Hrx). exists mtx. destruct (Z.eq_dec x gj) as [-> | Hne]; [rewrite Hmt in Hx; injection Hx as <-; rewrite Hrl in Hrx; discriminate Hrx|].
        rewrite (nA3_other x Hne). auto.
  Qed.

  (* [comment removed for export] *)
  Definition nc4 : ctx_rec := cupd (a_ctx A1) (KUsage sc) (a_ctx A1 (KUsage sc) + cnt1).
  Definition nA4 : astate := set_ctx nA3 nc4.
  Definition nmd5 : meta_rec := MT (in_f mt3 idx cnt1 sc) RDead.
  Definition nA5 : astate := ameta_upd nA4 m nmd5.
  Definition nA6 (ab : Z) : astate := instN nA5 m gj mt3 aib slots3 idx cnt1 sc ab.
  Definition nestA (ab : Z) : astate := queA (nA6 ab) sc m [] m m.

  Lemma usage_now : a_ctx A1 (KUsage sc) = usage_of A1 sc /\ 0 <= usage_of A1 sc < 2^47.
  Proof using HW1 Hsc. pu_keep (HW1, Hsc). split; [exact (ii_us HII sc Hsc) | exact (usage_of_range A1 sc HW1)]. Qed.
  Lemma act0 : a_ctx A1 (KActive sc) = 0.
  Proof using HW1 Hact Hsc. pu_keep (HW1, Hact, Hsc). rewrite (wf_act_head A1 HW1 sc Hsc), Hact. reflexivity. Qed.
  Lemma nc4_heur : forall k, ctx_heur k \/ nc4 k = a_ctx nA3 k.
  Proof using Type. pu_keep tt. intros k. unfold nc4, cupd. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hne]; [left; exact I | right; reflexivity]. Qed.
  Lemma nc4_nn : forall k, 0 <= nc4 k.
  Proof using HW1 Hcnt1 Hj Hsc. pu_keep (HW1, Hcnt1, Hj, Hsc). intros k. unfold nc4, cupd. pose proof (wf_ctx_nonneg A1 HW1 k). pose proof (wf_ctx_nonneg A1 HW1 (KUsage sc)). destruct (cslot_eq_dec k (KUsage sc)); lia. Qed.
  Lemma WF4n : WF nA4. Proof using HW1 Hcnt1 Hidx Hj Hmt Hrl Hsc Hslot Hstride. pu_keep (HW1, Hcnt1, Hidx, Hj, Hmt, Hrl, Hsc, Hslot, Hstride). exact (WF_ctx_heur nA3 WF_nA3 nc4 nc4_heur nc4_nn). Qed.
  Lemma VMok4n : forall h, VMok A1 h -> VMok nA4 h. Proof using Hmt Hrl. pu_keep (Hmt, Hrl). intros h Hv. exact (VMok_ctx_heur nA3 nc4 nc4_heur h (VMok_nA3 h Hv)). Qed.
  Lemma nA5_meta : forall x, a_meta nA5 x = if Z.eq_dec x m then Some nmd5 else a_meta nA3 x.
  Proof using Type. pu_keep tt. intros x. reflexivity. Qed.
  Lemma nA5_m : a_meta nA5 m = Some nmd5.
  Proof using Type. pu_keep tt. rewrite nA5_meta. destruct (Z.eq_dec m m); [reflexivity | contradiction]. Qed.
  Lemma nA5_other : forall x, x <> m -> a_meta nA5 x = a_meta nA4 x.
  Proof using Type. pu_keep tt. intros x Hx. rewrite nA5_meta. destruct (Z.eq_dec x m); [contradiction | reflexivity]. Qed.
  Lemma nA5_gj : a_meta nA5 gj = Some mt3.
  Proof using Hidx Hm Hmt Hr Hrl Hscj Hstride. pu_keep (Hidx, Hm, Hmt, Hr, Hrl, Hscj, Hstride). rewrite (nA5_other gj gj_ne_m). exact nA3_gj. Qed.
  Lemma nmd5_f : forall fl, mt_f nmd5 fl = in_f mt3 idx cnt1 sc fl. Proof using Type. pu_keep tt. intros fl. unfold nmd5. apply mt_f_MT. Qed.
  Lemma WF5n : WF nA5.
  Proof using HW1 Hcnt1 Hidx Hj Hm Hmt Hr Hrl Hsc Hscj Hslot Hstride. pu_keep (HW1, Hcnt1, Hidx, Hj, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hstride). apply (WF_dead_local nA4 nA5 m md nmd5 WF4n); try reflexivity; [exact nA3_m | exact Hr | exact nA5_m | exact nA5_other]. Qed.
  Lemma VMok5n : forall h, VMok A1 h -> VMok nA5 h.
  Proof using Hidx Hm Hmt Hr Hrl Hscj Hstride. pu_keep (Hidx, Hm, Hmt, Hr, Hrl, Hscj, Hstride). intros h Hv. apply (VMok_dead_local nA4 nA5 m md nmd5); try reflexivity; [exact nA3_m | exact Hr | exact nA5_m | exact nA5_other | exact (VMok4n h Hv)]. Qed.
  Lemma Hfit5 : 16 + cnt1 * (16 * size_class sc) <= mt_stride mt3.
  Proof using Hfitj Hj Hsc Hstride. pu_keep (Hfitj, Hj, Hsc, Hstride). rewrite mt3_stride, Hstride. lia. Qed.
  Lemma Hsmall5 : 16 + cnt1 * (16 * size_class sc) <= 2048.
  Proof using Hj Hsc Hsmall. pu_keep (Hj, Hsc, Hsmall). lia. Qed.

  Section Ab.
    Variable ab : Z.
    Hypothesis Hab : 0 <= ab < 256.

    Lemma WF6n : WF (nA6 ab).
    Proof using HW1 Hab Hcnt1 Hfitj Hidx Hj Hm Hmt Hr Hrl Hsc Hscj Hslot Hsmall Hstride. pu_keep (HW1, Hab, Hcnt1, Hfitj, Hidx, Hj, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hsmall, Hstride).
      unfold nA6. apply (WF_instN nA5 m nmd5 gj mt3 aib slots3 idx cnt1 sc ab WF5n nA5_m eq_refl nA5_gj eq_refl ltac:(lia) slots3_idx Hsc Hcnt1 Hab Hfit5 Hsmall5).
    Qed.
    Lemma nA6_active : a_active (nA6 ab) = a_active A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma nA6_act_sc : a_active (nA6 ab) sc = []. Proof using Hact. pu_keep (Hact). rewrite nA6_active. exact Hact. Qed.
    Lemma nA6_m : a_meta (nA6 ab) m = Some (in_mt mt3 idx cnt1 sc ab). Proof using Type. pu_keep tt. unfold nA6. apply in_meta_m. Qed.
    Lemma nA6_gj : a_meta (nA6 ab) gj = Some (pm' m mt3 aib slots3 idx).
    Proof using Hidx Hm Hmt Hr Hrl Hscj Hstride. pu_keep (Hidx, Hm, Hmt, Hr, Hrl, Hscj, Hstride). unfold nA6. apply (in_meta_pa nA5 m nmd5 gj mt3 aib slots3 idx cnt1 sc ab nA5_m eq_refl nA5_gj eq_refl). Qed.
    Lemma nA6_other : forall x, x <> m -> x <> gj -> a_meta (nA6 ab) x = a_meta A1 x.
    Proof using Type. pu_keep tt.
      intros x Hx Hx'. unfold nA6. rewrite (in_meta_other nA5 m gj mt3 aib slots3 idx cnt1 sc ab x Hx Hx').
      rewrite (nA5_other x Hx). cbn [a_meta nA4 set_ctx]. change (a_meta nA4 x) with (a_meta nA3 x). exact (nA3_other x Hx').
    Qed.
    Lemma in_sc' : mt_sc (in_mt mt3 idx cnt1 sc ab) = sc.
    Proof using Hab Hcnt1 Hsc. pu_keep (Hab, Hcnt1, Hsc). apply (in_sc mt3 idx cnt1 sc ab Hsc Hcnt1 Hab). Qed.

    Lemma WF7n : WF (nestA ab).
    Proof using HW1 Hab Hact Hcnt1 Hfitj Hidx Hj Hm Hmt Hr Hrl Hsc Hscj Hslot Hsmall Hstride. pu_keep (HW1, Hab, Hact, Hcnt1, Hfitj, Hidx, Hj, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hsmall, Hstride).
      unfold nestA. apply (WF_queA (nA6 ab) WF6n sc m (in_mt mt3 idx cnt1 sc ab) (in_aib cnt1 ab) (in_slots cnt1) [] m m Hsc nA6_m eq_refl in_sc' nA6_act_sc eq_refl eq_refl ltac:(intros []));
        intros H; exfalso; exact (H eq_refl).
    Qed.

    Definition nmt7 : meta_rec := MallocInv_wf3.relink (qP m m m) (qN m m m) m (in_mt mt3 idx cnt1 sc ab).
    Lemma nestA_m : a_meta (nestA ab) m = Some nmt7.
    Proof using Type. pu_keep tt. unfold nestA. rewrite (queA_meta (nA6 ab) sc m [] m m m), nA6_m. reflexivity. Qed.
    Lemma nmt7_role : mt_role nmt7 = RGroup (in_aib cnt1 ab) (in_slots cnt1). Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma nmt7_f : forall fl, mt_f nmt7 fl = match fl with FPrev => m | FNext => m | _ => in_f mt3 idx cnt1 sc fl end.
    Proof using Type. pu_keep tt.
      intros fl. unfold nmt7, MallocInv_wf3.relink. rewrite mt_f_MT. unfold qP, qN. rewrite Z.eqb_refl. destruct fl; reflexivity.
    Qed.
    Lemma nestA_other : forall x, x <> m -> a_meta (nestA ab) x = a_meta (nA6 ab) x.
    Proof using Hact. pu_keep (Hact).
      intros x Hx. unfold nestA.
      exact (queA_meta_other (nA6 ab) sc m (in_mt mt3 idx cnt1 sc ab) (in_aib cnt1 ab) [] m m nA6_act_sc eq_refl eq_refl ltac:(intros [])
               ltac:(intros H; exfalso; exact (H eq_refl)) ltac:(intros H; exfalso; exact (H eq_refl)) ltac:(intros H; exfalso; exact (H eq_refl)) x Hx ltac:(intros [])).
    Qed.
    Lemma nestA_gj : a_meta (nestA ab) gj = Some (pm' m mt3 aib slots3 idx).
    Proof using Hact Hidx Hm Hmt Hr Hrl Hscj Hstride. pu_keep (Hact, Hidx, Hm, Hmt, Hr, Hrl, Hscj, Hstride). rewrite (nestA_other gj gj_ne_m). exact nA6_gj. Qed.
    Lemma nestA_old : forall x, x <> m -> x <> gj -> a_meta (nestA ab) x = a_meta A1 x.
    Proof using Hact. pu_keep (Hact). intros x Hx Hx'. rewrite (nestA_other x Hx). exact (nA6_other x Hx Hx'). Qed.
    Lemma nestA_meta_inv : forall x mtx, a_meta (nestA ab) x = Some mtx ->
      (x = m /\ mtx = nmt7) \/ (x = gj /\ mtx = pm' m mt3 aib slots3 idx) \/ (x <> m /\ x <> gj /\ a_meta A1 x = Some mtx).
    Proof using Hact Hidx Hm Hmt Hr Hrl Hscj Hstride. pu_keep (Hact, Hidx, Hm, Hmt, Hr, Hrl, Hscj, Hstride).
      intros x mtx Hx. destruct (Z.eq_dec x m) as [-> | Hne]; [left; rewrite nestA_m in Hx; injection Hx as <-; auto|].
      destruct (Z.eq_dec x gj) as [-> | Hne']; [right; left; rewrite nestA_gj in Hx; injection Hx as <-; auto | right; right].
      rewrite (nestA_old x Hne Hne') in Hx. auto.
    Qed.
    Lemma nestA_active_sc : a_active (nestA ab) sc = [m].
    Proof using Type. pu_keep tt. unfold nestA. rewrite (queA_active_sc (nA6 ab) sc m [] m m). reflexivity. Qed.
    Lemma nestA_active_other : forall c, c <> sc -> a_active (nestA ab) c = a_active A1 c.
    Proof using Type. pu_keep tt. intros c Hc. unfold nestA. rewrite (queA_active_other (nA6 ab) sc m [] m m c Hc). reflexivity. Qed.
    Lemma nestA_ctx : forall k, cvalid k -> a_ctx (nestA ab) k =
      if cslot_eq_dec k (KActive sc) then m else if cslot_eq_dec k (KUsage sc) then a_ctx A1 (KUsage sc) + cnt1 else a_ctx A1 k.
    Proof using HW1 Hab Hcnt1 Hfitj Hidx Hj Hm Hmt Hr Hrl Hsc Hscj Hslot Hsmall Hstride. pu_keep (HW1, Hab, Hcnt1, Hfitj, Hidx, Hj, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hsmall, Hstride). intros k Hk. unfold nestA. rewrite (queA_ctx_valid (nA6 ab) WF6n sc m [] m m Hsc eq_refl k Hk). reflexivity. Qed.
    Lemma nestA_areas : a_areas (nestA ab) = a_areas A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma nestA_freelist : a_freelist (nestA ab) = a_freelist A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma nestA_live : a_live (nestA ab) = a_live A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma nestA_xmaps : a_xmaps (nestA ab) = a_xmaps A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma nestA_pages : a_pages (nestA ab) = a_pages A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma nestA_mblocks : a_mblocks (nestA ab) = a_mblocks A1. Proof using Type. pu_keep tt. reflexivity. Qed.
    Lemma dom_nestA : forall x, dom (nestA ab) x <-> dom A1 x.
    Proof using Hab Hcnt1 Hidx Hm Hmt Hr Hrl Hsc Hscj Hslot Hstride. pu_keep (Hab, Hcnt1, Hidx, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hstride).
      intros x. unfold nestA. rewrite (dom_queA (nA6 ab) sc m [] m m x). unfold nA6.
      rewrite (dom_instN nA5 m nmd5 gj mt3 aib slots3 idx cnt1 sc ab nA5_m eq_refl nA5_gj eq_refl slots3_idx Hsc Hcnt1 Hab x).
      rewrite (dom_dead_local nA4 nA5 m md nmd5 nA3_m Hr nA5_m eq_refl nA5_other eq_refl eq_refl x).
      rewrite (dom_set_ctx nA3 nc4 x). apply dom_nA3.
    Qed.
    Lemma VMok7n : VMok (nestA ab) (ms_vm s1).
    Proof using HII Hab Hcnt1 Hidx Hm Hmt Hr Hrl Hsc Hscj Hslot Hstride. pu_keep (HII, Hab, Hcnt1, Hidx, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hstride).
      unfold nestA. apply (VMok_queA (nA6 ab) sc m [] m m). unfold nA6.
      apply (VMok_instN nA5 m nmd5 gj mt3 aib slots3 idx cnt1 sc ab nA5_m eq_refl nA5_gj eq_refl slots3_idx Hsc Hcnt1 Hab).
      apply VMok5n. exact (ii_vm HII).
    Qed.
    Lemma meta_usage_nestA : forall c x, meta_usage (nestA ab) c x = meta_usage A1 c x + (if Z.eq_dec x m then (if sc =? c then cnt1 else 0) else 0).
    Proof using Hab Hact Hcnt1 Hidx Hj Hm Hmt Hr Hrl Hsc Hscj Hstride. pu_keep (Hab, Hact, Hcnt1, Hidx, Hj, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hstride).
      intros c x. unfold meta_usage at 1. destruct (Z.eq_dec x m) as [-> | Hne].
      - rewrite nestA_m. transitivity (if mt_sc (in_mt mt3 idx cnt1 sc ab) =? c then mt_cnt (in_mt mt3 idx cnt1 sc ab) else 0); [reflexivity|].
        rewrite in_sc', (in_cnt mt3 idx cnt1 sc ab Hsc Hcnt1 Hab). unfold meta_usage. rewrite Hm, Hr. destruct (sc =? c); lia.
      - destruct (Z.eq_dec x gj) as [-> | Hne'].
        + rewrite nestA_gj. transitivity (if mt_sc mt =? c then mt_cnt mt else 0); [reflexivity|].
          unfold meta_usage. rewrite Hmt, Hrl. lia.
        + rewrite (nestA_old x Hne Hne'). unfold meta_usage. lia.
    Qed.
    Lemma UsOK7n : UsOK (nestA ab).
    Proof using HW1 Hab Hact Hcnt1 Hfitj Hidx Hj Hm Hmt Hr Hrl Hsc Hscj Hslot Hsmall Hstride. pu_keep (HW1, Hab, Hact, Hcnt1, Hfitj, Hidx, Hj, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hsmall, Hstride).
      intros c Hc. rewrite (nestA_ctx (KUsage c) ltac:(cbn; lia)).
      destruct (cslot_eq_dec (KUsage c) (KActive sc)) as [E | _]; [discriminate E|].
      destruct (proj1 (wf_meta_dom A1 HW1 m) ltac:(rewrite Hm; discriminate)) as (pg & k & Hpg & Hk & Em).
      rewrite (usage_of_point A1 (nestA ab) c m pg k (- (if sc =? c then cnt1 else 0)) HW1 eq_refl Hpg Hk Em).
      - destruct (cslot_eq_dec (KUsage c) (KUsage sc)) as [E | Hne].
        + injection E as ->. rewrite Z.eqb_refl. rewrite (ii_us HII sc Hsc). lia.
        + replace (sc =? c) with false by (symmetry; apply Z.eqb_neq; intros ->; exact (Hne eq_refl)). rewrite (ii_us HII c Hc). lia.
      - intros x Hx. rewrite meta_usage_nestA. destruct (Z.eq_dec x m); [contradiction | lia].
      - rewrite meta_usage_nestA. destruct (Z.eq_dec m m); [lia | contradiction].
    Qed.
    Lemma AvOK7n : AvOK (nestA ab).
    Proof using HW1 Hab Hact Hcnt1 Hfitj Hidx Hj Hm Hmt Hr Hrl Hsc Hscj Hslot Hsmall Hstride. pu_keep (HW1, Hab, Hact, Hcnt1, Hfitj, Hidx, Hj, Hm, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hsmall, Hstride).
      apply (AvOK_transfer A1 (nestA ab) (ii_av HII)); [reflexivity | |].
      - rewrite (nestA_ctx KAmc I). reflexivity.
      - intros x mt' Hx Hrx. destruct (nestA_meta_inv x mt' Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & H)]]; [cbn in Hrx; discriminate Hrx | cbn in Hrx; discriminate Hrx | eauto].
    Qed.
    Lemma deads7n : deads (nestA ab) D.
    Proof using HII Hact Hidx Hm HmD Hmt Hr Hrl Hscj Hstride. pu_keep (HII, Hact, Hidx, Hm, HmD, Hmt, Hr, Hrl, Hscj, Hstride).
      intros x. split.
      - intros (mtx & Hx & Hrx). destruct (nestA_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (Hn1 & Hn2 & H)]]; [cbn in Hrx; discriminate Hrx | cbn in Hrx; discriminate Hrx |].
        destruct (proj1 (ii_dd HII x) (ex_intro _ mtx (conj H Hrx))) as [-> | Hin']; [contradiction | exact Hin'].
      - intros Hin'. assert (Hne : x <> m) by (intros ->; exact (HmD Hin')).
        destruct (proj2 (ii_dd HII x) (or_intror Hin')) as (mtx & Hx & Hrx).
        assert (Hne' : x <> gj) by (intros ->; rewrite Hmt in Hx; injection Hx as <-; rewrite Hrl in Hrx; discriminate Hrx).
        exists mtx. rewrite (nestA_old x Hne Hne'). auto.
    Qed.
  End Ab.

  (* [comment removed for export] *)
  Lemma span_m_apart : ne + 1 <= m \/ m + 40 <= p0 - 4.
  Proof using HW1 Hidx Hj Hm Hmt Hrl Hsc Hslot Hstride. pu_keep (HW1, Hidx, Hj, Hm, Hmt, Hrl, Hsc, Hslot, Hstride).
    pose proof idx_facts as (C & S16g & _). destruct (slot_in_ext mt idx ltac:(lia) C ltac:(lia)) as [E1 E2]. pose proof ne_eq as NE. pose proof szj_rng.
    unfold p0, ne in *.
    destruct (meta_grp_apart A1 m md gj mt aib slots (slot_start mt idx - 4) HW1 Hm Hmt Hrl ltac:(unfold gext_lo in *; lia)) as [H1 | H1]; [right; lia |].
    destruct (meta_grp_apart A1 m md gj mt aib slots (slot_end mt idx) HW1 Hm Hmt Hrl ltac:(unfold gext_lo in *; lia)) as [H2 | H2]; [| left; lia].
    exfalso. destruct (meta_grp_apart A1 m md gj mt aib slots m HW1 Hm Hmt Hrl ltac:(unfold gext_lo in *; lia)); lia.
  Qed.

  (* [comment removed for export] *)
  Fixpoint zws (t : Z) (k : nat) : list fct :=
    match k with O => [] | S k' => zws (t + 1) k' ++ [FCT (p0 + 12 + t * nsize) 1 0] end.

  Lemma zws_in : forall k t w, In w (zws t k) -> exists t', t <= t' < t + Z.of_nat k /\ w = FCT (p0 + 12 + t' * nsize) 1 0.
  Proof using Hj Hsc. pu_keep (Hj, Hsc).
    induction k as [|k IH]; intros t w Hw; [destruct Hw|]. cbn [zws] in Hw. apply in_app_iff in Hw. destruct Hw as [Hw | [<- | []]].
    - destruct (IH (t + 1) w Hw) as (t' & Ht' & ->). exists t'. split; [lia | reflexivity].
    - exists t. split; [lia | reflexivity].
  Qed.

  Lemma wlook_zws : forall k t ws x b, wlook (zws t k ++ ws) x = Some b ->
    (b = 0 /\ exists t', t <= t' < t + Z.of_nat k /\ x = p0 + 12 + t' * nsize) \/ wlook ws x = Some b.
  Proof using Hj Hsc. pu_keep (Hj, Hsc).
    induction k as [|k IH]; intros t ws x b Hw; [right; exact Hw|]. cbn [zws] in Hw. rewrite <- app_assoc in Hw.
    destruct (IH (t + 1) _ x b Hw) as [(-> & t' & Ht' & ->) | Hw']; [left; split; [reflexivity | exists t'; split; [lia | reflexivity]]|].
    cbn [wlook app] in Hw'. destruct (wcov (FCT (p0 + 12 + t * nsize) 1 0) x) eqn:E.
    - apply wcov_spec in E. cbn [f_a f_n] in E. injection Hw' as <-. left. split; [cbn [f_v f_a]; apply byte_of_zero | exists t; split; [lia | lia]].
    - right. exact Hw'.
  Qed.

  Lemma wlook_zws_none : forall k t ws x, (forall t', t <= t' < t + Z.of_nat k -> x <> p0 + 12 + t' * nsize) -> wlook (zws t k ++ ws) x = wlook ws x.
  Proof using Hj Hsc. pu_keep (Hj, Hsc).
    induction k as [|k IH]; intros t ws x Hx; [reflexivity|]. cbn [zws]. rewrite <- app_assoc. rewrite IH by (intros t' Ht'; apply Hx; lia).
    cbn [wlook app]. destruct (wcov (FCT (p0 + 12 + t * nsize) 1 0) x) eqn:E; [| reflexivity].
    exfalso. apply wcov_spec in E. cbn [f_a f_n] in E. apply (Hx t); lia.
  Qed.

  Lemma wlook_zws_hit : forall k t ws t', t <= t' < t + Z.of_nat k -> wlook (zws t k ++ ws) (p0 + 12 + t' * nsize) = Some 0.
  Proof using Hj Hsc. pu_keep (Hj, Hsc).
    induction k as [|k IH]; intros t ws t' Ht'; [lia|]. cbn [zws]. rewrite <- app_assoc.
    destruct (Z.eq_dec t' t) as [-> | Hne].
    - rewrite wlook_zws_none.
      + cbn [wlook app]. rewrite (proj2 (wcov_spec _ _)) by (cbn [f_a f_n]; lia). cbn [f_v f_a]. rewrite Z.sub_diag, byte_of_zero. reflexivity.
      + intros t2 Ht2 E. pose proof szc_rng. unfold nsize in E. assert (t * size_class sc = t2 * size_class sc) by lia.
        assert (t = t2) by (apply (Z.mul_reg_r _ _ (size_class sc)); lia). lia.
    - apply IH. lia.
  Qed.

  Lemma ts_zl : forall k t s ws (K : unit -> M R) P (m0 : word -> option byte),
    RepW nA3 m0 ws (ms_mem s) -> WIN s -> 0 <= t -> t + Z.of_nat k <= cnt1 + 1 ->
    (forall m', RepW nA3 m0 (zws t k ++ ws) m' -> tsafe (K tt (upd s m' (ms_vm s))) P) ->
    tsafe ((x <- zl (Z_to_bv 64 nsize) k (Z_to_bv 64 (p0 + 12 + t * nsize)) ;; K x) s) P.
  Proof using HW1 Hcnt1 Hfitj Hidx Hj Hmt Hrl Hsc Hslot Hstride MLok. pu_keep (HW1, Hcnt1, Hfitj, Hidx, Hj, Hmt, Hrl, Hsc, Hslot, Hstride, MLok).
    induction k as [|k IH]; intros t s ws K P m0 RW HWIN Ht Hk HK.
    - cbn [zl]. apply ts_bind_ret. specialize (HK (ms_mem s)). cbn [zws app] in HK. destruct s as [mm vv lo hi]. cbn [upd ms_mem ms_vm] in HK. apply HK. exact RW.
    - cbn [zl]. reassoc. pose proof ne_eq as NE. pose proof szj_rng. pose proof szc_rng.
      assert (Ht1 : 0 <= t * nsize /\ t * nsize <= cnt1 * nsize) by (unfold nsize; split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
      unfold m_sb. eapply (ts_st_domW nA3 WF_nA3 s m0 ws 1 (p0 + 12 + t * nsize)); [exact RW | exact HWIN | lia | |].
      { intros j0 Hj0. apply (proj2 (dom_nA3 _)). apply span_dom. unfold nsize in *. lia. }
      intros m1 RW1. rewrite v_add_Z. replace (p0 + 12 + t * nsize + nsize) with (p0 + 12 + (t + 1) * nsize) by lia.
      apply (IH (t + 1) (upd s m1 (ms_vm s)) _ K P m0 RW1 HWIN ltac:(lia) ltac:(lia)).
      intros m' RW'. change (bv_unsigned w0) with 0 in RW'.
      assert (E : zws (t + 1) k ++ FCT (p0 + 12 + t * nsize) (Z.of_nat 1) 0 :: ws = zws t (S k) ++ ws) by (cbn [zws]; rewrite <- app_assoc; reflexivity).
      rewrite E in RW'. exact (HK m' RW').
  Qed.

  (* [comment removed for export] *)
  Definition OFU : Z := (p0 - mt_mem mt - 16) / 16.

  Lemma nA2_hdr_facts : has nA2 (FCT (p0 - 3) 1 idx) /\ has nA2 (FCT (p0 - 2) 2 OFU) /\ has nA2 (FCT ne 1 0) /\ has nA2 (FCT (p0 - 4) 1 0).
  Proof using Hcnt1 Hidx Hj Hsc Hslot Hstride. pu_keep (Hcnt1, Hidx, Hj, Hsc, Hslot, Hstride).
    pose proof ne_eq as NE. pose proof nn_facts as (N1 & N2 & N3 & N4).
    assert (G : forall f, In f (slot_fields mt2 idx (SLive 0 nn)) -> has nA2 f).
    { intros f Hf. right; right; right. exists gj, mt2, aib, (list_set slots (Z.to_nat idx) (SLive 0 nn)). split; [exact nA2_gj|]. split; [reflexivity|].
      right. exists (Z.to_nat idx), (SLive 0 nn). split; [exact slots2_idx|]. rewrite Z2Nat.id by lia. exact Hf. }
    assert (Ess : slot_start mt2 idx = p0) by reflexivity. assert (Ese : slot_end mt2 idx = ne) by reflexivity.
    assert (Emem : mt_mem mt2 = mt_mem mt) by reflexivity. assert (Estr : mt_stride mt2 = mt_stride mt) by reflexivity.
    unfold slot_fields, slot_fields_g in G. unfold slot_start, slot_end in Ess, Ese. rewrite Ess, Ese, Emem in G.
    cbn [Z.eqb] in G.
    replace (p0 + 16 * 0) with p0 in G by lia. replace (ne - p0 - nn) with 0 in G by (rewrite NE; unfold nn; lia).
    change (Z.min 0 5) with 0 in G. replace (idx + 32 * 0) with idx in G by lia.
    split; [| split; [| split]]; apply G; cbn [In app]; tauto.
  Qed.

  Lemma nA3_end_facts : has nA3 (FCT ne 1 0) /\ has nA3 (FCT (p0 - 4) 1 0).
  Proof using Hidx Hj Hsc Hslot. pu_keep (Hidx, Hj, Hsc, Hslot).
    assert (G : forall f, In f (slot_fields mt3 idx STaken) -> has nA3 f).
    { intros f Hf. right; right; right. exists gj, mt3, aib, slots3. split; [exact nA3_gj|]. split; [reflexivity|].
      right. exists (Z.to_nat idx), STaken. split; [exact slots3_idx|]. rewrite Z2Nat.id by lia. exact Hf. }
    split; apply G; unfold slot_fields, slot_fields_g; cbn [In app]; [right; left | left]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition pre_ws : list fct := zws 0 (S (Z.to_nat cnt1)) ++ [FCT (p0 - 3) 1 (idx + 192); FCT (m + 32) 8 0].

  Lemma pre_commit : forall m2 m9, Rep nA2 m2 -> Rep nA3 m2 -> RepW nA3 m2 pre_ws m9 ->
    Rep nA3 m9 /\
    (forall t, 0 <= t <= cnt1 -> mbyte m9 (p0 + 12 + t * nsize) = Some 0) /\
    mbyte m9 (p0 - 3) = Some (idx + 192) /\ mbyte m9 (p0 - 2) = Some (OFU mod 256) /\ mbyte m9 (p0 - 1) = Some ((OFU / 256) mod 256) /\
    (forall a : word, (u a < p0 - 3 \/ ne + 1 <= u a) -> ~ (m + 32 <= u a < m + 40) -> m9 a = m2 a).
  Proof using HW1 Hcnt1 Hfitj Hidx Hj Hm Hmd0 Hmt Hr Hrl Hsc Hscj Hslot Hstride MLok. pu_keep (HW1, Hcnt1, Hfitj, Hidx, Hj, Hm, Hmd0, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hstride, MLok).
    intros m2 m9 R2 R3 RW. pose proof ne_eq as NE. pose proof szj_rng as SZJ. pose proof szc_rng as SZC. pose proof span_m_apart as SM.
    pose proof idx_facts as (C & S16g & I32). pose proof (meta_facts nA3 m md WF_nA3 nA3_m) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    pose proof span_heap as (SH1 & SH2 & SH3).
    destruct nA2_hdr_facts as (F3 & F2 & Fe & F4).
    (* [comment removed for export] *)
    assert (WL : forall x b, wlook pre_ws x = Some b ->
      (b = 0 /\ exists t', 0 <= t' < Z.of_nat (S (Z.to_nat cnt1)) /\ x = p0 + 12 + t' * nsize) \/
      (x = p0 - 3 /\ b = byte_of (idx + 192) 0) \/ (m + 32 <= x < m + 40 /\ b = byte_of 0 (x - (m + 32)))).
    { intros x b Hw. unfold pre_ws in Hw. destruct (wlook_zws _ 0 _ x b Hw) as [Hz | Hw']; [left; exact Hz | right].
      cbn [wlook app] in Hw'. destruct (wcov (FCT (p0 - 3) 1 (idx + 192)) x) eqn:E1.
      - apply wcov_spec in E1. cbn [f_a f_n] in E1. injection Hw' as <-. left. cbn [f_v f_a]. split; [lia|]. f_equal. lia.
      - destruct (wcov (FCT (m + 32) 8 0) x) eqn:E2; [| discriminate Hw'].
        apply wcov_spec in E2. cbn [f_a f_n] in E2. injection Hw' as <-. right. cbn [f_v f_a]. split; [lia | reflexivity]. }
    assert (SC : forall f, has nA3 f -> f_a f + f_n f <= p0 - 3 \/ ne <= f_a f).
    { intros f Hf. exact (span_clear nA3 WF_nA3 gj mt3 aib slots3 idx STaken nA3_gj mt3_role slots3_idx ltac:(lia) (or_intror eq_refl) f Hf). }
    assert (HR9 : Rep nA3 m9).
    { apply (repw_commit4 nA3 nA3 m2 pre_ws m9 WF_nA3 RW).
      - intros f Hf. left. exact Hf.
      - intros x b Hw. destruct (WL x b Hw) as [(-> & t' & Ht' & ->) | [(-> & ->) | (Hx & ->)]].
        + (* [comment removed for export] *)
          right; right; right. intros f Hf Hcov.
          assert (Ht2 : 0 <= t' * nsize /\ t' * nsize <= cnt1 * nsize) by (unfold nsize; split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
          destruct (SC f Hf) as [Dc | Dc]; [exfalso; lia|].
          assert (Ex : f_a f = ne /\ p0 + 12 + t' * nsize = ne) by (unfold nsize in *; lia). destruct Ex as [Efa Ex]. rewrite Ex.
          pose proof (rep_consistent nA3 m2 f (FCT ne 1 0) ne R3 Hf (proj1 nA3_end_facts) ltac:(lia) ltac:(cbn; lia)) as E.
          cbn [f_v f_a] in E. rewrite Z.sub_diag, byte_of_zero in E. exact E.
        + (* [comment removed for export] *)
          right; right; right. intros f Hf Hcov. exfalso. destruct (SC f Hf); lia.
        + (* [comment removed for export] *)
          left. exists m, md, FW32. split; [exact nA3_m|]. cbn [moff mlen]. split; [lia|]. rewrite (Hmd0 FW32). reflexivity.
      - intros x Hx. left. exact Hx. }
    split; [exact HR9|]. split.
    { intros t Ht. apply (rw_wr nA3 m2 pre_ws m9 RW). unfold pre_ws. apply wlook_zws_hit. lia. }
    split.
    { transitivity (Some (byte_of (idx + 192) 0)); [| f_equal; rewrite byte_of_0; apply Z.mod_small; lia].
      apply (rw_wr nA3 m2 pre_ws m9 RW). unfold pre_ws. rewrite wlook_zws_none by (intros t' Ht'; unfold nsize; pose proof (Z.mul_nonneg_nonneg t' (16 * size_class sc)); lia).
      cbn [wlook app]. rewrite (proj2 (wcov_spec _ _)) by (cbn [f_a f_n]; lia). cbn [f_v f_a]. rewrite Z.sub_diag. reflexivity. }
    assert (FR2 : forall x, (x = p0 - 2 \/ x = p0 - 1) -> mbyte m9 x = mbyte m2 x).
    { intros x Hx. apply mbyte_ext. apply (rw_frame nA3 m2 pre_ws m9 RW). rewrite uZ by lia. apply wlook_free_inv.
      unfold pre_ws. rewrite wlook_zws_none by (intros t' Ht'; unfold nsize; pose proof (Z.mul_nonneg_nonneg t' (16 * size_class sc)); lia).
      cbn [wlook app].
      destruct (wcov (FCT (p0 - 3) 1 (idx + 192)) x) eqn:E1; [apply wcov_spec in E1; cbn [f_a f_n] in E1; lia|].
      destruct (wcov (FCT (m + 32) 8 0) x) eqn:E2; [apply wcov_spec in E2; cbn [f_a f_n] in E2; lia|]. reflexivity. }
    split.
    { rewrite (FR2 (p0 - 2) (or_introl eq_refl)). apply (rep_facts nA2 m2 R2). exists (FCT (p0 - 2) 2 OFU). split; [exact F2|]. split; [cbn; lia | cbn [f_v f_a]; rewrite Z.sub_diag, byte_of_0; reflexivity]. }
    split.
    { rewrite (FR2 (p0 - 1) (or_intror eq_refl)). apply (rep_facts nA2 m2 R2). exists (FCT (p0 - 2) 2 OFU). split; [exact F2|]. split; [cbn; lia | cbn [f_v f_a]]. replace (p0 - 1 - (p0 - 2)) with 1 by lia. rewrite byte_of_1. reflexivity. }
    intros a Ha Hm32. apply (rw_frame nA3 m2 pre_ws m9 RW). apply wlook_free_inv. unfold pre_ws.
    pose proof (u64_range a).
    rewrite wlook_zws_none by (intros t' Ht'; unfold nsize in *; pose proof (Z.mul_nonneg_nonneg t' (16 * size_class sc)); assert (t' * (16 * size_class sc) <= cnt1 * (16 * size_class sc)) by (apply Z.mul_le_mono_nonneg_r; lia); lia).
    cbn [wlook app]. destruct (wcov (FCT (p0 - 3) 1 (idx + 192)) (u a)) eqn:E1; [apply wcov_spec in E1; cbn [f_a f_n] in E1; lia|].
    destruct (wcov (FCT (m + 32) 8 0) (u a)) eqn:E2; [apply wcov_spec in E2; cbn [f_a f_n] in E2; lia|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Section Ab2.
    Variable ab : Z.
    Hypothesis Hab : 0 <= ab < 256.

    Lemma nest_commit : forall m2 m9 m' av1 fr av2,
      Rep nA2 m2 -> Rep nA3 m2 -> RepW nA3 m2 pre_ws m9 ->
      av1 mod 2^32 = 2^(cnt1 - 1 + 1) - 1 -> fr mod 2^32 = ifr cnt1 (cnt1 - 1) -> av2 mod 2^32 = iav cnt1 (cnt1 - 1) -> 0 <= av1 -> 0 <= fr -> 0 <= av2 ->
      RepW nA3 m9 (tail_ws nA3 m sc cnt1 (cnt1 - 1) p0 0 ab av1 fr av2) m' ->
      Rep (nestA ab) m'.
    Proof using HW1 Hab Hact Hcnt1 Hfitj Hidx Hj Hm Hmd0 Hmt Hr Hrl Hsc Hscj Hslot Hsmall Hstride MLok. pu_keep (HW1, Hab, Hact, Hcnt1, Hfitj, Hidx, Hj, Hm, Hmd0, Hmt, Hr, Hrl, Hsc, Hscj, Hslot, Hsmall, Hstride, MLok).
      intros m2 m9 m' av1 fr av2 R2 R3 RW9 Hav1 Hfr Hav2 P1 P2 P3 RW.
      destruct (pre_commit m2 m9 R2 R3 RW9) as (R9 & Z9 & B3 & B2a & B2b & FR9).
      pose proof (meta_facts nA3 m md WF_nA3 nA3_m) as (M1 & M2 & M3 & M4 & Mdom). ceil. pose proof layout_small as LS.
      pose proof (ctx_slot_range (KUsage sc) ltac:(cbn; lia)) as (U1 & U2 & U3). cbn [clen] in U2, U3.
      pose proof (ctx_slot_range (KActive sc) ltac:(cbn; lia)) as (C1 & C2 & C3). cbn [clen] in C2, C3. unfold CTX_END in U2, C2.
      pose proof (caddr_usage sc) as CU. pose proof (caddr_active sc) as CA. pose proof span_m_apart as Hpm. pose proof span_heap as (SH1 & SH2 & SH3).
      pose proof ne_eq as NE. pose proof szj_rng as SZJ. pose proof szc_rng as SZC. pose proof act0 as Hact0.
      pose proof (masks_facts cnt1 (cnt1 - 1) ltac:(lia) ltac:(lia)) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). pose proof (iav_eq cnt1 (cnt1 - 1) ltac:(lia) ltac:(lia)) as Eiav.
      set (TW := tail_ws nA3 m sc cnt1 (cnt1 - 1) p0 0 ab av1 fr av2) in RW.
      assert (INW : forall w, In w TW ->
        w = FCT (caddr (KActive sc)) 8 m \/ w = FCT (m + 8) 8 m \/ w = FCT m 8 m \/ w = FCT (m + 24) 4 av2 \/
        w = FCT (m + 32) 8 (iw32 0 sc cnt1) \/ w = FCT (p0 + 8) 1 (Z.lor (cnt1 - 1) (Z.land ab 224)) \/ w = FCT p0 8 m \/
        w = FCT (m + 16) 8 p0 \/ w = FCT (m + 28) 4 fr \/ w = FCT (m + 24) 4 av1 \/ w = FCT (caddr (KUsage sc)) 8 (a_ctx nA3 (KUsage sc) + cnt1)).
      { intros w Hw. unfold TW, tail_ws in Hw. cbn [In] in Hw. intuition auto. }
      assert (ZR : forall t, 0 <= t <= cnt1 -> p0 + 12 <= p0 + 12 + t * nsize /\ p0 + 12 + t * nsize + 1 <= ne + 1).
      { intros t Ht. unfold nsize. assert (0 <= t * (16 * size_class sc)) by (apply Z.mul_nonneg_nonneg; lia).
        assert (t * (16 * size_class sc) <= cnt1 * (16 * size_class sc)) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
      apply (repw_commit4 nA3 (nestA ab) m9 TW m' (WF7n ab Hab) RW).
      - intros f Hf. unfold nestA in Hf.
        destruct (has_queA_inv (nA6 ab) (WF6n ab Hab) sc m [] m m Hsc eq_refl f Hf) as [Hf6 | [-> | (x0 & mt0 & fl & Hx0 & Hfl & Hx0m & ->)]].
        + unfold nA6 in Hf6.
          destruct (has_instN nA5 m nmd5 gj mt3 aib slots3 idx cnt1 sc ab nA5_m nA5_gj eq_refl ltac:(lia) slots3_idx Hsc Hcnt1 Hab nmd5_f f Hf6)
            as [Hf5 | [-> | [-> | [(t & Ht & Hft) | [-> | ->]]]]].
          * destruct (has_dead_local nA4 nA5 m md nmd5 nA5_m eq_refl nA5_other eq_refl eq_refl f Hf5) as [[Hf4 Hnot] | [(fl & ->) | Hf4]].
            -- destruct (has_set_ctx nA3 nc4 f Hf4) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | [Hmf | Hg]]]].
               ++ unfold nc4, cupd. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hku].
                  ** right; left. cbn [f_a f_n clen]. intros x Hx. unfold TW, tail_ws.
                     do 10 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
                  ** destruct (cslot_eq_dec k (KActive sc)) as [-> | Hka].
                     { right; left. cbn [f_a f_n clen]. intros x Hx. unfold TW, tail_ws. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate. }
                     left. left. exists k. auto.
               ++ left. right; left. exact Har.
               ++ left. right; left. exists pg. auto.
               ++ destruct Hmf as (x & mtx & fl & Hx0 & ->). assert (Hx : a_meta nA3 x = Some mtx) by exact Hx0. clear Hx0.
                  destruct (Z.eq_dec x m) as [-> | Hne]; [exfalso; rewrite nA3_m in Hx; injection Hx as <-; exact (Hnot fl eq_refl)|].
                  left. right; right; left. exists x, mtx, fl. auto.
               ++ left. right; right; right. exact Hg.
            -- right; left. rewrite nmd5_f. pose proof (mfield_range fl) as Hflr. intros x Hx. cbn [f_a f_n] in Hx. unfold TW, tail_ws.
               destruct fl; cbn [moff mlen] in Hx;
                 repeat (first [rewrite wlook_skip by (cbn [f_a f_n]; lia) | rewrite wlook_hit by (cbn [f_a f_n]; lia)]); discriminate.
            -- destruct (has_set_ctx nA3 nc4 f Hf4) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | [Hmf | Hg]]]].
               ++ unfold nc4, cupd. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hku].
                  ** right; left. cbn [f_a f_n clen]. intros x Hx. unfold TW, tail_ws.
                     do 10 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
                  ** destruct (cslot_eq_dec k (KActive sc)) as [-> | Hka].
                     { right; left. cbn [f_a f_n clen]. intros x Hx. unfold TW, tail_ws. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate. }
                     left. left. exists k. auto.
               ++ left. right; left. exact Har.
               ++ left. right; left. exists pg. auto.
               ++ destruct Hmf as (x & mtx & fl & Hx0 & ->). assert (Hx : a_meta nA3 x = Some mtx) by exact Hx0. clear Hx0.
                  destruct (Z.eq_dec x m) as [-> | Hne].
                  ** rewrite nA3_m in Hx. injection Hx as <-. right; left. pose proof (mfield_range fl) as Hflr. intros y Hy. cbn [f_a f_n] in Hy. unfold TW, tail_ws.
                     destruct fl; cbn [moff mlen] in Hy;
                       repeat (first [rewrite wlook_skip by (cbn [f_a f_n]; lia) | rewrite wlook_hit by (cbn [f_a f_n]; lia)]); discriminate.
                  ** left. right; right; left. exists x, mtx, fl. auto.
               ++ left. right; right; right. exact Hg.
          * (* [comment removed for export] *) right; left. cbn [f_a f_n]. change (in_p mt3 idx) with p0. intros x Hx. unfold TW, tail_ws.
            do 6 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
          * (* [comment removed for export] *) right; left. cbn [f_a f_n]. change (in_p mt3 idx) with p0. intros x Hx. unfold TW, tail_ws.
            do 5 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
          * (* [comment removed for export] *)
            right; right.
            assert (Hfz : f_v f = 0 /\ f_n f = 1 /\ exists t0, 0 <= t0 <= cnt1 /\ f_a f = p0 + 12 + t0 * nsize).
            { pose proof (in_stride mt3 idx cnt1 sc ab Hsc Hcnt1 Hab) as IS'. pose proof (in_mem mt3 idx cnt1 sc ab) as IM.
              unfold slot_start, slot_end, slot_start_g, slot_end_g in Hft. rewrite IS', IM in Hft. change (in_p mt3 idx) with p0 in Hft.
              destruct Hft as [-> | ->]; cbn [f_a f_n f_v]; (split; [reflexivity|]); (split; [reflexivity|]).
              - exists (Z.of_nat t). unfold nsize. split; [lia | lia].
              - exists (Z.of_nat t + 1). unfold nsize. split; [lia | lia]. }
            destruct Hfz as (Ev & En & t0 & Ht0 & Ea). rewrite Ev, En, Ea. destruct (ZR t0 Ht0) as [Z1 Z2]. intros x Hx. split.
            -- unfold TW, tail_ws. repeat (rewrite wlook_skip by (cbn [f_a f_n]; lia)). reflexivity.
            -- rewrite byte_of_zero. replace x with (p0 + 12 + t0 * nsize) by lia. apply Z9. exact Ht0.
          * (* [comment removed for export] *)
            right; right. cbn [f_a f_n f_v]. change (in_p mt3 idx) with p0. intros x Hx. split.
            -- unfold TW, tail_ws. repeat (rewrite wlook_skip by (cbn [f_a f_n]; lia)). reflexivity.
            -- replace x with (p0 - 3) by lia. rewrite Z.sub_diag, byte_of_0. rewrite B3. f_equal. symmetry. apply Z.mod_small. pose proof idx_facts as (_ & _ & I32). lia.
          * (* [comment removed for export] *)
            right; right. cbn [f_a f_n f_v]. change (in_p mt3 idx) with p0. change (mt_mem mt3) with (mt_mem mt). fold OFU. intros x Hx. split.
            -- unfold TW, tail_ws. repeat (rewrite wlook_skip by (cbn [f_a f_n]; lia)). reflexivity.
            -- destruct (Z.eq_dec x (p0 - 2)) as [-> | Hx1].
               ++ rewrite Z.sub_diag, byte_of_0. exact B2a.
               ++ replace x with (p0 - 1) by lia. replace (p0 - 1 - (p0 - 2)) with 1 by lia. rewrite byte_of_1. exact B2b.
        + (* [comment removed for export] *) right; left. cbn [f_a f_n]. intros x Hx. unfold TW, tail_ws. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
        + (* [comment removed for export] *) assert (x0 = m) by tauto. subst x0. right; left. intros x Hx. cbn [f_a f_n] in Hx. unfold TW, tail_ws.
          destruct Hfl as [-> | ->]; cbn [moff mlen] in Hx.
          * rewrite wlook_skip by (cbn [f_a f_n]; lia). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
          * do 2 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
      - (* [comment removed for export] *)
        intros x b Hw. destruct (wlook_some_cov TW x b Hw) as (w & Hwin & Hwx).
        destruct (INW w Hwin) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]; cbn [f_a f_n] in Hwx; unfold TW, tail_ws in Hw;
          repeat (first [rewrite wlook_skip in Hw by (cbn [f_a f_n]; lia) | rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia)]); cbn [f_a f_v] in Hw; injection Hw as <-.
        + right; left. exists (KActive sc). split; [cbn; lia|]. cbn [clen]. split; [lia|]. rewrite (nestA_ctx ab Hab (KActive sc) ltac:(cbn; lia)).
          destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction].
        + left. exists m, (nmt7 ab), FNext. split; [exact (nestA_m ab)|]. cbn [moff mlen]. split; [lia|]. rewrite (nmt7_f ab). reflexivity.
        + left. exists m, (nmt7 ab), FPrev. split; [exact (nestA_m ab)|]. cbn [moff mlen]. split; [lia|]. rewrite (nmt7_f ab). f_equal. lia.
        + left. exists m, (nmt7 ab), FAvail. split; [exact (nestA_m ab)|]. cbn [moff mlen]. split; [lia|]. rewrite (nmt7_f ab). cbn [in_f].
          apply byte_of_mod32; [lia|]. rewrite Hav2, Eiav. rewrite Z.mod_small by lia. reflexivity.
        + left. exists m, (nmt7 ab), FW32. split; [exact (nestA_m ab)|]. cbn [moff mlen]. split; [lia|]. rewrite (nmt7_f ab). reflexivity.
        + right; right; left. exists m, (nmt7 ab), (in_aib cnt1 ab), (in_slots cnt1), (FCT (p0 + 8) 1 (in_aib cnt1 ab)).
          split; [exact (nestA_m ab)|]. split; [reflexivity|]. split; [cbn; right; left; reflexivity|]. cbn [f_a f_n f_v]. split; [lia|].
          unfold in_aib. rewrite Z.lor_comm. reflexivity.
        + right; right; left. exists m, (nmt7 ab), (in_aib cnt1 ab), (in_slots cnt1), (FCT p0 8 m).
          split; [exact (nestA_m ab)|]. split; [reflexivity|]. split; [cbn; left; reflexivity|]. cbn [f_a f_n f_v]. split; [lia | reflexivity].
        + left. exists m, (nmt7 ab), FMem. split; [exact (nestA_m ab)|]. cbn [moff mlen]. split; [lia|]. rewrite (nmt7_f ab). reflexivity.
        + left. exists m, (nmt7 ab), FFreed. split; [exact (nestA_m ab)|]. cbn [moff mlen]. split; [lia|]. rewrite (nmt7_f ab). cbn [in_f].
          apply byte_of_mod32; [lia|]. rewrite Hfr. rewrite Z.mod_small by lia. reflexivity.
        + left. exists m, (nmt7 ab), FAvail. split; [exact (nestA_m ab)|]. cbn [moff mlen]. split; [lia|]. rewrite (nmt7_f ab). cbn [in_f].
          apply byte_of_mod32; [lia|]. rewrite Hav2, Eiav. rewrite Z.mod_small by lia. reflexivity.
        + right; left. exists (KUsage sc). split; [cbn; lia|]. cbn [clen]. split; [lia|]. rewrite (nestA_ctx ab Hab (KUsage sc) ltac:(cbn; lia)).
          destruct (cslot_eq_dec (KUsage sc) (KActive sc)) as [E|_]; [discriminate E|]. destruct (cslot_eq_dec (KUsage sc) (KUsage sc)); [reflexivity | contradiction].
      - intros x Hx. left. apply (proj2 (dom_nA3 x)). apply (proj1 (dom_nestA ab Hab x)). exact Hx.
    Qed.
  End Ab2.

End NestRest.



End WithLayout.
