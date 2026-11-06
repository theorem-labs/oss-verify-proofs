(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv KStep MI_Kit MI_Inv MI_List MI_WAMeta MI_WAMeta2
  VirginDefs MI_WNtf2 MReach MStrat KCost.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MAll () : Init.string Init.list := ["Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.MI_List.data_of"; "OSSVerify.KrLib.Heap.MI_Inv.MR"; "GOODm"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "Corelib.Init.Datatypes.None"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.mkGhdr"; "Corelib.Init.Logic.ex"; "mgok"; "Corelib.Init.Logic.not"; "DRVc"; "OSSVerify.KrLib.Heap.Malloc.s_metas"; "OSSVerify.KrLib.Heap.Malloc.c_active"; "OSSVerify.KrLib.Heap.Malloc.s_ctx"; "OSSVerify.KrLib.Heap.Malloc.c_usage"; "AF"; "OSSVerify.KrLib.Heap.Malloc.upd_ctx"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.MStrat.shift"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.KCost.sall"; "OSSVerify.KrLib.Heap.Malloc.am_take"; "OSSVerify.KrLib.Heap.Malloc.am_carve"; "OSSVerify.KrLib.Heap.Malloc.am_finish"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Nat.add"; "OSSVerify.KrLib.Heap.MStrat.MA"; "OSSVerify.KrLib.Heap.Malloc.am_after_brk"; "KAM"; "CAM"; "OSSVerify.KrLib.Heap.Malloc.alloc_meta"; "OSSVerify.KrLib.Heap.Malloc.MMAP_THRESHOLD"; "OSSVerify.KrLib.Heap.MStrat.GB"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "MPOST"; "KM"; "CM"; "OSSVerify.KrLib.Heap.Malloc.cmalloc"; "OSSVerify.KrLib.Heap.Malloc.active"; "OSSVerify.KrLib.Heap.Malloc.usage"; "OSSVerify.KrLib.Heap.Malloc.mkMeta"; "OSSVerify.KrLib.Heap.Malloc.m_prev"; "OSSVerify.KrLib.Heap.Malloc.m_next"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_freeable"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "OSSVerify.KrLib.Heap.MStrat.UND"; "OSSVerify.KrLib.Heap.Malloc.M"; "OSSVerify.KrLib.Heap.Malloc.activate_group"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.MStrat.is_undef"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Heap.Malloc.okay_to_free"; "Corelib.Init.Datatypes.true"; "FPOST"; "OSSVerify.KrLib.Heap.Malloc.cfree"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition GOODm (r : meta) : Prop :=
  undersized r /\ (48 <= m_sizeclass r -> m_avail r = 0 /\ m_freed r = 0).

Definition DRVc (cs : mstate) : Prop :=
  forall b m ai, s_groups cs !! b = Some (mkGhdr (Some m) ai) -> GOODm (MR cs m).

(* [comment removed for export] *)
Definition nosmallc (cs : mstate) : Prop :=
  forall b m ai, s_groups cs !! b = Some (mkGhdr (Some m) ai) -> 48 <= m_sizeclass (MR cs m).

(* [comment removed for export] *)
Definition nosmallb (cs : mstate) : bool :=
  forallb (fun bh => match g_meta (snd bh) with Some m => 48 <=? m_sizeclass (MR cs m) | None => true end) (map_to_list (s_groups cs)).

Lemma nosmallb_sound cs : nosmallb cs = true -> nosmallc cs.
Proof.
  intros H b m ai Hb. unfold nosmallb in H. rewrite forallb_forall in H.
  specialize (H (b, mkGhdr (Some m) ai) ltac:(apply (proj1 (list_elem_of_In _ _)); apply elem_of_map_to_list; exact Hb)). cbn in H. apply Z.leb_le. exact H.
Qed.

Lemma GOODm_data r r' : data_of r' = data_of r -> GOODm r -> GOODm r'.
Proof.
  intros E G. apply data_of_eq in E. ddestruct E as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold GOODm, undersized in *. rewrite (get_stride_data r' r) by (apply data_of_eq; repeat split; assumption).
  rewrite E2, E3, E6. exact G.
Qed.

(* [comment removed for export] *)
Definition mgok (cs cs' : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MAll ()) "(0.Pm,$1.(2.(3.$4.(5.(6.O1.R1.))(5.(6.O2.R1.)))(2.(7.(6.O1.R1.))(3.$8.(9.(6.O1.R1.))(:.$1.))))Pb,$1.Pm,$1.Pai,$;.P,(3.(<.$=.)(>.$1.$=.(?.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$=.)(17.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$=.)R3.(18.O1.))(19.$=.(1:.(19.$1.R2.)R1.)))(2.(1;.$;.Lai0,$;.(3.(<.$=.)(>.$1.$=.(?.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$=.)(17.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$=.)R5.(18.O2.))(19.$=.(1:.(19.$1.R4.)R1.))))(2.(7.(6.O1.R3.))(3.$8.(9.(6.O1.R3.))(:.$1.)))))")
(* [comment removed for export] *).

Lemma mgok_refl cs : mgok cs cs.
Proof. split; [intros m; left; reflexivity| intros b m ai H; left; exists ai; exact H]. Qed.

(* [comment removed for export] *)
Lemma mgok_DRVc cs cs' : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(1<.O2.O1.)P,Pb,$1.Pm,$1.Pai,$;.P,(3.(<.$=.)(>.$1.$=.(?.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$=.)(17.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$=.)R3.(18.O1.))(19.$=.(1:.(19.$1.R2.)R1.)))(1=.(3.$8.(9.(6.O1.R3.))(:.$1.)))P,(1>.O2.)(1>.O1.)")
(* [comment removed for export] *).
Proof.
  intros [M Gr] HM D b m ai H. pose proof (HM _ _ _ H) as Hm.
  destruct (Gr b m ai H) as [[ai0 H0]|[G|G]]; [| exact G| congruence].
  destruct (M m) as [E|[G|G]]; [| exact G| congruence]. eapply GOODm_data; [exact E| exact (D _ _ _ H0)].
Qed.

Lemma data_of_mem r r' : data_of r' = data_of r -> m_mem r' = m_mem r.
Proof. intros E. apply data_of_eq in E. tauto. Qed.

Lemma mgok_trans a b c : mgok a b -> mgok b c -> mgok a c.
Proof.
  intros [M1 G1] [M2 G2]. split.
  - intros m. destruct (M2 m) as [E2|[G|G]]; [| right; left; exact G| right; right; exact G].
    destruct (M1 m) as [E1|[G|G]]; [left; congruence| |].
    + right; left. eapply GOODm_data; [exact E2| exact G].
    + right; right. rewrite (data_of_mem _ _ E2). exact G.
  - intros bb m ai H. destruct (G2 bb m ai H) as [[ai1 H1]|[G|G]]; [| right; left; exact G| right; right; exact G].
    destruct (G1 bb m ai1 H1) as [[ai0 H0]|[G|G]]; [left; exists ai0; exact H0| |].
    + destruct (M2 m) as [E2|[G'|G']]; [| right; left; exact G'| right; right; exact G']. right; left. eapply GOODm_data; [exact E2| exact G].
    + destruct (M2 m) as [E2|[G'|G']]; [| right; left; exact G'| right; right; exact G']. right; right. rewrite (data_of_mem _ _ E2). exact G.
Qed.

Lemma mgok_data cs cs' : (forall m, data_of (MR cs' m) = data_of (MR cs m)) -> s_groups cs' = s_groups cs -> mgok cs cs'.
Proof. intros M G. split; [intros m; left; apply M| intros b m ai H; left; exists ai; rewrite <- G; exact H]. Qed.

Lemma mgok_metas cs cs' : s_metas cs' = s_metas cs -> s_groups cs' = s_groups cs -> mgok cs cs'.
Proof. intros M G. apply mgok_data; [| exact G]. intros m. unfold MR. rewrite (get_meta_rec_ext cs cs' m M). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record AF (st st1 : mstate) : Prop := mkAF {
  af_data : forall m, data_of (MR st1 m) = data_of (MR st m);
  af_groups : s_groups st1 = s_groups st;
  af_active : c_active (s_ctx st1) = c_active (s_ctx st);
  af_usage : c_usage (s_ctx st1) = c_usage (s_ctx st)
}.

Lemma AF_refl st : AF st st. Proof. constructor; reflexivity. Qed.
Lemma AF_trans a b c : AF a b -> AF b c -> AF a c.
Proof. intros [] []; constructor; congruence. Qed.
Lemma AF_metas st st1 : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(3.(?.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$4.)(1?.O1.)(1?.O2.))P,(3.(?.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$=.)(18.O1.)(18.O2.))P,(3.(?.$;.$13.$16.$1.)(20.(21.O1.))(20.(21.O2.)))P,(3.(?.$;.$13.$16.$;.)(22.(21.O1.))(22.(21.O2.)))(23.O2.O1.)")
(* [comment removed for export] *).
Proof. intros; constructor; auto. intros m. unfold MR. rewrite (get_meta_rec_ext st st1 m) by assumption. reflexivity. Qed.
Lemma AF_mgok st st1 : AF st st1 -> mgok st st1.
Proof. intros F. apply mgok_data; [apply (af_data _ _ F)| apply (af_groups _ _ F)]. Qed.
Lemma AF_UND st st1 : AF st st1 -> UND st -> UND st1.
Proof. intros F. apply UND_data. apply (af_data _ _ F). Qed.
Lemma AF_usage st st1 sc : AF st st1 -> usage st1 sc = usage st sc.
Proof. intros F. unfold usage, ctx. rewrite (af_usage _ _ F). reflexivity. Qed.
Lemma AF_active st st1 sc : AF st st1 -> active st1 sc = active st sc.
Proof. intros F. unfold active, ctx. rewrite (af_active _ _ F). reflexivity. Qed.

Lemma AF_upd_links st m f : (forall r, data_of (f r) = data_of r) -> AF st (upd_meta m f st).
Proof. intros Hf. constructor; try reflexivity. intros x. apply data_upd_links. exact Hf. Qed.

Lemma AF_upd_ctx st f : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(3.(?.$;.$13.$16.$1.)(20.A1.O1.(21.O2.))(20.(21.O2.)))P,(3.(?.$;.$13.$16.$;.)(22.A1.O1.(21.O2.))(22.(21.O2.)))(23.O2.(24.O1.O2.))")
(* [comment removed for export] *).
Proof. intros. apply AF_metas; try reflexivity; assumption. Qed.

Lemma AF_dequeue_free st m : AF st (dequeue LFree m st).
Proof.
  constructor; [intros x; apply dequeue_data| ..];
  (unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _)|]; cbn; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KAM : nat := 3.
Definition CAM : Z := MA + 4 * PGSZ.

Section AM.
Context {R : Type}.
Variable Q : R -> Prop.

#[using="Type"] Lemma am_take_all K C st (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(25.=O4.)P,Pst1,$26.Pm,$1.P,(23.O3.R2.)P,(3.$;.(27.R3.)(27.O3.))P,(3.(?.$11.$12.$15.$28.)(29.R4.)(29.O3.))(2:.VR,VQ,O5.O4.A2.O2.R5.(19.$1.R4.))(2:.VR,VQ,O5.O4.(2;.VR,O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros HC HK. unfold am_take. destruct (c_avail_meta (ctx st)) as [m|]; [| constructor; exact HC].
  apply HK; [| reflexivity| reflexivity].
  eapply AF_trans; [| apply AF_upd_links; intros r; reflexivity]. apply AF_upd_ctx; reflexivity.
Qed.

#[using="Type"] Lemma AF_carve_rest s p : AF s (carve_rest s p).
Proof. unfold carve_rest, ctx. destruct (c_meta_area_tail (s_ctx s)); apply AF_metas; reflexivity. Qed.

#[using="Type"] Lemma AF_adv s p : AF s (adv s p).
Proof. unfold adv. apply AF_upd_ctx; reflexivity. Qed.

#[using="Type"] Lemma am_carve_all K C st p (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(25.=O5.)P,Pst1,$26.Pm,$1.P,(23.O4.R2.)P,(3.$;.(27.R3.)(27.O4.))P,(3.(?.$11.$12.$15.$28.)(29.R4.)(29.O4.))(2:.VR,VQ,O6.O5.A2.O2.R5.(19.$1.R4.))(2:.VR,VQ,O6.O5.(2<.VR,O4.O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros HC HK. rewrite am_carve_eq. dpose (carve_rest_facts (adv st p) p) as (M1 & S1 & C1 & R1).
  apply am_take_all; [exact HC|]. intros st1 m F1 S2 R2. apply HK.
  - eapply AF_trans; [| exact F1]. eapply AF_trans; [apply AF_adv| apply AF_carve_rest].
  - rewrite S2, S1. reflexivity.
  - rewrite R2, R1. reflexivity.
Qed.

#[using="Type"] Lemma am_finish_all K C st nu (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(25.=O5.)P,Pst1,$26.P,(23.O4.R1.)P,(3.$;.(27.R2.)(27.O4.))(2:.VR,VQ,O6.O5.A2.O2.R3.(:.$1.))P,Pst1,$26.Pm,$1.P,(23.O4.R2.)P,(3.$;.(27.R3.)(27.O4.))(2:.VR,VQ,O6.O5.A2.O2.R4.(19.$1.R3.))(2:.VR,VQ,O6.O5.(2=.VR,O4.O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros HC KN KS. unfold am_finish.
  destruct (c_avail_meta_areas (ctx st)) as [p|]; [| constructor; exact HC].
  assert (CARVE : sall Q K C (am_carve st p k bail)).
  { apply am_carve_all; [exact HC|]. intros st1 m F S _. apply KS; assumption. }
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu); [| exact CARVE].
  replace K with (K + emaps (EMprotect (conc st p) PGSZ PROT_RW))%nat by (cbn; lia).
  replace C with (C + ecost (EMprotect (conc st p) PGSZ PROT_RW)) by (cbn; lia).
  apply sa_vis; [exact HC| cbn; lia|]. intros z.
  destruct (negb (mprotect_answer_ok z)); [apply sall_bad_answer; exact HC|].
  destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); [exact CARVE|]. apply KN; [apply AF_refl| reflexivity].
Qed.

#[using="Type"] Lemma shiftl_2_bound s : 0 <= s <= 13 -> 2 <= Z.shiftl 2 s <= 2 ^ 14.
Proof.
  intros Hs. rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
  split; [lia| change (2 ^ 14) with (2 * 2 ^ 13); apply Z.mul_le_mono_nonneg_l; [lia| apply Z.pow_le_mono_r; lia]].
Qed.

#[using="Type"] Lemma am_after_brk_all K C st nu (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(0.(25.=(27.O4.))(25.(27.O4.)+=.))P,(25.=O5.)P,Pst1,$26.P,(23.O4.R1.)P,(0.(25.(27.O4.)(27.R2.))(25.(27.R2.)(2>.(27.O4.)+1.)))(2:.VR,VQ,O6.O5.A2.O2.R3.(:.$1.))P,Pst1,$26.Pm,$1.P,(23.O4.R2.)P,(0.(25.(27.O4.)(27.R3.))(25.(27.R3.)(2>.(27.O4.)+1.)))(2:.VR,VQ,O6.O5.A2.O2.R4.(19.$1.R3.))(2:.VR,VQ,(2?.O6.#1.)(2>.O5.$30.)(31.VR,O4.O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros SH HC KN KS. unfold am_after_brk.
  destruct (c_avail_meta_area_count (ctx st) =? 0).
  - set (n := Z.shiftl 2 (c_meta_alloc_shift (ctx st))).
    pose proof (shiftl_2_bound _ SH) as Hn. fold (shift st) in n. change (Z.shiftl 2 (shift st)) with n in Hn.
    assert (Hlen : 0 < n * PGSZ /\ mmap_len (n * PGSZ) <= MA).
    { unfold PGSZ, MA. split; [lia|]. rewrite mmap_len_of_aligned; [nia| lia| apply Z.mod_mul; lia]. }
    destruct Hlen as [Hl0 Hml].
    apply (sall_mono Q Q (K + emaps (EMmap 0 (n * PGSZ) PROT_NONE (MAP_PRIVATE + MAP_ANON)))%nat (C + ecost (EMmap 0 (n * PGSZ) PROT_NONE (MAP_PRIVATE + MAP_ANON))));
      [| auto| cbn; lia| cbn [ecost]; lia].
    apply sa_vis; [exact HC| cbn [ecost]; pose proof (mmap_len_bound (n * PGSZ) Hl0); unfold MA in Hml; lia|].
    intros z. destruct (negb (mmap_answer_ok (s_ceil st) (live_ranges st) (n * PGSZ) z)); [apply sall_bad_answer; exact HC|].
    destruct (is_err z); [apply KN; [apply AF_refl| lia]|].
    destruct (new_region RKMeta z (n * PGSZ) st) as [st1 rid] eqn:Enr. apply (f_equal fst) in Enr. cbn [fst] in Enr. subst st1.
    match goal with |- sall _ _ _ (am_finish ?s2 _ _ _) => set (st2 := s2) end.
    assert (F2 : AF st st2) by (subst st2; apply AF_metas; reflexivity).
    assert (S2 : shift st2 = shift st + 1) by (subst st2; unfold shift, ctx; cbn -[Z.add]; reflexivity).
    apply am_finish_all; [exact HC| |].
    + intros st1 F1 S1. apply KN; [eapply AF_trans; eassumption| rewrite S1, S2; lia].
    + intros st1 m F1 S1. apply KS; [eapply AF_trans; eassumption| rewrite S1, S2; lia].
  - apply (sall_mono Q Q K C); [| auto| lia| unfold MA; lia].
    apply am_finish_all; [exact HC| |].
    + intros st1 F1 S1. apply KN; [exact F1| rewrite S1; lia].
    + intros st1 m F1 S1. apply KS; [exact F1| rewrite S1; lia].
Qed.

#[using="Type"] Lemma AF_am_init st : AF st (am_init st).
Proof. unfold am_init, ctx. destruct (c_init_done (s_ctx st) =? 0); [apply AF_upd_ctx; reflexivity| apply AF_refl]. Qed.

#[using="Type"] Theorem alloc_meta_all K C st (k : mstate -> optr -> M R) bail : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(0.(25.=(27.O3.))(25.(27.O3.)+=.))P,(25.=O4.)P,Pst1,$26.P,(23.O3.R1.)P,(0.(25.(27.O3.)(27.R2.))(25.(27.R2.)(2>.(27.O3.)+1.)))(2:.VR,VQ,O5.O4.A2.O2.R3.(:.$1.))P,Pst1,$26.Pm,$1.P,(23.O3.R2.)P,(0.(25.(27.O3.)(27.R3.))(25.(27.R3.)(2>.(27.O3.)+1.)))(2:.VR,VQ,O5.O4.A2.O2.R4.(19.$1.R3.))(2:.VR,VQ,(2?.O5.$32.)(2>.O4.$33.)(34.VR,O3.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros SH HC KN KS. rewrite alloc_meta_eq.
  dpose (am_init_facts st) as (IM & IS & IC & IR). pose proof (AF_am_init st) as F0. set (st0 := am_init st) in *.
  assert (HC' : 0 <= C + CAM) by (unfold CAM, MA, PGSZ; lia).
  assert (AFTER : forall s nu, AF st s -> shift s = shift st -> sall Q (K + KAM)%nat (C + CAM) (am_after_brk s nu k bail)).
  { intros s nu Fs Ss. apply (sall_mono Q Q (K + 1)%nat (C + MA)); [| auto| unfold KAM; lia| unfold CAM, PGSZ; lia].
    apply am_after_brk_all; [rewrite Ss; exact SH| exact HC| |].
    - intros st1 F1 S1. apply KN; [eapply AF_trans; eassumption| rewrite <- Ss; exact S1].
    - intros st1 m F1 S1. apply KS; [eapply AF_trans; eassumption| rewrite <- Ss; exact S1]. }
  unfold am_body.
  destruct (c_free_meta_head (ctx st0)) as [m|].
  { eapply sall_mono; [apply KS; [eapply AF_trans; [exact F0| apply AF_dequeue_free]|]| auto| unfold KAM; lia| unfold CAM, MA, PGSZ; lia].
    unfold shift, ctx in *. autorewrite with mst. rewrite IS. lia. }
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)).
  { apply am_take_all; [exact HC'|]. intros st1 m F1 S1 _. eapply sall_mono; [apply KS; [eapply AF_trans; eassumption| rewrite S1, IS; lia]| auto| unfold KAM; lia| unfold CAM, MA, PGSZ; lia]. }
  destruct ((c_avail_meta_area_count (ctx st0) =? 0) && _); [| apply (AFTER st0 true F0 IS)].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - (* [comment removed for export] *)
    replace (K + KAM)%nat with ((K + KAM) + emaps (EBrk 0))%nat by (cbn; lia). replace (C + CAM) with ((C + CAM) + ecost (EBrk 0)) by (cbn; lia).
    apply sa_vis; [exact HC'| cbn; lia|]. intros cur.
    destruct (brk0_answer_ok cur) eqn:Hcur; cbn [negb]; [| apply sall_bad_answer; exact HC'].
    assert (Hnew : round_up_pg cur + 2 * PGSZ <> 0).
    { unfold brk0_answer_ok in Hcur. apply andb_prop in Hcur as [Hcur _]. apply andb_prop in Hcur as [Hcur _]. apply Z.ltb_lt in Hcur.
      pose proof (round_up_pg_ge cur). unfold PGSZ. lia. }
    replace (K + KAM)%nat with ((K + 2) + emaps (EBrk (round_up_pg cur + 2 * PGSZ)))%nat by (unfold emaps, KAM; rewrite (proj2 (Z.eqb_neq _ _) Hnew); lia).
    replace (C + CAM) with ((C + MA + PGSZ) + ecost (EBrk (round_up_pg cur + 2 * PGSZ))) by (unfold ecost, CAM; rewrite (proj2 (Z.eqb_neq _ _) Hnew); lia).
    apply sa_vis; [unfold MA, PGSZ; lia| unfold ecost; rewrite (proj2 (Z.eqb_neq _ _) Hnew); unfold PGSZ; lia|]. intros r.
    destruct (negb (brk_answer_ok cur _ r)); [apply sall_bad_answer; unfold MA, PGSZ; lia|].
    destruct (negb (r =? _)).
    { apply (sall_mono Q Q (K + 1)%nat (C + MA)); [apply am_after_brk_all; [| exact HC| |]| auto| unfold KAM; lia| unfold CAM, MA, PGSZ; lia].
      - unfold shift, ctx in *. cbn -[Z.add]. rewrite IS. exact SH.
      - intros st1 F1 S1. apply KN; [exact (AF_trans _ _ _ F0 (AF_trans _ _ _ (AF_upd_ctx st0 (set_brk BrkDead) eq_refl eq_refl) F1))|].
        revert S1. unfold shift, ctx in *. cbn -[Z.add]. rewrite IS. exact (fun x => x).
      - intros st1 m F1 S1. apply KS; [exact (AF_trans _ _ _ F0 (AF_trans _ _ _ (AF_upd_ctx st0 (set_brk BrkDead) eq_refl eq_refl) F1))|].
        revert S1. unfold shift, ctx in *. cbn -[Z.add]. rewrite IS. exact (fun x => x). }
    destruct (negb (brk_pages_ok st0 _ _)); [apply sall_bad_answer; unfold MA, PGSZ; lia|].
    replace (K + 2)%nat with ((K + 1) + emaps (EMmap (round_up_pg cur) PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)))%nat by (cbn; lia).
    replace (C + MA + PGSZ) with ((C + MA) + ecost (EMmap (round_up_pg cur) PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED))) by (cbn [ecost]; change (mmap_len PGSZ) with PGSZ; reflexivity).
    apply sa_vis; [unfold MA; lia| cbn [ecost]; change (mmap_len PGSZ) with PGSZ; unfold PGSZ; lia|]. intros rg.
    destruct (negb (mmap_fixed_answer_ok _ rg)); [apply sall_bad_answer; unfold MA; lia|].
    destruct (new_region RKBrk _ _ st0) as [st1 rid] eqn:Enr. apply (f_equal fst) in Enr. cbn [fst] in Enr. subst st1.
    match goal with |- sall _ _ _ (am_after_brk ?s2 _ _ _) => set (st2 := s2) end.
    assert (F2 : AF st st2) by (subst st2; eapply AF_trans; [exact F0| apply AF_metas; reflexivity]).
    assert (S2 : shift st2 = shift st) by (subst st2; unfold shift, ctx in *; cbn; exact IS).
    apply (sall_mono Q Q (K + 1)%nat (C + MA)); [apply am_after_brk_all; [rewrite S2; exact SH| exact HC| |]| auto| unfold KAM; lia| unfold CAM, MA, PGSZ; lia].
    + intros st1 F1 S1. apply KN; [eapply AF_trans; eassumption| rewrite <- S2; exact S1].
    + intros st1 m F1 S1. apply KS; [eapply AF_trans; eassumption| rewrite <- S2; exact S1].
  - apply (AFTER st0 true F0 IS).
  - (* [comment removed for export] *)
    set (new := conc st0 (rid, off) + PGSZ).
    destruct (Z.eq_dec new 0) as [Ez|Nz].
    + replace (K + KAM)%nat with ((K + KAM) + emaps (EBrk new))%nat by (unfold emaps; rewrite (proj2 (Z.eqb_eq _ _) Ez); lia).
      replace (C + CAM) with ((C + CAM) + ecost (EBrk new)) by (unfold ecost; rewrite (proj2 (Z.eqb_eq _ _) Ez); lia).
      apply sa_vis; [exact HC'| unfold ecost; rewrite (proj2 (Z.eqb_eq _ _) Ez); lia|]. intros r.
      destruct (negb (brk_answer_ok _ _ r)); [apply sall_bad_answer; exact HC'|].
      destruct (negb (r =? new)).
      { apply (AFTER _ true); [exact (AF_trans _ _ _ F0 (AF_upd_ctx st0 (set_brk BrkDead) eq_refl eq_refl))| unfold shift, ctx in *; cbn; exact IS]. }
      replace (brk_pages_ok st0 (conc st0 (rid, off)) PGSZ) with false; [apply sall_bad_answer; exact HC'|].
      symmetry. unfold brk_pages_ok. replace (0 <? conc st0 (rid, off)) with false by (symmetry; apply Z.ltb_ge; subst new; unfold PGSZ in Ez; lia). reflexivity.
    + replace (K + KAM)%nat with ((K + 2) + emaps (EBrk new))%nat by (unfold emaps, KAM; rewrite (proj2 (Z.eqb_neq _ _) Nz); lia).
      replace (C + CAM) with ((C + MA + PGSZ) + ecost (EBrk new)) by (unfold ecost, CAM; rewrite (proj2 (Z.eqb_neq _ _) Nz); lia).
      apply sa_vis; [unfold MA, PGSZ; lia| unfold ecost; rewrite (proj2 (Z.eqb_neq _ _) Nz); unfold PGSZ; lia|]. intros r.
      destruct (negb (brk_answer_ok _ _ r)); [apply sall_bad_answer; unfold MA, PGSZ; lia|].
      destruct (negb (r =? new)).
      { apply (sall_mono Q Q (K + 1)%nat (C + MA)); [apply am_after_brk_all; [| exact HC| |]| auto| lia| unfold PGSZ; lia].
        - unfold shift, ctx in *. cbn -[Z.add]. rewrite IS. exact SH.
        - intros st1 F1 S1. apply KN; [exact (AF_trans _ _ _ F0 (AF_trans _ _ _ (AF_upd_ctx st0 (set_brk BrkDead) eq_refl eq_refl) F1))|].
          revert S1. unfold shift, ctx in *. cbn -[Z.add]. rewrite IS. exact (fun x => x).
        - intros st1 m F1 S1. apply KS; [exact (AF_trans _ _ _ F0 (AF_trans _ _ _ (AF_upd_ctx st0 (set_brk BrkDead) eq_refl eq_refl) F1))|].
          revert S1. unfold shift, ctx in *. cbn -[Z.add]. rewrite IS. exact (fun x => x). }
      destruct (negb (brk_pages_ok st0 _ _)); [apply sall_bad_answer; unfold MA, PGSZ; lia|].
      match goal with |- sall _ _ _ (am_after_brk ?s2 _ _ _) => set (st2 := s2) end.
      assert (F2 : AF st st2).
      { subst st2. eapply AF_trans; [exact F0|]. eapply AF_trans; [| apply AF_upd_ctx; reflexivity]. apply AF_metas; autorewrite with mst; reflexivity. }
      assert (S2 : shift st2 = shift st) by (subst st2; unfold shift, ctx in *; cbn; autorewrite with mst; exact IS).
      apply (sall_mono Q Q (K + 1)%nat (C + MA)); [apply am_after_brk_all; [rewrite S2; exact SH| exact HC| |]| auto| unfold KAM; lia| unfold CAM, MA, PGSZ; lia].
      * intros st1 F1 S1. apply KN; [eapply AF_trans; eassumption| rewrite <- S2; exact S1].
      * intros st1 m F1 S1. apply KS; [eapply AF_trans; eassumption| rewrite <- S2; exact S1].
Qed.
End AM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KM : nat := 4.
Definition CM : Z := GB + CAM.

Definition MPOST (cs : mstate) (r : mstate * option cptr) : Prop :=
  mgok cs (fst r) /\ 0 <= shift (fst r) <= shift cs + 1.

Lemma MR_ext st st' m : s_metas st' = s_metas st -> MR st' m = MR st m.
Proof. intros H. unfold MR. apply get_meta_rec_ext. exact H. Qed.

Lemma mgok_strip cs st : mgok cs st -> mgok cs (strip st).
Proof. intros [M G]. split; [intros m; rewrite (MR_ext st (strip st) m) by reflexivity; apply M| intros b m ai H; cbn in H; rewrite (MR_ext st (strip st) m) by reflexivity; apply (G b m ai H)]. Qed.

Lemma shift_strip st : shift (strip st) = shift st. Proof. reflexivity. Qed.

Lemma GOODm_big r : m_sizeclass r = 63 -> m_avail r = 0 -> m_freed r = 0 -> GOODm r.
Proof. intros A B C. split; [intros H; rewrite A in H; lia| intros _; auto]. Qed.

Theorem cmalloc_sall_big cs n : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(0.(25.=(27.O2.))(25.(27.O2.)+=.))P,(25.$35.O1.)P,(25.(2>.O1.+2014.)$36.)(2:.(37.$26.(<.$38.))(39.O2.)$3:.$3;.(3<.O2.O1.))")
(* [comment removed for export] *).
Proof.
  intros SH Hn HnB. assert (Hn0 : 0 <= n) by (unfold MMAP_THRESHOLD in Hn; lia). unfold cmalloc.
  replace KM with (KM + 0)%nat by lia. replace CM with (CM + 0) by lia.
  eapply (sall_bind (fun r : mstate * option (aptr * Z) => mgok cs (fst r) /\ 0 <= shift (fst r) <= shift cs + 1)); [| lia|].
  2:{ intros [st1 r] [HM HS]. cbn [fst] in *. apply sa_ret; [| lia]. split; cbn [fst]; [apply mgok_strip; exact HM| rewrite shift_strip; exact HS]. }
  unfold malloc_core. rewrite size_overflows_small by (unfold GB in HnB; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hn).
  pose proof (mmap_len_bound (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as Hml.
  match goal with |- sall ?Q _ _ _ =>
  apply (sall_mono Q Q ((0 + KAM) + emaps (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)))%nat ((0 + CAM) + ecost (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON))));
    [| auto| unfold KM, KAM; cbn; lia| unfold CM, GB, IB, UNIT in *; cbn [ecost]; lia] end.
  apply sa_vis; [unfold CAM, MA, PGSZ; lia| cbn [ecost]; unfold GB, IB, UNIT in *; lia|]. intros z.
  destruct (negb (mmap_answer_ok _ _ _ z)); [apply sall_bad_answer; unfold CAM, MA, PGSZ; lia|].
  destruct (is_err z). { apply sa_ret; [| unfold CAM, MA, PGSZ; lia]. split; [apply mgok_refl| cbn; lia]. }
  destruct (new_region RKGroup z (n + IB + UNIT) cs) as [st1 rid] eqn:Enr. apply (f_equal fst) in Enr. cbn [fst] in Enr. subst st1. cbv zeta.
  match goal with |- sall _ _ _ (alloc_meta ?s2 _ _) => set (st2 := s2) end.
  assert (F2 : AF cs st2). { subst st2. apply AF_metas; unfold step_seq; destruct (c_seq _ =? 255); cbn; reflexivity. }
  assert (S2 : shift st2 = shift cs). { subst st2. unfold shift, ctx, step_seq. destruct (c_seq _ =? 255); cbn; reflexivity. }
  replace (0 + KAM)%nat with (0 + KAM)%nat by reflexivity.
  apply alloc_meta_all; [rewrite S2; exact SH| lia| |].
  - (* [comment removed for export] *)
    intros st3 F3 S3.
    match goal with |- sall ?Q _ _ _ =>
    apply (sall_mono Q Q (0 + emaps (EMunmap z (n + IB + UNIT)))%nat (0 + ecost (EMunmap z (n + IB + UNIT)))); [| auto| cbn; lia| cbn; lia] end.
    apply sa_vis; [lia| cbn; lia|]. intros ru. destruct (munmap_answer_ok ru); [| apply sall_bad_answer; lia].
    apply sa_ret; [| lia]. cbn [fst]. split.
    + eapply mgok_trans; [apply AF_mgok; exact (AF_trans _ _ _ F2 F3)|]. apply mgok_metas; reflexivity.
    + unfold shift, ctx in *. cbn. rewrite <- S2. lia.
  - (* [comment removed for export] *)
    intros st3 m F3 S3. cbv zeta. apply sa_ret; [| lia]. cbn [fst].
    pose proof (AF_trans _ _ _ F2 F3) as F.
    match goal with |- mgok cs ?s7 /\ _ => set (st7 := s7) end.
    assert (MRm : forall x, MR st7 x = if aptr_eqb x m then MR st7 m else MR st3 x).
    { intros x. subst st7. unfold MR. cbn [lh_hdr lay_none]. rewrite !get_meta_rec_upd_ctx.
      rewrite !(get_meta_rec_ext (put_group _ _ _ _) (add_slots _ _ _ _ _)) by apply s_metas_add_slots.
      rewrite !(get_meta_rec_ext (upd_meta _ _ _) (put_group _ _ _ _)) by apply s_metas_put_group.
      rewrite !get_meta_rec_upd, aptr_eqb_refl. destruct (aptr_eqb x m) eqn:E; reflexivity. }
    assert (Gm : GOODm (MR st7 m)).
    { subst st7. unfold MR. cbn [lh_hdr lay_none]. rewrite !get_meta_rec_upd_ctx.
      rewrite !(get_meta_rec_ext (put_group _ _ _ _) (add_slots _ _ _ _ _)) by apply s_metas_add_slots.
      rewrite !(get_meta_rec_ext (upd_meta _ _ _) (put_group _ _ _ _)) by apply s_metas_put_group.
      rewrite !get_meta_rec_upd, aptr_eqb_refl. apply GOODm_big; reflexivity. }
    split.
    + split.
      * intros x. rewrite MRm. destruct (aptr_eqb x m); [right; left; exact Gm| left; apply (af_data _ _ F)].
      * intros b m' ai H. subst st7. cbn -[get_meta_rec] in H. autorewrite with mst in H.
        unfold put_group in H. cbn in H. rewrite lookup_insert_Some in H.
        destruct H as [[<- E]|[NE H]].
        -- injection E as <- <-. right; left. exact Gm.
        -- left. exists ai. rewrite <- (af_groups _ _ F). exact H.
    + subst st7. unfold shift, ctx in *. cbn -[Z.add]. rewrite <- S2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fm_st_data st g x : x <> g -> data_of (MR (fm_st st g) x) = data_of (MR st x).
Proof.
  intros NE. unfold fm_st. rewrite queue_data. unfold MR. rewrite get_meta_rec_put_other by exact NE. reflexivity.
Qed.
Lemma fm_st_mem st g : m_mem (MR (fm_st st g) g) = None.
Proof.
  unfold fm_st. pose proof (queue_data LFree g (put_meta g meta0 st) g) as E. apply data_of_mem in E. rewrite E.
  unfold MR. rewrite get_meta_rec_put_same. reflexivity.
Qed.
Lemma fm_st_groups st g : s_groups (fm_st st g) = s_groups st.
Proof.
  unfold fm_st, queue_st, q_link, q_single. destruct (get_head _ _); [destruct (m_prev _)|]; cbn; autorewrite with mst; reflexivity.
Qed.

Lemma mgok_fm_st cs st g : mgok cs st -> mgok cs (fm_st st g).
Proof.
  intros HM. eapply mgok_trans; [exact HM|]. split.
  - intros m. destruct (aptr_eqb_spec m g) as [->|NE]; [right; right; apply fm_st_mem| left; apply fm_st_data; exact NE].
  - intros b m ai H. rewrite fm_st_groups in H. left. exists ai. exact H.
Qed.

(* [comment removed for export] *)
Definition AGK {T} (lay : layout_hook) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T)
    (sc req : Z) (k : mstate -> optr -> M T) (bail : M T) : mstate -> optr -> M T :=
  let size := UNIT * size_class sc in
  fun st mo =>
  match mo with
  | None => k st None
  | Some m =>
    let usage0 := usage st sc in
    let cnt :=
      if sc <? 9 then small_cnt_pick sc usage0
      else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
    let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
    let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : M T := ag_tail lay st sc m p cnt active_idx k in
    if PGSZ / 2 <? size * cnt + UNIT then
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (s_ceil st1) (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => k st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          tail st4 (rid, 0) cnt ai)
    else
      let j := size_to_class (UNIT + cnt * size - IB) in
      rec st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => k st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            let p := slot_of st1 g idx in
            let st2 := lh_nest lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            tail st3 p cnt (cnt - 1)
          end) bail
  end.

Lemma alloc_group_eq {T} lay rec st sc req (k : mstate -> optr -> M T) bail :
  alloc_group T lay rec st sc req k bail = alloc_meta st (AGK lay rec sc req k bail) bail.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ag44 {T} (k : mstate -> optr -> M T) (bail : M T) (st : mstate) (m : aptr) : M T :=
  let st1 := step_seq (account_bounce 44 st) in
  SVis (EMmap 0 69632 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (s_ceil st1) (live_ranges st1) 69632 r) then bad_answer bail else
    if is_err r then free_meta m st1 (fun st2 => k st2 None) bail
    else
      let '(st2, rid) := new_region RKGroup r 69632 st1 in
      let st3 := upd_meta m (m_set_maplen 17) st2 in
      let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
      ag_tail lay_none st4 44 m (rid, 0) 1 0 k).

Lemma AGK_44 {T} rec (k : mstate -> optr -> M T) bail st m :
  usage st 44 = 0 -> AGK lay_none rec 44 65536 k bail st (Some m) = ag44 k bail st m.
Proof. intros HU. unfold AGK. cbv beta iota. rewrite HU. reflexivity. Qed.

Lemma GOODm_44 r : m_sizeclass r = 44 -> m_last_idx r = 0 -> m_maplen r = 17 -> GOODm r.
Proof.
  intros A B C. split; [| intros H; rewrite A in H; lia].
  intros _. unfold get_stride. rewrite A, B, C. vm_compute. reflexivity.
Qed.

Theorem cmalloc_sall_65536 cs : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(0.(25.=(27.O1.))(25.(27.O1.)+=.))P,(3.$8.(3=.O1.+2<.)(:.$1.))P,(3.$;.(3>.O1.+2<.)=)(2:.(37.$26.(<.$38.))(39.O1.)$3:.$3;.(3<.O1.+10000.))")
(* [comment removed for export] *).
Proof.
  intros SH HA HU. unfold cmalloc.
  replace KM with (KM + 0)%nat by lia. replace CM with (CM + 0) by lia.
  eapply (sall_bind (fun r : mstate * option (aptr * Z) => mgok cs (fst r) /\ 0 <= shift (fst r) <= shift cs + 1)); [| lia|].
  2:{ intros [st1 r] [HM HS]. cbn [fst] in *. apply sa_ret; [| lia]. split; cbn [fst]; [apply mgok_strip; exact HM| rewrite shift_strip; exact HS]. }
  unfold malloc_core. change (size_overflows 65536) with false. change (MMAP_THRESHOLD <=? 65536) with false. cbv iota.
  cbv beta delta [malloc_small_ctrl]. change (size_to_class 65536) with 44. cbv zeta. rewrite HA.
  change ((4 <=? 44) && (44 <? 32) && negb (44 =? 6) && Z.even 44 && (usage cs 44 =? 0)) with false. cbv iota. rewrite HA.
  cbn [lowbit Z.land Z.opp Z.eqb negb].
  change FUEL with (S 63). remember 63%nat as f63 eqn:Ef63. clear Ef63.
  cbn [alloc_slot]. unfold try_avail. rewrite HA. cbn [Z.eqb negb].
  rewrite alloc_group_eq.
  match goal with |- sall ?Q _ _ _ =>
  apply (sall_mono Q Q (1 + KAM)%nat ((GB - 1) + CAM)); [| auto| unfold KM, KAM; lia| unfold CM; lia] end.
  match goal with |- sall _ _ _ (alloc_meta _ (AGK _ _ _ _ ?k2 _) _) => set (K2 := k2) end.
  apply alloc_meta_all; [exact SH| unfold GB; lia| |].
  { intros st1 F1 S1. subst K2. cbn [AGK]. change (-1 <? 0) with true. cbv iota. apply sa_ret; [| unfold GB; lia]. split; cbn [fst]; [apply AF_mgok; exact F1| lia]. }
  intros st1 m F1 S1. rewrite AGK_44 by (rewrite (AF_usage cs st1 44 F1); exact HU). unfold ag44.
  set (st2 := step_seq (account_bounce 44 st1)).
  assert (F2 : AF cs st2).
  { eapply AF_trans; [exact F1|]. subst st2. unfold account_bounce. change (sc_in_seq_range 44) with false. cbv iota.
    unfold step_seq. destruct (c_seq _ =? 255); apply AF_metas; reflexivity. }
  assert (S2 : shift st2 = shift st1).
  { subst st2. unfold account_bounce. change (sc_in_seq_range 44) with false. cbv iota. unfold shift, ctx, step_seq. destruct (c_seq _ =? 255); reflexivity. }
  match goal with |- sall ?Q _ _ _ =>
  apply (sall_mono Q Q (0 + emaps (EMmap 0 69632 PROT_RW (MAP_PRIVATE + MAP_ANON)))%nat (0 + ecost (EMmap 0 69632 PROT_RW (MAP_PRIVATE + MAP_ANON))));
    [| auto| cbn; lia| cbn [ecost]; change (mmap_len 69632) with 69632; unfold GB; lia] end.
  apply sa_vis; [lia| cbn [ecost]; change (mmap_len 69632) with 69632; lia|]. intros z.
  destruct (negb (mmap_answer_ok _ _ _ z)); [apply sall_bad_answer; lia|].
  destruct (is_err z).
  { (* [comment removed for export] *)
    rewrite free_meta_eq. subst K2. cbv beta iota. change (-1 <? 0) with true. cbv iota. apply sa_ret; [| lia]. split; cbn [fst].
    - apply mgok_fm_st. apply AF_mgok. exact F2.
    - unfold fm_st, shift, ctx in *. rewrite (proj1 (proj2 (carve_rest_facts st2 m)) ) || idtac.
      pose proof (queue_data LFree m (put_meta m meta0 st2)) as _x. clear _x.
      assert (E : c_meta_alloc_shift (s_ctx (queue_st LFree m (put_meta m meta0 st2))) = c_meta_alloc_shift (s_ctx st2)).
      { unfold queue_st, q_link, q_single. destruct (get_head _ _); [destruct (m_prev _)|]; cbn; reflexivity. }
      rewrite E. fold (shift st2). unfold shift in S2. rewrite S2. lia. }
  (* [comment removed for export] *)
  destruct (new_region RKGroup z 69632 st2) as [st3 rid] eqn:Enr. apply (f_equal fst) in Enr. cbn [fst] in Enr. subst st3.
  cbv beta delta [ag_tail]. cbn [lh_hdr lay_none]. cbv zeta. subst K2. cbv beta iota.
  match goal with |- sall _ _ _ (queue ?h ?g ?s ?kk ?bb) => destruct (queue_cases h g s kk bb) as [Eq |(u & k' & Eq)] end.
  2:{ rewrite Eq. apply sa_undef. lia. }
  rewrite Eq at 1. cbv beta.
  change (0 <? 0) with false. cbv iota.
  lazymatch goal with |- sall _ _ _ (match ?a with _ => _ end) => destruct a as [gp|]; [| apply sa_undef; lia] end.
  apply sa_ret; [| lia]. cbn [fst].
  match goal with |- mgok cs ?sF /\ _ => set (stF := sF) end.
  match goal with stF := queue_st _ _ ?s6 |- _ => set (st6 := s6) in * end.
  assert (MR6 : forall x, data_of (MR stF x) = data_of (MR st6 x)) by (intros x; subst stF; apply queue_data).
  assert (MRm : forall x, x <> m -> MR st6 x = MR st2 x).
  { intros x NE. subst st6. unfold MR. rewrite get_meta_rec_upd_other by exact NE.
    rewrite (get_meta_rec_ext (put_group _ _ _ _) (add_slots _ _ _ _ _)) by apply s_metas_add_slots.
    rewrite (get_meta_rec_ext (upd_meta _ _ _) (put_group _ _ _ _)) by apply s_metas_put_group.
    rewrite get_meta_rec_upd_other by exact NE.
    rewrite (get_meta_rec_ext (upd_ctx _ _) (set_usage _ _ _)) by apply s_metas_set_usage. rewrite get_meta_rec_upd_ctx.
    rewrite get_meta_rec_upd_other by exact NE. apply get_meta_rec_ext. cbn. autorewrite with mst. reflexivity. }
  assert (Gm : GOODm (MR st6 m)).
  { subst st6. unfold MR. rewrite get_meta_rec_upd_same.
    rewrite (get_meta_rec_ext (put_group _ _ _ _) (add_slots _ _ _ _ _)) by apply s_metas_add_slots.
    rewrite (get_meta_rec_ext (upd_meta _ _ _) (put_group _ _ _ _)) by apply s_metas_put_group.
    rewrite get_meta_rec_upd_same.
    rewrite (get_meta_rec_ext (upd_ctx _ _) (set_usage _ _ _)) by apply s_metas_set_usage. rewrite get_meta_rec_upd_ctx, get_meta_rec_upd_same.
    apply GOODm_44; reflexivity. }
  split.
  - split.
    + intros x. rewrite MR6. destruct (aptr_eqb_spec x m) as [->|NE]; [right; left; eapply GOODm_data; [apply MR6| exact Gm]|].
      left. rewrite (MRm x NE). apply (af_data _ _ F2).
    + intros b m' ai H.
      assert (Hg : s_groups stF = s_groups st6).
      { subst stF. unfold queue_st, q_link, q_single. destruct (get_head _ _); [destruct (m_prev _)|]; cbn; autorewrite with mst; reflexivity. }
      rewrite Hg in H. subst st6. cbn in H. autorewrite with mst in H. unfold put_group in H. cbn in H. autorewrite with mst in H.
      rewrite lookup_insert_Some in H. destruct H as [[<- E]|[NE H]].
      * injection E as <- <-. right; left. eapply GOODm_data; [apply MR6| exact Gm].
      * left. exists ai. rewrite <- (af_groups _ _ F2). revert H. cbn. autorewrite with mst. exact (fun x => x).
  - assert (E : shift stF = shift st2).
    { subst stF st6. unfold shift, ctx, queue_st, q_link, q_single. destruct (get_head _ _); [destruct (m_prev _)|]; cbn; autorewrite with mst; reflexivity. }
    rewrite E, S2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shift_eq_intro st st' : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st) -> shift st' = shift st.
Proof. intros H. exact H. Qed.

Lemma meta_eta r : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "(3.$4.O1.(3?.(40.O1.)(41.O1.)(9.O1.)(42.O1.)(43.O1.)(44.O1.)(45.O1.)(46.O1.)(47.O1.)))")
(* [comment removed for export] *).
Proof. destruct r; reflexivity. Qed.

Definition FPOST (cs : mstate) (r : mstate) : Prop := mgok cs r /\ shift r = shift cs.

(* [comment removed for export] *)
Lemma free_group_sall (cs st : mstate) (g p : aptr) (f : nat) :
  mgok cs st -> shift st = shift cs -> 0 <= shift cs ->
  m_mem (MR st g) = Some p -> m_maplen (MR st g) <> 0 ->
  sall (FPOST cs) 0%nat 0
    (free_group mstate dec_slots (nontrivial_free dec_slots f) st g
       (fun st2 mi => match mi with
                      | Some (base, len) =>
                          if negb (len =? 0) then SVis (EMunmap (conc st2 base) len)
                            (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret cs))
                          else ret st2
                      | None => ret st2
                      end) (ret cs)).
Proof.
  intros MG SH SH0 Hm Hml. unfold free_group. unfold MR in Hm, Hml. rewrite Hm.
  replace (negb (m_maplen (get_meta_rec st g) =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Hml).
  rewrite free_meta_eq.
  replace (negb (m_maplen (get_meta_rec st g) * 4096 =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
  lazymatch goal with |- sall ?Q _ _ (SVis ?e _) =>
    apply (sall_mono Q Q (0 + emaps e)%nat (0 + ecost e)); [| auto| cbn; lia| cbn; lia]; apply sa_vis; [lia| cbn; lia|] end.
  intros ru. destruct (munmap_answer_ok ru); [| apply sall_bad_answer; lia].
  apply sa_ret; [| lia].
  (* [comment removed for export] *)
  match goal with |- FPOST cs (drop_region _ (fm_st ?s2 g)) => set (st2 := s2) end.
  assert (M2 : s_metas st2 = s_metas st).
  { subst st2. rewrite s_metas_record_seq. autorewrite with mst. destruct (m_sizeclass _ <? 48); reflexivity. }
  assert (G2 : s_groups st2 = delete p (s_groups st)).
  { subst st2. rewrite s_groups_record_seq. autorewrite with mst. destruct (m_sizeclass _ <? 48); reflexivity. }
  assert (C2 : shift st2 = shift st).
  { subst st2. unfold shift, ctx. autorewrite with mst. destruct (m_sizeclass _ <? 48); autorewrite with mst; reflexivity. }
  split.
  - eapply mgok_trans; [exact MG|]. split.
    + intros m. unfold MR. rewrite (get_meta_rec_ext (fm_st st2 g) (drop_region p.1 (fm_st st2 g)) m) by reflexivity.
      destruct (aptr_eqb_spec m g) as [->|NE]; [right; right; apply fm_st_mem|].
      left. fold (MR (fm_st st2 g) m). rewrite (fm_st_data st2 g m NE). unfold MR. rewrite (get_meta_rec_ext st st2 m M2). reflexivity.
    + intros b m ai H. rewrite s_groups_drop_region, fm_st_groups, G2 in H. apply lookup_delete_Some in H as [NE H]. left. exists ai. exact H.
  - replace (shift (drop_region p.1 (fm_st st2 g))) with (shift st2); [rewrite C2, SH; reflexivity|].
    unfold shift, ctx, fm_st, queue_st, q_link, q_single. destruct (get_head _ _); [destruct (m_prev _)|]; cbn; autorewrite with mst; reflexivity.
Qed.

Lemma activate_group_zero st a (k : mstate -> Z -> M mstate) bail : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(48.O4.)(2.(1;.$26.Lst',$26.(0.(3.(49.$26.)(4:.$26.O3.O4.O2.O1.)A2.O2.R1.=)(0.Pm,$1.(3.$4.(6.R2.R1.)(6.O4.R1.))(0.(3.(?.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)$=.)(18.R1.)(18.O4.))(3.$4;.(21.R1.)(21.O4.))))))(4<.$26.(4:.$26.O3.O4.O2.O1.)))")
(* [comment removed for export] *).
Proof.
  intros U. unfold activate_group. destruct (U a) as [A F]. unfold MR in A, F.
  destruct (m_avail (get_meta_rec st a) =? 0); [| right; eexists _, _; reflexivity].
  left. eexists. rewrite F, Z.land_0_l. split; [reflexivity|]. split; [| split; reflexivity].
  intros m. unfold MR. rewrite get_meta_rec_upd. destruct (aptr_eqb_spec m a) as [->|NE]; [| reflexivity].
  rewrite Z.ldiff_0_l. destruct (get_meta_rec st a); cbn in A, F |- *. subst. reflexivity.
Qed.

Theorem cfree_sall cs c g p : ltac2:(CDefT.buildp (gd_tbl_MAll ()) "P,(3.(<.(37.$1.$;.))(>.$38.(37.$1.$;.)(?.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)(37.$1.$;.))(17.$1.(10.$11.$12.$;.$13.)(14.$11.$12.$15.$;.$13.$16.)(37.$1.$;.))O3.(4=.O4.))(19.(37.$1.$;.)(4>.$1.$;.O2.=)))P,(48.O4.)P,(25.=(27.O4.))P,(3.$;.(44.(6.O4.O2.))=)P,(3.$4?.(50.O4.O2.)$51.)P,(3.$8.(9.(6.O4.O2.))(19.$1.O1.))P,(1=.(3.$;.(47.(6.O4.O2.))=))(2:.$26.(52.O4.)#0.=(53.O4.(19.$38.O3.)))")
(* [comment removed for export] *).
Proof.
  intros Hc U SH0 Hli Hok Hm Hml. unfold cfree. rewrite Hc.
  apply (sall_mono (FPOST cs) (FPOST cs) (0 + 0)%nat (0 + 0)); [| auto| lia| lia].
  eapply (sall_bind (FPOST cs)); [| lia| intros st1 [M1 S1]; apply sa_ret; [| lia]; split; [apply mgok_strip; exact M1| rewrite shift_strip; exact S1]].
  unfold free_tail. destruct (U g) as [A F]. unfold MR in A, F, Hli, Hm, Hml. rewrite A, F, Hli.
  change (Z.lor 0 0) with 0. change (testbit 0 0) with false. change ((0 =? 0) || (0 + bit 0 =? mask_upto 0)) with true.
  cbn [negb]. unfold guard at 1. cbv iota.
  change FUEL with (S 63). remember 63%nat as f63 eqn:E63. clear E63. rewrite ntf_unfold. unfold MR. rewrite A, F, Hli, Hok.
  change (Z.lor 0 0) with 0. change ((0 + bit 0 =? mask_upto 0) && true) with true. cbv iota.
  assert (FG : forall st, mgok cs st -> shift st = shift cs -> m_mem (MR st g) = Some p -> m_maplen (MR st g) <> 0 ->
            sall (FPOST cs) 0%nat 0 (free_group mstate dec_slots (nontrivial_free dec_slots f63) st g
              (fun st2 mi => match mi with
                             | Some (base, len) => if negb (len =? 0) then SVis (EMunmap (conc st2 base) len)
                                 (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret cs)) else ret st2
                             | None => ret st2 end) (ret cs))).
  { intros st MG SH Hm' Hml'. apply (free_group_sall cs st g p); auto. }
  destruct (m_next (get_meta_rec cs g)) as [nx|].
  - apply sall_guard; [lia|]. intros Hsc.
    set (st1 := dequeue (LActive (m_sizeclass (get_meta_rec cs g))) g cs).
    assert (D1 : forall m, data_of (MR st1 m) = data_of (MR cs m)) by (intros m; apply dequeue_data).
    assert (MG1 : mgok cs st1) by (apply mgok_data; [exact D1| subst st1; autorewrite with mst; reflexivity]).
    assert (SH1 : shift st1 = shift cs) by (subst st1; unfold shift, ctx; autorewrite with mst; reflexivity).
    assert (Hm1 : m_mem (MR st1 g) = Some p) by (rewrite (data_of_mem _ _ (D1 g)); exact Hm).
    assert (Hml1 : m_maplen (MR st1 g) <> 0).
    { pose proof (D1 g) as E. apply data_of_eq in E. ddestruct E as (_ & _ & _ & _ & _ & _ & E). rewrite E. exact Hml. }
    destruct (optr_eqb (active cs _) (Some g)); [| apply FG; [exact MG1| exact SH1| exact Hm1| exact Hml1]].
    destruct (active st1 _) as [a|]; [| apply FG; [exact MG1| exact SH1| exact Hm1| exact Hml1]].
    lazymatch goal with |- sall _ _ _ (activate_group ?a' ?s' ?k' ?b') =>
      destruct (activate_group_zero s' a' k' b' (UND_dequeue cs _ g U)) as [(st' & E & MR' & G' & C')|(u & k'' & E)]; rewrite E; [| apply sa_undef; lia] end.
    apply FG.
    + eapply mgok_trans; [exact MG1|]. apply mgok_data; [intros m; rewrite MR'; reflexivity| exact G'].
    + unfold shift, ctx. rewrite C'. exact SH1.
    + rewrite MR'. exact Hm1.
    + rewrite MR'. exact Hml1.
  - apply FG; [apply mgok_refl| reflexivity| exact Hm| exact Hml].
Qed.
