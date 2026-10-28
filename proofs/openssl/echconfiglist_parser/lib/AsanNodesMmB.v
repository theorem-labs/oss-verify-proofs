(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes RefNodes AllocSim MmapSim AsanAcct AsanAcctShape AsanPlacement BackingAlgebra AsanNodesMmLib AsanNodesLibE.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanCeil Scfg AsanRefNodes. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lit_diff_sound : forall E e f d,
  lit_diff e f = Some d ->
  0 <= d < two64 /\ (bv_unsigned (edenot E e) - bv_unsigned (edenot E f)) mod two64 = d.
Proof.
  intros E e f d H. unfold lit_diff in H.
  pose proof (mkAlu_denot E ALU_SUB e f) as D. unfold esub in H.
  destruct (mkAlu ALU_SUB e f) eqn:Hm; try discriminate. injection H as <-.
  cbn [edenot] in D. apply (f_equal bv_unsigned) in D. rewrite u_sub64 in D. rewrite u_lit64 in D.
  split; [apply Z.mod_pos_bound; unfold two64; lia|]. unfold two64 in *. rewrite <- D. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_aligned_sound : forall SEGS E M k e,
  know_ok SEGS E M k -> page_aligned k e = true -> bv_unsigned (edenot E e) mod 4096 = 0.
Proof.
  intros SEGS E M k e HK H. unfold page_aligned in H.
  assert (GEN : 12 <= ealign k e -> bv_unsigned (edenot E e) mod 4096 = 0).
  { intros Hle. destruct (ealign_sound SEGS E M k e HK) as [Hr Hdiv]. apply Z.mod_divide; [lia|].
    eapply Z.divide_trans; [|exact Hdiv]. change 4096 with (2 ^ 12). apply pow2_divide_le. lia. }
  destruct e; try (apply GEN; apply Z.leb_le; exact H).
  apply Z.eqb_eq in H. cbn [edenot]. rewrite u_lit64. unfold two64.
  rewrite Z.mod_mod_divide; [exact H|]. exists (2 ^ 52). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_false_of_overlap : forall L (lo n a sz : word),
  In (a, sz) L -> iv_overlap lo n a sz = true -> region_free L lo n = false.
Proof.
  intros L lo n a sz Hin Hov. induction L as [|[a' sz'] L IH]; [destruct Hin|].
  cbn [region_free]. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite Hov. reflexivity.
  - rewrite (IH Hin). apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_regupd_same : forall E sr R (r : Prelude.reg) v,
  regs_ok E sr R -> getr R r = v -> r <> 0%bv -> regs_ok E sr (regupd R r v).
Proof.
  intros E sr R r v HR Hv Hr r'. destruct (bv_eq_dec _ r' r) as [->|Hne].
  - rewrite getr_same by exact Hr. rewrite <- Hv. apply HR.
  - rewrite getr_other by exact Hne. apply HR.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_refuted : forall m d (a sz : word),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d + page_size < 2 ^ 64)%Z ->  (* [comment removed for export] *)
  In (a, sz) (vm_reserved h ++ vm_maps h) ->
  (bv_unsigned b < bv_unsigned a + bv_unsigned sz)%Z -> (bv_unsigned a < bv_unsigned b + d)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false.
Proof.
  intros m d a sz h b Hbal Hdal Hd Hb0 Hnw Hin Hov1 Hov2.
  unfold page_size in Hnw. pose proof (u64_range b) as Hbr.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia.
  rewrite (region_free_false_of_overlap _ b (Z_to_bv 64 (d + page_size)) a sz Hin).
  - rewrite andb_false_r. reflexivity.
  - unfold iv_overlap. rewrite (u64_lit (d + page_size)) by (unfold page_size in *; lia).
    assert (Hov2' : (bv_unsigned a < bv_unsigned b + (d + page_size))%Z) by (unfold page_size in *; lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hov1), (proj2 (Z.ltb_lt _ _) Hov2'). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_elim : forall m d,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d + page_size < 2 ^ 64)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  (bv_unsigned b + d <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true
  /\ (vm_backing_used m + d <= vm_limit h)%Z.
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Hnw H.
  unfold page_size in Hnw. pose proof (u64_range b) as Hbr.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in H. fold h in H. fold b in H. rewrite Hureq in H.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) in H by lia. cbn [andb] in H.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in H by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in H
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) in H by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b in H by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z in H by lia.
  apply andb_prop in H as [H Hbud]. apply andb_prop in H as [Htop Hrf].
  apply Z.leb_le in Htop. apply Z.leb_le in Hbud.
  split; [exact Htop|]. split; [exact Hrf|].
  rewrite bv_sub_unsigned in Hbud. rewrite Hureq in Hbud. fold h b in Hbud.
  replace (bv_unsigned b + d - bv_unsigned b)%Z with d in Hbud by lia.
  unfold bv_wrap in Hbud. change (bv_modulus 64) with (2 ^ 64)%Z in Hbud. rewrite Z.mod_small in Hbud by lia. exact Hbud.
Qed.

Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof. intros l1 l2. induction l1 as [|iv l1 IH]; cbn [sum_sizes app]; [lia|]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma Some_pair_inj : forall {T U : Type} (a c : T) (b d : U), Some (a, b) = Some (c, d) -> a = c /\ b = d.
Proof. intros T U a c b d H. split; congruence. Qed.

Lemma zfill_in : forall (b l : word) m (x : word),
  bv_unsigned b <= bv_unsigned x < bv_unsigned b + bv_unsigned l ->
  zfill b l m x = Some (Z_to_bv 8 0).
Proof.
  intros b l m x Hx. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma region_free_intro : forall L (lo n : word),
  (forall a sz, In (a, sz) L -> iv_overlap lo n a sz = false) -> region_free L lo n = true.
Proof.
  intros L lo n H. induction L as [|[a sz] L IH]; [reflexivity|]. cbn [region_free].
  rewrite (H a sz (or_introl eq_refl)). cbn [negb andb]. apply IH. intros a' sz' Hin. apply H. right. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma eager_used_sem_brk : forall m,
  ivs_wf (vm_maps (m_vmmaps m)) ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
  intros m W. unfold eager_used, vm_backed_maps. rewrite <- maps_subtract_all_app_cuts.
  apply (proj1 (live_msa _ _ W)).
Qed.

(* [comment removed for export] *)
Lemma eager_used_cons_le : forall m (b n : word) h',
  ivs_wf (vm_maps (m_vmmaps m)) -> iv_wf (b, n) ->
  vm_maps h' = (b, n) :: vm_maps (m_vmmaps m) ->
  vm_noaccess h' = vm_noaccess (m_vmmaps m) ->
  eager_used (with_vmmaps h' m) <= eager_used m + bv_unsigned n.
Proof.
  intros m b n h' W Wb Hm Hn.
  assert (W' : ivs_wf (vm_maps (m_vmmaps (with_vmmaps h' m)))).
  { rewrite m_vmmaps_with_vmmaps, Hm. apply ivs_wf_cons; assumption. }
  rewrite (eager_used_sem_brk _ W'), (eager_used_sem_brk _ W).
  rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, Hm, Hn. cbn [sum_count].
  pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (B (b, n)) (Z.to_nat (S (b, n)))) as Hc.
  unfold iv_count. unfold S in *. cbn [snd] in *. pose proof (u64_range n). rewrite Z2Nat.id in Hc by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le : forall Aset m,
  A_wf Aset -> MInv Aset m -> vm_backing_used m <= eager_used m + A_bytes Aset.
Proof.
  intros Aset m Hwf [N1 N2 N3 N4 N5]. rewrite vm_backing_used_split.
  pose proof (allowed_pages_bound Aset (m_vm_materialized m) Hwf N1 N2 N3). lia.
Qed.

Lemma in_ivs_cons : forall z (a n : word) l,
  in_ivs z ((a, n) :: l) = (((bv_unsigned a <=? z) && (z <? bv_unsigned a + bv_unsigned n)) || in_ivs z l)%bool.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma seps_cons_inv : forall p l, seps (p :: l) -> Forall (iv_disjoint p) l /\ seps l.
Proof. intros p l H. inversion H; subst; auto. Qed.

Lemma seps_In_disjoint : forall l p q,
  seps l -> (forall iv, In iv l -> 0 < bv_unsigned (snd iv)) -> In p l -> In q l -> p <> q -> iv_disjoint p q.
Proof.
  induction l as [|h t IH]; intros p q Hs Hpos Hp Hq Hne; [destruct Hp|].
  apply seps_cons_inv in Hs as [Hf Ht].
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf q Hq).
  - pose proof (proj1 (Forall_forall _ _) Hf p Hp) as D. unfold iv_disjoint in *. lia.
  - apply IH; auto. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.

Lemma seps_NoDup : forall l, seps l -> (forall iv, In iv l -> 0 < bv_unsigned (snd iv)) -> List.NoDup l.
Proof.
  induction l as [|h t IH]; intros Hs Hpos; [constructor|].
  apply seps_cons_inv in Hs as [Hf Ht]. constructor.
  - intros Hin. pose proof (proj1 (Forall_forall _ _) Hf h Hin) as D. pose proof (Hpos h (or_introl eq_refl)). unfold iv_disjoint in D. lia.
  - apply IH; [exact Ht|]. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.

Section SoundB.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_cover : img_lo A < img_hi A /\ forall z, img_lo A <= z < img_hi A ->
  exists iv, In iv (segments_reserved SEGS) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Hypothesis argH_sp0 : forall E (a : word), argH E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.
Hypothesis E_SP0 : AP.expr_vars_lt nx0 e_sp0_early = true.
Context {SC : StepCfg} {AF : AllocForced SC}.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
Let kn_grant_filter_ok := AsanNodesMmLib.kn_grant_filter_ok SEGS A RES_len RES_cover HULL_ok.

(* [comment removed for export] *)
Theorem node_exit_sound : exit_stmt SEGS A LIMIT SINV argH FS0.
Proof.
  intros cs code E R FULL model HC Hec Hn.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  unfold node_exit in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [c0|] eqn:H10.
  2:{ destruct a7; try discriminate; repeat (destruct p; try discriminate). }
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 c0 HC ltac:(lia) H10) as [G10 Hc0].
  assert (H94 : (a7 = 94 \/ a7 = 93) /\ code = Z.land c0 255).
  { destruct a7 as [|p|p]; try discriminate;
      repeat (destruct p as [p|p|]; try discriminate); injection Hn as <-; auto. }
  destruct H94 as [Ha7 ->].
  assert (G17 : getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94 \/ getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 93).
  { destruct Ha7 as [-> | ->].
    - left. exact (proj1 (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 94 HC ltac:(lia) H17)).
    - right. exact (proj1 (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 93 HC ltac:(lia) H17)). }
  unfold cfg_of. rewrite <- (bv_and_255 c0 Hc0).
  eapply srz_exit_at_lazy; [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact G10].
Qed.


(* [comment removed for export] *)
Theorem node_sys_sound_YSetTid : sys_stmt SEGS A nx0 LIMIT SINV argH FS0 YSetTid.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn Hk.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  cbn [node_sys] in Hn. unfold node_settid in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (negb (a_tidset cs) && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hts Hfresh]. apply negb_true_iff in Hts.
  apply Some_inj in Hn. rename Hn into Ecs'.
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 96 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_tid _ _ _ _ _ _ _ _ _ _ _ HC Hts) as Htid.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  unfold cfg_of.
  eapply (srz_set_tid_lazy SEGS); [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact Htid |].
  intros tid Htidr.
  set (v := nxt cs) in *.
  set (E' := ext1 E v tid).
  assert (Hag : env_agree v E E') by apply (ext1_agree).
  pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH E_SP0 argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
  rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
  replace (pc cs + 4) with (pc cs') by (rewrite <- Ecs'; reflexivity).
  apply (Hk E' (regupd R 10 tid) FULL (with_tid tid model)).
  - split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
  - (* [comment removed for export] *)
    assert (Hv : edenot E' (EVar v) = tid) by (cbn [edenot]; unfold E'; apply ext1_at).
    assert (HMr : Mr A argH E' cs' (with_tid tid model) FULL = Mr A argH E' cs model FULL).
    { unfold Mr. f_equal. apply functional_extensionality. intros a. rewrite <- Ecs'.
      unfold hid, vis, in_allow, in_vis, in_sh. reflexivity. }
    assert (HA : allowA A E' cs' = allowA A E' cs) by (rewrite <- Ecs'; reflexivity).
    subst cs'.
    destruct HC'; constructor; rewrite ?HMr, ?HA;
      cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next];
      try assumption; try reflexivity; try discriminate.
    + (* [comment removed for export] *) apply (regs_ok_set_n); [exact co_regs0 | lia | exact Hv].
    + (* [comment removed for export] *) constructor; [|exact co_know0].
      cbn [kentry_ok]. rewrite Hv. unfold PID_MAX. unfold PID_MAX_ENVELOPE in Htidr. lia.
    + (* [comment removed for export] *) destruct co_minv0; constructor; assumption.
  - reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brk_keep_ok : forall E cs R FULL model,
  cs_ok E cs R FULL model ->
  cs_ok E (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) (regupd R 10 (vm_brk (m_vmmaps model))) FULL model.
Proof.
  intros E cs R FULL model HC.
  change (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4))
    with (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs (a_ss cs)) 10 (a_brk cs)) (kn cs) (nxt cs))).
  eapply (cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0);
    [exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC)
    | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
  cbn [mk_ss s_regs]. apply (regs_ok_set_n);
    [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | symmetry; exact (co_brk _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.

(* [comment removed for export] *)
Lemma brk_req_sound : forall E cs R FULL model d,
  cs_ok E cs R FULL model -> brk_req cs = Some d ->
  0 < d /\ d mod 4096 = 0 /\ d <= 2 ^ 40 /\
  (bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (vm_brk (m_vmmaps model))) mod two64 = d.
Proof.
  intros E cs R FULL model d HC H. unfold brk_req in H.
  destruct (lit_diff (reg cs 10) (a_brk cs)) as [d0|] eqn:Hld; [|discriminate].
  destruct (Z.ltb 0 d0 && Z.eqb (d0 mod 4096) 0 && Z.leb d0 (2 ^ 40))%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3.
  destruct (lit_diff_sound E _ _ _ Hld) as [_ Hm].
  rewrite (co_brk _ _ _ _ _ _ _ _ _ _ _ HC). auto.
Qed.

(* [comment removed for export] *)
Lemma brk_base_ok_sound : forall E cs R FULL model d,
  cs_ok E cs R FULL model -> brk_base_ok A cs d = true ->
  let b := vm_brk (m_vmmaps model) in
  bv_unsigned b mod 4096 = 0 /\ 0 < bv_unsigned b /\ img_hi A <= bv_unsigned b /\ bv_unsigned b + d <= KHI.
Proof.
  intros E cs R FULL model d HC H b. unfold brk_base_ok in H.
  apply andb_prop in H as [Hal H].
  destruct (xlo (kn cs) (a_brk cs)) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) (a_brk cs)) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [H0 Hi].
  apply Z.ltb_lt in H0. apply Z.leb_le in Hi. apply Z.leb_le in Hk.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hlo) as L.
  pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hhi) as Hh.
  pose proof (page_aligned_sound SEGS E _ (kn cs) _ HK Hal) as P.
  rewrite <- (co_brk _ _ _ _ _ _ _ _ _ _ _ HC) in L, Hh, P. unfold b. lia.
Qed.

(* [comment removed for export] *)
Lemma brk_req_val : forall E cs R FULL model d,
  cs_ok E cs R FULL model -> brk_req cs = Some d -> brk_base_ok A cs d = true ->
  getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d).
Proof.
  intros E cs R FULL model d HC Hr Hb.
  destruct (brk_req_sound E cs R FULL model d HC Hr) as (D1 & D2 & D3 & Dm).
  destruct (brk_base_ok_sound E cs R FULL model d HC Hb) as (B1 & B2 & B3 & B4).
  rewrite (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)).
  pose proof (u64_range (edenot E (reg cs 10))) as Hr10. pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
  apply bv_eq. rewrite u64_lit by (unfold KHI in *; lia). unfold two64, KHI in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem node_sys_sound_YBrk : sys_stmt SEGS A nx0 LIMIT SINV argH FS0 YBrk.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn Hk.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  cbn [node_sys] in Hn. unfold node_brk1 in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
  (* [comment removed for export] *)
  assert (POST : forall ok : bool, (if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None) = Some cs' ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 (vm_brk (m_vmmaps model))) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) T).
  { intros ok Hok. destruct ok; [|discriminate]. apply Some_inj in Hok.
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc cs') by (rewrite <- Hok; reflexivity).
    apply (Hk E (regupd R 10 (vm_brk (m_vmmaps model))) FULL model);
      [split; apply env_agree_refl | rewrite <- Hok; apply brk_keep_ok; exact HC | reflexivity]. }
  unfold cfg_of.
  destruct (reg_lit cs 10) as [[|p|p]|] eqn:H10.
  1: { (* [comment removed for export] *)
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 0 HC ltac:(lia) H10) as [G10 _].
    eapply (srz_brk_query_lazy SEGS); [exact HF | exact HE | exact Hh | exact G17 | exact G10 |].
    exact (POST true Hn). }
  (* [comment removed for export] *)
    all: destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
    all: destruct (brk_grow_blocked A cs d) eqn:Hblk; [|discriminate].
    all: specialize (POST true Hn).
    all: unfold brk_grow_blocked in Hblk; apply andb_prop in Hblk as [Hbase Hex].
    all: destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
    all: destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
    all: pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
    all: apply existsb_exists in Hex as [m [Hmin Hm]]; apply andb_prop in Hm as [Hm Hm2]; apply andb_prop in Hm as [Hnf Hm1]; apply negb_true_iff in Hnf.
    all: pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hm1) as L1;
         pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hm2) as L2;
         cbn [xt_den] in L1, L2; rewrite <- (co_brk _ _ _ _ _ _ _ _ _ _ _ HC) in L1, L2.
    all: pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
    all: eapply (srz_brk_grow_blocked_lazy SEGS); [exact HF | exact HE | exact Hh | exact G17 | exact G10
         | rewrite u64_lit by (unfold KHI in *; lia); lia
         | rewrite u64_lit by (unfold KHI in *; lia); pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ HC); lia
         | rewrite u64_lit by (unfold KHI in *; lia); lia
         | | exact POST].
    all: apply (brk_grow_ok_aligned_refuted model d (edenot E (am_base m)) (edenot E (am_len m)));
         [exact B1 | exact D2 | exact D1 | exact B2 | unfold KHI, page_size in *; lia | | lia | lia].  (* [comment removed for export] *)
    all: apply in_or_app; right; exact (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hmin Hnf).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vis_add_shape : forall cs b n k cs2,
  vis_add A LIMIT cs b n k = Some cs2 ->
  flat_x (kn cs) (fst (split_lit b)) (snd (split_lit b)) n = true
  /\ pc cs2 = pc cs /\ s_regs (a_ss cs2) = s_regs (a_ss cs) /\ a_vis cs2 = (b, n) :: a_vis cs
  /\ a_maps cs2 = a_maps cs /\ a_ghost cs2 = a_ghost cs.
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk] eqn:Hsplit.
  destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|] eqn:Hnhi; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hv as <-. cbn [fst snd pc a_ss s_pc s_regs a_vis a_maps a_ghost mk_ss].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Hflat].
  repeat split; try reflexivity. exact Hflat.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem node_brk2_sound : brk2_stmt SEGS A nx0 LIMIT SINV argH FS0.
Proof.
  intros cs csa csb E R FULL model T HC Hec Hn HkA HkB.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
  unfold node_brk2 in Hn. rewrite kn_grant_filterM_eq in Hn. (* [comment removed for export] *)
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
  destruct (brk_grow_admissible A LIMIT cs d && AP.expr_vars_lt (nxt cs) (reg cs 10))%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hposs _].
  destruct (split_lit (a_brk cs)) as [bb bk] eqn:Hsplit.
  set (csB := ACS _ _ _ _ _ _ _ _ _ _ _ _) in Hn.
  destruct (vis_add A LIMIT csB (a_brk cs) (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB)) as [csB'|] eqn:Hva; [|discriminate].
  apply Some_pair_inj in Hn as [EcsA EcsB]. subst csB'.
  (* [comment removed for export] *)
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 214 HC ltac:((first [clear; lia | lia])) H17) as [G17 _].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  unfold brk_grow_admissible in Hposs.
  apply andb_prop in Hposs as [Hposs Hbudget]. apply andb_prop in Hposs as [Hbase Hnf].
  unfold budget_ok in Hbudget. apply Z.leb_le in Hbudget.
  destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
  destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
  pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
  pose proof (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as Hres.
  pose proof (proj1 (APS.maps_match_exact nx0 (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)) as Hmaps.
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ HC) as Hlim. pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ HC) as Hsbrk.
  pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ HC) as Hbrk.
  pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as HTOP. pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as HSP0. unfold CEIL, CEILMAX in HTOP.
  set (h := m_vmmaps model) in *. set (b := vm_brk h) in *.
  pose proof (u64_range b) as Hbr.
  assert (Eb : edenot E (a_brk cs) = b) by (symmetry; exact Hbrk).
  (* [comment removed for export] *)
  destruct (vis_add_shape csB (a_brk cs) (ELit d) _ _ Hva) as (Hflat & HpcB' & HregsB' & HvisB' & HmapsB' & HghostB').
  rewrite Hsplit in Hflat. cbn [fst snd] in Hflat.
  set (dw := Z_to_bv 64 d). assert (Udw : bv_unsigned dw = d) by (unfold dw; apply u64_lit; unfold KHI in *; lia).
  pose proof (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs) as HAwf.
  unfold cfg_of.
  eapply (srz_brk_grow_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w d T HF HE Hh G17);
    fold h b; [exact B1 | exact D2 | exact D1 | exact B2 | unfold KHI in *; lia
    | lia | exact G10 | |].
  - (* [comment removed for export] *)
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csa) by (rewrite <- EcsA; reflexivity).
    apply (HkA E (regupd R 10 b) FULL model);
      [split; apply env_agree_refl | rewrite <- EcsA; apply (brk_keep_ok); exact HC | reflexivity].
  - (* [comment removed for export] *)
    intros Hadm.
    destruct (brk_grow_ok_aligned_elim model d B1 D2 D1 B2 ltac:(fold h b; unfold KHI, page_size in *; lia) Hadm) as (HadmT & Hrfg & HadmB).
    fold h b in HadmT, Hrfg, HadmB.
    (* [comment removed for export] *)
    assert (APARTG : forall m, In m (a_maps cs) ->
              bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
              \/ bv_unsigned b + (d + 4096) <= bv_unsigned (edenot E (am_base m))).
    { intros m Hin. rewrite region_free_app in Hrfg. apply andb_prop in Hrfg as [_ Hrf2]. rewrite Hmaps in Hrf2.
      pose proof (RefNodes.region_free_In _ b (Z_to_bv 64 (d + page_size)) (edenot E (am_base m)) (edenot E (am_len m)) Hrf2
                    (in_map (amap_den E) _ _ Hin)) as D.
      rewrite (u64_lit (d + page_size)) in D by (unfold KHI, page_size in *; lia). unfold page_size in D. lia. }
    assert (APART : forall m, In m (a_maps cs) ->
              bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
              \/ bv_unsigned b + d <= bv_unsigned (edenot E (am_base m))).
    { intros m Hin. destruct (APARTG m Hin) as [Hm|Hm]; [left; exact Hm | right; lia]. }
    assert (MAPART : AsanNodesMmLib.maps_apart E (a_maps cs) (bv_unsigned b) d).
    { intros m Hin _. destruct (APART m Hin); lia. }
    (* [comment removed for export] *)
    assert (HKdisj : forall M, know_ok SEGS E M (kdisj_new (a_maps cs) (a_brk cs) (ELit (d + 4096)))).
    { intros M. unfold kdisj_new. apply Forall_flat_map. apply Forall_forall. intros m Hm.
      destruct (is_fog m); [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
      cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Eb. rewrite (u64_lit (d + 4096)) by (unfold KHI in *; lia).
      pose proof (APARTG m Hm). lia. }
    assert (HKf : know_ok SEGS E (Mr A argH E cs model FULL) (kn csB)).
    { unfold csB, kn. cbn [a_ss mk_ss s_know].
      assert (HKf0 : know_ok SEGS E (Mr A argH E cs model FULL) (kdisj_new (a_maps cs) (a_brk cs) (ELit (d + 4096)) ++ kn_grant_filter A (kn cs) (a_maps cs))).
      { apply Forall_app. split; [apply HKdisj|].
        unfold kn_grant_filter, kimg_clip. apply know_ok_filter. apply know_ok_filter. exact HK. }
      apply Forall_app. split; [| exact HKf0]. apply (APS.brk_range_facts_ok SEGS _ E (Mr A argH E cs model FULL)). cbn [kn a_ss s_know]. exact HKf0. }
    destruct (flat_x_sound SEGS E _ (kn csB) bb bk (ELit d) HKf Hflat) as (Fb1 & Fb2 & Fb3).
    cbn [edenot] in Fb2, Fb3. rewrite (u64_lit d) in Fb2, Fb3 by (unfold KHI in *; lia).
    assert (Hest : estart E (SA bb bk) = bv_unsigned b).
    { rewrite <- Eb. symmetry. apply (u_of_split E (a_brk cs) bb bk Hsplit). lia. }
    assert (Hrf : region_free (vm_reserved h ++ vm_maps h) b dw = true).
    { apply region_free_intro. intros a sz Hin.
      pose proof (RefNodes.region_free_In _ b (Z_to_bv 64 (d + page_size)) a sz Hrfg Hin) as D.
      rewrite (u64_lit (d + page_size)) in D by (unfold KHI, page_size in *; lia).
      unfold iv_overlap. rewrite Udw. apply andb_false_iff.
      destruct D as [D|D]; [right; apply Z.ltb_ge; unfold page_size in D; lia | left; apply Z.ltb_ge; lia]. }
    assert (Hused : vm_backing_used model <= a_eager cs + a_abytes cs).
    { pose proof (vm_backing_used_le _ _ HAwf (co_minv _ _ _ _ _ _ _ _ _ _ _ HC)).
      pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC). lia. }
    set (req := Z_to_bv 64 (bv_unsigned b + d)) in *. fold dw.
    assert (Ureq : bv_unsigned req = bv_unsigned b + d) by (unfold req; apply u64_lit; unfold KHI in *; lia).
    set (h' := mkVmMapsFull (vm_reserved h) ((b, dw) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
    set (model' := with_vmmaps h' model). set (FULL' := zfill b dw FULL). set (R' := regupd R 10 req).
    assert (Hvm' : m_vmmaps model' = h') by reflexivity.
    assert (Hlz' : m_vm_lazy model' = m_vm_lazy model) by reflexivity.
    assert (HTOPEQ : TOP model' = TOP model) by reflexivity.
    (* [comment removed for export] *)
    assert (V1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
                 vis A E csB model' x = vis A E cs model x).
    { intros x Hx. unfold vis. rewrite HTOPEQ, Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw.
      replace ((bv_unsigned b <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned b + d))%bool with false
        by (symmetry; apply andb_false_iff; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      reflexivity. }
    assert (H1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
                 hid A argH E csB model' x = hid A argH E cs model x).
    { intros x Hx. unfold hid. rewrite (V1 x Hx). reflexivity. }
    assert (F1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x -> FULL' x = FULL x).
    { intros x Hx. unfold FULL'. apply zfill_out. rewrite Udw. exact Hx. }
    assert (M1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
                 Mr A argH E csB model' FULL' x = Mr A argH E cs model FULL x).
    { intros x Hx. unfold Mr, mrestrict. rewrite (H1 x Hx), (F1 x Hx). reflexivity. }
    (* [comment removed for export] *)
    assert (NA : forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d ->
                 in_ivs (bv_unsigned x) (vm_noaccess h) = false).
    { intros x Hx. destruct (in_ivs (bv_unsigned x) (vm_noaccess h)) eqn:Hna; [|reflexivity]. exfalso.
      pose proof (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC (bv_unsigned x) Hna) as Hm. fold h in Hm. rewrite Hmaps in Hm.
      apply (in_ivs_true) in Hm as (iv & Hin & Hiv).
      apply in_map_iff in Hin as (m & <- & Hin). unfold amap_den in Hiv. cbn [fst snd] in Hiv.
      destruct (APART m Hin); lia. }
    assert (Wf : ivs_wf (vm_maps h)) by exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)).
    assert (Wb : iv_wf (b, dw)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite Udw; unfold KHI in *; lia).
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csb) by (rewrite HpcB'; reflexivity).
    apply (HkB E R' FULL' model'); [split; apply env_agree_refl | | reflexivity].
    apply (vis_add_sound SEGS A LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) SHADOW_ok SINV argH argH_sp0 FS0 0%nat
             E csB (a_brk cs) (ELit d) _ csb R' FULL' model' Hva).
    + (* [comment removed for export] *)
      assert (HK1 : know_ok SEGS E (Mr A argH E csB model' FULL') (kn csB)).
      { unfold csB, kn. cbn [a_ss mk_ss s_know].
        assert (HK0 : know_ok SEGS E (Mr A argH E csB model' FULL') (kdisj_new (a_maps cs) (a_brk cs) (ELit (d + 4096)) ++ kn_grant_filter A (kn cs) (a_maps cs))).
        { apply Forall_app. split; [apply HKdisj|].
          apply (kn_grant_filter_ok E (Mr A argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned b) d HK MAPART);
            [right; exact B3 | unfold KHI in *; lia | lia | exact M1]. }
        apply Forall_app. split; [| exact HK0]. apply (APS.brk_range_facts_ok SEGS _ E (Mr A argH E csB model' FULL')). cbn [kn a_ss s_know]. exact HK0. }
      subst b. subst h.
      destruct HC; constructor; unfold csB;
        cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_vmops kn mk_ss s_regs s_log s_know s_pc s_next];
        fold csB; rewrite ?HTOPEQ; try assumption; try reflexivity.
      all: try (change (m_halted model') with (m_halted model); assumption).
      all: lazymatch goal with
      | |- regs_ok _ _ _ =>
          apply regs_ok_regupd_same; [exact co_regs0 | exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate]
      | |- know_ok _ _ _ _ => exact HK1
      | |- maps_match _ _ (vm_maps _) =>
          rewrite Hvm'; unfold h'; cbn [vm_maps maps_match is_fog am_kind mkind_eqb];
          exists (vm_maps (m_vmmaps model)); split; [|exact co_maps0];
          unfold amap_den; cbn [am_base am_len edenot]; rewrite Eb; fold dw; reflexivity
      | |- seps _ =>
          rewrite Hvm'; unfold h'; cbn [vm_maps]; constructor; [|exact co_seps0];
          rewrite Hmaps; apply Forall_forall; intros iv Hin; apply in_map_iff in Hin as (m & <- & Hin);
          unfold iv_disjoint, amap_den; cbn [fst snd]; rewrite Udw; destruct (APART m Hin); lia
      | |- model_ivs_wf _ =>
          apply model_ivs_wf_with_vmmaps; [exact co_wf0 | apply ivs_wf_cons; [exact Wb | exact Wf] | exact (proj1 (proj2 co_wf0)) | reflexivity]  (* [comment removed for export] *)
      | |- Forall _ (vm_maps _) =>
          rewrite Hvm'; unfold h'; cbn [vm_maps]; constructor; [|exact co_bounds0];
          cbn [fst snd]; rewrite Udw; unfold CEIL, KHI in *; lia
      | |- forall z, in_ivs z _ = true -> _ =>
          intros z Hz; rewrite Hvm'; unfold h'; cbn [vm_maps]; rewrite in_ivs_cons;
          rewrite (co_nasub0 z Hz); apply orb_true_r
      | |- Forall (hole_ok _ _ _) (_ :: _) =>      (* [comment removed for export] *)
          constructor; [intros Hk; discriminate|];
          rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps];
          apply Forall_forall; intros m0 Hm0 Hk0;
          destruct (proj1 (Forall_forall _ _) co_holes0 m0 Hm0 Hk0) as [HF1 HF2]; split; [|exact HF2];
          intros iv Hiv; apply in_app_iff in Hiv as [Hiv|[<-|Hiv]];
          [ apply HF1; apply in_app_iff; left; exact Hiv
          | cbn [fst snd]; rewrite Udw; unfold uE; destruct (APART m0 Hm0); lia
          | apply HF1; apply in_app_iff; right; exact Hiv ]
      | |- Forall _ (_ :: _) =>
          constructor; [first [intros Hk; discriminate | intros [Hk|Hk]; discriminate] | assumption]
      | |- sum_sizes _ <= _ =>
          rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps]; rewrite sum_sizes_app in *; cbn [sum_sizes snd]; rewrite Udw;
          cbn [sum_sizes] in co_totsz0; lia
      | |- vm_brk _ = _ =>
          rewrite Hvm'; unfold h'; cbn [vm_brk];
          rewrite <- (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 ltac:(constructor; assumption) ltac:(lia)); symmetry; exact G10
      | |- bv_unsigned (vm_start_brk _) <= _ =>
          rewrite Hvm'; unfold h'; cbn [vm_start_brk vm_brk]; rewrite Ureq; lia
      | |- eager_used _ <= _ =>
          pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He; lia
      | |- MInv _ _ =>
          eapply MInv_transport; [exact co_minv0 | reflexivity | reflexivity |];
          pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He;
          rewrite Hvm'; unfold h'; cbn [vm_limit]; rewrite co_limit0;
          change (allowA A E csB) with (allowA A E cs); lia
      | |- forall a, hid _ _ _ _ _ a = true -> _ =>
          intros a Ha Hm Hna Hlz Hgh;
          rewrite Hvm' in Hm; unfold h' in Hm; cbn [vm_maps] in Hm; rewrite in_ivs_cons, Udw in Hm;
          destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)))) as [Hlt|Hge];
          [|destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)) + d)) as [Hlt2|Hge2]];
          [ rewrite (F1 a ltac:(lia)); rewrite (H1 a ltac:(lia)) in Ha; apply (co_zero0 a Ha); [|exact Hna|exact Hlz|exact Hgh];
            apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [Hm _]; apply Z.leb_le in Hm; lia
          | unfold FULL'; apply zfill_in; rewrite Udw; lia
          | rewrite (F1 a ltac:(lia)); rewrite (H1 a ltac:(lia)) in Ha; apply (co_zero0 a Ha); [|exact Hna|exact Hlz|exact Hgh];
            apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [_ Hm]; apply Z.ltb_lt in Hm; lia ]
      | |- SINV _ _ =>
          eapply SINV_frame; [|exact co_sinv0]; intros a Ha; apply F1; pose proof (argH_high _ _ Ha); unfold CEIL, KHI in *; lia
      | |- vm_noaccess _ = _ /\ m_vm_lazy _ = _ =>     (* [comment removed for export] *)
          rewrite Hvm', Hlz'; unfold h'; cbn [vm_noaccess]; exact co_vmx0
      | |- ?g => idtac "UNSOLVED FIELD:" g
      end.
    + (* [comment removed for export] *)
      assert (INB : forall i, 0 <= i < d ->
                Mr A argH E csb model' FULL' (Z_to_bv 64 (bv_unsigned b + i)) = Some (Z_to_bv 8 0)).
      { intros i Hi. set (a := Z_to_bv 64 (bv_unsigned b + i)).
        assert (Ua : bv_unsigned a = bv_unsigned b + i) by (unfold a; apply u64_lit; unfold KHI in *; lia).
        assert (Hargh : argH E a = false).
        { destruct (argH E a) eqn:Ha; [|reflexivity]. pose proof (argH_high _ _ Ha). unfold CEIL, KHI in *. lia. }
        assert (Hvis : vis A E csb model' a = true).
        { assert (Hal : in_allow A E csb (bv_unsigned a) = true).
          { unfold in_allow, in_vis. rewrite HvisB'. cbn [existsb fst snd]. unfold uE at 1 2 3. rewrite Eb. cbn [edenot].
            rewrite (u64_lit d) by (unfold KHI in *; lia). rewrite Ua.
            replace (bv_unsigned b <=? bv_unsigned b + i) with true by (symmetry; apply Z.leb_le; lia).
            replace (bv_unsigned b + i <? bv_unsigned b + d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          unfold vis. rewrite Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw, Hal.
          rewrite (NA a) by lia. rewrite Ua.
          replace (bv_unsigned b <=? bv_unsigned b + i) with true by (symmetry; apply Z.leb_le; lia).
          replace (bv_unsigned b + i <? bv_unsigned b + d) with true by (symmetry; apply Z.ltb_lt; lia).
          cbn [andb orb negb]. rewrite !orb_true_r. reflexivity. }
        unfold Mr, mrestrict, hid. rewrite Hargh, Hvis. cbn [negb orb]. unfold FULL'. apply zfill_in. rewrite Udw, Ua. lia. }
      assert (Hfl : flat E (SA bb bk) (elenZ E (ELit d))).
      { unfold flat. rewrite (elenZ_lit E d) by (unfold KHI in *; lia). rewrite Hest. unfold KHI in *. lia. }
      constructor; [|constructor].
      * (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros off m Hoff Hm.
        rewrite (elenZ_lit E d) in Hm by (unfold KHI in *; lia). rewrite Hest.
        destruct m as [|m']; [reflexivity|].
        apply store_ok_of_all; [rewrite u64_lit by (unfold KHI in *; lia); unfold KHI in *; lia|].
        intros x Hx. rewrite u64_lit in Hx by (unfold KHI in *; lia).
        unfold wview. replace x with (Z_to_bv 64 (bv_unsigned b + (bv_unsigned x - bv_unsigned b)))
          by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); unfold KHI in *; lia).
        rewrite (INB (bv_unsigned x - bv_unsigned b)) by lia. discriminate.
      * (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros i Hi.
        rewrite (elenZ_lit E d) in Hi by (unfold KHI in *; lia). rewrite Hest. apply INB. exact Hi.
      * (* [comment removed for export] *)
        assert (HK1 : know_ok SEGS E (Mr A argH E csB model' FULL') (kn csB)).
        { unfold csB, kn. cbn [a_ss mk_ss s_know].
          assert (HK0 : know_ok SEGS E (Mr A argH E csB model' FULL') (kdisj_new (a_maps cs) (a_brk cs) (ELit (d + 4096)) ++ kn_grant_filter A (kn cs) (a_maps cs))).
          { apply Forall_app. split; [apply HKdisj|].
            apply (kn_grant_filter_ok E (Mr A argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned b) d HK MAPART);
              [right; exact B3 | unfold KHI in *; lia | lia | exact M1]. }
          apply Forall_app. split; [| exact HK0]. apply (APS.brk_range_facts_ok SEGS _ E (Mr A argH E csB model' FULL')). cbn [kn a_ss s_know]. exact HK0. }
        unfold Mr in HK1 |- *.
        apply (know_ok_unhide SEGS A E (hid A argH E csB model') (hid A argH E csb model') FULL' (kn csB)).
        -- apply (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high).
        -- unfold csB, kn. cbn [a_ss mk_ss s_know]. apply kimg_in_hull_app; [| apply kimg_in_hull_app; [|unfold kn_grant_filter; apply (kimg_clip_in_hull A)]].
           ++ apply AsanNodesMmLib.kimg_in_hull_pure. unfold brk_range_facts.
              destruct (gaps_of _ 5 4096) as [gaps|]; [destruct (gaps_lohi gaps) as [g|]|]; repeat constructor.
           ++ apply AsanNodesMmLib.kimg_in_hull_pure. apply AsanNodesMmLib.kdisj_new_pure.
        -- intros a Ha. unfold hid in Ha |- *. apply orb_true_iff in Ha. apply orb_true_iff.
           destruct Ha as [Ha|Ha]; [left; exact Ha|]. right. apply negb_true_iff in Ha. apply negb_true_iff.
           destruct (vis A E csB model' a) eqn:Hv; [|reflexivity]. exfalso.
           rewrite (vis_mono A E csB csb model' a) in Ha; [discriminate| |exact Hv].
           intros z Hz. unfold in_allow, in_vis, in_sh in Hz |- *. rewrite HvisB'. cbn [existsb].
           apply orb_true_iff in Hz. apply orb_true_iff.
           destruct Hz as [Hz|Hz]; [left|right]; apply orb_true_iff; right; exact Hz.
        -- intros a Ha. apply (hid_hull A HULL_ok argH argH_high). exact Ha.
        -- exact HK1.
Qed.


End SoundB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundMunmap.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : length (segments_reserved SEGS) = n_res A.
Hypothesis HULL_ok : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis SHADOW_ok : 0 <= shadow_off A <= 2 ^ 47.
Hypothesis RES_hullH : RES_hull_def SEGS A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis argH_sp0 : forall E (a : word), argH E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis E_SP0 : AP.expr_vars_lt nx0 e_sp0_early = true.
Variable FS0 : Fs.Fs.
Context {SC : StepCfg} {AF : AllocForced SC}.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH E_SP0 argH_agree SINV_agree FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_sp0 FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.

Lemma mmap_len_sound : forall E cs R FULL model ne nlo nhi,
  CSOK E cs R FULL model -> mmap_len cs = Some (ne, nlo, nhi) ->
  let len := bv_unsigned (edenot E (reg cs 11)) in
  getr R (Z_to_bv 5 11) = Z_to_bv 64 len
  /\ 0 < len < 2 ^ 64
  /\ edenot E ne = Z_to_bv 64 (page_round_up_Z len)
  /\ 0 < nlo /\ nlo <= page_round_up_Z len <= nhi
  /\ page_round_up_Z len mod 4096 = 0
  /\ (forall E', edenot E' (reg cs 11) = edenot E (reg cs 11) -> edenot E' ne = edenot E ne).
Proof.
  intros E cs R FULL model ne nlo nhi HC HML len.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  pose proof (u64_range (edenot E (reg cs 11))) as Hr.
  rewrite mmap_len_eq in HML. (* [comment removed for export] *) unfold mmap_len_ref in HML.
  destruct (reg_lit cs 11) as [lz|] eqn:H11.
  - destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
    destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
    assert (Hlen : len = lz).
    { unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
    rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
    rewrite page_up_eq.
    split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [apply page_round_up_Z_aligned'|]. intros E' _. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection HML as <- <- <-.
    apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo Hal].
    apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal. apply Z.leb_le in Hhi.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
    pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
    destruct (ealign_sound SEGS E _ (kn cs) (reg cs 11) HK) as [_ Hdiv].
    assert (Hmod : len mod 4096 = 0).
    { unfold len. destruct Hdiv as [q Hq]. rewrite Hq.
      replace (2 ^ ealign (kn cs) (reg cs 11)) with (2 ^ (ealign (kn cs) (reg cs 11) - 12) * 4096)
        by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    assert (Hpr : page_round_up_Z len = len).
    { unfold page_round_up_Z, page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold len in *. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    rewrite Hpr.
    split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [unfold len in *; lia|]. split; [symmetry; apply Z_to_bv_bv_unsigned|].
    split; [lia|]. split; [unfold len in *; lia|]. split; [exact Hmod|].
    intros E' HE'. exact HE'.
Qed.

Lemma bv5_of_nat : forall n, (n < 32)%nat -> Z_to_bv 5 (Z.of_nat n) = Z_to_bv 5 (Z.of_nat n). Proof. reflexivity. Qed.
Lemma bv5_10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_11 : (11%bv : bv 5) = Z_to_bv 5 (Z.of_nat 11). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_12 : (12%bv : bv 5) = Z_to_bv 5 (Z.of_nat 12). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_13 : (13%bv : bv 5) = Z_to_bv 5 (Z.of_nat 13). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_14 : (14%bv : bv 5) = Z_to_bv 5 (Z.of_nat 14). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_15 : (15%bv : bv 5) = Z_to_bv 5 (Z.of_nat 15). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_17 : (17%bv : bv 5) = Z_to_bv 5 (Z.of_nat 17). Proof. apply bv_eq. reflexivity. Qed.

Lemma some_inj : forall {T} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. injection H as H1. exact H1. Qed.

Lemma CEIL_eq : alloc_ceiling = CEIL.
Proof. reflexivity. Qed.
Lemma KHI_eq : kHighMemBeg = KHI.
Proof. reflexivity. Qed.
Lemma FLOOR_eq : bottomup_floor = FLOOR.
Proof. rewrite bottomup_floor_val. reflexivity. Qed.

Lemma Z_to_bv64_m1 : forall m1, m1 = two64 - 1 -> Z_to_bv 64 m1 = Z_to_bv 64 (-1).
Proof. intros m1 ->. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reserved_free_above : forall model (lo n : word),
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  img_hi A <= bv_unsigned lo ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. right. lia.
Qed.

(* [comment removed for export] *)
Lemma vis_add_inv : forall cs b n k cs2,
  vis_add A LIMIT cs b n k = Some cs2 ->
  exists nhi, xhi (kn cs) n = Some nhi /\
  cs2 = ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts A (kn cs) (a_maps cs) b n ++ vis_twins A (kn cs) b n (a_vis cs) ++ k) (nxt cs))   (* [comment removed for export] *)
            (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
            ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk]. destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|]; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection Hv as <-. exists nhi. split; [reflexivity|]. unfold shadow_facts, vis_twins. rewrite Hsh. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_allow_ext : forall E cs cs', a_vis cs' = a_vis cs -> in_allow A E cs' = in_allow A E cs.
Proof. intros E cs cs' H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. rewrite H. reflexivity. Qed.

Lemma split_flat_estart : forall E M k e b off n,
  know_ok SEGS E M k -> split_lit e = (b, off) -> flat_x k b off n = true ->
  estart E (SA b off) = bv_unsigned (edenot E e)
  /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k e b off n HK Hsp Hfl.
  destruct (APS.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3).
  pose proof (APS.u_of_split E e b off Hsp ltac:(lia)). repeat split; lia.
Qed.

Lemma seps_map_disjoint : forall (f : amap -> word * word) ms m m',
  seps (map f ms) -> In m ms -> In m' ms -> m <> m' -> iv_disjoint (f m) (f m').
Proof.
  intros f ms. induction ms as [|h t IH]; intros m m' Hs Hm Hm' Hne; [destruct Hm|].
  cbn [map] in Hs. inversion Hs as [|p l Hf Hl]; subst.
  destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf (f m') (in_map f t m' Hm')).
  - pose proof (proj1 (Forall_forall _ _) Hf (f m) (in_map f t m Hm)) as D. unfold iv_disjoint in *. lia.
  - exact (IH m m' Hl Hm Hm' Hne).
Qed.

Lemma covered_maps_subtract : forall l lo hi x,
  ivs_wf l -> lo <= hi ->
  covered (maps_subtract l lo hi) x = (covered l x && negb (in_rng lo hi x))%bool.
Proof. intros. apply (proj2 (proj2 (maps_subtract_sem l lo hi H H0))). Qed.

(* [comment removed for export] *)
Lemma len_eqb_sound : forall E M k n m,
  know_ok SEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
  intros E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as B1.
    cbn [xt_den] in A1, B1. apply bv_eq. lia.
Qed.

(* [comment removed for export] *)
Lemma kzero_x_sound : forall E M allkn k b off n,
  know_ok SEGS E M allkn -> know_ok SEGS E M k -> kzero_x allkn k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64
  /\ forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n -> M x = Some (Z_to_bv 8 0).
Proof.
  intros E M allkn k b off n HA HK. induction k as [|K k IH]; intros H; [discriminate|].
  apply Forall_cons_iff in HK as [HKK HK]. cbn [kzero_x] in H.
  assert (CONT : forall zb zk zn,
            kentry_ok SEGS E M (KZero (SA zb zk) zn) ->
            estart E (SA zb zk) <= estart E (SA b off) -> estart E (SA b off) + elenZ E n <= estart E (SA zb zk) + elenZ E zn ->
            0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64
            /\ forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n -> M x = Some (Z_to_bv 8 0)).
  { intros zb zk zn [Hfl Hz] I1 I2. destruct Hfl as (F1 & F2 & F3 & F4). split; [lia|]. split; [lia|].
    intros x Hx. replace x with (Z_to_bv 64 (estart E (SA zb zk) + (bv_unsigned x - estart E (SA zb zk)))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); lia).
    apply Hz. lia. }
  destruct K as [|[zb zk] zn| | | | | | | |]; try (apply IH; assumption).
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end.
  - destruct (expr_eqb b zb && (zk <=? off))%bool eqn:Hb; [|discriminate].
    apply andb_prop in Hb as [Hb Hzk]. apply expr_eqb_eq in Hb. subst zb. apply Z.leb_le in Hzk.
    destruct (xhi allkn n) as [nh|] eqn:Hnh; [|discriminate]. destruct (xlo allkn zn) as [zl|] eqn:Hzl; [|discriminate].
    apply Z.leb_le in Hc. pose proof (xhi_sound SEGS E M allkn n nh HA Hnh). pose proof (xlo_sound SEGS E M allkn zn zl HA Hzl).
    apply (CONT b zk zn HKK); unfold estart, elenZ; cbn [a_base a_off]; lia.
  - destruct (xinside allkn b off n zb zk zn) eqn:Hins; [|apply IH; assumption].
    pose proof (xinside_sound SEGS E M allkn b off n zb zk zn HA Hins) as [I1 I2]. apply (CONT zb zk zn HKK I1 I2).
Qed.

(* [comment removed for export] *)
Lemma kentry_keep_foot : forall E M M' K,
  kentry_ok SEGS E M K ->
  (forall x : word, match kfoot E K with
                    | Some (s, l) => s <= bv_unsigned x < s + l
                    | None => False end -> M' x = M x) ->
  (forall x : word, M x = None -> M' x = None) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' K HK Hin Hnone.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok kfoot] in *;
    try exact HK.
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hrd. apply rdn_ext; [rewrite (flat_u E _ _ Hfl); destruct Hfl; lia|].
    intros x Hx. apply Hin. rewrite (flat_u E _ _ Hfl) in Hx. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi. apply Hnone. apply HC. exact Hi.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hin by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Definition sh_iv (E : env) (k : list kentry) (p : expr * expr) : Z * Z :=
  let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in (estart E (SA sb sk), elenZ E sn).

(* [comment removed for export] *)
Lemma fold_unfill_inv : forall E M k gone acc K,
  know_ok SEGS E M k ->
  (forall K', In K' acc -> In K' k) ->
  In K (fold_left (fun kk p => let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in kn_unfill kk sb sk sn) gone acc) ->
  In K acc /\ (kimg_b K = true \/ forall p, In p gone -> kfoot_apart E K (fst (sh_iv E k p)) (snd (sh_iv E k p))).
Proof.
  intros E M k gone. induction gone as [|p gone IH]; intros acc K HK Hacc Hin.
  - cbn in Hin. split; [exact Hin|]. right. intros q [].
  - cbn [fold_left] in Hin.
    destruct (shadow_of A k (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
    assert (Hacc' : forall K', In K' (kn_unfill acc sb sk sn) -> In K' k).
    { intros K' HK'. unfold kn_unfill in HK'. apply filter_In in HK' as [HK' _]. apply Hacc. exact HK'. }
    destruct (IH _ K HK Hacc' Hin) as [Hin1 Hrest].
    unfold kn_unfill in Hin1. apply filter_In in Hin1 as [Hin0 Hkeep]. split; [exact Hin0|].
    apply orb_prop in Hkeep as [Himg|Hap]; [left; exact Himg|].
    destruct Hrest as [Himg|Hrest]; [left; exact Himg|]. right.
    intros q [<-|Hq]; [|apply Hrest; exact Hq].
    unfold sh_iv. rewrite Hsh. cbn [fst snd].
    rewrite APS.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [|exact Hap].
    unfold know_ok. apply Forall_forall. intros K' HK'. exact (proj1 (Forall_forall _ _) HK K' (Hacc K' HK')).
Qed.

Lemma existsb_filter_split : forall {T} (g h : T -> bool) l,
  existsb h l = (existsb h (List.filter g l) || existsb h (List.filter (fun x => negb (g x)) l))%bool.
Proof.
  intros T g h l. induction l as [|x l IH]; cbn; [reflexivity|].
  destruct (g x); cbn; rewrite IH; destruct (h x); cbn; rewrite ?orb_true_r; reflexivity.
Qed.

Lemma node_munmap_sound : forall cs cs' E R FULL model T,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  node_munmap A cs = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn HK.
  destruct (AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
  rewrite node_munmap_eq in Hn. (* [comment removed for export] *) unfold node_munmap_ref in Hn.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 215).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  subst z17.
  destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsp.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hgone]. apply andb_prop in Hcond as [Hcond Hhi64]. apply andb_prop in Hcond as [Hcond HFLAT]. apply andb_prop in Hcond as [Hhas Hpal].
  set (k := kn cs) in *.
  set (g := fun p : expr * expr => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) in *.
  set (ng := fun p : expr * expr => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) in *.
  assert (NG : forall l, List.filter ng l = List.filter (fun p => negb (g p)) l).
  { intros l. induction l as [|p l IH]; cbn; [reflexivity|]. rewrite IH. subst g ng. cbv beta. destruct (split_lit (fst p)); reflexivity. }
  rewrite !NG in Hn, Hgone. clear NG ng.
  set (gone := List.filter (fun p => negb (g p)) (a_vis cs)) in *.
  set (kept := List.filter g (a_vis cs)) in *.
  apply some_inj in Hn. subst cs'.
  (* [comment removed for export] *)
  apply existsb_exists in Hhas as (m & Hm & Hmatch). unfold amap_match in Hmatch. apply andb_prop in Hmatch as [Hb Hlen_eq].
  pose proof (len_eqb_sound E _ k ne (am_len m) HKN Hlen_eq) as Hne_eq.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & _ & _).
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (addr := edenot E (reg cs 10)). set (n := edenot E (am_len m)).
  assert (Haddr : True) by exact I.
  apply andb_prop in Hb as [Hnf Hb]. apply negb_true_iff in Hnf. apply expr_eqb_eq in Hb.
  assert (Haddr' : edenot E (am_base m) = addr) by (subst addr; rewrite Hb; reflexivity). clear Haddr. rename Haddr' into Haddr.
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
  pose proof (maps_match_In E _ _ m MM Hm Hnf) as HIN.
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
  assert (BPOS : forall iv, In iv (vm_maps (m_vmmaps model)) -> 0 < bv_unsigned (snd iv)).
  { intros iv Hiv. exact (proj1 (proj1 (Forall_forall _ _) HB iv Hiv)). }
  pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5).
  unfold amap_den in B1, B2, B3, B4, B5. cbn [fst snd] in B1, B2, B3, B4, B5. rewrite Haddr in B2, B4, B5. fold n in B1, B3, B4, B5.
  pose proof (u64_range addr) as Ra. pose proof (u64_range n) as Rn.
  destruct (xhi k (reg cs 10)) as [ahi|] eqn:Hahi; [|discriminate]. apply Z.leb_le in Hhi64.
  pose proof (xhi_sound SEGS E _ k (reg cs 10) ahi HKN Hahi) as Hahi'. fold addr in Hahi'. unfold two64 in Hhi64.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. rewrite <- Hne_eq, Hne. apply u64_lit. lia. }
  assert (HnZw : Z_to_bv 64 nZ = n) by (rewrite <- Un; apply Z_to_bv_bv_unsigned).
  destruct (split_flat_estart E _ k (reg cs 10) bb bk ne HKN Hsp HFLAT) as (Hest & _ & _). fold addr in Hest.
  assert (HelenZ : elenZ E ne = nZ) by (unfold elenZ; rewrite Hne; apply u64_lit; lia).
  set (lo := bv_unsigned addr) in *. set (hi := lo + nZ).
  pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as HTOP. pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as HSP0. unfold CEIL, CEILMAX in HTOP.
  assert (Hlohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= TOP model /\ lo < hi /\ lo mod 4096 = 0 /\ hi mod 4096 = 0).   (* [comment removed for export] *)
  { subst hi. split; [lia|]. repeat split; try lia. rewrite Z.add_mod, B2 by lia. rewrite <- Un, B3. reflexivity. }
  pose proof HULL_ok as (HU0 & HU1 & HU2 & HU3).
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 215 HC ltac:(lia) H17) as [R17 _]. rewrite <- bv5_17 in R17.
  pose proof (reg_sound' E cs R FULL model 10 HC ltac:(lia)) as R10. fold addr in R10. rewrite <- bv5_10 in R10.
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  (* [comment removed for export] *)
  pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS.
  assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
            bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m'))).
  { intros m' Hm' Hnf' Hne'. pose proof (maps_match_disjoint SEGS A RES_len E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne') as D.
    unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. rewrite Haddr in D. fold n lo in D. subst hi. lia. }
  (* [comment removed for export] *)
  assert (DISJl : forall iv, In iv (vm_maps (m_vmmaps model)) -> iv <> amap_den E m ->
            bv_unsigned (fst iv) + bv_unsigned (snd iv) <= lo \/ hi <= bv_unsigned (fst iv)).
  { intros iv Hiv Hne'. pose proof (seps_In_disjoint _ iv (amap_den E m) SEPS BPOS Hiv HIN Hne') as D.
    unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. rewrite Haddr in D. fold n lo in D. subst hi. lia. }
  assert (UNIQ : forall iv, In iv (vm_maps (m_vmmaps model)) -> fst iv = addr -> iv = amap_den E m).
  { intros [ib isz] Hiv Hb0. cbn [fst] in Hb0. subst ib.
    destruct (bv_eqb isz n) eqn:Hs.
    - apply bv_eqb_eq in Hs. subst isz. unfold amap_den. rewrite Haddr. reflexivity.
    - exfalso. assert (Hne' : (addr, isz) <> amap_den E m).
      { unfold amap_den. rewrite Haddr. fold n. intros Heq. injection Heq as Heq. rewrite Heq, bv_eqb_refl in Hs. discriminate. }
      pose proof (DISJl _ Hiv Hne') as D. cbn [fst snd] in D. pose proof (BPOS _ Hiv) as P. cbn [snd] in P. subst lo hi. lia. }
  assert (MATCH : forall m', In m' (a_maps cs) -> negb (amap_match k (reg cs 10) ne m') = negb (amap_eqb m' m)).
  { intros m' Hm'. f_equal. unfold amap_match.
    destruct (amap_eqb m' m) eqn:Hmm.
    - apply APS.amap_eqb_eq in Hmm. subst m'. rewrite Hnf, <- Hb, expr_eqb_refl, Hlen_eq. reflexivity.
    - assert (Hne' : m <> m') by (intros <-; rewrite amap_eqb_refl in Hmm; discriminate).
      destruct (is_fog m') eqn:Hnf'; [reflexivity|]. cbn [negb andb].
      destruct (expr_eqb (reg cs 10) (am_base m')) eqn:Heq; [|reflexivity]. exfalso.
      apply expr_eqb_eq in Heq.
      pose proof (DISJ' m' Hm' Hnf' Hne') as D. rewrite <- Heq in D. fold addr lo in D.
      pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' MM Hm' Hnf')) as (C1 & _). unfold amap_den in C1. cbn [snd] in C1. lia. }
  assert (MAPS' : maps_match E (List.filter (fun m' => negb (amap_match k (reg cs 10) ne m')) (a_maps cs)) (map_remove (vm_maps (m_vmmaps model)) addr)).
  { rewrite (filter_ext_in _ (fun m' => negb (amap_eqb m' m))) by (intros m' Hm'; exact (MATCH m' Hm')).
    rewrite <- Haddr. apply maps_match_remove; [exact MM | exact Hm | exact Hnf | exact (seps_NoDup _ SEPS BPOS) |].
    intros iv Hiv Hfst. apply UNIQ; [exact Hiv | rewrite Hfst; exact Haddr]. }
  assert (INMAPS' : forall z, in_ivs z (map_remove (vm_maps (m_vmmaps model)) addr) = (in_ivs z (vm_maps (m_vmmaps model)) && negb (in_rng lo hi z))%bool).
  { intros z. unfold map_remove.
    destruct (in_ivs z (List.filter (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model)))) eqn:Hl; symmetry.
    - apply in_ivs_true' in Hl as (iv & Hiv & Hziv). apply filter_In in Hiv as [Hiv Hkeep]. apply negb_true_iff in Hkeep.
      assert (Hne' : iv <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
      pose proof (DISJl iv Hiv Hne') as D.
      apply andb_true_intro. split; [apply (proj2 (in_ivs_true' _ _)); exists iv; auto|].
      apply negb_true_iff. unfold in_rng. apply andb_false_iff. destruct D; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
    - apply andb_false_iff.
      destruct (in_ivs z (vm_maps (m_vmmaps model))) eqn:Hin; [right|left; reflexivity].
      apply in_ivs_true' in Hin as (iv & Hiv & Hziv). apply negb_false_iff.
      destruct (bv_eqb (fst iv) addr) eqn:Hfa.
      + apply bv_eqb_eq in Hfa. pose proof (UNIQ iv Hiv Hfa) as ->. unfold amap_den in Hziv. cbn [fst snd] in Hziv. rewrite Haddr in Hziv. fold n lo in Hziv.
        unfold in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; subst hi; lia.
      + exfalso. assert (X : in_ivs z (List.filter (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) = true); [|congruence].
        apply (proj2 (in_ivs_true' _ _)). exists iv. split; [|exact Hziv]. apply filter_In. rewrite Hfa. auto. }
  (* [comment removed for export] *)
  assert (GONE : forall p, In p gone ->
            (forall z, (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)) = true -> lo <= z < hi)%bool
            /\ (0 <= fst (sh_iv E k p))
            /\ (forall x : word, fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p) -> MR E cs model FULL x = Some (Z_to_bv 8 0))
            /\ (forall z, (sh_lo A E p <=? z) && (z <? sh_hi A E p) = true -> fst (sh_iv E k p) <= z < fst (sh_iv E k p) + snd (sh_iv E k p))%bool).
  { intros p Hp.
    pose proof (proj1 (forallb_forall _ _) Hgone p Hp) as G. cbv beta in G.
    assert (Hpv : In p (a_vis cs)) by (unfold gone in Hp; apply filter_In in Hp as [Hp _]; exact Hp).
    destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
    destruct (shadow_of A k (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
    apply andb_prop in G as [G Gz]. apply andb_prop in G as [G Gin]. apply andb_prop in G as [Gab Gan].
    apply Z.leb_le in Gab. apply Z.leb_le in Gan.
    assert (AL8 : forall e, 3 <= ealign k e -> uE E e mod 8 = 0).
    { intros e Hee. destruct (ealign_sound SEGS E _ k e HKN) as [_ [q Hq]]. unfold uE. rewrite Hq.
      replace (2 ^ ealign k e) with (2 ^ (ealign k e - 3) * 8) by (rewrite <- (Z.pow_add_r 2 _ 3) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    pose proof (AL8 _ Gab) as A8b. pose proof (AL8 _ Gan) as A8n.
    pose proof (xinside_sound SEGS E _ k pb pk (snd p) bb bk ne HKN Gin) as [I1 I2]. rewrite Hest, ?HelenZ in I1, I2. rewrite HelenZ in I2.
    unfold elenZ in I2.
    pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(pose proof (u64_range (edenot E (snd p))); unfold CEIL in *; (first [clear - RES_len B1 Ra HTOP Hlohi I1 I2 H; lia | lia]))) as Up.
    destruct (kzero_x_sound E _ k k sb sk sn HKN HKN Gz) as (Z1 & Z2 & Z3).
    unfold sh_iv. rewrite Hsh. cbn [fst snd].
    split; [|split; [exact Z1 | split; [exact Z3|]]].
    - intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold uE in *. rewrite Up in Hz1, Hz2. subst hi. (first [clear - RES_len B1 Ra Hlohi I1 I2 Up Hz1 Hz2; lia | lia]).
    - (* [comment removed for export] *)
      unfold shadow_of in Hsh.
      destruct (split_lit (eadd (mkSrl k (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
      assert (Usn : elenZ E (mkSrl k (snd p) 3) = bv_unsigned (edenot E (snd p)) / 8).
      { unfold elenZ. rewrite (mkSrl_denot SEGS E _ k (snd p) 3 (Z_to_bv 64 3) HKN) by (rewrite u64_lit by lia; reflexivity).
        rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
      rewrite Usn in *.
      pose proof (APS.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
      apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
      rewrite (mkSrl_denot SEGS E _ k (fst p) 3 (Z_to_bv 64 3) HKN) in D by (rewrite u64_lit by lia; reflexivity).
      rewrite u_srl64 in D. pose proof SHADOW_ok as SO. pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn'.
      change (2 ^ (3 mod 64)) with 8 in D.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite !u64_lit in D by (lia_guard; (lia_guard; first [clear - RES_len SHADOW_ok; lia | lia])).
      rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (first [clear - Rb SO; lia | lia]).
      intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold sh_lo, sh_hi, uE in Hz1, Hz2.
      unfold estart. cbn [a_base a_off]. unfold estart in Z1, Z2. cbn [a_base a_off] in Z1, Z2.
      (* [comment removed for export] *)
      rewrite Z_to_bv_unsigned, bv_wrap64_mod in D. unfold uE in A8b, A8n. (first [clear - Hz2 Hz1 D Z2 Z1 A8n E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia]).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & Wsp).
  unfold cfg_of.
  eapply (srz_munmap_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len T Hf He Hhalt R17 R10 B2 R11 ltac:(lia)).
  { unfold TASK_SIZE. fold nZ. unfold CEIL in *. lia. }  (* [comment removed for export] *)
  { fold nZ. rewrite HnZw. apply map_has_intro. rewrite <- Haddr. exact HIN. }
  fold nZ. rewrite HnZw. rewrite (v_addi_pc (pc cs) Hp0 Hp4).
  set (model' := munmap_model addr n model). set (FULL' := unfill addr n FULL).
  match goal with |- srealizes _ (mkCfg _ ?mo) _ => change mo with model' end.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _) in HK.
  specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
  unfold cfg_of in HK. replace (pc cs') with (pc cs + 4) in HK by reflexivity. rewrite bv5_10. apply HK; [|reflexivity]. clear HK.
  (* [comment removed for export] *)
  assert (PM : vm_maps (m_vmmaps model') = map_remove (vm_maps (m_vmmaps model)) addr) by reflexivity.
  assert (PN : vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) lo (lo + bv_unsigned n)) by reflexivity.
  assert (PL : m_vm_lazy model' = maps_subtract (m_vm_lazy model) lo (lo + bv_unsigned n)) by reflexivity.
  assert (PISP : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)) by reflexivity.  (* [comment removed for export] *)
  assert (PT : m_vm_materialized model' = List.filter (page_outside_range lo (lo + bv_unsigned n)) (m_vm_materialized model)) by reflexivity.
  rewrite Un in PN, PL, PT. fold hi in PN, PL, PT.
  (* [comment removed for export] *)
  assert (NOACC : forall z, in_ivs z (vm_noaccess (m_vmmaps model')) = (in_ivs z (vm_noaccess (m_vmmaps model)) && negb (in_rng lo hi z))%bool).
  { intros z. rewrite PN, !in_ivs_covered. apply covered_maps_subtract; [exact W2 | lia]. }
  assert (LAZYOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
            page_in_ranges (page_base x) (m_vm_lazy model') = page_in_ranges (page_base x) (m_vm_lazy model)).
  { intros x Hx. rewrite PL. destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
    pose proof (page_of_byte_out_aligned x lo hi L4 L5 Hx). apply page_in_ranges_subtract_out; [exact W3 | lia | unfold page_size; lia]. }
  assert (ALW : forall z, in_allow A E cs z = (in_allow A E cs' z || existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool gone
                                                 || existsb (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool gone)%bool).
  { intros z. unfold in_allow, in_vis, in_sh, cs'. cbn [a_vis]. subst kept gone.
    rewrite (existsb_filter_split g (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs)).
    rewrite (existsb_filter_split g (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool (a_vis cs)).
    destruct (existsb _ _), (existsb _ _), (existsb _ _), (existsb _ _); reflexivity. }
  assert (VISLE : forall x : word, VIS E cs' model' x = true -> VIS E cs model x = true /\ (lo <= bv_unsigned x < hi -> False)).
  { intros x Hv. unfold vis in Hv |- *. change (TOP model') with (TOP model) in Hv. rewrite PM, INMAPS', NOACC in Hv. destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
    destruct (in_rng lo hi (bv_unsigned x)) eqn:Hr.
    - unfold in_rng in Hr. apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2.
      replace (in_hull A (bv_unsigned x)) with false in Hv
        by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      replace (TOP model <=? bv_unsigned x) with false in Hv by (symmetry; apply Z.leb_gt; lia).
      rewrite andb_false_r in Hv. cbn in Hv. discriminate.
    - assert (Hx : bv_unsigned x < lo \/ hi <= bv_unsigned x).
      { unfold in_rng in Hr. apply andb_false_iff in Hr as [Hr|Hr]; [apply Z.leb_gt in Hr | apply Z.ltb_ge in Hr]; lia. }
      split; [|lia]. rewrite (LAZYOUT x Hx) in Hv. rewrite !andb_true_r in Hv.
      apply orb_prop in Hv as [Hv|Hv]; [rewrite Hv; reflexivity|]. apply orb_true_iff. right.
      apply andb_prop in Hv as [Hv1 Hv2]. apply andb_prop in Hv1 as [Hv0 Hv1]. rewrite Hv0, Hv1. cbn [andb negb].
      apply orb_prop in Hv2 as [Hv2|Hv2]; [rewrite Hv2; reflexivity|]. rewrite (ALW (bv_unsigned x)), Hv2. cbn [orb]. apply orb_true_r. }
  assert (VISEQ : forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
            (forall p, In p gone -> ~ (fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p))) ->
            VIS E cs' model' x = VIS E cs model x).
  { intros x Hx Hnsh. unfold vis. rewrite PM, INMAPS', NOACC, (LAZYOUT x Hx), (ALW (bv_unsigned x)).
    replace (in_rng lo hi (bv_unsigned x)) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [negb]. rewrite !andb_true_r.
    replace (existsb (fun p => (uE E (fst p) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p) + uE E (snd p)))%bool gone) with false.
    2: { symmetry. apply APS.existsb_false_forall. intros p Hp. destruct (GONE p Hp) as (G1 & _).
         match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
    replace (existsb (fun p => (sh_lo A E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E p))%bool gone) with false.
    2: { symmetry. apply APS.existsb_false_forall. intros p Hp. destruct (GONE p Hp) as (_ & _ & _ & G4).
         match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. exact (Hnsh p Hp (G4 _ Ht)). }
    rewrite !orb_false_r. reflexivity. }
  (* [comment removed for export] *)
  assert (MRNONE : forall x : word, MR E cs model FULL x = None -> MR E cs' model' FULL' x = None).
  { intros x Hx. unfold Mr, mrestrict, hid in Hx |- *.
    destruct (argH E x); [reflexivity|]. cbn [orb] in *.
    destruct (VIS E cs' model' x) eqn:Hv'; [|reflexivity]. cbn [negb].
    destruct (VISLE x Hv') as [Hv Hnin]. rewrite Hv in Hx. cbn [negb] in Hx.
    unfold FULL'. rewrite unfill_out by (rewrite Un; lia). exact Hx. }
  assert (MRKEEP : forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
            (forall p, In p gone -> ~ (fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p))) ->
            MR E cs' model' FULL' x = MR E cs model FULL x).
  { intros x Hx Hnsh. unfold Mr, mrestrict, hid. rewrite (VISEQ x Hx Hnsh). unfold FULL'. rewrite unfill_out by (rewrite Un; exact Hx). reflexivity. }
  (* [comment removed for export] *)
  assert (HALLOW_in : forall iv, In iv (ALLOW E cs') <-> In iv (ALLOW E cs)).
  { intros iv. unfold allowA, cs'. cbn [a_vis a_ghost]. subst kept gone. rewrite <- ?app_assoc. apply in_flat_map_split. }
  assert (HALLOW_bytes : A_bytes (ALLOW E cs') = A_bytes (ALLOW E cs)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. subst kept gone. rewrite <- ?app_assoc. apply A_bytes_flat_map_split. }
  assert (DISJF : forall m', In m' (List.filter (fun m0 => negb (amap_match k (reg cs 10) ne m0)) (a_maps cs)) ->
            In m' (a_maps cs) /\ m <> m'
            /\ (is_fog m' = false -> bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m')))).
  { intros m' Hm'. apply filter_In in Hm' as [Hm' Hnm].
    assert (Hne' : m <> m').
    { intros <-. unfold amap_match in Hnm. rewrite Hnf, <- Hb, expr_eqb_refl, Hlen_eq in Hnm. discriminate. }
    split; [exact Hm'|]. split; [exact Hne'|]. intros Hnf'. exact (DISJ' m' Hm' Hnf' Hne'). }
  assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
  { intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xtop Xsp0 Xnasub Xnone Xkinds Xtotsz Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xvmx].
  destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
  assert (HAeq : ALLOW E cs' = flat_map (allow1 A E) (kept ++ gone ++ a_ghost cs)) by reflexivity.
  assert (HTOPEQ : TOP model' = TOP model) by (unfold TOP, alloc_top; rewrite PISP; reflexivity).
  constructor; rewrite ?HAeq; subst cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_next mk_ss];
    try set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _) in *; rewrite ?HTOPEQ.
  - (* [comment removed for export] *) apply regs_ok_set_n'; [exact Xregs | lia | reflexivity].
  - reflexivity.
  - (* [comment removed for export] *) unfold know_ok. apply Forall_forall. intros K HinK.
    destruct (fold_unfill_inv E _ k gone (kn_unfill k bb bk ne) K Xknow
                ltac:(intros K' HK'; unfold kn_unfill in HK'; apply filter_In in HK' as [HK' _]; exact HK') HinK) as [Hin0 Hsh].
    unfold kn_unfill in Hin0. apply filter_In in Hin0 as [Hin0 Hkeep0].
    pose proof (proj1 (Forall_forall _ _) Xknow K Hin0) as HKK.
    destruct (kimg_b K) eqn:HnotImg.
    { destruct K; try discriminate. cbn [kentry_ok] in HKK |- *. destruct HKK as (HA' & HB' & HCC).
      split; [exact HA'|]. split; [exact HB'|]. intros i Hi. apply MRNONE. apply HCC. exact Hi. }
    apply kentry_keep_foot with (M := MR E cs model FULL); [exact HKK | | exact MRNONE].
    intros x Hfx.
    cbn [orb] in Hkeep0. rewrite APS.kentry_apart_bp_eq in Hkeep0.
    pose proof (kentry_apart_b_sem' E _ k K bb bk ne Xknow Hkeep0) as Hap0. rewrite Hest, HelenZ in Hap0.
    destruct Hsh as [Himg|Hsh]; [rewrite Himg in HnotImg; discriminate|].
    unfold kfoot_apart in Hap0, Hsh.
    destruct (kfoot E K) as [[fs fl]|] eqn:Hkf; [|destruct Hfx].
    apply MRKEEP; [subst hi; (first [clear - Hap0 Hfx E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia])|]. intros p Hp Hin. pose proof (Hsh p Hp) as HH. rewrite ?Hkf in HH. cbn [fst snd] in Hin. (first [clear - HH Hin Hfx E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia]).
  - unfold model'. rewrite munmap_model_halted. exact Xhalt.
  - unfold fds_ok in *. exact Xfds.
  - exact Xfs.
  - exact Xtid.
  - exact Xres.
  - exact Xlimit.
  - rewrite PM. exact MAPS'.
  - (* [comment removed for export] *)
    rewrite PM. apply Forall_forall. intros m' Hm' Hk'. destruct (DISJF m' Hm') as (Hm0 & _ & _).
    destruct (proj1 (Forall_forall _ _) Xholes m' Hm0 Hk') as [HF1 HF2]. split; [|exact HF2].
    intros iv Hiv. apply HF1. apply in_app_iff in Hiv as [Hiv|Hiv]; apply in_app_iff; [left; exact Hiv | right].
    unfold map_remove in Hiv. apply filter_In in Hiv as [Hiv _]. exact Hiv.
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. apply seps_filter. exact Xseps.
  - (* [comment removed for export] *) unfold model_ivs_wf. rewrite PM, PN, PL. split; [|split; [|split; [|unfold init_sp_ok in *; rewrite PISP; exact Wsp]]].
    + unfold map_remove. apply ivs_wf_filter. exact W1.
    + apply maps_subtract_wf; [exact W2 | lia].
    + apply maps_subtract_wf; [exact W3 | lia].
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. apply Forall_forall. intros iv Hiv. apply filter_In in Hiv as [Hiv _]. exact (proj1 (Forall_forall _ _) Xbounds iv Hiv).
  - (* [comment removed for export] *) rewrite PL. apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
    pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. (first [clear - Y2 Y1 R2 R1 E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia]).
  - (* [comment removed for export] *) exact Xtop.
  - (* [comment removed for export] *) exact Xsp0.
  - (* [comment removed for export] *) intros z Hz. rewrite PM, INMAPS'. rewrite NOACC in Hz. apply andb_prop in Hz as [Hz1 Hz2]. rewrite (Xnasub z Hz1), Hz2. reflexivity.
  - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct (DISJF m' Hm') as (Hm0 & Hne' & D).
    assert (Hnf' : is_fog m' = false) by (apply KNF; (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])])). specialize (D Hnf').
    rewrite PN. pose proof (proj1 (Forall_forall _ _) Xnone m' Hm0 Hk') as X.
    pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' Xmaps Hm0 Hnf')) as (C1 & _).
    unfold amap_den in *. apply maps_subtract_keeps; [lia | exact C1 | exact X | cbn [fst snd]; subst hi; lia].
  - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk' x Hx. destruct (DISJF m' Hm') as (Hm0 & Hne' & D).
    specialize (D ltac:(apply KNF; (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]))).
    destruct (proj1 (Forall_forall _ _) Xkinds m' Hm0 Hk' x Hx) as [K1 K2].
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x) by lia.
    rewrite NOACC, K1, (LAZYOUT x Hxo), K2. split; reflexivity.
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. rewrite sum_sizes_app. rewrite sum_sizes_app in Xtotsz.
    pose proof (sum_sizes_filter_le (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) as SF.
    change (vm_reserved (m_vmmaps model')) with (vm_reserved (m_vmmaps model)). lia.
  - exact Xbrk.
  - exact Xsbrk.
  - (* [comment removed for export] *) rewrite (eager_used_sem model'), (eager_used_sem model Xwf) in *.
    2: { unfold model_ivs_wf. rewrite PM, PN, PL. split; [unfold map_remove; apply ivs_wf_filter; exact W1|]. split; [apply maps_subtract_wf; try assumption; lia|]. split; [apply maps_subtract_wf; try assumption; lia | unfold init_sp_ok in *; rewrite PISP; exact Wsp]. }
    rewrite PM. unfold map_remove.
    eapply Z.le_trans; [|exact Xeager]. apply sum_count_filter_le.
    intros q Hq Hkeep x Hx. apply negb_true_iff in Hkeep.
    (* [comment removed for export] *)
    assert (Hxo : x < lo \/ hi <= x).
    { assert (Hne' : q <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
      pose proof (DISJl q Hq Hne'). unfold B, S in Hx. lia. }
    f_equal. rewrite !covered_app, PN, PL. rewrite !covered_maps_subtract by (first [exact W2 | exact W3 | lia]).
    replace (in_rng lo hi x) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [negb]. rewrite !andb_true_r. reflexivity.
  - (* [comment removed for export] *) rewrite <- HAeq, HALLOW_bytes. exact Xabytes.
  - (* [comment removed for export] *) rewrite <- HAeq. destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?PT.
    + apply NoDup_filter. exact N1.
    + intros q Hq. apply filter_In in Hq as [Hq _]. exact (N2 q Hq).
    + intros q Hq. apply filter_In in Hq as [Hq _]. pose proof (N3 q Hq) as P3.
      unfold page_allowedb in *. apply existsb_exists in P3 as (iv & Hiv & Hbb). apply existsb_exists. exists iv. split; [apply HALLOW_in; exact Hiv | exact Hbb].
    + intros q Hq. apply filter_In in Hq as [Hq Ho]. pose proof (N4 q Hq) as P4.
      unfold page_outside_range in Ho. apply negb_true_iff in Ho.
      pose proof (N2 q Hq) as Qa. unfold page_size in Qa.
      rewrite PL. rewrite page_in_ranges_subtract_out; [exact P4 | exact W3 | lia | ].
      unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; (first [clear - Qa Ho L4 E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia]).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + rewrite HALLOW_bytes.
      assert (EG : eager_used model' <= eager_used model); [|change (vm_limit (m_vmmaps model')) with (vm_limit (m_vmmaps model)); lia].
      rewrite (eager_used_sem model'), (eager_used_sem model Xwf).
      2: { unfold model_ivs_wf. rewrite PM, PN, PL. split; [unfold map_remove; apply ivs_wf_filter; exact W1|]. split; [apply maps_subtract_wf; try assumption; lia|]. split; [apply maps_subtract_wf; try assumption; lia | unfold init_sp_ok in *; rewrite PISP; exact Wsp]. }
      rewrite PM. unfold map_remove. apply sum_count_filter_le.
      intros q Hq Hkeep x Hx. apply negb_true_iff in Hkeep.
      assert (Hxo : x < lo \/ hi <= x).
      { assert (Hne' : q <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
        pose proof (DISJl q Hq Hne'). unfold B, S in Hx. lia. }
      f_equal. rewrite !covered_app, PN, PL. rewrite !covered_maps_subtract by (first [exact W2 | exact W3 | lia]).
      replace (in_rng lo hi x) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      cbn [negb]. rewrite !andb_true_r. reflexivity.
  - (* [comment removed for export] *) intros x Hh Hmx Hna Hlz Hgh.
    assert (Hgh0 : in_ghost E cs (bv_unsigned x) = false).
    { unfold in_ghost in Hgh |- *. subst cs'. cbn [a_ghost] in Hgh. rewrite existsb_app in Hgh. apply orb_false_iff in Hgh as [_ Hgh]. exact Hgh. }
    rewrite PM, INMAPS' in Hmx. apply andb_prop in Hmx as [Hmx Hxo'].
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x).
    { apply negb_true_iff in Hxo'. unfold in_rng in Hxo'. apply andb_false_iff in Hxo' as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; lia. }
    unfold FULL'. rewrite unfill_out by (rewrite Un; exact Hxo).
    rewrite NOACC in Hna. apply andb_false_iff in Hna as [Hna|Hna]; [| rewrite Hxo' in Hna; discriminate].
    rewrite (LAZYOUT x Hxo) in Hlz.
    (* [comment removed for export] *)
    destruct (HID E cs model x) eqn:Hold; [exact (Xzero x Hold Hmx Hna Hlz Hgh0)|].
    unfold hid in Hh, Hold. destruct (argH E x); [discriminate|]. cbn [orb] in Hh, Hold.
    apply negb_true_iff in Hh. apply negb_false_iff in Hold.
    (* [comment removed for export] *)
    assert (SHX : exists p, In p gone /\ fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p)).
    { destruct (existsb (fun p => (sh_lo A E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E p))%bool gone) eqn:Hex.
      - apply existsb_exists in Hex as (p & Hp & Hpx). exists p. split; [exact Hp|]. destruct (GONE p Hp) as (_ & _ & _ & G4). exact (G4 _ Hpx).
      - exfalso. unfold vis in Hh, Hold. change (TOP model') with (TOP model) in Hh. rewrite PM, INMAPS', NOACC, (LAZYOUT x Hxo) in Hh. rewrite (ALW (bv_unsigned x)), Hex in Hold.
        replace (existsb (fun p0 => (uE E (fst p0) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p0) + uE E (snd p0)))%bool gone) with false in Hold.
        2: { symmetry. apply APS.existsb_false_forall. intros p0 Hq0. destruct (GONE p0 Hq0) as (G1 & _).
             match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
        rewrite Hxo' in Hh. cbn [negb] in Hh. rewrite !andb_true_r in Hh. rewrite !orb_false_r in Hold. rewrite Hh in Hold. discriminate. }
    destruct SHX as (p & Hp & Hpx). destruct (GONE p Hp) as (_ & _ & G3 & _).
    pose proof (G3 x Hpx) as Z0. unfold Mr, mrestrict, hid in Z0. rewrite Hold in Z0.
    destruct (argH E x); [discriminate|]. cbn in Z0. exact Z0.
  - (* [comment removed for export] *) eapply SINV_frame; [|exact Xsinv]. intros x Hx. unfold FULL'. apply unfill_out. pose proof (argH_sp0 _ _ Hx). rewrite Un. subst hi. lia.
  - (* [comment removed for export] *) subst cs'. cbn [a_vmops vm_replay]. destruct (vm_replay E (a_vmops cs)) as [na lz]. cbn [fst snd] in Xvmx |- *. destruct Xvmx as [Xna Xlz].
    rewrite PN, PL, <- Xna, <- Xlz. unfold vm_step, vm_lo, vm_hi. rewrite Hne, HnZw. fold addr. fold lo. rewrite Un. unfold hi. split; reflexivity.
Qed.


Theorem node_sys_sound_YMunmap : sys_stmt SEGS A nx0 LIMIT SINV argH FS0 YMunmap.
Proof. intros cs cs' E R FULL model T HC Hpre Hn HK. eapply node_munmap_sound; eauto. Qed.

End SoundMunmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundSys.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis RES_cover : img_lo A < img_hi A /\ forall z, img_lo A <= z < img_hi A ->
  exists iv, In iv (segments_reserved SEGS) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Hypothesis argH_sp0 : forall E (a : word), argH E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.
Hypothesis E_SP0 : AP.expr_vars_lt nx0 e_sp0_early = true.
Context {SC : StepCfg} {AF : AllocForced SC}.

Theorem node_sys_sound : forall y, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y.
Proof.
  intros [| |].
  - eapply (node_sys_sound_YMunmap SEGS A nx0 LIMIT SINV argH); eauto.
  - eapply (node_sys_sound_YBrk SEGS A nx0 LIMIT SINV argH FS0); eauto.
  - eapply (node_sys_sound_YSetTid SEGS A nx0 LIMIT SINV argH FS0); eauto.
Qed.
End SoundSys.
