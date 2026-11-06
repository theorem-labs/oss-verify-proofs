(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AzSMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3Sound AzSymRun3 AzPlanCore AzPlan AzAPS AzGPS AzSIface.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= PuLia.lia_nd.
#[local] Ltac nia ::= PuLia.znia_nd.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
  (bv_unsigned b < bv_unsigned a + bv_unsigned sz)%Z -> (bv_unsigned a < bv_unsigned b + d + page_size)%Z ->   (* [comment removed for export] *)
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
Variable RR : shape_rel SEGS.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
(* [comment removed for export] *)
Variable ISP : expr.
Hypothesis ISP_vars : expr_vars_lt nx0 ISP = true.
Hypothesis argH_high : forall E (a : word), argH E a = true -> sp_window_lo <= bv_unsigned a /\ bv_unsigned (edenot E ISP) <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis RES_tile : forall z, img_lo A <= z < img_hi A -> in_ivs z (segments_reserved SEGS) = true.
Hypothesis HULL_ne : img_lo A < img_hi A.
Context {fx : FPState}.

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.

(* [comment removed for export] *)
Let kn_grant_filter_ok := AzSMmLib.kn_grant_filter_ok SEGS A RES_len HULL_ok ISP.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH ISP FS0).

(* [comment removed for export] *)
Theorem node_exit_here : SIF.exit_here SEGS RR A LIMIT SINV argH ISP FS0 fx.
Proof.
  intros cs code E R FULL model HC Hec Hn.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  unfold node_exit in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [c0|] eqn:H10.
  2:{ destruct a7; try discriminate; repeat (destruct p; try discriminate). }
  destruct (reg_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 10 c0 HC ltac:(lia) H10) as [G10 Hc0].
  assert (H94 : (a7 = 94 \/ a7 = 93) /\ code = Z.land c0 255).
  { destruct a7 as [|p|p]; try discriminate;
      repeat (destruct p as [p|p|]; try discriminate); injection Hn as <-; auto. }
  destruct H94 as [Ha7 ->].
  assert (G17 : getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94 \/ getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 93).
  { destruct Ha7 as [-> | ->].
    - left. exact (proj1 (reg_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 17 94 HC ltac:(lia) H17)).
    - right. exact (proj1 (reg_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 17 93 HC ltac:(lia) H17)). }
  unfold GPS.cfgF, GPS.mkstF. rewrite <- (bv_and_255 c0 Hc0).
  eapply sr_exit_at_lazy; [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact G10].
Qed.


(* [comment removed for export] *)
Theorem node_sys_here_YSetTid : SIF.sys_here SEGS RR A nx0 LIMIT SINV argH ISP FS0 fx YSetTid.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn Hk.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  cbn [node_sys] in Hn. unfold node_settid in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (negb (a_tidset cs) && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hts Hfresh]. apply negb_true_iff in Hts.
  apply Some_inj in Hn. rename Hn into Ecs'.
  destruct (reg_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 17 96 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_tid _ _ _ _ _ _ _ _ _ _ _ _ HC Hts) as Htid.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  unfold GPS.cfgF, GPS.mkstF.
  eapply (sr_set_tid_lazy SEGS); [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact Htid |].
  intros tid Htidr.
  set (v := nxt cs) in *.
  set (E' := ext1 E v tid).
  assert (Hag : env_agree v E E') by apply (ext1_agree).
  pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
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
  eapply (cs_ok_frame SEGS A LIMIT SINV argH ISP SINV_frame FS0);
    [exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)
    | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity | intros a Ha; exact Ha].
  cbn [mk_ss s_regs]. apply (regs_ok_set_n);
    [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) | lia | symmetry; exact (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC)].
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
  rewrite (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC). auto.
Qed.

(* [comment removed for export] *)
Lemma brk_base_ok_sound : forall E cs R FULL model d,
  cs_ok E cs R FULL model -> brk_base_ok A cs d = true ->
  let b := vm_brk (m_vmmaps model) in
  bv_unsigned b mod 4096 = 0 /\ 0 < bv_unsigned b /\ img_hi A <= bv_unsigned b /\ bv_unsigned b + d <= CEIL.   (* [comment removed for export] *)
Proof.
  intros E cs R FULL model d HC H b. unfold brk_base_ok in H.
  apply andb_prop in H as [Hal H].
  destruct (xlo (kn cs) (a_brk cs)) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) (a_brk cs)) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [H0 Hi].
  apply Z.ltb_lt in H0. apply Z.leb_le in Hi. apply Z.leb_le in Hk.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hlo) as L.
  pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hhi) as Hh.
  pose proof (page_aligned_sound SEGS E _ (kn cs) _ HK Hal) as P.
  rewrite <- (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) in L, Hh, P. unfold b. lia.
Qed.

(* [comment removed for export] *)
Lemma brk_req_val : forall E cs R FULL model d,
  cs_ok E cs R FULL model -> brk_req cs = Some d -> brk_base_ok A cs d = true ->
  getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d).
Proof.
  intros E cs R FULL model d HC Hr Hb.
  destruct (brk_req_sound E cs R FULL model d HC Hr) as (D1 & D2 & D3 & Dm).
  destruct (brk_base_ok_sound E cs R FULL model d HC Hb) as (B1 & B2 & B3 & B4).
  rewrite (reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 10 HC ltac:(lia)).
  pose proof (u64_range (edenot E (reg cs 10))) as Hr10. pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
  apply bv_eq. rewrite u64_lit by (unfold CEIL, KHI in *; lia). unfold two64, CEIL, KHI in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem node_sys_here_YBrk : SIF.sys_here SEGS RR A nx0 LIMIT SINV argH ISP FS0 fx YBrk.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn Hk.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  cbn [node_sys] in Hn. unfold node_brk1 in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (reg_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
  (* [comment removed for export] *)
  assert (POST : forall ok : bool, (if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None) = Some cs' ->
            RR (mkCfg (mkst (regupd R 10 (vm_brk (m_vmmaps model))) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) T).
  { intros ok Hok. destruct ok; [|discriminate]. apply Some_inj in Hok.
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc cs') by (rewrite <- Hok; reflexivity).
    apply (Hk E (regupd R 10 (vm_brk (m_vmmaps model))) FULL model);
      [split; apply env_agree_refl | rewrite <- Hok; apply brk_keep_ok; exact HC | reflexivity]. }
  unfold GPS.cfgF, GPS.mkstF.
  destruct (reg_lit cs 10) as [[|p|p]|] eqn:H10.
  1: { (* [comment removed for export] *)
    destruct (reg_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 10 0 HC ltac:(lia) H10) as [G10 _].
    eapply (sr_brk_query_lazy SEGS); [exact HF | exact HE | exact Hh | exact G17 | exact G10 |].
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
    all: pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm1) as L1;
         pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hm2) as L2;
         cbn [xt_den] in L1, L2; rewrite <- (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) in L1, L2.
    all: pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
    all: eapply (sr_brk_grow_blocked_lazy SEGS); [exact HF | exact HE | exact Hh | exact G17 | exact G10
         | rewrite u64_lit by (unfold CEIL, KHI in *; lia); lia
         | rewrite u64_lit by (unfold CEIL, KHI in *; lia); pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ _ HC); lia
         | rewrite u64_lit by (unfold CEIL, KHI in *; lia); lia
         | | exact POST].
    all: apply (brk_grow_ok_aligned_refuted model d (edenot E (am_base m)) (edenot E (am_len m)));
         [exact B1 | exact D2 | exact D1 | exact B2 | unfold CEIL, KHI, page_size in *; lia | | lia | unfold page_size; lia].
    all: apply in_or_app; right; exact (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hmin Hnf).
Qed.



(* [comment removed for export] *)
Theorem node_brk2_here : SIF.brk2_here SEGS RR A nx0 LIMIT SINV argH ISP FS0 fx.
Proof.
  intros cs csa csb E R FULL model TA TB HC Hec Hn Heq HkA HkB.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
  unfold node_brk2 in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate]. cbv zeta in Hn.
  destruct (split_lit (a_brk cs)) as [bb bk] eqn:Hsplit.
  destruct (brk_grow_possible A LIMIT cs d && AP.expr_vars_lt (nxt cs) (reg cs 10) && flat_x (kn cs) bb bk (ELit d))%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Hposs _].
  set (csB := ACS _ _ _ _ _ _ _ _ _ _ _ _ _ _) in Hn.
  apply Some_pair_inj in Hn as [EcsA EcsB].
  (* [comment removed for export] *)
  destruct (reg_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  unfold brk_grow_possible in Hposs. rewrite Hsplit in Hposs.
  apply andb_prop in Hposs as [Hposs Hbudget]. apply andb_prop in Hposs as [Hbase Hapart]. apply andb_prop in Hbase as [Hbase Hnf].
  unfold budget_ok in Hbudget. apply Z.leb_le in Hbudget.
  destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
  destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
  pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
  pose proof (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hres.
  pose proof (proj1 (APS.maps_match_exact_etok nx0 (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC)) as Hmaps.   (* [comment removed for export] *)
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hlim. pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hsbrk.
  pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hbrk.
  set (h := m_vmmaps model) in *. set (b := vm_brk h) in *.
  pose proof (u64_range b) as Hbr.
  assert (Eb : edenot E (a_brk cs) = b) by (symmetry; exact Hbrk).
  (* [comment removed for export] *)
  assert (HpcB' : pc csb = pc cs + 4) by (rewrite <- EcsB; reflexivity).
  assert (HKf : know_ok SEGS E (Mr A argH E cs model FULL) (kn csB)).
  { unfold csB, kn. cbn [a_ss mk_ss s_know]. rewrite kn_grant_filter_unf. unfold kimg_clip.   (* [comment removed for export] *)
    apply know_ok_filter. apply know_ok_filter. exact HK. }
  destruct (flat_x_sound SEGS E _ (kn cs) bb bk (ELit d) HK Hflat) as (Fb1 & Fb2 & Fb3).
  cbn [edenot] in Fb2, Fb3. rewrite (u64_lit d) in Fb2, Fb3 by (unfold CEIL, KHI in *; lia).
  assert (Hest : estart E (SA bb bk) = bv_unsigned b).
  { rewrite <- Eb. symmetry. apply (u_of_split E (a_brk cs) bb bk Hsplit). lia. }
  (* [comment removed for export] *)
  assert (APARTG : forall m, In m (a_maps cs) ->
            bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
            \/ bv_unsigned b + (d + 4096) <= bv_unsigned (edenot E (am_base m))).  (* [comment removed for export] *)
  { intros m Hin. pose proof (proj1 (forallb_forall _ _) Hapart m Hin) as Hm. cbv beta in Hm.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hm) as Hd.
    rewrite Hest in Hd. rewrite (elenZ_lit E (d + 4096)) in Hd by (unfold CEIL, KHI in *; lia).
    unfold estart, elenZ in Hd. cbn [a_base a_off] in Hd. lia. }
  assert (APART : forall m, In m (a_maps cs) ->
            bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
            \/ bv_unsigned b + d <= bv_unsigned (edenot E (am_base m))).
  { intros m Hin. destruct (APARTG m Hin) as [Hm|Hm]; [left; exact Hm | right; lia]. }
  assert (APARTM : AzSMmLib.maps_apart E (a_maps cs) (bv_unsigned b) d).
  { intros m Hin _. destruct (APART m Hin); lia. }
  (* [comment removed for export] *)
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as HISP. pose proof (co_ispok _ _ _ _ _ _ _ _ _ _ _ _ HC) as [HISPOK0 _].
  pose proof HISPOK0 as HISPOK. unfold init_sp_ok in HISPOK. fold h in HISP, HISPOK, HISPOK0. rewrite HISP in HISPOK.
  assert (HbISP : bv_unsigned b + d <= bv_unsigned (edenot E ISP) - STACK_MAX) by (unfold STACK_MAX, CEIL, sp_window_lo in *; lia).
  assert (HbTOP : bv_unsigned b + d <= alloc_top h) by (unfold alloc_top, stack_max_size; rewrite HISP; unfold STACK_MAX in HbISP; lia).
  (* [comment removed for export] *)
  set (dw := Z_to_bv 64 d). assert (Udw : bv_unsigned dw = d) by (unfold dw; apply u64_lit; unfold CEIL, KHI in *; lia).
  assert (Hrf : region_free (vm_reserved h ++ vm_maps h) b dw = true).
  { apply region_free_intro. intros a sz Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin.
      pose proof (proj1 (Forall_forall _ _) RES_hull _ Hin) as [R1 R2]. cbn [fst snd] in R1, R2.
      unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge. lia.
    - rewrite Hmaps in Hin. apply in_map_iff in Hin as (m & Em & Hin). apply filter_In in Hin as [Hin _].
      unfold amap_den in Em. injection Em as <- <-.
      unfold iv_overlap. rewrite Udw. apply andb_false_iff.
      destruct (APART m Hin) as [Hm|Hm]; [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; lia]. }
  (* [comment removed for export] *)
  set (dwg := Z_to_bv 64 (d + page_size)).
  assert (Udwg : bv_unsigned dwg = d + page_size) by (unfold dwg; apply u64_lit; unfold CEIL, KHI, page_size in *; lia).
  assert (Hrfg : region_free (vm_reserved h ++ vm_maps h) b dwg = true).
  { apply region_free_intro. intros a sz Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite Hres in Hin.
      pose proof (proj1 (Forall_forall _ _) RES_hull _ Hin) as [R1 R2]. cbn [fst snd] in R1, R2.
      unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge. lia.
    - rewrite Hmaps in Hin. apply in_map_iff in Hin as (m & Em & Hin). apply filter_In in Hin as [Hin _].
      unfold amap_den in Em. injection Em as <- <-.
      unfold iv_overlap. rewrite Udwg. apply andb_false_iff.
      destruct (APARTG m Hin) as [Hm|Hm]; [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; unfold page_size in *; lia]. }
  pose proof (APS.A_wf_allowA A E cs) as HAwf.
  assert (Hused : vm_backing_used model <= a_eager cs + a_abytes cs).
  { pose proof (vm_backing_used_le _ _ HAwf (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)).
    pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC). lia. }
  assert (Hadm : Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true).
  { apply (brk_grow_ok_aligned_intro model d); fold h b;
      [exact B1 | exact D2 | exact D1 | exact B2 | rewrite alloc_ceiling_val; unfold CEIL, KHI in *; lia
      | exact HISPOK0 | exact Hrfg |].
    lia. }
  unfold GPS.cfgF, GPS.mkstF.
  eapply (sr_brk_grow_lazy SEGS RR R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w d TA TB HF HE Hh G17);
    fold h b; [exact B1 | exact D2 | exact D1 | exact B2 | unfold CEIL, KHI in *; lia
    | lia | exact G10 | exact Hadm | exact (fun tr Ht => proj1 (Heq tr) Ht) | |].
  - (* [comment removed for export] *)
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csa) by (rewrite <- EcsA; reflexivity).
    apply (HkA E (regupd R 10 b) FULL model);
      [split; apply env_agree_refl | rewrite <- EcsA; apply (brk_keep_ok); exact HC | reflexivity].
  - (* [comment removed for export] *)
    set (req := Z_to_bv 64 (bv_unsigned b + d)) in *. fold dw.
    assert (Ureq : bv_unsigned req = bv_unsigned b + d) by (unfold req; apply u64_lit; unfold CEIL, KHI in *; lia).
    set (h' := mkVmMapsFull (vm_reserved h) ((b, dw) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
    set (model' := with_vmmaps h' model). set (FULL' := zfill b dw FULL). set (R' := regupd R 10 req).
    assert (Hvm' : m_vmmaps model' = h') by reflexivity.
    assert (Hlz' : m_vm_lazy model' = m_vm_lazy model) by reflexivity.
    (* [comment removed for export] *)
    assert (V1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
                 vis A E csB model' x = vis A E cs model x).
    { intros x Hx. unfold vis. rewrite Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw.
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
      pose proof (co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC (bv_unsigned x) Hna) as Hm. fold h in Hm. rewrite Hmaps in Hm.
      apply (in_ivs_true) in Hm as (iv & Hin & Hiv).
      apply in_map_iff in Hin as (m & <- & Hin). apply filter_In in Hin as [Hin _]. unfold amap_den in Hiv. cbn [fst snd] in Hiv.
      destruct (APART m Hin); lia. }
    (* [comment removed for export] *)
    assert (LZ0 : forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d ->
                  page_in_ranges (page_base x) (m_vm_lazy model) = false).
    { intros x Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:Hl; [|reflexivity]. exfalso.
      destruct (co_lazysub _ _ _ _ _ _ _ _ _ _ _ _ HC x Hl) as (m0 & Hm0 & Hlh & Hr0). unfold amap_den in Hr0. cbn [fst snd] in Hr0.
      destruct (APART m0 Hm0); lia. }
    assert (Wf : ivs_wf (vm_maps h)) by exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)).
    assert (Wb : iv_wf (b, dw)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite Udw; unfold CEIL, KHI in *; lia).
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csb) by (rewrite HpcB'; reflexivity).
    apply (HkB E R' FULL' model'); [split; apply env_agree_refl | | reflexivity].
    rewrite <- EcsB. apply (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0 E csB R' FULL' model').
    + (* [comment removed for export] *)
      subst b. subst h.
      destruct HC; constructor; unfold csB;
        cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next];
        fold csB; try assumption; try reflexivity.
      all: try (change (m_halted model') with (m_halted model); assumption).
      all: lazymatch goal with
      | |- regs_ok _ _ _ =>
          apply regs_ok_regupd_same; [exact co_regs0 | exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate]
      | |- know_ok _ _ _ _ =>
          apply (kn_grant_filter_ok E (Mr A argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned (vm_brk (m_vmmaps model))) d HK);
          [exact APARTM | right; exact B3 | exact HbISP | exact M1]
      | |- maps_match _ _ (vm_maps _) =>
          rewrite Hvm'; unfold h'; cbn [vm_maps maps_match is_etok is_fog am_kind mkind_eqb];
          exists (vm_maps (m_vmmaps model)); split; [|exact co_maps0];
          unfold amap_den; cbn [am_base am_len edenot]; rewrite Eb; fold dw; reflexivity
      | |- seps _ =>
          rewrite Hvm'; unfold h'; cbn [vm_maps]; constructor; [|exact co_seps0];
          rewrite Hmaps; apply Forall_forall; intros iv Hin; apply in_map_iff in Hin as (m & <- & Hin); apply filter_In in Hin as [Hin _];
          unfold iv_disjoint, amap_den; cbn [fst snd]; rewrite Udw; destruct (APART m Hin); lia
      | |- model_ivs_wf _ =>
          apply model_ivs_wf_with_vmmaps; [exact co_wf0 | apply ivs_wf_cons; [exact Wb | exact Wf] | exact (proj1 (proj2 co_wf0)) | reflexivity]  (* [comment removed for export] *)
      | |- Forall _ (vm_maps _) =>      (* [comment removed for export] *)
          rewrite Hvm'; unfold h'; cbn [vm_maps];
          change (alloc_top (mkVmMapsFull (vm_reserved (m_vmmaps model)) ((vm_brk (m_vmmaps model), dw) :: vm_maps (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
                    (vm_start_brk (m_vmmaps model)) req (vm_limit (m_vmmaps model)) (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model))))
            with (alloc_top (m_vmmaps model));
          constructor; [|exact co_bounds0];
          cbn [fst snd]; rewrite Udw; unfold CEIL, KHI in *; repeat split; lia
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
      | |- Forall (fun m0 : amap => is_etok m0 = true -> _) (_ :: _) =>      (* [comment removed for export] *)
          constructor; [intros Hk; discriminate|];
          apply Forall_forall; intros m0 Hm0 Hk0;
          destruct (proj1 (Forall_forall _ _) co_etok0 m0 Hm0 Hk0) as (T1 & T2 & T3); split; [exact T1|]; split; [exact T2|];
          intros x Hx; destruct (T3 x Hx) as [T4 T5]; split;
          [ rewrite Hvm'; unfold h'; cbn [vm_maps]; rewrite in_ivs_cons, T4; apply orb_true_r
          | change (m_vm_lazy model') with (m_vm_lazy model); exact T5 ]
      | |- Forall _ (_ :: _) =>
          constructor; [first [intros Hk; discriminate | intros [Hk|Hk]; discriminate] | assumption]
      | |- sum_sizes _ <= _ =>
          rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps]; rewrite sum_sizes_app in *; cbn [sum_sizes snd]; rewrite Udw;
          cbn [sum_sizes] in co_totsz0; lia
      | |- exists Y, _ =>
          destruct co_split0 as [Y (Y1 & Y2 & Y3 & Y4)]; exists Y; rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps vm_mmap_base];
          split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|];
          intros b' s' Hin; apply in_app_iff in Hin as [Hin|[Hin|Hin]];
          [ apply Y4; apply in_app_iff; left; exact Hin
          | injection Hin as <- <-; left; rewrite Udw; unfold kHighMemBeg; unfold CEIL, KHI in *; lia
          | apply Y4; apply in_app_iff; right; exact Hin ]
      | |- vm_brk _ = _ =>
          rewrite Hvm'; unfold h'; cbn [vm_brk];
          rewrite <- (reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 10 ltac:(constructor; assumption) ltac:(lia)); symmetry; exact G10
      | |- bv_unsigned (vm_start_brk _) <= _ =>
          rewrite Hvm'; unfold h'; cbn [vm_start_brk vm_brk]; rewrite Ureq; lia
      | |- eager_used _ <= _ =>
          pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He; lia
      | |- MInv _ _ =>
          eapply MInv_transport; [exact co_minv0 | reflexivity | reflexivity |];
          pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He;
          rewrite Hvm'; unfold h'; cbn [vm_limit];
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
          eapply SINV_frame; [|exact co_sinv0]; intros a Ha; apply F1; pose proof (argH_high _ _ Ha); unfold CEIL, KHI, sp_window_lo in *; lia
      | |- forall a, in_ivs (bv_unsigned a) _ = true -> in_ivs (bv_unsigned a) _ = false -> _ =>      (* [comment removed for export] *)
          intros a Hm Hna;
          rewrite Hvm' in Hm; unfold h' in Hm; cbn [vm_maps] in Hm; rewrite in_ivs_cons, Udw in Hm;
          rewrite Hvm' in Hna; unfold h' in Hna; cbn [vm_noaccess] in Hna;
          destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)))) as [Hlt|Hge];
          [|destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)) + d)) as [Hlt2|Hge2]];
          [ rewrite (F1 a ltac:(lia)); apply (co_mdef0 a); [|exact Hna];
            apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [Hm _]; apply Z.leb_le in Hm; cbn [fst] in Hm; lia
          | unfold FULL'; rewrite zfill_in by (rewrite Udw; lia); discriminate
          | rewrite (F1 a ltac:(lia)); apply (co_mdef0 a); [|exact Hna];
            apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [_ Hm]; apply Z.ltb_lt in Hm; cbn [fst snd] in Hm; lia ]
      | |- forall a, page_in_ranges _ _ = true -> _ =>      (* [comment removed for export] *)
          intros a Hlz; change (m_vm_lazy model') with (m_vm_lazy model) in Hlz;
          destruct (co_lazysub0 a Hlz) as (m0 & Hin0 & Hk0 & Hr0); exists m0; split; [right; exact Hin0 | split; [exact Hk0 | exact Hr0]]
      | |- ?g => idtac "UNSOLVED FIELD:" g
      end.
    + (* [comment removed for export] *)
      assert (INB : forall i, 0 <= i < d ->
                Mr A argH E csB model' FULL' (Z_to_bv 64 (bv_unsigned b + i)) = Some (Z_to_bv 8 0)).
      { intros i Hi. set (a := Z_to_bv 64 (bv_unsigned b + i)).
        assert (Ua : bv_unsigned a = bv_unsigned b + i) by (unfold a; apply u64_lit; unfold CEIL, KHI in *; lia).
        assert (Hargh : argH E a = false).
        { destruct (argH E a) eqn:Ha; [|reflexivity]. pose proof (argH_high _ _ Ha). unfold CEIL, KHI, sp_window_lo in *. lia. }
        assert (Hvis : vis A E csB model' a = true).
        { unfold vis. rewrite Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw.
          rewrite (NA a) by lia. rewrite (LZ0 a) by lia. rewrite Ua.
          replace (bv_unsigned b <=? bv_unsigned b + i) with true by (symmetry; apply Z.leb_le; lia).
          replace (bv_unsigned b + i <? bv_unsigned b + d) with true by (symmetry; apply Z.ltb_lt; lia).
          cbn [andb orb negb]. rewrite !orb_true_r. reflexivity. }
        unfold Mr, mrestrict, hid. rewrite Hargh, Hvis. cbn [negb orb]. unfold FULL'. apply zfill_in. rewrite Udw, Ua. lia. }
      assert (Hfl : flat E (SA bb bk) (elenZ E (ELit d))).
      { unfold flat. rewrite (elenZ_lit E d) by (unfold CEIL, KHI in *; lia). rewrite Hest. unfold CEIL, KHI in *. lia. }
      constructor; [|constructor].
      * (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros off m Hoff Hm.
        rewrite (elenZ_lit E d) in Hm by (unfold CEIL, KHI in *; lia). rewrite Hest.
        destruct m as [|m']; [reflexivity|].
        apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL, KHI in *; lia); unfold CEIL, KHI in *; lia|].
        intros x Hx. rewrite u64_lit in Hx by (unfold CEIL, KHI in *; lia).
        unfold wview. replace x with (Z_to_bv 64 (bv_unsigned b + (bv_unsigned x - bv_unsigned b)))
          by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); unfold CEIL, KHI in *; lia).
        rewrite (INB (bv_unsigned x - bv_unsigned b)) by lia. discriminate.
      * (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros i Hi.
        rewrite (elenZ_lit E d) in Hi by (unfold CEIL, KHI in *; lia). rewrite Hest. apply INB. exact Hi.
      * (* [comment removed for export] *)
        unfold csB, kn. cbn [a_ss mk_ss s_know].
        apply (kn_grant_filter_ok E (Mr A argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned b) d HK);
          [exact APARTM | right; exact B3 | exact HbISP | exact M1].
Qed.


(* [comment removed for export] *)
Theorem node_brk2x_here : SIF.brk2x_here SEGS RR A nx0 LIMIT SINV argH ISP FS0 fx.
Proof.
  intros cs csa csb E R FULL model T HC Hec Hn HT HkA HkB.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
  unfold node_brk2x in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate]. cbv zeta in Hn.
  destruct (split_lit (a_brk cs)) as [bb bk] eqn:Hsplit.
  lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Hbudget]. apply andb_prop in Hc as [Hbase Hnf].
  set (csB := ACS _ _ _ _ _ _ _ _ _ _ _ _ _ _) in Hn.
  apply Some_pair_inj in Hn as [EcsA EcsB].
  (* [comment removed for export] *)
  destruct (reg_lit_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  unfold budget_ok in Hbudget. apply Z.leb_le in Hbudget.
  destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
  destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
  pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
  pose proof (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hres.
  pose proof (proj1 (APS.maps_match_exact_etok nx0 (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC)) as Hmaps.   (* [comment removed for export] *)
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hlim. pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hsbrk.
  pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hbrk.
  set (h := m_vmmaps model) in *. set (b := vm_brk h) in *.
  pose proof (u64_range b) as Hbr.
  assert (Eb : edenot E (a_brk cs) = b) by (symmetry; exact Hbrk).
  (* [comment removed for export] *)
  assert (HpcB' : pc csb = pc cs + 4) by (rewrite <- EcsB; reflexivity).
  (* [comment removed for export] *)
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as HISP. pose proof (co_ispok _ _ _ _ _ _ _ _ _ _ _ _ HC) as [HISPOK0 _].
  pose proof HISPOK0 as HISPOK. unfold init_sp_ok in HISPOK. fold h in HISP, HISPOK, HISPOK0. rewrite HISP in HISPOK.
  assert (HbISP : bv_unsigned b + d <= bv_unsigned (edenot E ISP) - STACK_MAX) by (unfold STACK_MAX, CEIL, sp_window_lo in *; lia).
  assert (HbTOP : bv_unsigned b + d <= alloc_top h) by (unfold alloc_top, stack_max_size; rewrite HISP; unfold STACK_MAX in HbISP; lia).
  set (dw := Z_to_bv 64 d). assert (Udw : bv_unsigned dw = d) by (unfold dw; apply u64_lit; unfold CEIL, KHI in *; lia).
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Ureq : bv_unsigned req = bv_unsigned b + d) by (unfold req; apply u64_lit; unfold CEIL, KHI in *; lia).
  unfold GPS.cfgF, GPS.mkstF.
  (* [comment removed for export] *)
  destruct (Mmap.brk_grow_ok model req req) eqn:Hadm.
  2:{ (* [comment removed for export] *)
      eapply (sr_brk_grow_blocked_lazy SEGS RR R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w req T HF HE Hh G17);
        fold h b; [exact G10 | rewrite Ureq; lia | rewrite Ureq; lia | rewrite Ureq; lia | exact Hadm |].
      rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
      replace (pc cs + 4) with (pc csa) by (rewrite <- EcsA; reflexivity).
      apply (HkA E (regupd R 10 b) FULL model);
        [split; apply env_agree_refl | rewrite <- EcsA; apply (brk_keep_ok); exact HC | reflexivity]. }
  (* [comment removed for export] *)
  assert (APARTV : forall a sz, In (a, sz) (vm_reserved h ++ vm_maps h) ->
            bv_unsigned a + bv_unsigned sz <= bv_unsigned b \/ bv_unsigned b + (d + 4096) <= bv_unsigned a).
  { assert (NW : bv_unsigned b + d + page_size < 2 ^ 64) by (unfold CEIL, KHI, page_size in *; lia).
    intros a sz Hin.
    destruct (Z_lt_le_dec (bv_unsigned b) (bv_unsigned a + bv_unsigned sz)) as [H1|H1]; [|left; lia].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned b + d + page_size)) as [H2|H2]; [|right; unfold page_size in H2; lia].
    exfalso. pose proof (brk_grow_ok_aligned_refuted model d a sz B1 D2 D1 B2 NW Hin H1 H2) as X.
    fold h b in X. unfold req in Hadm. rewrite X in Hadm. discriminate Hadm. }
  assert (ETF : forall m, is_etok m = true -> is_fog m = true).
  { intros m0 H0. unfold is_etok, is_fog, is_tok_kind in *. destruct (am_kind m0); cbn in *; congruence. }
  assert (APART : forall m, In m (a_maps cs) -> is_etok m = false ->
            bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
            \/ bv_unsigned b + d <= bv_unsigned (edenot E (am_base m))).
  { intros m Hin Hne. destruct (APARTV (edenot E (am_base m)) (edenot E (am_len m))) as [X|X]; [|left; exact X|right; lia].
    apply in_app_iff. right. rewrite Hmaps. apply in_map_iff. exists m. split; [reflexivity|]. apply filter_In. split; [exact Hin | rewrite Hne; reflexivity]. }
  assert (APARTG : forall m, In m (a_maps cs) -> is_etok m = false ->
            bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
            \/ bv_unsigned b + (d + 4096) <= bv_unsigned (edenot E (am_base m))).
  { intros m Hin Hne. apply (APARTV (edenot E (am_base m)) (edenot E (am_len m))).
    apply in_app_iff. right. rewrite Hmaps. apply in_map_iff. exists m. split; [reflexivity|]. apply filter_In. split; [exact Hin | rewrite Hne; reflexivity]. }
  assert (APARTM : AzSMmLib.maps_apart E (a_maps cs) (bv_unsigned b) d).
  { intros m Hin Hfog. destruct (APART m Hin ltac:(destruct (is_etok m) eqn:He; [rewrite (ETF m He) in Hfog; discriminate | reflexivity])); lia. }
  assert (APARTMG : AzSMmLib.maps_apart E (a_maps cs) (bv_unsigned b) (d + 4096)).
  { intros m Hin Hfog. destruct (APARTG m Hin ltac:(destruct (is_etok m) eqn:He; [rewrite (ETF m He) in Hfog; discriminate | reflexivity])); lia. }
  assert (HOLE0 : forall m0, In m0 (a_maps cs) -> is_hole m0 = true -> False).
  { intros m0 Hm0 Hk0. pose proof (proj1 (forallb_forall _ _) Hnf m0 Hm0) as X. cbv beta in X.
    unfold is_hole, is_etok, is_fog, is_tok_kind in *. destruct (am_kind m0); cbn in *; congruence. }
  (* [comment removed for export] *)
  assert (KD : forall MM, know_ok SEGS E MM (kdisj_all (a_maps cs) (a_brk cs) (ELit (d + 4096)))).
  { intros MM. unfold kdisj_all. apply Forall_app. split.
    - apply Forall_flat_map. apply Forall_forall. intros m Hm.
      destruct (is_fog m) eqn:Hfm; [apply Forall_nil|].
      pose proof (APARTMG m Hm Hfm) as DJ.
      apply Forall_cons; [|apply Forall_nil].
      cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite Eb, edenot_lit. rewrite (u64_lit (d + 4096)) by (unfold CEIL, KHI in *; lia). lia.
    - unfold kdisj_bands. apply Forall_flat_map.
      pose proof (lit_bands_apart SEGS A RES_len HULL_ok E (a_maps cs) (bv_unsigned b) (d + 4096) ltac:(lia) APARTMG) as LB.
      apply Forall_forall. intros [[lo hi] c] Ht. pose proof (proj1 (Forall_forall _ _) LB _ Ht) as DJ. cbn beta iota in DJ.
      match goal with |- Forall _ (if ?bb then _ else _) => destruct bb eqn:Hcnd end; [|apply Forall_nil].
      apply andb_prop in Hcnd as [Hcnd Hc3]. apply andb_prop in Hcnd as [Hcnd Hc2]. apply andb_prop in Hcnd as [_ Hc1].
      apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. apply Z.ltb_lt in Hc3. unfold two64 in Hc3.
      apply Forall_cons; [|apply Forall_nil].
      cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite Eb, !edenot_lit. rewrite !u64_lit by (unfold CEIL, KHI in *; lia). lia. }
  assert (HKf : know_ok SEGS E (Mr A argH E cs model FULL) (kn csB)).
  { unfold csB, kn. cbn [a_ss mk_ss s_know]. apply Forall_app. split; [apply KD|]. rewrite kn_grant_filter_unf. unfold kimg_clip.   (* [comment removed for export] *)
    apply know_ok_filter. apply know_ok_filter. exact HK. }
  destruct (flat_x_sound SEGS E _ (kn cs) bb bk (ELit d) HK Hflat) as (Fb1 & Fb2 & Fb3).
  cbn [edenot] in Fb2, Fb3. rewrite (u64_lit d) in Fb2, Fb3 by (unfold CEIL, KHI in *; lia).
  assert (Hest : estart E (SA bb bk) = bv_unsigned b).
  { rewrite <- Eb. symmetry. apply (u_of_split E (a_brk cs) bb bk Hsplit). lia. }
  (* [comment removed for export] *)
  assert (Hrf : region_free (vm_reserved h ++ vm_maps h) b dw = true).
  { apply region_free_intro. intros a sz Hin. unfold iv_overlap. rewrite Udw. apply andb_false_iff.
    destruct (APARTV a sz Hin) as [Hm|Hm]; [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; lia]. }
  pose proof (APS.A_wf_allowA A E cs) as HAwf.
  assert (Hused : vm_backing_used model <= a_eager cs + a_abytes cs).
  { pose proof (vm_backing_used_le _ _ HAwf (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)).
    pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC). lia. }
  (* [comment removed for export] *)
  apply (sr_conseq _ RR _ (t_alt2 T T)); [| intros tr; unfold t_alt2; tauto].
  eapply (sr_brk_grow_lazy SEGS RR R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w d T T HF HE Hh G17);
    fold h b; [exact B1 | exact D2 | exact D1 | exact B2 | unfold CEIL, KHI in *; lia
    | lia | exact G10 | exact Hadm | exact (fun tr Ht => Ht) | |].
  - (* [comment removed for export] *)
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csa) by (rewrite <- EcsA; reflexivity).
    apply (HkA E (regupd R 10 b) FULL model);
      [split; apply env_agree_refl | rewrite <- EcsA; apply (brk_keep_ok); exact HC | reflexivity].
  - (* [comment removed for export] *)
    fold dw. fold req.
    set (h' := mkVmMapsFull (vm_reserved h) ((b, dw) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
    set (model' := with_vmmaps h' model). set (FULL' := zfill b dw FULL). set (R' := regupd R 10 req).
    assert (Hvm' : m_vmmaps model' = h') by reflexivity.
    assert (Hlz' : m_vm_lazy model' = m_vm_lazy model) by reflexivity.
    (* [comment removed for export] *)
    assert (V1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
                 vis A E csB model' x = vis A E cs model x).
    { intros x Hx. unfold vis. rewrite Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw.
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
      pose proof (co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC (bv_unsigned x) Hna) as Hm. fold h in Hm. rewrite Hmaps in Hm.
      apply (in_ivs_true) in Hm as (iv & Hin & Hiv).
      destruct iv as [ia isz]. cbn [fst snd] in Hiv.
      destruct (APARTV ia isz ltac:(apply in_app_iff; right; rewrite Hmaps; exact Hin)); lia. }
    (* [comment removed for export] *)
    assert (LZ0 : forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d ->
                  page_in_ranges (page_base x) (m_vm_lazy model) = false).
    { intros x Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:Hl; [|reflexivity]. exfalso.
      destruct (co_lazysub _ _ _ _ _ _ _ _ _ _ _ _ HC x Hl) as (m0 & Hm0 & Hlh & Hr0). unfold amap_den in Hr0. cbn [fst snd] in Hr0.
      assert (He0 : is_etok m0 = false) by (unfold lazy_host in Hlh; unfold is_etok; destruct (am_kind m0); cbn in *; congruence).
      destruct (APART m0 Hm0 He0); lia. }
    assert (Wf : ivs_wf (vm_maps h)) by exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)).
    assert (Wb : iv_wf (b, dw)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite Udw; unfold CEIL, KHI in *; lia).
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csb) by (rewrite HpcB'; reflexivity).
    apply (HkB E R' FULL' model'); [split; apply env_agree_refl | | reflexivity].
    rewrite <- EcsB. apply (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0 E csB R' FULL' model').
    + (* [comment removed for export] *)
      subst b. subst h.
      destruct HC; constructor; unfold csB;
        cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next];
        fold csB; try assumption; try reflexivity.
      all: try (change (m_halted model') with (m_halted model); assumption).
      all: lazymatch goal with
      | |- regs_ok _ _ _ =>
          apply regs_ok_regupd_same; [exact co_regs0 | exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate]
      | |- know_ok _ _ _ _ =>
          apply Forall_app; split; [apply KD|];
          apply (kn_grant_filter_ok E (Mr A argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned (vm_brk (m_vmmaps model))) d HK);
          [exact APARTM | right; exact B3 | exact HbISP | exact M1]
      | |- maps_match _ _ (vm_maps _) =>
          rewrite Hvm'; unfold h'; cbn [vm_maps maps_match is_etok is_fog am_kind mkind_eqb];
          exists (vm_maps (m_vmmaps model)); split; [|exact co_maps0];
          unfold amap_den; cbn [am_base am_len edenot]; rewrite Eb; fold dw; reflexivity
      | |- seps _ =>
          rewrite Hvm'; unfold h'; cbn [vm_maps]; constructor; [|exact co_seps0];
          apply Forall_forall; intros [ia isz] Hin;
          unfold iv_disjoint; cbn [fst snd]; rewrite Udw; destruct (APARTV ia isz ltac:(apply in_app_iff; right; exact Hin)); lia
      | |- model_ivs_wf _ =>
          apply model_ivs_wf_with_vmmaps; [exact co_wf0 | apply ivs_wf_cons; [exact Wb | exact Wf] | exact (proj1 (proj2 co_wf0)) | reflexivity]  (* [comment removed for export] *)
      | |- Forall _ (vm_maps _) =>      (* [comment removed for export] *)
          rewrite Hvm'; unfold h'; cbn [vm_maps];
          change (alloc_top (mkVmMapsFull (vm_reserved (m_vmmaps model)) ((vm_brk (m_vmmaps model), dw) :: vm_maps (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
                    (vm_start_brk (m_vmmaps model)) req (vm_limit (m_vmmaps model)) (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model))))
            with (alloc_top (m_vmmaps model));
          constructor; [|exact co_bounds0];
          cbn [fst snd]; rewrite Udw; unfold CEIL, KHI in *; repeat split; lia
      | |- forall z, in_ivs z _ = true -> _ =>
          intros z Hz; rewrite Hvm'; unfold h'; cbn [vm_maps]; rewrite in_ivs_cons;
          rewrite (co_nasub0 z Hz); apply orb_true_r
      | |- Forall (hole_ok _ _ _) (_ :: _) =>      (* [comment removed for export] *)
          constructor; [intros Hk; discriminate|];
          rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps];
          apply Forall_forall; intros m0 Hm0 Hk0;
          exfalso; exact (HOLE0 m0 Hm0 Hk0)
      | |- Forall (fun m0 : amap => is_etok m0 = true -> _) (_ :: _) =>      (* [comment removed for export] *)
          constructor; [intros Hk; discriminate|];
          apply Forall_forall; intros m0 Hm0 Hk0;
          destruct (proj1 (Forall_forall _ _) co_etok0 m0 Hm0 Hk0) as (T1 & T2 & T3); split; [exact T1|]; split; [exact T2|];
          intros x Hx; destruct (T3 x Hx) as [T4 T5]; split;
          [ rewrite Hvm'; unfold h'; cbn [vm_maps]; rewrite in_ivs_cons, T4; apply orb_true_r
          | change (m_vm_lazy model') with (m_vm_lazy model); exact T5 ]
      | |- Forall _ (_ :: _) =>
          constructor; [first [intros Hk; discriminate | intros [Hk|Hk]; discriminate] | assumption]
      | |- sum_sizes _ <= _ =>
          rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps]; rewrite sum_sizes_app in *; cbn [sum_sizes snd]; rewrite Udw;
          cbn [sum_sizes] in co_totsz0; lia
      | |- exists Y, _ =>
          destruct co_split0 as [Y (Y1 & Y2 & Y3 & Y4)]; exists Y; rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps vm_mmap_base];
          split; [exact Y1|]; split; [exact Y2|]; split; [exact Y3|];
          intros b' s' Hin; apply in_app_iff in Hin as [Hin|[Hin|Hin]];
          [ apply Y4; apply in_app_iff; left; exact Hin
          | injection Hin as <- <-; left; rewrite Udw; unfold kHighMemBeg; unfold CEIL, KHI in *; lia
          | apply Y4; apply in_app_iff; right; exact Hin ]
      | |- vm_brk _ = _ =>
          rewrite Hvm'; unfold h'; cbn [vm_brk];
          rewrite <- (reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 10 ltac:(constructor; assumption) ltac:(lia)); symmetry; exact G10
      | |- bv_unsigned (vm_start_brk _) <= _ =>
          rewrite Hvm'; unfold h'; cbn [vm_start_brk vm_brk]; rewrite Ureq; lia
      | |- eager_used _ <= _ =>
          pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He; lia
      | |- MInv _ _ =>
          eapply MInv_transport; [exact co_minv0 | reflexivity | reflexivity |];
          pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He;
          rewrite Hvm'; unfold h'; cbn [vm_limit];
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
          eapply SINV_frame; [|exact co_sinv0]; intros a Ha; apply F1; pose proof (argH_high _ _ Ha); unfold CEIL, KHI, sp_window_lo in *; lia
      | |- forall a, in_ivs (bv_unsigned a) _ = true -> in_ivs (bv_unsigned a) _ = false -> _ =>      (* [comment removed for export] *)
          intros a Hm Hna;
          rewrite Hvm' in Hm; unfold h' in Hm; cbn [vm_maps] in Hm; rewrite in_ivs_cons, Udw in Hm;
          rewrite Hvm' in Hna; unfold h' in Hna; cbn [vm_noaccess] in Hna;
          destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)))) as [Hlt|Hge];
          [|destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)) + d)) as [Hlt2|Hge2]];
          [ rewrite (F1 a ltac:(lia)); apply (co_mdef0 a); [|exact Hna];
            apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [Hm _]; apply Z.leb_le in Hm; cbn [fst] in Hm; lia
          | unfold FULL'; rewrite zfill_in by (rewrite Udw; lia); discriminate
          | rewrite (F1 a ltac:(lia)); apply (co_mdef0 a); [|exact Hna];
            apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [_ Hm]; apply Z.ltb_lt in Hm; cbn [fst snd] in Hm; lia ]
      | |- forall a, page_in_ranges _ _ = true -> _ =>      (* [comment removed for export] *)
          intros a Hlz; change (m_vm_lazy model') with (m_vm_lazy model) in Hlz;
          destruct (co_lazysub0 a Hlz) as (m0 & Hin0 & Hk0 & Hr0); exists m0; split; [right; exact Hin0 | split; [exact Hk0 | exact Hr0]]
      | |- ?g => idtac "UNSOLVED FIELD:" g
      end.
    + (* [comment removed for export] *)
      assert (INB : forall i, 0 <= i < d ->
                Mr A argH E csB model' FULL' (Z_to_bv 64 (bv_unsigned b + i)) = Some (Z_to_bv 8 0)).
      { intros i Hi. set (a := Z_to_bv 64 (bv_unsigned b + i)).
        assert (Ua : bv_unsigned a = bv_unsigned b + i) by (unfold a; apply u64_lit; unfold CEIL, KHI in *; lia).
        assert (Hargh : argH E a = false).
        { destruct (argH E a) eqn:Ha; [|reflexivity]. pose proof (argH_high _ _ Ha). unfold CEIL, KHI, sp_window_lo in *. lia. }
        assert (Hvis : vis A E csB model' a = true).
        { unfold vis. rewrite Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw.
          rewrite (NA a) by lia. rewrite (LZ0 a) by lia. rewrite Ua.
          replace (bv_unsigned b <=? bv_unsigned b + i) with true by (symmetry; apply Z.leb_le; lia).
          replace (bv_unsigned b + i <? bv_unsigned b + d) with true by (symmetry; apply Z.ltb_lt; lia).
          cbn [andb orb negb]. rewrite !orb_true_r. reflexivity. }
        unfold Mr, mrestrict, hid. rewrite Hargh, Hvis. cbn [negb orb]. unfold FULL'. apply zfill_in. rewrite Udw, Ua. lia. }
      assert (Hfl : flat E (SA bb bk) (elenZ E (ELit d))).
      { unfold flat. rewrite (elenZ_lit E d) by (unfold CEIL, KHI in *; lia). rewrite Hest. unfold CEIL, KHI in *. lia. }
      constructor; [|constructor].
      * (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros off m Hoff Hm.
        rewrite (elenZ_lit E d) in Hm by (unfold CEIL, KHI in *; lia). rewrite Hest.
        destruct m as [|m']; [reflexivity|].
        apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL, KHI in *; lia); unfold CEIL, KHI in *; lia|].
        intros x Hx. rewrite u64_lit in Hx by (unfold CEIL, KHI in *; lia).
        unfold wview. replace x with (Z_to_bv 64 (bv_unsigned b + (bv_unsigned x - bv_unsigned b)))
          by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); unfold CEIL, KHI in *; lia).
        rewrite (INB (bv_unsigned x - bv_unsigned b)) by lia. discriminate.
      * (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros i Hi.
        rewrite (elenZ_lit E d) in Hi by (unfold CEIL, KHI in *; lia). rewrite Hest. apply INB. exact Hi.
      * (* [comment removed for export] *)
        unfold csB, kn. cbn [a_ss mk_ss s_know]. apply Forall_app. split; [apply KD|].
        apply (kn_grant_filter_ok E (Mr A argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned b) d HK);
          [exact APARTM | right; exact B3 | exact HbISP | exact M1].
Qed.



End SoundB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundMunmap.
Variable SEGS : list Segment.
Variable RR : shape_rel SEGS.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
(* [comment removed for export] *)
Variable ISP : expr.
Hypothesis ISP_vars : expr_vars_lt nx0 ISP = true.
Hypothesis argH_high : forall E (a : word), argH E a = true -> sp_window_lo <= bv_unsigned a /\ bv_unsigned (edenot E ISP) <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis RES_tile : forall z, img_lo A <= z < img_hi A -> in_ivs z (segments_reserved SEGS) = true.
Hypothesis HULL_ne : img_lo A < img_hi A.
Context {fx : FPState}.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH ISP FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (GPS.cfgF SEGS fx).

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH ISP FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH ISP FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH ISP ISP_vars argH_agree SINV_agree FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HULL_ok SHADOW_ok SINV argH ISP argH_high FS0.
Let A_wf_allowA' := APS.A_wf_allowA A.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH ISP argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH ISP argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
Let mmap_len_sound := AzSMmLib.mmap_len_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok ISP.
Let split_flat_estart := AzSMmLib.split_flat_estart SEGS A RES_len HULL_ok HULL_ne.
Let covered_maps_subtract := AzSMmLib.covered_maps_subtract.
Let maps_match_disjoint := AzSMmLib.maps_match_disjoint SEGS A RES_len.
Let bv5_10 := AzSMmLib.bv5_10. Let bv5_11 := AzSMmLib.bv5_11. Let bv5_17 := AzSMmLib.bv5_17.

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
  destruct K as [|[zb zk] zn| | | | | | | | | |]; try (apply IH; assumption).
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
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn|[b k] nn|fv flo fd]; cbn [kentry_ok kfoot] in *;
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
  - (* [comment removed for export] *) destruct HK as (Hfl & H47 & Hz). split; [exact Hfl|]. split; [exact H47|]. intros z Hzz.
    destruct Hfl as (F1 & F2 & F3 & F4).
    destruct (Hz z Hzz) as (bt & Hbt & Hv). exists bt. split; [|exact Hv].
    rewrite Hin; [exact Hbt|]. unfold SB in *.
    assert (D1 : (estart E (SA b k) / 8 <= z / 8)%Z) by (apply Z.div_le_mono; lia).
    assert (D2 : (z / 8 <= (estart E (SA b k) + elenZ E nn - 1) / 8)%Z) by (apply Z.div_le_mono; lia).
    assert (D3 : (0 <= estart E (SA b k) / 8)%Z) by (apply Z.div_pos; lia).
    assert (D4 : ((estart E (SA b k) + elenZ E nn - 1) / 8 < 2 ^ 44)%Z) by (apply Z.div_lt_upper_bound; lia).
    rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [HK HR]. split; [|exact HR].
    destruct (APS.kfpc_cases _ _ _ _ HK) as [ANY | (T & FR & LT)]; [apply ANY|]. rewrite T in Hin.
    apply (AX2S.fpc_kept M M'); [exact HK|]. intros a Ha. unfold AX2S.FPC_HI in *.
    pose proof (u64_range (edenot E flo)). apply Hin. rewrite u64_lit by lia. lia.
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
      RR (cfg R' (pc cs') FULL' model') T) ->
  RR (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn HK.
  destruct (AzSMmLib.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
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
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
  pose proof (maps_match_In E _ _ m MM Hm Hnf) as HIN.
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
  assert (BPOS : forall iv, In iv (vm_maps (m_vmmaps model)) -> 0 < bv_unsigned (snd iv)).
  { intros iv Hiv. exact (proj1 (proj1 (Forall_forall _ _) HB iv Hiv)). }
  pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B0 & B5 & B4).   (* [comment removed for export] *)
  unfold amap_den in B1, B2, B3, B0, B4, B5. cbn [fst snd] in B1, B2, B3, B0, B4, B5. rewrite Haddr in B2, B0, B4, B5. fold n in B1, B3, B4, B5.
  pose proof (u64_range addr) as Ra. pose proof (u64_range n) as Rn.
  pose proof (alloc_top_room (m_vmmaps model)) as ATR. unfold stack_max_size, two_pow_64 in ATR.
  destruct (xhi k (reg cs 10)) as [ahi|] eqn:Hahi; [|discriminate]. apply Z.ltb_lt in Hhi64.
  pose proof (xhi_sound SEGS E _ k (reg cs 10) ahi HKN Hahi) as Hahi'. fold addr in Hahi'. unfold two64 in Hhi64.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. rewrite <- Hne_eq, Hne. apply u64_lit. lia. }
  assert (HnZw : Z_to_bv 64 nZ = n) by (rewrite <- Un; apply Z_to_bv_bv_unsigned).
  destruct (split_flat_estart E _ k (reg cs 10) bb bk ne HKN Hsp HFLAT) as (Hest & _ & _). fold addr in Hest.
  assert (HelenZ : elenZ E ne = nZ) by (unfold elenZ; rewrite Hne; apply u64_lit; lia).
  set (lo := bv_unsigned addr) in *. set (hi := lo + nZ).
  assert (Hlohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= alloc_top (m_vmmaps model) /\ lo < hi /\ lo mod 4096 = 0 /\ hi mod 4096 = 0).
  { subst hi. repeat split; try lia. rewrite Z.add_mod, B2 by lia. rewrite <- Un, B3. reflexivity. }
  pose proof HULL_ok as (HU0 & HU1 & HU2 & HU3).
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 215 HC ltac:(lia) H17) as [R17 _]. rewrite <- bv5_17 in R17.
  pose proof (reg_sound' E cs R FULL model 10 HC ltac:(lia)) as R10. fold addr in R10. rewrite <- bv5_10 in R10.
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  (* [comment removed for export] *)
  pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS.
  assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
            bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m'))).
  { intros m' Hm' Hnf' Hne'. pose proof (maps_match_disjoint E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne') as D.
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
    pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(pose proof (u64_range (edenot E (snd p))); unfold CEIL in *; lia)) as Up.
    destruct (kzero_x_sound E _ k k sb sk sn HKN HKN Gz) as (Z1 & Z2 & Z3).
    unfold sh_iv. rewrite Hsh. cbn [fst snd].
    split; [|split; [exact Z1 | split; [exact Z3|]]].
    - intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold uE in *. rewrite Up in Hz1, Hz2. subst hi. lia.
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
      rewrite !u64_lit in D by lia.
      rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (first [ clear - Rb SHADOW_ok'; lia | lia ]).
      intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold sh_lo, sh_hi, uE in Hz1, Hz2.
      unfold estart. cbn [a_base a_off]. unfold estart in Z1, Z2. cbn [a_base a_off] in Z1, Z2.
      (* [comment removed for export] *)
      rewrite Z_to_bv_unsigned, bv_wrap64_mod in D. unfold uE in A8b, A8n. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & Wsp).
  unfold GPS.cfgF, GPS.mkstF.
  eapply (sr_munmap_lazy SEGS RR R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len T Hf He Hhalt R17 R10 B2 R11 ltac:(lia)).
  { (* [comment removed for export] *)
    pose proof (co_ispok _ _ _ _ _ _ _ _ _ _ _ _ HC) as [_ HISPHI]. unfold TASK_SIZE, sp_window_hi in *. fold nZ.
    destruct Hlohi as (_ & L2 & _). unfold alloc_top, stack_max_size in L2. subst hi lo. lia. }
  { fold nZ. rewrite HnZw. apply map_has_intro. rewrite <- Haddr. exact HIN. }
  fold nZ. rewrite HnZw. rewrite (v_addi_pc (pc cs) Hp0 Hp4).
  set (model' := munmap_model addr n model). set (FULL' := unfill addr n FULL).
  match goal with |- sr_rel _ RR (mkCfg _ ?mo) _ => change mo with model' end.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _ _ _) in HK.
  specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
  unfold GPS.cfgF, GPS.mkstF in HK. replace (pc cs') with (pc cs + 4) in HK by reflexivity. rewrite bv5_10. apply HK; [|reflexivity]. clear HK.
  (* [comment removed for export] *)
  assert (PM : vm_maps (m_vmmaps model') = map_remove (vm_maps (m_vmmaps model)) addr) by reflexivity.
  assert (PN : vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) lo (lo + bv_unsigned n)) by reflexivity.
  assert (PL : m_vm_lazy model' = maps_subtract (m_vm_lazy model) lo (lo + bv_unsigned n)) by reflexivity.
  assert (PISP : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)) by reflexivity.  (* [comment removed for export] *)
  assert (PTOP : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by reflexivity.   (* [comment removed for export] *)
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
  { intros x Hv. unfold vis in Hv |- *. rewrite PM, INMAPS', NOACC, PTOP in Hv. destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
    destruct (in_rng lo hi (bv_unsigned x)) eqn:Hr.
    - unfold in_rng in Hr. apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2.
      replace (in_hull A (bv_unsigned x)) with false in Hv by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1 as [L1|L1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      replace (alloc_top (m_vmmaps model) <=? bv_unsigned x) with false in Hv by (symmetry; apply Z.leb_gt; lia).
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
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xispok Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xmdef Xlazysub Xsinv Xlazyal Xetok Xnapos].
  destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
  (* [comment removed for export] *)
  assert (DROPIN : forall m', In m' (drop_etoks k bb bk ne (List.filter (fun m0 => negb (amap_match k (reg cs 10) ne m0)) (a_maps cs))) ->
            In m' (List.filter (fun m0 => negb (amap_match k (reg cs 10) ne m0)) (a_maps cs))
            /\ (is_etok m' = true -> bv_unsigned (fst (amap_den E m')) + bv_unsigned (snd (amap_den E m')) <= lo \/ hi <= bv_unsigned (fst (amap_den E m')))).
  { intros m' Hm'. unfold drop_etoks in Hm'. apply filter_In in Hm' as [Hin HP]. split; [exact Hin|]. intros Het.
    rewrite Het in HP. cbn [negb orb] in HP. unfold etok_apart in HP.
    destruct (split_lit (am_base m')) as [mb mk] eqn:Hspm. destruct (base_range k mb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
    apply andb_prop in HP as [HP0 HP]. apply andb_prop in HP0 as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
    destruct (base_range_sound SEGS E _ k mb blo bhi Xknow Hbr) as [Q1 Q2].
    assert (U : bv_unsigned (edenot E (am_base m')) = estart E (SA mb mk)).
    { apply (APS.u_of_split E (am_base m') mb mk Hspm). unfold estart. cbn [a_base a_off]. unfold two64 in Hb2. lia. }
    pose proof (ranges_apart_x_sound SEGS E _ k _ _ _ _ _ _ Xknow HP) as AP0.
    unfold amap_den. cbn [fst snd]. rewrite U. rewrite Hest, HelenZ in AP0. subst hi. exact AP0. }
  assert (DROPKEEP : forall m', In m' (List.filter (fun m0 => negb (amap_match k (reg cs 10) ne m0)) (a_maps cs)) -> is_etok m' = false ->
            In m' (drop_etoks k bb bk ne (List.filter (fun m0 => negb (amap_match k (reg cs 10) ne m0)) (a_maps cs)))).
  { intros m' Hm' Het. unfold drop_etoks. apply filter_In. split; [exact Hm'|]. rewrite Het. reflexivity. }
  assert (HAeq : ALLOW E cs' = flat_map (allow1 A E) (kept ++ gone ++ a_ghost cs)) by reflexivity.
  constructor; rewrite ?HAeq; subst cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_meter a_fake a_fbud kn s_regs s_log s_know s_next mk_ss];
    try set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _ _ _) in *.
  all: try replace (alloc_top (m_vmmaps model')) with (alloc_top (m_vmmaps model)) by (symmetry; exact PTOP).   (* [comment removed for export] *)
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
    apply MRKEEP; [subst hi; lia|]. intros p Hp Hin. pose proof (Hsh p Hp) as HH. rewrite ?Hkf in HH. cbn [fst snd] in Hin. lia.
  - unfold model'. rewrite munmap_model_halted. exact Xhalt.
  - unfold fds_ok in *. exact Xfds.
  - exact Xfs.
  - exact Xtid.
  - exact Xres.
  - exact Xlimit.
  - rewrite PM. unfold drop_etoks. apply maps_match_filter_etok; [|exact MAPS'].
    intros m0 _ HP. apply orb_false_iff in HP as [HP _]. apply negb_false_iff in HP. exact HP.
  - (* [comment removed for export] *)
    rewrite PM. apply Forall_forall. intros m' Hm1 Hk'. destruct (DROPIN m' Hm1) as [Hm' _]. destruct (DISJF m' Hm') as (Hm0 & _ & _).
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
    pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. lia.
  - (* [comment removed for export] *) intros z Hz. rewrite PM, INMAPS'. rewrite NOACC in Hz. apply andb_prop in Hz as [Hz1 Hz2]. rewrite (Xnasub z Hz1), Hz2. reflexivity.
  - (* [comment removed for export] *) apply Forall_forall. intros m' Hm1 Hk'. destruct (DROPIN m' Hm1) as [Hm' _]. destruct (DISJF m' Hm') as (Hm0 & Hne' & D).
    assert (Hnf' : is_fog m' = false) by (apply KNF; tauto). specialize (D Hnf').
    rewrite PN. pose proof (proj1 (Forall_forall _ _) Xnone m' Hm0 Hk') as X.
    pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' Xmaps Hm0 Hnf')) as (C1 & _).
    unfold amap_den in *. apply maps_subtract_keeps; [lia | exact C1 | exact X | cbn [fst snd]; subst hi; lia].
  - (* [comment removed for export] *) apply Forall_forall. intros m' Hm1 Hk' x Hx. destruct (DROPIN m' Hm1) as [Hm' _]. destruct (DISJF m' Hm') as (Hm0 & Hne' & D).
    specialize (D ltac:(apply KNF; tauto)).
    destruct (proj1 (Forall_forall _ _) Xkinds m' Hm0 Hk' x Hx) as [K1 K2].
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x) by lia.
    rewrite NOACC, K1, (LAZYOUT x Hxo), K2. split; reflexivity.
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. rewrite sum_sizes_app. rewrite sum_sizes_app in Xtotsz.
    pose proof (sum_sizes_filter_le (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) as SF.
    change (vm_reserved (m_vmmaps model')) with (vm_reserved (m_vmmaps model)). lia.
  - (* [comment removed for export] *) rewrite PISP. exact Xisp.
  - (* [comment removed for export] *) unfold init_sp_ok in *. rewrite PISP. exact Xispok.
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
      apply andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; lia.
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
      - exfalso. unfold vis in Hh, Hold. rewrite PM, INMAPS', NOACC, (LAZYOUT x Hxo), PTOP in Hh. rewrite (ALW (bv_unsigned x)), Hex in Hold.
        replace (existsb (fun p0 => (uE E (fst p0) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p0) + uE E (snd p0)))%bool gone) with false in Hold.
        2: { symmetry. apply APS.existsb_false_forall. intros p0 Hq0. destruct (GONE p0 Hq0) as (G1 & _).
             match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
        rewrite Hxo' in Hh. cbn [negb] in Hh. rewrite !andb_true_r in Hh. rewrite !orb_false_r in Hold. rewrite Hh in Hold. discriminate. }
    destruct SHX as (p & Hp & Hpx). destruct (GONE p Hp) as (_ & _ & G3 & _).
    pose proof (G3 x Hpx) as Z0. unfold Mr, mrestrict, hid in Z0. rewrite Hold in Z0.
    destruct (argH E x); [discriminate|]. cbn in Z0. exact Z0.
  - (* [comment removed for export] *) intros x Hmx Hna.
    rewrite PM, INMAPS' in Hmx. apply andb_prop in Hmx as [Hmx Hout]. apply negb_true_iff in Hout.
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x).
    { unfold in_rng in Hout. apply andb_false_iff in Hout as [Hout|Hout]; [apply Z.leb_gt in Hout | apply Z.ltb_ge in Hout]; lia. }
    rewrite NOACC in Hna. replace (in_rng lo hi (bv_unsigned x)) with false in Hna
      by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [negb] in Hna. rewrite andb_true_r in Hna.
    unfold FULL'. rewrite unfill_out by (rewrite Un; subst hi; lia). exact (Xmdef x Hmx Hna).
  - (* [comment removed for export] *) intros x Hlz.
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x).
    { destruct (Z_lt_le_dec (bv_unsigned x) lo) as [|Hge]; [left; assumption|].
      destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt|]; [|right; assumption]. exfalso.
      pose proof (page_of_byte_in_aligned x lo hi L4 L5 ltac:(lia)) as [P1 P2].
      rewrite PL in Hlz. rewrite (page_in_ranges_subtract_in (page_base x) (m_vm_lazy model) lo hi W3) in Hlz; [discriminate | lia]. }
    rewrite (LAZYOUT x Hxo) in Hlz. destruct (Xlazysub x Hlz) as (m0 & Hm0 & Hk0 & Hr0).
    exists m0. split; [|split; [exact Hk0 | exact Hr0]].
    apply DROPKEEP; [| unfold is_etok; destruct (am_kind m0); cbn in Hk0 |- *; congruence].   (* [comment removed for export] *)
    apply filter_In. split; [exact Hm0|]. apply negb_true_iff.
    destruct (amap_match k (reg cs 10) ne m0) eqn:Hmm; [|reflexivity]. exfalso.
    unfold amap_match in Hmm. apply andb_prop in Hmm as [Hb0 Hl0]. apply andb_prop in Hb0 as [_ Hb0]. apply expr_eqb_eq in Hb0.
    pose proof (len_eqb_sound E _ k ne (am_len m0) HKN Hl0) as Hn0.
    unfold amap_den in Hr0. cbn [fst snd] in Hr0. rewrite <- Hb0, <- Hn0, Hne in Hr0. fold addr lo in Hr0.
    rewrite u64_lit in Hr0 by lia. subst hi. lia.
  - (* [comment removed for export] *) eapply SINV_frame; [|exact Xsinv]. intros x Hx. unfold FULL'. apply unfill_out. pose proof (argH_high _ _ Hx) as [_ HAx]. rewrite <- Xisp in HAx.
    unfold alloc_top, stack_max_size in L2. rewrite Un. subst hi. lia.
  - (* [comment removed for export] *) rewrite PL. apply (AzSMmLib.maps_subtract_aligned SEGS A RES_len HULL_ok HULL_ne); [exact W3 | exact Xlazyal | exact L4 | exact L5 | subst lo; lia | subst hi lo; unfold CEIL in *; lia].
  - (* [comment removed for export] *)
    apply Forall_forall. intros m' Hm1 Het. destruct (DROPIN m' Hm1) as [Hm' Hap]. specialize (Hap Het).
    apply filter_In in Hm' as [Hm0 _]. destruct (proj1 (Forall_forall _ _) Xetok m' Hm0 Het) as (T1 & T2 & T3).
    split; [exact T1|]. split; [exact T2|]. intros x Hx. destruct (T3 x Hx) as [T4 T5]. split.
    + rewrite PM, INMAPS', T4. cbn [andb]. apply negb_true_iff. unfold in_rng. apply andb_false_iff.
      destruct Hap as [Hap|Hap]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
    + rewrite PL. destruct (page_in_ranges (page_base x) (maps_subtract (m_vm_lazy model) lo hi)) eqn:Hp; [|reflexivity]. exfalso.
      rewrite (AzSMmLib.page_in_ranges_subtract_mono SEGS A RES_len HULL_ok HULL_ne _ _ _ _ W3 Hp) in T5. discriminate.
  - (* [comment removed for export] *) rewrite PN. apply AzSMmLib.ivs_pos_subtract. exact Xnapos.
Qed.


Theorem node_sys_here_YMunmap : SIF.sys_here SEGS RR A nx0 LIMIT SINV argH ISP FS0 fx YMunmap.
Proof. intros cs cs' E R FULL model T HC Hpre Hn HK. eapply node_munmap_sound; eauto. Qed.

End SoundMunmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundSys.
Variable SEGS : list Segment.
Variable RR : shape_rel SEGS.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Variable FXOK : GPS.FX -> Prop.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Variable ISP : expr.   (* [comment removed for export] *)
Hypothesis ISP_vars : expr_vars_lt nx0 ISP = true.
Hypothesis argH_high : forall E (a : word), argH E a = true -> sp_window_lo <= bv_unsigned a /\ bv_unsigned (edenot E ISP) <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis RES_tile : forall z, img_lo A <= z < img_hi A -> in_ivs z (segments_reserved SEGS) = true.
Hypothesis HULL_ne : img_lo A < img_hi A.

Theorem node_sys_sound : forall y, SIF.sys_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK y.
Proof.
  intros y. apply SIF.sys_pack. intros fx. destruct y.
  - eapply @node_sys_here_YMunmap; eassumption.
  - eapply @node_sys_here_YBrk; eassumption.
  - eapply @node_sys_here_YSetTid; eassumption.
Qed.

Theorem node_exit_sound : SIF.exit_stmt SEGS RR A LIMIT SINV argH ISP FS0 FXOK.
Proof. apply SIF.exit_pack. intros fx. eapply @node_exit_here; eassumption. Qed.

Theorem node_brk2_sound : SIF.brk2_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK.
Proof. apply SIF.brk2_pack. intros fx. eapply @node_brk2_here; eassumption. Qed.
Theorem node_brk2x_sound : SIF.brk2x_stmt SEGS RR A nx0 LIMIT SINV argH ISP FS0 FXOK.
Proof. apply SIF.brk2x_pack. intros fx. eapply @node_brk2x_here; eassumption. Qed.
End SoundSys.
