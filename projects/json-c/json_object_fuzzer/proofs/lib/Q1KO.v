(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHWH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition is_file_node (n : node) : Prop :=
match n with NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ => True | _ => False end.

Lemma open_result_msim : forall moA moB ent eff mo2, msim moA moB ->
open_result moA ent eff mo2 -> exists mo2b, open_result moB ent eff mo2b /\ msim mo2 mo2b.
Proof.
intros moA moB ent eff mo2 Hs H. pose proof (msim_facts (mkLVP [] [] [] 0) _ _ Hs) as (Hfd & _).
destruct H as [(e & He & -> & ->)|(Hlk & -> & ->)].
- exists moB. split; [left; exists e; auto| exact Hs].
- exists (with_fds (fd_insert (m_fds moB) (alloc_fd (m_fds moB)) ent) moB). unfold open_result. rewrite Hfd in *.
split; [right; auto|]. apply msim_with_fds. exact Hs.
Qed.

Lemma nstep_file_msim : forall n moA moB rsp mo2 evs, is_file_node n -> msim moA moB ->
nstep n moA rsp mo2 evs -> exists mo2b, nstep n moB rsp mo2b evs /\ msim mo2 mo2b.
Proof.
intros n moA moB rsp mo2 evs Hn Hs H. pose proof (msim_facts (mkLVP [] [] [] 0) _ _ Hs) as (Hfd & Hfs & _).
destruct n; try destruct Hn; cbn [nstep] in *.
- destruct H as [-> H]. exists moB. split; [split; [reflexivity| exact H]| exact Hs].
- destruct H as [-> H]. rewrite Hfs.
destruct (path_max <=? length path)%nat; [destruct H as [-> ->]; exists moB; auto|].
destruct path; [destruct H as [-> ->]; exists moB; auto|].
destruct (path_eqb _ _); [| destruct (fs_lookup _ _); [| destruct H as [-> ->]; exists moB; auto]];
(destruct (open_result_msim _ _ _ _ _ Hs H) as (mo2b & H2 & Hs2); exists mo2b; auto).
- destruct H as [-> H]. rewrite Hfd, Hfs.
destruct (fd_lookup (m_fds moA) _) as [[c| p off| p off| p off| p off| | sk| id wr| dnr dnw| ]|]; try (destruct H; fail).
+ destruct (fs_lookup _ _); [| destruct H]. destruct H as [-> ->].
eexists. split; [split; [reflexivity| split; reflexivity]|]. apply msim_with_fds. exact Hs.
+ destruct H as [-> ->]. exists moB. auto.
+ destruct H as [-> ->]. exists moB. auto.
- destruct H as (-> & Hr & H). rewrite Hfd. destruct (fd_lookup (m_fds moA) _); destruct H as [-> ->].
+ eexists. split; [split; [reflexivity| split; [exact Hr| split; reflexivity]]|]. apply msim_with_fds. exact Hs.
+ exists moB. split; [split; [reflexivity| split; [exact Hr| split; reflexivity]]| exact Hs].
- destruct H as (-> & -> & ->). exists moB. split; [split; [reflexivity| split; reflexivity]| exact Hs].
Qed.

Definition cinvA (L : lvp) : machine_state -> Model -> Prop := cinv L (xinvA L) (jsome L).
Definition nstepsA (L : lvp) : node -> Model -> resp -> Model -> list event -> Prop := nstepA L (nstep_raw L).
Definition nexitsA (L : lvp) : node -> Model -> word -> Model -> Prop := nexitA L nexit_raw.
Definition tsetA (L : lvp) {R} (t : itree node R) (mo : Model) : TSet := tset L (nstep_raw L) nexit_raw t mo.
Definition tset0A (L : lvp) {R} (t : itree node R) (mo : Model) : TSet := tset0 (nstep_raw L) nexit_raw t mo.

Section Sound.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.
Hypothesis HL : shoff_ok L.
Hypothesis HBe : bands_excl L.
Hypothesis HBc : bands_cover L.

Lemma conceal_msim : forall moA moB a n, msim moA moB -> conceal L moB a n = conceal L moA a n.
Proof.
intros moA moB a n Hs. unfold conceal. rewrite (hidden_ext_fun L moA moB (proj1 (msim_frame _ _ Hs))). reflexivity.
Qed.
Lemma reveal_msim : forall moA moB a n, msim moA moB -> reveal L moB a n = reveal L moA a n.
Proof.
intros moA moB a n Hs. unfold reveal. rewrite (hidden_ext_fun L moA moB (proj1 (msim_frame _ _ Hs))). reflexivity.
Qed.

Lemma m_vmmaps_msim : forall moA moB, msim moA moB -> m_vmmaps moB = m_vmmaps moA.
Proof. intros moA moB Hs. exact (proj1 (proj1 (msim_frame _ _ Hs))). Qed.

Lemma nstep_raw_msim : forall n moA moB rsp mo' evs, msim moA moB ->
nstep_raw L n moA rsp mo' evs -> exists mo'b, nstep_raw L n moB rsp mo'b evs /\ msim mo' mo'b.
Proof.
intros n moA moB rsp mo' evs Hs H.
assert (FILE : is_file_node n -> exists mo'b, nstep_raw L n moB rsp mo'b evs /\ msim mo' mo'b).
{ intros Hn. assert (H' : exists mo2, nstep n moA rsp mo2 evs /\ drift L mo2 mo') by (destruct n; try destruct Hn; exact H).
destruct H' as (mo2 & Hst & Hd). destruct (nstep_file_msim n moA moB rsp mo2 evs Hn Hs Hst) as (mo2b & Hst2 & Hs2).
exists mo2b. split.
- assert (exists mo2', nstep n moB rsp mo2' evs /\ drift L mo2' mo2b) by (exists mo2b; split; [exact Hst2| apply drift_refl]).
destruct n; try destruct Hn; exact H0.
- eapply msim_trans; [apply msim_sym; eapply drift_msim; exact Hd| exact Hs2]. }
pose proof (m_vmmaps_msim _ _ Hs) as Hvm.
destruct n; try (apply FILE; exact I); try (destruct H; fail).
-  clear FILE. cbn -[rlen rlenw grant_model commit_model remap_model anon_place_ok fixed_contained fixed_free reveal wunit rsp_grant rsp_remap rsp_err mmap_kind] in H |- *.
destruct H as [-> H].
assert (Hap : forall r k, anon_place_ok moB r k = anon_place_ok moA r k) by (intros; unfold anon_place_ok; rewrite Hvm; reflexivity).
assert (Hfc : forall r k, fixed_contained moB r k = fixed_contained moA r k) by (intros; unfold fixed_contained; rewrite Hvm; reflexivity).
assert (Hff : forall r k, fixed_free moB r k = fixed_free moA r k) by (intros; unfold fixed_free; rewrite Hvm; reflexivity).
assert (Hrv : forall r k, reveal L moB r k = reveal L moA r k) by (intros; apply reveal_msim; exact Hs).

destruct (mmap_kind addr prot flags).
+ destruct H as (r & ws & Hp & Hf & Hw & -> & ->).
exists (grant_model moB r (rlenw len)). split; [split; [reflexivity| exists r, ws; rewrite Hap, Hrv; auto 6]| apply (msim_grant L); exact Hs].
+ rewrite Hfc, Hff. destruct (fixed_contained moA _ _).
* destruct H as (-> & ->).
exists (commit_model moB (Z_to_bv 64 addr) (rlenw len)). split; [split; [reflexivity| auto]| apply (msim_commit L); exact Hs].
* destruct (fixed_free moA _ _); [| destruct H].
destruct H as (ws & Hf & Hw & -> & ->).
exists (grant_model moB (Z_to_bv 64 addr) (rlenw len)). split; [split; [reflexivity| exists ws; rewrite Hrv; auto]| apply (msim_grant L); exact Hs].
+ destruct H as (-> & ->).
exists (remap_model moB (Z_to_bv 64 addr) (rlenw len)). split; [split; [reflexivity| auto]| apply (msim_remap L); exact Hs].
+ destruct H.
-  clear FILE. cbn -[rlenw munmap_model rsp_munmap] in H |- *. destruct H as (-> & -> & ->).
exists (munmap_model moB (Z_to_bv 64 addr) (rlenw len)).
pose proof (msim_munmap L _ _ (Z_to_bv 64 addr) (rlenw len) Hs) as Hs2.
split; [| exact Hs2]. split; [reflexivity|]. split; [reflexivity|]. unfold rsp_munmap. rewrite (conceal_msim _ _ _ _ Hs2). reflexivity.
Qed.

Lemma nexit_raw_msim : forall n moA moB code mo', msim moA moB ->
nexit_raw n moA code mo' -> exists mo'b, nexit_raw n moB code mo'b /\ msim mo' mo'b.
Proof.
intros n moA moB code mo' Hs H. destruct n; try (destruct H; fail). cbn [nexit_raw nexit] in *. destruct H as [Hc Hm]. subst code mo'.
exists (with_halted (bv_and (Z_to_bv 64 code0) (Z_to_bv 64 255)) moB). split; [split; reflexivity| apply msim_with_halted; exact Hs].
Qed.

Lemma range_vis_vmeq : forall mo mo' a n, vmeq mo mo' -> range_vis L mo a n -> range_vis L mo' a n.
Proof. intros mo mo' a n Hv H x Hx. rewrite (hidden_ext L mo mo' Hv). apply H. exact Hx. Qed.

Lemma excl_mapped_vmeq : forall mo mo', vmeq mo mo' -> excl_mapped L mo -> excl_mapped L mo'.
Proof. intros mo mo' [Hv _] H. unfold excl_mapped in *. rewrite Hv. exact H. Qed.

Lemma nsafeA_drift : forall n mo mo', drift L mo mo' -> nsafeA L n mo -> nsafeA L n mo'.
Proof.
intros n mo mo' Hd H. pose proof (drift_vmeq L _ _ Hd) as Hv. pose proof (drift_Phi L _ _ Hd) as HP. destruct Hv as [Hvm Hlz].
assert (Hv : vmeq mo mo') by (split; assumption).
assert (Hfc : forall r k, fixed_contained mo' r k = fixed_contained mo r k) by (intros; unfold fixed_contained; rewrite Hvm; reflexivity).
assert (Hff : forall r k, fixed_free mo' r k = fixed_free mo r k) by (intros; unfold fixed_free; rewrite Hvm; reflexivity).
assert (Hcc : forall x y, cost_commit mo' x y = cost_commit mo x y) by (intros; unfold cost_commit; rewrite Hvm; reflexivity).
assert (Htp : forall x y, fixed_top mo' x y = fixed_top mo x y) by (intros; unfold fixed_top; rewrite Hvm; reflexivity).
destruct n; cbn -[mmap_kind fixed_contained fixed_free Phi cost_anon cost_commit cost_fixed fixed_gates fixed_top range_vis excl_mapped rlenw rlen Z.pow vm_gap_available] in H |- *; try exact H.
- destruct (mmap_kind addr prot flags); rewrite ?Hfc, ?Hff, ?Hcc, ?HP, ?Hvm, ?Htp.
+ destruct H as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [eapply excl_mapped_vmeq; eassumption|]. split; [exact H4| exact H5].
+ destruct H as (Hg & Ht & [(H1 & H2 & H3)|(H1 & H2 & H3 & H4)]); split; [exact Hg| split; [exact Ht|] |exact Hg| split; [exact Ht|]].
* left. split; [exact H1|]. split; [eapply range_vis_vmeq; eassumption| exact H3].
* right. auto.
+ destruct H as (H1 & Ht & H2 & H3). split; [exact H1|]. split; [exact Ht|]. split; [exact H2|]. eapply range_vis_vmeq; eassumption.
+ exact H.
- rewrite Hvm. exact H.
Qed.

Lemma file_node_dec : forall n, is_file_node n \/ ~ is_file_node n.
Proof. intros n; destruct n; cbn; tauto. Qed.

Lemma nstep_file_vm : forall n mo rsp mo2 evs, is_file_node n -> nstep n mo rsp mo2 evs -> m_vm mo2 = m_vm mo.
Proof.
intros n mo rsp mo2 evs Hn H.
assert (OR : forall ent eff mo', open_result mo ent eff mo' -> m_vm mo' = m_vm mo).
{ intros ent eff mo' [(e & _ & _ & ->)|(_ & _ & ->)]; [reflexivity| apply m_vm_with_fds]. }
destruct n; try destruct Hn; cbn [nstep] in H.
- destruct H as [-> _]. reflexivity.
- destruct H as [_ H]. destruct (path_max <=? length path)%nat; [destruct H as [_ ->]; reflexivity|].
destruct path; [destruct H as [_ ->]; reflexivity|].
destruct (path_eqb _ _); [exact (OR _ _ _ H)|]. destruct (fs_lookup _ _); [exact (OR _ _ _ H)| destruct H as [_ ->]; reflexivity].
- destruct H as [_ H]. destruct (fd_lookup (m_fds mo) _) as [[c| p off| p off| p off| p off| | sk| id wr| dnr dnw| ]|]; try (destruct H; fail).
+ destruct (fs_lookup _ _); [| destruct H]. destruct H as [_ ->]. apply m_vm_with_fds.
+ destruct H as [_ ->]. reflexivity.
+ destruct H as [_ ->]. reflexivity.
- destruct H as (_ & _ & H). destruct (fd_lookup (m_fds mo) _); destruct H as [_ ->]; [apply m_vm_with_fds| reflexivity].
- destruct H as (_ & _ & ->). reflexivity.
Qed.

Theorem Phi_nstep_raw : forall n mo rsp mo' evs,
xinvA L mo -> nsafeA L n mo -> nstep_raw L n mo rsp mo' evs ->
Phi L mo' <= Phi L mo + costA L n mo rsp /\ vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo).
Proof.
intros n mo rsp mo' evs [HF [W [X Y]]] Hns H.
destruct (file_node_dec n) as [Hf|Hnf].
{ assert (H' : exists mo2, nstep n mo rsp mo2 evs /\ drift L mo2 mo') by (destruct n; try destruct Hf; exact H).
destruct H' as (mo2 & Hst & Hd). pose proof (nstep_file_vm n mo rsp mo2 evs Hf Hst) as Hvm.
assert (Hv : vmeq mo mo2) by (unfold vmeq, m_vmmaps, m_vm_lazy; rewrite Hvm; split; reflexivity).
assert (Hmat : m_vm_materialized mo2 = m_vm_materialized mo) by (unfold m_vm_materialized; rewrite Hvm; reflexivity).
rewrite (drift_Phi L _ _ Hd), (Phi_ext L mo mo2 Hv Hmat). destruct (drift_vmeq L _ _ Hd) as [-> _]. destruct Hv as [-> _].
assert (Hz : costA L n mo rsp = 0) by (destruct n; try destruct Hf; reflexivity). lia. }
destruct n; try (exfalso; exact (Hnf I)); try (destruct H; fail).
-
cbn -[rlen rlenw grant_model commit_model remap_model anon_place_ok fixed_contained fixed_free reveal wunit
rsp_grant rsp_remap rsp_err mmap_kind Phi errno_ret_in cost_anon cost_commit cost_fixed Z.le Z.add
fixed_gates fixed_top range_vis excl_mapped vm_gap_available] in H, Hns |- *.
destruct H as [_ H]. pose proof (mmap_kind_cases addr prot flags) as HK.
destruct (mmap_kind addr prot flags); [| | | destruct H].
+ destruct Hns as (Hl1 & Hl2 & Hem & _). pose proof (rlen_facts len Hl1 Hl2) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
destruct H as (r & ws & Hp & Hf & Hw & -> & ->).
cbn [rsp_grant eff_ret]. unfold anon_place_ok in Hp. apply andb_prop in Hp as [Hp Hfree].
apply andb_prop in Hp as [Hp Hce]. apply andb_prop in Hp as [Hal Hpos]. apply Z.eqb_eq in Hal. apply Z.leb_le in Hce. unfold page_size in Hal.
rewrite (placed_not_errno0 r (rlen len)) by (first [exact (below_top_room _ _ Hce) | lia]). split; [| apply limit_grant].
pose proof (region_free_app_r _ _ _ _ Hfree) as Hfree2. fold (rlenw len) in Hfree2.
assert (Hex : excl_entry L (r, rlenw len) = false) by (apply (fresh_not_excl L mo); [exact Hem| rewrite R6; lia| exact Hfree2]).
assert (Hb : bv_unsigned r + bv_unsigned (rlenw len) <= 2^64) by (rewrite R6; pose proof (below_top_room _ _ Hce); lia).
pose proof (Phi_grant L mo r (rlenw len) W Hex ltac:(rewrite R6; lia) Hb) as HP. rewrite length_app, Nat2Z.inj_add in HP.
pose proof (range_pages_eq r (rlenw len) Hal ltac:(rewrite R6; exact R3)) as HR.
pose proof (sh_pages_le L r (rlenw len) Hal ltac:(rewrite R6; exact R3) ltac:(rewrite R6; lia)) as Hsh.
unfold cost_anon. unfold shadow_iv in Hsh. rewrite R6 in *. lia.
+ destruct HK as [-> ->]. destruct Hns as (Hg & Htop & Hns).
pose proof (fixed_facts addr len Hg) as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
assert (Hb : bv_unsigned (Z_to_bv 64 addr) + bv_unsigned (rlenw len) <= 2^64) by (rewrite Ua, Un; unfold grant_ceilA, sp_window_hi, stack_max_size in G5; lia).
assert (Hroom : addr + rlen len <= 2^64 - 4096) by exact (below_top_room _ _ Htop).
destruct (fixed_contained mo (Z_to_bv 64 addr) (rlenw len)) eqn:Hc.
* destruct H as (-> & ->).
cbn [rsp_grant eff_ret]. rewrite (placed_not_errno0 (Z_to_bv 64 addr) (rlen len)) by (first [rewrite Ua; exact Hroom| lia]). split; [| apply limit_commit].
pose proof (Phi_commit L mo (Z_to_bv 64 addr) (rlenw len) W) as HP. unfold cost_commit. rewrite Ua, Un in HP. lia.
* destruct Hns as [(Hc' & _)|(_ & Hfr & Hex & _)]; [congruence|]. rewrite Hfr in H.
destruct H as (ws & Hf & Hw & -> & ->).
cbn [rsp_grant eff_ret]. rewrite (placed_not_errno0 (Z_to_bv 64 addr) (rlen len)) by (first [rewrite Ua; exact Hroom| lia]). split; [| apply limit_grant].
pose proof (Phi_grant L mo (Z_to_bv 64 addr) (rlenw len) W Hex ltac:(rewrite Un; lia) Hb) as HP. rewrite length_app, Nat2Z.inj_add in HP.
pose proof (range_pages_eq (Z_to_bv 64 addr) (rlenw len) ltac:(rewrite Ua; exact G4) ltac:(rewrite Un; exact Rm)) as HR.
unfold cost_fixed, sh_cost_at. unfold wiv2z in HP, HR. cbn [fst snd] in HP, HR. rewrite Ua, Un in *. lia.
+ destruct HK as [-> ->]. destruct Hns as (Hg & Htop & Hc & Hvis).
pose proof (fixed_facts addr len Hg) as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
assert (Hb : bv_unsigned (Z_to_bv 64 addr) + bv_unsigned (rlenw len) <= 2^64) by (rewrite Ua, Un; unfold grant_ceilA, sp_window_hi, stack_max_size in G5; lia).
assert (H0 : Phi L mo' <= Phi L mo /\ vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo)).
{ destruct H as (-> & ->).
split; [| apply limit_remap]. apply (Phi_remap L mo _ _ W); [rewrite Ua; unfold page_size; exact G4| rewrite Un; unfold page_size; exact Rm| rewrite Un; exact Rp| exact Hb]. }
destruct (errno_ret_in _ _); lia.
-  cbn -[rlenw munmap_model rsp_munmap Phi Z.le Z.add Z.lt Z.pow Z.modulo rlen] in H, Hns |- *.
destruct H as (_ & -> & _). destruct Hns as (H1 & H2 & H3 & H4 & H5 & Hhas & Hsz & Hfree & _).
pose proof (rlen_facts len H1 H2) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
split; [| apply limit_munmap]. pose proof (Phi_munmap L mo (Z_to_bv 64 addr) (rlenw len) W Hsz Hfree ltac:(rewrite R6; lia)). lia.
Qed.

Lemma at_node_exit_view : forall c mo ms, at_node segs (NExit c) (msview L mo ms) -> at_node segs (NExit c) ms.
Proof. intros c mo ms H. exact H. Qed.

Lemma exit_sysno : forall c ms x8, at_node segs (NExit c) ms -> ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof. intros c ms x8 [[Hs|Hs] _] Hx; rewrite Hx in Hs; injection Hs as ->; intros Hin; vm_compute in Hin; lia. Qed.

Lemma file_node_sysno : forall n ms mo x8, is_file_node n -> at_nodeA L segs n (msview L mo ms) ->
ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
intros n ms mo x8 Hn Hat Hx. change (ms_svc_pending (msview L mo ms) = Some x8) in Hx.
destruct n; try destruct Hn; cbn [at_nodeA at_node] in Hat; destruct Hat as [Hs _]; rewrite Hx in Hs; injection Hs as ->;
intros Hin; vm_compute in Hin; lia.
Qed.

Lemma exit_completeA : forall c ms mo evs X,
at_node segs (NExit c) (msview L mo ms) -> m_halted mo = None -> sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X ->
exists code mo', X = SNext (mkCfg ms mo') /\ nexit_raw (NExit c) mo code mo' /\
evs = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code.
Proof.
intros c ms mo evs X Hat Hh Hst.
destruct (proj1 (exit_node_facts segs ms mo c (at_node_exit_view _ _ _ Hat) Hh) evs X (sstep_cfg_sub segs _ _ _ _ Hst)) as [-> ->].
exists (exit_code c), (with_halted (exit_code c) mo). split; [reflexivity|]. split; [split; reflexivity|].
rewrite m_fs_with_halted, m_halted_with_halted. split; reflexivity.
Qed.

Lemma exit_soundA : forall c ms mo code mo',
at_node segs (NExit c) (msview L mo ms) -> m_halted mo = None -> nexit_raw (NExit c) mo code mo' ->
m_halted mo' = Some code /\ sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo')).
Proof.
intros c ms mo code mo' Hat Hh [-> ->]. rewrite m_halted_with_halted, m_fs_with_halted. split; [reflexivity|].
apply sstep_cfg_nonalloc; [intros x8 Hx; exact (exit_sysno c ms x8 (at_node_exit_view _ _ _ Hat) Hx)|].
exact (proj2 (exit_node_facts segs ms mo c (at_node_exit_view _ _ _ Hat) Hh)).
Qed.

Lemma file_factsA : forall n ms mo, is_file_node n ->
at_nodeA L segs n (msview L mo ms) -> cinvA L ms mo -> file_facts segs L ms mo (nstep n mo).
Proof.
intros n ms mo Hn Hat ([HF HV] & HI & HJ). destruct n; try destruct Hn; cbn [at_nodeA] in Hat.
- apply writev_factsA; assumption.
- apply open_factsA; assumption.
- apply read_factsA; assumption.
- apply close_factsA; [exact Hat| exact HF].
- apply ioctl_factsA; [exact Hat| exact HF].
Qed.

Lemma file_nodeA : forall n ms mo, is_file_node n ->
at_nodeA L segs n (msview L mo ms) -> m_halted mo = None -> cinvA L ms mo ->
(forall evs X, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw L n mo rsp mo' evs /\ cinvA L ms' mo' /\ m_halted mo' = None)
/\ (forall rsp mo' evs, nstep_raw L n mo rsp mo' evs ->
exists ms' mo2 rsp2, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp2 /\
nstep_raw L n mo rsp2 mo2 evs /\ msim mo' mo2 /\ rvarA n rsp rsp2 /\ m_halted mo2 = None)
/\ (exists rsp mo' evs, nstep_raw L n mo rsp mo' evs).
Proof.
intros n ms mo Hn Hat Hh HC.
destruct (file_factsA n ms mo Hn Hat HC) as (x8 & chk & Hsvc & Hchk & Hnu & Hok & Hcompl).
destruct (file_kit segs L ms mo x8 (nstep n mo) chk Hsvc Hh HC Hchk Hnu Hok Hcompl) as (K1 & K2 & K3).
assert (RAW : forall rsp mo' evs, nstep_raw L n mo rsp mo' evs <-> exists mo2, nstep n mo rsp mo2 evs /\ drift L mo2 mo').
{ intros. destruct n; try destruct Hn; reflexivity. }
split; [|split].
- intros evs X Hst. destruct (K1 evs X (sstep_cfg_sub segs _ _ _ _ Hst)) as (rsp & ms' & mo' & HX & Hv & HP & HC' & Hh').
exists rsp, ms', mo'. rewrite RAW. auto.
- intros rsp mo' evs Hr. apply RAW in Hr as (mo2 & HP & Hd).
destruct (K2 rsp mo2 mo' evs HP Hd) as (ms' & mo3 & Hst & Hv & HP3 & Hs & Hh3).
exists ms', mo3, rsp. rewrite RAW. split.
{ apply sstep_cfg_nonalloc; [| exact Hst]. intros y Hy. rewrite Hsvc in Hy. injection Hy as <-.
exact (file_node_sysno n ms mo x8 Hn Hat Hsvc). }
split; [exact Hv|]. split; [exact HP3|]. split; [exact Hs|]. split; [apply rvarA_refl| exact Hh3].
- destruct K3 as (rsp & mo2 & evs & HP). exists rsp, mo2, evs. apply RAW. exists mo2. split; [exact HP| apply drift_refl].
Qed.

Lemma mmap_nodeA : forall addr len prot flags ms mo,
at_nodeA L segs (NMmap addr len prot flags) (msview L mo ms) -> m_halted mo = None -> cinvA L ms mo -> nsafeA L (NMmap addr len prot flags) mo ->
(forall evs X, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw L (NMmap addr len prot flags) mo rsp mo' evs /\ cinvA L ms' mo' /\ m_halted mo' = None)
/\ (forall rsp mo' evs, nstep_raw L (NMmap addr len prot flags) mo rsp mo' evs ->
exists ms' mo2 rsp2, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp2 /\
nstep_raw L (NMmap addr len prot flags) mo rsp2 mo2 evs /\ msim mo' mo2 /\ rvarA (NMmap addr len prot flags) rsp rsp2 /\ m_halted mo2 = None)
/\ (exists rsp mo' evs, nstep_raw L (NMmap addr len prot flags) mo rsp mo' evs).
Proof.
intros addr len prot flags ms mo Hat Hh HC Hns.
assert (Hat' : at_node segs (NMmap addr len prot flags) ms) by exact Hat.
pose proof (mmap_kind_cases addr prot flags) as HK. unfold nsafeA in Hns.
destruct (mmap_kind addr prot flags).
- destruct HK as (-> & -> & ->).
split; [|split]; [apply anon_complete| apply anon_sound| apply anon_progress]; assumption.
- destruct HK as (-> & ->).
split; [|split]; [apply fixed_complete| apply fixed_sound| apply fixed_progress]; assumption.
- destruct HK as (-> & ->).
split; [|split]; [apply remap_complete| apply remap_sound| apply remap_progress]; assumption.
- destruct Hns.
Qed.

Lemma munmap_nodeA : forall addr len ms mo,
at_nodeA L segs (NMunmap addr len) (msview L mo ms) -> m_halted mo = None -> cinvA L ms mo -> nsafeA L (NMunmap addr len) mo ->
(forall evs X, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw L (NMunmap addr len) mo rsp mo' evs /\ cinvA L ms' mo' /\ m_halted mo' = None)
/\ (forall rsp mo' evs, nstep_raw L (NMunmap addr len) mo rsp mo' evs ->
exists ms' mo2 rsp2, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp2 /\
nstep_raw L (NMunmap addr len) mo rsp2 mo2 evs /\ msim mo' mo2 /\ rvarA (NMunmap addr len) rsp rsp2 /\ m_halted mo2 = None)
/\ (exists rsp mo' evs, nstep_raw L (NMunmap addr len) mo rsp mo' evs).
Proof.
intros addr len ms mo [Hat Hss] Hh HC Hns.
assert (Hat' : at_node segs (NMunmap addr len) ms) by exact Hat. unfold nsafeA in Hns.
split; [|split]; [eapply munmap_complete| eapply munmap_sound| eapply munmap_progress]; eassumption.
Qed.

Theorem nodesA_sound :
node_soundA node segs L (at_nodeA L segs) (nstep_raw L) nexit_raw (nsafeA L) (xinvA L) is_spinA rvarA (jsome L).
Proof.
constructor.
-  intros n msr Hsp Hat. destruct n; try discriminate. exact Hat.
-  intros n Hsp. destruct n; try discriminate. split; [intros mo rsp mo' evs H; exact H| intros mo c mo' H; exact H].
-  intros n ms mo evs X Hsp Hat Hh HC Hns Hst.
destruct (file_node_dec n) as [Hf|Hnf]; [left; exact (proj1 (file_nodeA n ms mo Hf Hat Hh HC) evs X Hst)|].
destruct n; try (exfalso; exact (Hnf I)); try discriminate; try (destruct Hat; fail); try (destruct Hns; fail).
+ right. apply (exit_completeA code ms mo evs X Hat Hh Hst).
+ left. apply (proj1 (mmap_nodeA _ _ _ _ ms mo Hat Hh HC Hns)). exact Hst.
+ left. apply (proj1 (munmap_nodeA _ _ ms mo Hat Hh HC Hns)). exact Hst.
-  intros n ms mo rsp mo' evs Hsp Hat Hh HC Hns Hr.
destruct (file_node_dec n) as [Hf|Hnf]; [exact (proj1 (proj2 (file_nodeA n ms mo Hf Hat Hh HC)) rsp mo' evs Hr)|].
destruct n; try (exfalso; exact (Hnf I)); try discriminate; try (destruct Hat; fail); try (destruct Hr; fail).
+ apply (proj1 (proj2 (mmap_nodeA _ _ _ _ ms mo Hat Hh HC Hns))). exact Hr.
+ apply (proj1 (proj2 (munmap_nodeA _ _ ms mo Hat Hh HC Hns))). exact Hr.
-  intros n ms mo code mo' Hsp Hat Hh HC Hns Hx.
destruct n; try (destruct Hx; fail). apply (exit_soundA _ ms mo code mo' Hat Hh Hx).
-  intros n ms mo Hsp Hat Hh HC Hns.
destruct (file_node_dec n) as [Hf|Hnf]; [left; exact (proj2 (proj2 (file_nodeA n ms mo Hf Hat Hh HC)))|].
destruct n; try (exfalso; exact (Hnf I)); try discriminate; try (destruct Hat; fail); try (destruct Hns; fail).
+ right. exists (exit_code code), (with_halted (exit_code code) mo). split; reflexivity.
+ left. apply (proj2 (proj2 (mmap_nodeA _ _ _ _ ms mo Hat Hh HC Hns))).
+ left. apply (proj2 (proj2 (munmap_nodeA _ _ ms mo Hat Hh HC Hns))).
-  intros n moA moB rsp mo' evs Hs H. apply (nstep_raw_msim n moA moB rsp mo' evs Hs H).
-  intros n moA moB code mo' Hs H. apply (nexit_raw_msim n moA moB code mo' Hs H).
-  intros mo mo' Hd HX. eapply xinvA_drift; eassumption.
-  intros n mo mo' Hd H. eapply nsafeA_drift; eassumption.
Qed.

End Sound.

