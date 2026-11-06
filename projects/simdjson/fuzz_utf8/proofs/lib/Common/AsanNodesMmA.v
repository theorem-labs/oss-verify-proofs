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
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes AllocSim AsanAcct AsanAcctShape AsanPlacement BackingAlgebra MmapSim RefNodes. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import NoReserve.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanNodesIface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesLibE. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesMmN.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesMmLib AsanCeil.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma if_none_some {T : Type} (b : bool) (X : option T) (c : T) :
  (if b then None else X) = Some c -> X = Some c /\ b = false.
Proof. destruct b; [discriminate | auto]. Qed.

Section Nodes.
Context {fx : FPState}.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Hypothesis NX0_min : APS.nx0_min_ok nx0.   (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis argH_sp : forall E M (a : word), SINV E M -> argH E a = true -> APS.uE E e_sp0 <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis SINV_sp : forall E M, SINV E M -> sp_window_lo <= APS.uE E e_sp0 <= sp_window_hi.
Hypothesis HULL_tight : hull_tight_b (segments_reserved SEGS) (img_lo A) (img_hi A) = true /\ img_lo A < img_hi A.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

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
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 NX0_min LIMIT SINV argH argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_high argH_sp FS0 0%nat.   (* [comment removed for export] *)
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
Let budget_slack := AsanNodesMmLib.budget_slack SEGS A LIMIT SINV argH FS0 RES_len HULL_ok HULL_tight.
Let find_containing_sound := AsanNodesMmLib.find_containing_sound SEGS A RES_len.
Let fixed_args_sound := AsanNodesMmLib.fixed_args_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok HULL_tight.
Let fixed_cs1 := AsanNodesMmLib.fixed_cs1 A.
Let gap_ok_sound := AsanNodesMmLib.gap_ok_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok HULL_tight.
Let gap_ok_available := AsanNodesMmLib.gap_ok_available SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok HULL_tight.
Let gap_weight_eq := AsanNodesMmLib.gap_weight_eq SEGS A RES_len.
Let grant_cs1_ok := AsanNodesMmLib.grant_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_frame argH_sp SINV_sp HULL_tight.
Let grant_eager_le := AsanNodesMmLib.grant_eager_le SEGS A RES_len HULL_ok HULL_tight.
Let grant_keep_apart := AsanNodesMmLib.grant_keep_apart SEGS A RES_len HULL_ok HULL_tight.
Let grant_new_facts := AsanNodesMmLib.grant_new_facts SEGS A LIMIT SINV argH FS0 RES_len HULL_ok argH_sp HULL_tight.
Let grant_vis_add := AsanNodesMmLib.grant_vis_add SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high argH_sp HULL_tight.
Let hid_grant_out2 := AsanNodesMmLib.hid_grant_out2 SEGS A argH RES_len HULL_ok.
Let mmap_win_sem := AsanNodesMmLib.mmap_win_sem SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok HULL_tight.
Let grant_wf := AsanNodesMmLib.grant_wf SEGS A RES_len.
Let region_free_hull := AsanNodesMmLib.region_free_hull SEGS A RES_len HULL_ok HULL_tight.   (* [comment removed for export] *)
Let in_allow_ext := AsanNodesMmLib.in_allow_ext A.
Let inside_maps_apart := AsanNodesMmLib.inside_maps_apart SEGS A RES_len HULL_ok HULL_tight.
Let kimg_in_hull_cons2 := AsanNodesMmLib.kimg_in_hull_cons2 SEGS A HULL_ok SHADOW_ok HULL_tight.
Let kimg_in_hull_pure := AsanNodesMmLib.kimg_in_hull_pure A.
Let kmem_ok := AsanNodesMmLib.kmem_ok SEGS A RES_len HULL_ok HULL_tight.
Let kn_grant_filter_ok := AsanNodesMmLib.kn_grant_filter_ok SEGS A RES_len HULL_ok HULL_tight.
Let kn_rezero_clip_ok := AsanNodesMmLib.kn_rezero_clip_ok SEGS A RES_len HULL_ok HULL_tight.
Let kn_rezero_hull_ok := AsanNodesMmLib.kn_rezero_hull_ok SEGS A RES_len HULL_ok HULL_tight.
Let kn_rezero_ok_gen := AsanNodesMmLib.kn_rezero_ok_gen SEGS A RES_len HULL_ok HULL_tight.
Let kn_unfill_clip_ok := AsanNodesMmLib.kn_unfill_clip_ok SEGS A RES_len HULL_ok HULL_tight.
Let maps_match_disjoint := AsanNodesMmLib.maps_match_disjoint SEGS A RES_len.
Let mmap_fixed_grant_cs1 := AsanNodesMmLib.mmap_fixed_grant_cs1 SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame argH_sp SINV_sp HULL_tight.
Let mmap_fixed_old_facts := AsanNodesMmLib.mmap_fixed_old_facts SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok HULL_tight.
Let fixed_pre := AsanNodesMmLib.fixed_pre SEGS A LIMIT SINV argH FS0 RES_len HULL_ok HULL_tight.
Let mmap_len_sound := AsanNodesMmLib.mmap_len_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok HULL_tight.
Let overlap_sum_contained := AsanNodesMmLib.overlap_sum_contained SEGS A RES_len HULL_ok HULL_tight.
Let page_aligned_sound := AsanNodesMmLib.page_aligned_sound SEGS A RES_len.
Let refuse_cont := AsanNodesMmLib.refuse_cont .
Let refuse_ok := AsanNodesMmLib.refuse_ok SEGS A LIMIT SINV argH FS0 RES_len SINV_frame.
Let region_free_of_apart := AsanNodesMmLib.region_free_of_apart SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok HULL_tight.
Let regs_ok_regupd_same := AsanNodesMmLib.regs_ok_regupd_same SEGS A RES_len.
Let reserved_free_above := AsanNodesMmLib.reserved_free_above SEGS A RES_len RES_hull HULL_ok HULL_tight.
Let safe_range_apart := AsanNodesMmLib.safe_range_apart SEGS A RES_len HULL_ok HULL_tight.
Let seps_map_disjoint := AsanNodesMmLib.seps_map_disjoint SEGS A RES_len.
Let shadow_facts_new_ok := AsanNodesMmLib.shadow_facts_new_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok HULL_tight.
Let slice_args := AsanNodesMmLib.slice_args SEGS A LIMIT SINV argH FS0 RES_len RES_hull HULL_ok SINV_sp HULL_tight.
Let slice_hyps := AsanNodesMmLib.slice_hyps SEGS A LIMIT SINV argH FS0.
Let split_flat_estart := AsanNodesMmLib.split_flat_estart SEGS A RES_len HULL_ok.
Let vis_add_inv := AsanNodesMmLib.vis_add_inv A LIMIT.
Let vis_add_slice_ok := AsanNodesMmLib.vis_add_slice_ok SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high argH_sp HULL_tight.
Let vis_grant_out := AsanNodesMmLib.vis_grant_out SEGS A RES_len.
Let page_base_aligned := AsanNodesMmLib.page_base_aligned SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_MR_out := AsanNodesMmLib.sl_MR_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_bounds := AsanNodesMmLib.sl_bounds SEGS A LIMIT SINV argH FS0.
Let sl_eager := AsanNodesMmLib.sl_eager SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_in_maps := AsanNodesMmLib.sl_in_maps SEGS A LIMIT SINV argH FS0 RES_len HULL_ok HULL_tight.
Let sl_lazy_in := AsanNodesMmLib.sl_lazy_in SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_lazy_out := AsanNodesMmLib.sl_lazy_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_lohi := AsanNodesMmLib.sl_lohi SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_noacc_in := AsanNodesMmLib.sl_noacc_in SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_noacc_out := AsanNodesMmLib.sl_noacc_out SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_vis_in_E := AsanNodesMmLib.sl_vis_in_E SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_vis_in_F := AsanNodesMmLib.sl_vis_in_F SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_vis_in_G := AsanNodesMmLib.sl_vis_in_G SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_vis_out := AsanNodesMmLib.sl_vis_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let sl_wf' := AsanNodesMmLib.sl_wf' SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_sp HULL_tight.
Let slice_cs1_ok := AsanNodesMmLib.slice_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame argH_sp SINV_sp HULL_tight.
Let shadow_band_range := AsanNodesMmLib.shadow_band_range A.   (* [comment removed for export] *)
Let band_apart := AsanNodesMmLib.band_apart A.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition null_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nlo nhi : Z) : acs :=
  let v := nxt cs in
  let base := escale 4096 (EVar v) in
  add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base)
    (grant_facts A v base ne nlo (a_maps cs) ++ kn_grant_filter A (kn cs) (a_maps cs))
    (Datatypes.S v) (AM base ne kd) nhi eager (a_ylo cs).

(* [comment removed for export] *)
Lemma null_kend_ok : forall E M base ne nlo (a n : word),
  edenot E base = a -> edenot E ne = n ->
  4096 <= bv_unsigned a -> nlo <= bv_unsigned n -> bv_unsigned a + bv_unsigned n <= ATOP_MAX ->
  know_ok SEGS E M (null_kend base ne nlo).
Proof.
  intros E M base ne nlo a n Hb Hn Hlo Hnlo HaC. unfold null_kend.
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn. unfold two64 in *.
  destruct ne; try (apply Forall_nil); apply Forall_cons; try apply Forall_nil;
    cbn [kentry_ok]; unfold eadd; rewrite AX2S.mkAlu_denot; cbn [alu64 alu]; rewrite bv_add_unsigned, Hb, Hn;
    unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64)%Z;
    unfold ATOP_MAX in *; rewrite Z.mod_small by lia; lia.
Qed.
Lemma null_kend_pure : forall base ne nlo,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kend base ne nlo).
Proof. intros. unfold null_kend. destruct ne; repeat constructor. Qed.
Lemma grant_facts_pure : forall v base ne nlo ms,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (grant_facts A v base ne nlo ms).
Proof.
  intros. unfold grant_facts. apply Forall_cons; [exact I|]. apply Forall_app; split; [apply null_kend_pure|].
  apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|].
  apply Forall_app. split; [|apply Forall_app; split; [unfold kabove_band; apply Forall_nil | unfold kend_sp; apply Forall_nil]].  (* [comment removed for export] *)
  unfold kdisj_new, kdisj_new0, kdisj_band. apply Forall_app. split.
  - apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); repeat constructor.
  - destruct (shadow_band A ms) as [[? ?]|]; repeat constructor.   (* [comment removed for export] *)
Qed.

Lemma escale_4096_denot : forall E v (a : word),
  ev E v = Z_to_bv 64 (bv_unsigned a / 4096) -> bv_unsigned a mod 4096 = 0 ->
  edenot E (escale 4096 (EVar v)) = a.
Proof.
  intros E v a Hv Hal. unfold escale. rewrite mkMd_denot. cbn [edenot]. rewrite Hv.
  pose proof (u64_range a) as Ra. apply bv_eq. rewrite u_mul64.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite !u64_lit by (first [solve [try pose proof I as H; try pose proof I as H5; try pose proof I as Hal; try pose proof I as HULL_ok'; clear - H H5 Hal HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H; try pose proof I as __sat6; try pose proof I as H5; try pose proof I as Hal; try pose proof I as HULL_ok'; clear - H __sat6 H5 Hal HULL_ok'; xlia zchecker] | lia]). rewrite Z.mod_small; (first [solve [try pose proof I as H; try pose proof I as Hal; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as H5; try pose proof I as H4; clear - H Hal HULL_ok' HULL_tight H5 H4; lia] | solve [Zify.zify; try pose proof I as H; try pose proof I as Hal; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as H5; try pose proof I as H4; clear - H Hal HULL_ok' HULL_tight H5 H4; xlia zchecker] | lia]).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.


Lemma mmap_null_cs1 : forall cs kd (eager : bool) ne nlo nhi E R FULL model (a : word) model' FULL',
  CSOK E cs R FULL model ->
  mmap_len cs = Some (ne, nlo, nhi) ->
  fresh_ok nx0 cs = true -> expr_vars_lt (nxt cs) ne = true ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  (plain A = true -> kind_lazy kd = false) ->     (* [comment removed for export] *)
  no_holes (a_maps cs) = true ->      (* [comment removed for export] *)
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  grant_ok_na_pin model a nZ = true ->
  grant_post kd a n model model' -> grant_mem kd a n FULL FULL' ->
  let v := nxt cs in
  let E' := ext1 E v (Z_to_bv 64 (bv_unsigned a / 4096)) in
  let cs1 := null_cs1 cs kd eager ne nlo nhi in
  CSOK E' cs1 (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model'
  /\ edenot E' (escale 4096 (EVar v)) = a /\ edenot E' ne = n /\ bv_unsigned n = nZ
  /\ env_agree nx0 E E'
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
        in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
        /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
        /\ argH E' x = false /\ in_hull A (bv_unsigned x) = false).
Proof.
  intros cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev Hbudget Hkind Hkfog Hlazy Hnoh len nZ n Hg GPo GM v E' cs1.
  assert (Hnoholes : Forall (fun m => is_hole m = false) (a_maps cs)).
  { unfold no_holes in Hnoh. apply Forall_forall. intros m Hm. pose proof (proj1 (forallb_forall _ _) Hnoh m Hm) as X. apply negb_true_iff in X. exact X. }
  (* [comment removed for export] *)
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  pose proof Hg as Hg0.
  unfold grant_ok_na_pin in Hg. apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. fold n in Hrf. unfold page_size in Hal.
  pose proof (u64_range a) as Ra.
  assert (Htop64 : alloc_top (m_vmmaps model) + 8388608 < 2 ^ 64)
    by (unfold alloc_top, stack_max_size; pose proof (u64_range (vm_init_sp (m_vmmaps model))); lia).
  assert (Un : bv_unsigned n = nZ) by (subst n; apply u64_lit; lia).
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  (* [comment removed for export] *)
  pose proof (ext1_agree'' E v (Z_to_bv 64 (bv_unsigned a / 4096))) as Hag. fold E' in Hag.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fvis & Fbrk & Ffd & Fle). fold v in Fsr, Fkn, Fmaps, Fvis, Fbrk, Ffd, Fle.
  assert (HC' : CSOK E' cs R FULL model) by (eapply cs_ok_agree'; [exact Hag | exact Hfresh | exact HC]).
  assert (Hag0 : env_agree nx0 E E') by (eapply env_agree_le'; [exact Hag | exact Fle]).
  assert (Hv : ev E' v = Z_to_bv 64 (bv_unsigned a / 4096)) by apply ext1_at.
  assert (Hbase : edenot E' (escale 4096 (EVar v)) = a) by (apply escale_4096_denot; assumption).
  assert (HneE' : edenot E' ne = n).
  { rewrite (HneE E'); [exact Hne| |exact Hag]. symmetry. eapply edenot_agree'; [exact Hag|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  assert (HnZpos : 0 < nZ) by lia.
  (* [comment removed for export] *)
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC') as Hisp.
  pose proof (SINV_sp _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC')) as [Slo Shi]. unfold sp_window_lo, sp_window_hi in Slo, Shi.
  assert (Hsp : bv_unsigned a + nZ <= APS.uE E' e_sp0 - STK_BELOW).
  { unfold alloc_top, stack_max_size in Htop. rewrite Hisp in Htop. unfold APS.uE, STK_BELOW. lia. }
  assert (HaTop : bv_unsigned a + nZ <= ATOP_MAX) by (unfold ATOP_MAX; unfold STK_BELOW in Hsp; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (Ha4096 : 4096 <= bv_unsigned a) by (clear -Hal Hpos; lia).   (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC') as Hmaps.
  pose proof (maps_apart_of_region_free E' (a_maps cs) model a n Hmaps Hrf) as Hapart. rewrite Un in Hapart.
  pose proof (region_free_hull model a n (co_res _ _ _ _ _ _ _ _ _ _ _ HC') Hrf ltac:(lia)) as Hhull. rewrite Un in Hhull.
  pose proof (grant_new_facts E' cs R FULL model a n nZ HC' Hrf Un HnZpos Htop) as NEW.
  (* [comment removed for export] *)
  destruct (grant_cs1_ok E' cs R FULL model kd a n nZ model' FULL'
              (sr_upd (s_regs (a_ss cs)) 10 (escale 4096 (EVar v))) (regupd R (Z_to_bv 5 (Z.of_nat 10)) a)
              (grant_facts A v (escale 4096 (EVar v)) ne nlo (a_maps cs))
              (escale 4096 (EVar v)) ne nhi eager (a_ylo cs) (Datatypes.S v)
              HC' Un HnZpos HnZal Hal Htop Hrf GPo GM) as (HC1 & MROUT & MRSAME).
  - apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | lia | exact Hbase].
  - exact Hbase.
  - exact HneE'.
  - (* [comment removed for export] *)
    unfold grant_facts. apply Forall_cons; [|apply Forall_app; split; [|apply Forall_cons; [|apply Forall_cons]]].
    + (* [comment removed for export] *)
      assert (GLO : 4096 * grant_lo A (a_maps cs) nlo <= bv_unsigned a /\ 1 <= grant_lo A (a_maps cs) nlo).
      { unfold grant_lo. destruct (shadow_band A (a_maps cs)) as [[L0 L3]|] eqn:HB; [|clear -Ha4096; lia].
        destruct (Z.ltb L0 (4096 + nlo) && Z.eqb (L3 mod 4096) 0)%bool eqn:HT; [|clear -Ha4096; lia].
        apply andb_prop in HT as [HT1 HT2]. apply Z.ltb_lt in HT1. apply Z.eqb_eq in HT2.
        pose proof (shadow_band_range (a_maps cs) L0 L3 HB) as (B0 & BL & B3).
        pose proof (band_apart E' (a_maps cs) (bv_unsigned a) nZ L0 L3 Hapart HnZpos HB) as BA.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        clear -BA Ha4096 HnZ HT1 HT2 B0 BL. split; lia. }
      destruct GLO as [GLO1 GLO2]. set (glo := grant_lo A (a_maps cs) nlo) in *. clearbody glo.
      cbn [kentry_ok edenot]. rewrite Hv.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      (* [comment removed for export] *)
      rewrite u64_lit by (clear -Ra; lia). unfold ATOP_MAX in *. split; [clear -GLO1 GLO2 Ra; lia|].
      apply Z.div_le_mono; [clear -Ra; lia | clear -HaTop HnZ; lia].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + (* [comment removed for export] *)
      eapply null_kend_ok; [exact Hbase | exact HneE' | exact Ha4096 | rewrite Un; lia | rewrite Un; exact HaTop].
    + (* [comment removed for export] *)
      cbn [kentry_ok]. rewrite APS.stack_side_start. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hbase, HneE', Un.
      right. unfold STK_BELOW in Hsp |- *. lia.
    + (* [comment removed for export] *)
      cbn [kentry_ok]. rewrite (APS.hull_side_start A). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hbase, HneE', Un.
      match goal with |- ?g => idtac "F4GOAL" g end.
      rewrite u64_lit by (unfold KHI in *; lia). unfold KHI in *. lia.
    + (* [comment removed for export] *)
      apply Forall_app. split.
      2:{ apply Forall_app. split; [unfold kabove_band; apply Forall_nil | unfold kend_sp; apply Forall_nil]. }   (* [comment removed for export] *)
      unfold kdisj_new, kdisj_new0, kdisj_band. apply Forall_app. split.
      * apply Forall_flat_map. apply Forall_forall. intros m Hm.
        destruct (is_fog m) eqn:Hfm; [apply Forall_nil|].
        pose proof (Hapart m Hm Hfm) as D.
        apply Forall_cons; [|apply Forall_nil].
        cbn [kentry_ok]. rewrite APS.lit_side_start. unfold estart, elenZ. cbn [a_base a_off]. rewrite Hbase, HneE', Un. lia.
      * destruct (shadow_band A (a_maps cs)) as [[L0 L3]|] eqn:HB; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
        pose proof (shadow_band_range (a_maps cs) L0 L3 HB) as (B0 & BL & B3).
        pose proof (band_apart E' (a_maps cs) (bv_unsigned a) nZ L0 L3 Hapart HnZpos HB) as BA.
        cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Hbase, HneE', Un. unfold two64 in B3.
        rewrite !u64_lit by lia. lia.
  - exact Hkind.
  - exact Hkfog.
  - exact Hlazy.
  - lia.
  - exact Hbudget.
  - cbn [a_ylo]. lia.
  - intros m Hm Hk. exfalso. pose proof (proj1 (Forall_forall _ _) Hnoholes m Hm) as X. congruence.
  - split; [exact HC1|]. split; [exact Hbase|]. split; [exact HneE'|]. split; [exact Un|]. split; [exact Hag0|].
    intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & N3).
    split; [|auto]. rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_null_sound1 : forall cs kd (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 -> reg_lit cs 10 = Some 0 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some (if kind_lazy kd then 16418 else 34) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd)%bool = negb eager -> is_tok_kind kd = false ->
  (plain A = true -> kind_lazy kd = false) ->
  visible = negb (kind_none kd) ->
  mmap_null A nx0 LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      (forall W a, AP.mmap_win A cs' = Some W -> ws_out E' W a -> FULL' a = FULL a) ->
      (forall W a, AP.mmap_win A cs' = Some W -> ws_out E' W a -> HID E' cs' model' a = HID E cs model a) ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd eager visible cs' E R FULL model TB HC Hec H17 H10 H12 H13 H14 H15 Hkind' Hkfog Hplain Hvisible Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  pose proof Hn as Hn0.
  unfold mmap_null in Hn.
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hnoh].     (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hcond Hgap].
  apply andb_prop in Hcond as [Hfresh Hnev].
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 10 0 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_10 in R10. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ).
  destruct (gap_ok_sound E cs R FULL model nhi nZ HC Hgap ltac:(lia)) as [a0 Ha0].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  (* [comment removed for export] *)
  assert (CONT : forall (a : word) model' FULL',
            grant_ok_na_pin model a nZ = true ->
            grant_post kd a n model model' -> grant_mem kd a n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 a) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros a model' FULL' Hg GPo GM Hfs.
    destruct (mmap_null_cs1 cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev
                ltac:(intros ->; cbn in Hbud; unfold budget_ok in Hbud; apply Z.leb_le in Hbud; exact Hbud)
                Hkind' Hkfog Hplain Hnoh Hg GPo GM) as (HC1 & Hbase & HneE' & Un & Hag0 & NEW).
    fold len nZ n in HC1, HneE', Un, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    set (E' := ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))) in *.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|injection Hn as <-; reflexivity].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HK E' (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model' (conj Hag0 (ext1_agree'' E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))))).
    unfold cfg_of in HK. rewrite Hpc in HK.
    pose proof Hg as HgF. unfold grant_ok_na_pin in HgF. apply andb_prop in HgF as [HgF _]. apply andb_prop in HgF as [HgF HtopF].
    apply andb_prop in HgF as [HalF HposF].
    apply Z.eqb_eq in HalF. apply Z.ltb_lt in HposF. apply Z.leb_le in HtopF. unfold page_size in HalF.
    assert (Htop64 : alloc_top (m_vmmaps model) + 8388608 < 2 ^ 64).
    { unfold alloc_top, stack_max_size. pose proof (u64_range (vm_init_sp (m_vmmaps model))). lia. }
    assert (HCOK : CSOK E' cs' (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model').
    {
      destruct visible.
      - (* [comment removed for export] *)
        assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hvisible |- *; congruence).
        pose proof (u64_range a) as Ra.
        eapply (grant_vis_add E' (null_cs1 cs kd eager ne nlo nhi) cs' _ ne _ FULL' model' a n nZ HC1 Hn).
        + unfold null_cs1, add_entry. cbn [kn a_ss mk_ss s_know]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
          apply kimg_in_hull_pure. apply grant_facts_pure.
        + exact Hbase.
        + exact HneE'.
        + exact Un.
        + lia.
        + lia.
        + intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & _). rewrite (gp_noacc _ _ _ _ _ GPo), Hrw. auto.
        + intros x Hx. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity.
      - injection Hn as <-. exact HC1. }
    (* [comment removed for export] *)
    assert (HmsF : exists ms, a_maps cs' = AM (escale 4096 (EVar (nxt cs))) ne kd :: ms
                             /\ (a_vis cs' = a_vis cs \/ a_vis cs' = (escale 4096 (EVar (nxt cs)), ne) :: a_vis cs)).
    { destruct visible.
      - destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & E2). rewrite E2. unfold null_cs1, add_entry. cbn [a_maps a_vis].
        eexists; split; [reflexivity | right; reflexivity].
      - injection Hn as E2. rewrite <- E2. unfold null_cs1, add_entry. cbn [a_maps a_vis]. eexists; split; [reflexivity | left; reflexivity]. }
    destruct HmsF as (msF & HmsF & HvisF).
    destruct (fresh_ok_parts nx0 cs Hfresh) as (_ & _ & _ & FallowF & _ & _ & FleF).
    assert (SEMF : forall W x, AP.mmap_win A cs' = Some W -> ws_out E' W x ->
              (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)
              /\ (plain A = false -> ~ (sh_lo A E' (escale 4096 (EVar (nxt cs)), ne) <= bv_unsigned x < sh_hi A E' (escale 4096 (EVar (nxt cs)), ne)))).
    { intros W x HW Hx. eapply mmap_win_sem; [exact HW | exact HmsF | exact HCOK | exact Hbase | exact HneE' | exact HalF | exact Hx]. }
    apply HK; [exact HCOK | exact Hfs | |].
    - intros W x HW Hx. pose proof (proj1 (SEMF W x HW Hx)) as HH. apply (proj1 GM). first [exact HH | rewrite Un in HH; exact HH | rewrite <- Un in HH; exact HH].
    - intros W x HW Hx. destruct (SEMF W x HW Hx) as [Hout Hsh].
      assert (HAG : HID E' cs model = HID E cs model) by (apply (hid_agree' (nxt cs) E E' cs model (ext1_agree'' E (nxt cs) _) FleF FallowF)).
      rewrite <- HAG.
      eapply hid_grant_out2; [exact GPo | exact HvisF | exact Hbase | rewrite HneE'; lia | try rewrite Un; lia | exact HalF
                             | try rewrite Un; exact HnZal | | first [exact Hout | rewrite Un in Hout; exact Hout | rewrite <- Un in Hout; exact Hout] | exact Hsh].
      intros Hpl. split; [exact (co_plain _ _ _ _ _ _ _ _ _ _ _ HC Hpl) | exact (Hplain Hpl)]. }
  (* [comment removed for export] *)
  assert (LAZY : forall a mdl, grant_ok_na_pin model a nZ = true ->
            m_vm_lazy (vm_add_lazy a n mdl) = (a, n) :: m_vm_lazy mdl).
  { intros a mdl Hg. rewrite m_vm_lazy_vm_add_lazy.
    unfold grant_ok_na_pin in Hg. apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hg HtopF]. apply andb_prop in Hg as [HalF HposF].
    apply Z.eqb_eq in HalF. apply Z.ltb_lt in HposF. apply Z.leb_le in HtopF. unfold page_size in HalF.
    pose proof (alloc_top_lt (m_vmmaps model)) as ATL. unfold two_pow_64 in ATL.
    assert (Un : bv_unsigned n = nZ) by (unfold n; apply u64_lit; lia).
    rewrite lazy_interior_fresh; [reflexivity | exact HalF | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; lia]. }
  (* [comment removed for export] *)
  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; try discriminate Hkfog.
  - (* [comment removed for export] *)
    destruct eager; [|discriminate].
    eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
    + exists a0. split; [exact Ha0|]. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22.
      apply Z.leb_le. cbn in Hbud. eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + intros a Hg _. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
    + exists a0. split; [exact Ha0|]. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_4022. reflexivity.
    + intros a Hg _. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; try reflexivity. rewrite (LAZY a _ Hg). reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_mmap_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
    + exists a0. exact Ha0.
    + intros a Hg. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_mmap_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
    + exists a0. exact Ha0.
    + intros a Hg. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; try reflexivity. rewrite (LAZY a _ Hg). reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fl_ok (kd : mkind) (fl : Z) : Prop :=
  mmap_noreserve_b (Z_to_bv 64 fl) = kind_lazy kd
  /\ (mmap_flags_core (Z_to_bv 64 fl) = 50 \/ mmap_noreplace_flags_b (Z_to_bv 64 fl) = true).

Lemma mmap_fixed_grant_sound1 : forall cs ms0 b off ne nlo nhi kd (fl : Z) (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some fl -> fl_ok kd fl -> 0 <= fl < two64 ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd)%bool = negb eager -> is_tok_kind kd = false ->
  (plain A = true -> kind_lazy kd = false) ->
  visible = eager ->
  fixed_args A cs = Some (b, off, ne, nlo, nhi) ->
  (negb eager || budget_ok LIMIT cs nhi)%bool = true ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (edenot E (reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= uE E (am_base m)
     \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (edenot E (reg cs 10))) ->
  mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      (forall W a, AP.mmap_win A cs' = Some W -> ws_out E' W a -> FULL' a = FULL a) ->
      (forall W a, AP.mmap_win A cs' = Some W -> ws_out E' W a -> HID E' cs' model' a = HID E cs model a) ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs ms0 b off ne nlo nhi kd fl eager visible cs' E R FULL model TB HC Hec H17 H12 H13 [Hnrs Hflk] Hflr H14 H15 Hkind Hkfog Hplain Hvisible HFA Hbud HC0 Hrf Hholes Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  assert (Hbudget : eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
  { intros ->. cbn in Hbud. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }
  unfold mmap_fixed_grant in Hn.
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (fixed_args_sound E cs R FULL model b off ne nlo nhi HC HFA) as (Hsp & HML & _).
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & _).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & Wsp0).
  (* [comment removed for export] *)
  destruct (fixed_pre cs b off ne nlo nhi E R FULL model HC HFA)
    as (HneE & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold len nZ n addr in HneE, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaK : bv_unsigned addr + nZ <= CEIL) by lia.   (* [comment removed for export] *)
  rewrite <- bv5_10 in R10.
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_ceiling) by (rewrite CEIL_eq; fold nZ; lia).
  (* [comment removed for export] *)
  assert (CONT : forall model' FULL',
            grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' GPo GM Hfs.
    destruct (mmap_fixed_grant_cs1 cs ms0 kd eager b off ne nlo nhi E R FULL model model' FULL' HC HFA HC0 Hrf Hholes Hbudget Hkind Hkfog Hplain GPo GM) as (HC1 & NEW).
    fold len nZ n addr in HC1, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|injection Hn as <-; reflexivity].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HK. rewrite Hpc in HK.
    assert (HCOK : CSOK E cs' (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model').
    {
      destruct visible.
      - (* [comment removed for export] *)
        subst eager. assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hkind |- *; congruence).
        pose proof (u64_range addr) as Ra.
        eapply (vis_add_sound'); [exact Hn | exact HC1 |].
        destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs2).
        apply Forall_app. split.
        + (* [comment removed for export] *)
          assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat, elenZ; rewrite Hest, HneE, Un; unfold CEIL in HaK; lia).
          assert (BYTE : forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
                    MR E cs' model' FULL' x = Some (Z_to_bv 8 0)).
          { intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
            unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1. rewrite (gp_noacc _ _ _ _ _ GPo), Hrw, N2. cbn [negb andb].
            assert (Hallow : in_allow A E cs' (bv_unsigned x) = true).
            { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd with_maps0]. unfold uE. fold addr. rewrite HneE, Un.
              rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
            rewrite Hallow, !orb_true_r. cbn [negb]. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity. }
          constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; unfold elenZ; rewrite Hest, HneE, Un.
          * intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
            apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in HaK; lia); unfold CEIL in HaK; lia|].
            intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in HaK; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
          * intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in HaK; lia). lia.
        + (* [comment removed for export] *)
          pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
          eapply know_ok_unhide'; [apply H_off_segments_cs' | | | | exact HK1].
          * unfold fixed_cs1, add_entry. cbn [kn a_ss mk_ss s_know with_maps0]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
            destruct kd; cbn [mkind_eqb]; try (apply kimg_in_hull_pure; apply Forall_nil).
            apply kimg_in_hull_pure. apply Forall_flat_map. apply Forall_forall. intros p _. unfold shadow_facts_in.
            destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn]. destruct (find_containing_j _ _ _ _ _ _); [|apply Forall_nil].
            apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
          * intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
          * intros y Hy. apply hid_hull'. exact Hy.
      - injection Hn as <-. exact HC1. }
    (* [comment removed for export] *)
    assert (HmsF : exists ms, a_maps cs' = AM (reg cs 10) ne kd :: ms
                             /\ (a_vis cs' = a_vis cs \/ a_vis cs' = (reg cs 10, ne) :: a_vis cs)).
    { destruct visible.
      - destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & E2). rewrite E2. unfold add_entry, with_maps0. cbn [a_maps a_vis].
        eexists; split; [reflexivity | right; reflexivity].
      - injection Hn as E2. rewrite <- E2. unfold add_entry, with_maps0. cbn [a_maps a_vis]. eexists; split; [reflexivity | left; reflexivity]. }
    destruct HmsF as (msF & HmsF & HvisF).
    assert (SEMF : forall W x, AP.mmap_win A cs' = Some W -> ws_out E W x ->
              (bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= bv_unsigned x)
              /\ (plain A = false -> ~ (sh_lo A E (reg cs 10, ne) <= bv_unsigned x < sh_hi A E (reg cs 10, ne)))).
    { intros W x HW Hx. eapply mmap_win_sem; [exact HW | exact HmsF | exact HCOK | reflexivity | exact HneE | exact Hal | exact Hx]. }
    apply HK; [exact HCOK | exact Hfs | |].
    - intros W x HW Hx. pose proof (proj1 (SEMF W x HW Hx)) as HH. apply (proj1 GM). first [exact HH | rewrite Un in HH; exact HH | rewrite <- Un in HH; exact HH].
    - intros W x HW Hx. destruct (SEMF W x HW Hx) as [Hout Hsh].
      eapply hid_grant_out2; [exact GPo | exact HvisF | reflexivity | rewrite HneE; lia | try rewrite Un; lia | exact Hal
                             | try rewrite Un; exact HnZal | | first [exact Hout | rewrite Un in Hout; exact Hout | rewrite <- Un in Hout; exact Hout] | exact Hsh].
      intros Hpl. split; [exact (co_plain _ _ _ _ _ _ _ _ _ _ _ HC Hpl) | exact (Hplain Hpl)]. }
  (* [comment removed for export] *)
  assert (LAZY : forall mdl, m_vm_lazy (vm_add_lazy addr n mdl) = (addr, n) :: m_vm_lazy mdl).
  { intros mdl. rewrite m_vm_lazy_vm_add_lazy.
    rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia]. }
  assert (GPeager : kind_lazy kd = false -> forall mdl, with_mmap_backing (Z_to_bv 64 fl) addr n mdl = mdl).
  { intros Hk mdl. apply with_mmap_backing_plain. rewrite Hnrs, Hk. reflexivity. }
  assert (GPlazy : kind_lazy kd = true -> forall mdl, with_mmap_backing (Z_to_bv 64 fl) addr n mdl = vm_add_lazy addr n mdl).
  { intros Hk mdl. apply with_mmap_backing_lazy. rewrite Hnrs, Hk. reflexivity. }
  (* [comment removed for export] *)
  unfold cfg_of.
  assert (RW : kind_none kd = false ->
     srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) (zfill addr n FULL) (seg_rom SEGS))
                          (with_mmap_backing (Z_to_bv 64 fl) addr n (mmap_model addr n model))) TB ->
     mmap_noreserve_backed_ok (Z_to_bv 64 fl) model nZ = true ->
     srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) model) TB).
  { intros Hk HB Hbk. rewrite Hk in R12.
    destruct Hflk as [Hcore|Hnrp].
    - exact (srz_mmap_fixed_rw_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 fl) TB
               Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Wsp0 R12 R13 Hcore R14 R15 Hrf Hbk HB).
    - exact (srz_mmap_noreplace_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 fl) TB
               Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Wsp0 R12 R13 Hnrp R14 R15 Hrf Hbk HB). }
  assert (NONE : kind_none kd = true ->
     srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) (unfill addr n FULL) (seg_rom SEGS))
                          (with_mmap_backing (Z_to_bv 64 fl) addr n (noaccess_model addr n model))) TB ->
     srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) model) TB).
  { intros Hk HB. rewrite Hk in R12.
    destruct Hflk as [Hcore|Hnrp].
    - exact (srz_mmap_fixed_none_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 fl) TB
               Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Wsp0 R12 R13 Hcore R14 R15 Hrf HB).
    - exact (srz_mmap_noreplace_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 fl) TB
               Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Wsp0 R12 R13 Hnrp R14 R15 Hrf HB). }
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
  - (* [comment removed for export] *)
    destruct eager; [|discriminate]. apply RW; [reflexivity | | ].
    + rewrite (GPeager eq_refl). apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + unfold mmap_noreserve_backed_ok. rewrite Hnrs. apply Z.leb_le. cbn in Hbud.
      eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
  - (* [comment removed for export] *)
    destruct eager; [discriminate|]. apply RW; [reflexivity | | ].
    + rewrite (GPlazy eq_refl). fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity. rewrite LAZY. reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + unfold mmap_noreserve_backed_ok. rewrite Hnrs. reflexivity.
  - (* [comment removed for export] *)
    destruct eager; [discriminate|]. apply NONE; [reflexivity |].
    rewrite (GPeager eq_refl). apply CONT; [constructor; reflexivity | | reflexivity].
    split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|]. apply NONE; [reflexivity |].
    rewrite (GPlazy eq_refl). fold nZ. fold n. apply CONT; [| | reflexivity].
    * constructor; try reflexivity. rewrite LAZY. reflexivity.
    * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Lemma mmap_fixed_free_sound1 : forall cs kd (fl : Z) (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some fl -> fl_ok kd fl -> 0 <= fl < two64 ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd)%bool = negb eager -> is_tok_kind kd = false ->
  (plain A = true -> kind_lazy kd = false) ->
  visible = eager ->
  mmap_fixed_free A LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      (forall W a, AP.mmap_win A cs' = Some W -> ws_out E' W a -> FULL' a = FULL a) ->
      (forall W a, AP.mmap_win A cs' = Some W -> ws_out E' W a -> HID E' cs' model' a = HID E cs model a) ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd fl eager visible cs' E R FULL model TB HC Hec H17 H12 H13 Hflok Hfl H14 H15 Hkind Hkfog Hplain Hvisible Hn HK.
  unfold mmap_fixed_free in Hn.
  destruct (fixed_args A cs) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
  apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hnf Hall].
  destruct (mmap_fixed_old_facts cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall) as (HC0 & Hrf & Hholes).
  eapply (mmap_fixed_grant_sound1 cs (a_maps cs) b off ne nlo nhi kd fl eager visible cs' E R FULL model TB
            HC Hec H17 H12 H13 Hflok Hfl H14 H15 Hkind Hkfog Hplain Hvisible HFA Hbud HC0 Hrf Hholes Hn HK).
Qed.

(* [comment removed for export] *)
Lemma kn_unfill_clip_ok_hd : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  know_ok SEGS E M' (kimg_clip A (kn_unfill k b off ne)).
Proof.
  intros E M M' k b off ne HK Hhull Hout.
  pose proof (kimg_clip_in_hull' (kn_unfill k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. unfold kn_unfill in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  apply orb_prop in Hkeep as [Himg|Hap].
  - destruct K; try discriminate. unfold kfoot_apart, kfoot. cbn in HKh. lia.
  - rewrite APS.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [exact HK | exact Hap].
Qed.

Lemma node_mprotect_sound1 : forall cs cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  node_mprotect A LIMIT cs = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs cs' E R FULL model TB HC Hec Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  rewrite node_mprotect_eq in Hn. (* [comment removed for export] *) unfold node_mprotect_ref in Hn.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 12) as [z12|] eqn:H12.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (fixed_args_in cs) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.   (* [comment removed for export] *)
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 226 /\ z12 = 3).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  destruct Hz as [-> ->].
  destruct (find_containing (kn cs) (a_maps cs) [KNONE; KNONELAZY] b off ne) as [m|] eqn:Hfind; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [Hbud _].   (* [comment removed for export] *)
  unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
  (* [comment removed for export] *)
  assert (ATOP : alloc_top (m_vmmaps model) <= ATOP_MAX /\ forall x : word, bv_unsigned x < alloc_top (m_vmmaps model) -> argH E x = false).
  { pose proof (SINV_sp _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as [_ Shi]. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as I.
    unfold alloc_top, stack_max_size, ATOP_MAX. rewrite I. unfold APS.uE, sp_window_hi in Shi. split; [lia|].
    intros x Hx. destruct (argH E x) eqn:Ea; [|reflexivity]. exfalso.
    pose proof (argH_sp _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) Ea) as SP. unfold APS.uE in SP. lia. }
  destruct ATOP as [ATOP ARGH].
  destruct (reg_lit_sound' E cs R FULL model 17 226 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 3 HC ltac:(lia) H12) as [R12 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12.
  destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (u64_range addr) as Ra.
  assert (Hkind' : am_kind m = KNONE \/ am_kind m = KNONELAZY) by (cbn in Hkind; destruct Hkind as [<-|[<-|[]]]; auto).
  (* [comment removed for export] *)
  assert (Hna : map_contains (vm_noaccess (m_vmmaps model)) addr n = true).
  { pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hkind') as X.
    eapply map_contains_intro; [exact X | exact Hin1 | rewrite Un; exact Hin2]. }
  unfold cfg_of.
  eapply (srz_mprotect1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len TB Hf He Hhalt R17 R10 Hal R11 ltac:(lia)).
  - unfold two_pow_64. fold nZ.
    assert (Htop64 : alloc_top (m_vmmaps model) + 8388608 < 2 ^ 64)
      by (unfold alloc_top, stack_max_size; pose proof (u64_range (vm_init_sp (m_vmmaps model))); lia).
    lia.
  - exact R12.
  - exact Hna.
  - exact Hmc.
  - apply mprotect_budget_ok_intro_gen; [exact Hwf|]. pose proof (budget_slack E cs R FULL model nhi HC ltac:(unfold budget_ok; apply Z.leb_le; exact Hbud)). fold nZ n. lia.
  - fold nZ. fold n.
    set (model' := mprotect_model addr n model). set (FULL' := zfill addr n FULL).
    assert (SPo : slice_post SlM addr n model model') by (constructor; reflexivity).
    assert (SM : slice_mem SlM addr n FULL FULL').
    { split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx]. }
    assert (SH : slice_hyps E cs R FULL model SlM m addr n nZ model' FULL').
    { constructor; try assumption; intros HH; [discriminate HH|]. intros Hk. rewrite Hk in Hkind'. destruct Hkind'; discriminate. }
    rewrite (v_addi_pc (pc cs) Hp0 Hp4).
    destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs').
    assert (Hpc : pc cs' = pc cs + 4) by (rewrite Ecs'; reflexivity).
    specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HK. rewrite Hpc, <- bv5_10 in HK. apply HK; [|reflexivity]. clear HK.
    assert (Hregs' : regs_ok E (sr_upd (s_regs (a_ss cs)) 10 (ELit 0)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0))).
    { apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | reflexivity]. }
    assert (MROUT := fun x => sl_MR_out E cs R FULL model SlM m addr n nZ model' FULL' SH cs x eq_refl).
    assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
                      MR E cs model' FULL' x = MR E cs model FULL x).
    { intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
    assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
    { eapply kn_unfill_clip_ok_hd; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; lia | exact MROUT']. }
    pose proof (slice_cs1_ok E cs R FULL model SlM m addr n nZ model' FULL' SH _ _ _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud) ltac:(intros _; exact I)) as HC1.
    cbn [sl_charge] in HC1.
    eapply (vis_add_slice_ok E _ cs' (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
    + exact Hn.
    + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
    + reflexivity.
    + exact Hest.
    + unfold elenZ. rewrite Hne. exact Un.
    + lia.
    + lia.
    + lia.
    + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
      split; [exact (sl_in_maps E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [exact (sl_noacc_in E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [apply ARGH; lia|].
      rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gate_sound : forall cs prot flags isnull,
  mmap_gate cs = Some (prot, flags, isnull) ->
  reg_lit cs 17 = Some 222 /\ reg_lit cs 12 = Some prot /\ reg_lit cs 13 = Some flags
  /\ reg_lit cs 14 = Some (two64 - 1) /\ reg_lit cs 15 = Some 0
  /\ (isnull = true -> reg_lit cs 10 = Some 0).
Proof.
  intros cs prot flags isnull Hg. unfold mmap_gate in Hg.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 12) as [p|] eqn:H12.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 13) as [f|] eqn:H13.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 14) as [m1|] eqn:H14.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 15) as [z15|] eqn:H15.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 222 /\ z15 = 0).
  { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  destruct Hz as [-> ->]. cbn iota in Hg.
  match type of Hg with (if negb ?c then None else _) = _ => destruct c eqn:Hm1; [|discriminate] end. cbn [negb] in Hg.
  apply Z.eqb_eq in Hm1. subst m1. injection Hg as <- <- <-.
  repeat split; try reflexivity.
  destruct (reg_lit cs 10) as [[|p10|p10]|]; intros H; try discriminate H. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem node_mmap_sound : node1_stmtWP SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmap A nx0 LIMIT) (AP.mmap_win A).
Proof.
  intros cs csG E R FULL model TB HC Hec Hn HKB.
  unfold node_mmap in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & H10).
  rename Hn into HG.
  destruct isnull.
  - (* [comment removed for export] *)
    specialize (H10 eq_refl).
    assert (ARMS : exists kd e, prot = (if kind_none kd then 0 else 3) /\ flags = (if kind_lazy kd then 16418 else 34)
              /\ (kind_none kd || kind_lazy kd)%bool = negb e /\ is_tok_kind kd = false /\ (plain A = true -> kind_lazy kd = false)
              /\ mmap_null A nx0 LIMIT cs kd e (negb (kind_none kd)) = Some csG).
    { destruct (Sumbool.sumbool_of_bool (plain A)) as [HPL|HPL]; rewrite HPL in HG; revert HG; intros HG;
        repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate HG end;
        let arm kd e := (exists kd, e; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
                         split; [intros HH; first [reflexivity | rewrite HPL in HH; discriminate HH] | exact HG]) in
        first [ arm KRW true | arm KNONE false | arm KRWLAZY false | arm KNONELAZY false ]. }
    destruct ARMS as (kd & e & -> & -> & Hkind & Hkfog & Hplain & Hm).
    eapply (mmap_null_sound1 cs kd e (negb (kind_none kd))); eauto.
  - (* [comment removed for export] *)
    assert (ARMS : exists kd e, fl_ok kd flags /\ 0 <= flags < two64 /\ prot = (if kind_none kd then 0 else 3)
              /\ (kind_none kd || kind_lazy kd)%bool = negb e /\ is_tok_kind kd = false /\ (plain A = true -> kind_lazy kd = false)
              /\ mmap_fixed_free A LIMIT cs kd e e = Some csG).
    { destruct (Sumbool.sumbool_of_bool (plain A)) as [HPL|HPL]; rewrite HPL in HG; revert HG; intros HG;
        repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate HG end;
        let arm kd e := (exists kd, e;
                         split; [split; [vm_compute; reflexivity | first [left; vm_compute; reflexivity | right; vm_compute; reflexivity]] |];
                         split; [unfold two64; lia|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
                         split; [intros HH; first [reflexivity | rewrite HPL in HH; discriminate HH] | exact HG]) in
        first [ arm KRW true | arm KNONE false | arm KRWLAZY false | arm KNONELAZY false ]. }
    destruct ARMS as (kd & e & Hflok & Hfl & -> & Hkind & Hkfog & Hplain & Hm).
    eapply (mmap_fixed_free_sound1 cs kd flags e e); eauto.
Qed.

Theorem node_mprotect_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mprotect A LIMIT).
Proof.
  intros cs csG E R FULL model TB HC Hec Hn HKB.
  eapply node_mprotect_sound1; eauto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slarm_of (arm : fixed_in_arm) : slarm := match arm with ArmE => SlE | ArmF => SlF | ArmG => SlG end.

(* [comment removed for export] *)
Lemma eu_sub : forall E a b, bv_unsigned (edenot E b) <= bv_unsigned (edenot E a) ->
  bv_unsigned (edenot E (esub a b)) = bv_unsigned (edenot E a) - bv_unsigned (edenot E b).
Proof.
  intros E a b H. unfold esub. rewrite mkAlu_denot, u_sub64. pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)).
  apply Z.mod_small. lia.
Qed.

Lemma eu_add : forall E a b, bv_unsigned (edenot E a) + bv_unsigned (edenot E b) < 2 ^ 64 ->
  bv_unsigned (edenot E (eadd a b)) = bv_unsigned (edenot E a) + bv_unsigned (edenot E b).
Proof.
  intros E a b H. unfold eadd. rewrite mkAlu_denot, u_add64. pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)).
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma dest_cases_complete : forall E M cs ne m (lne rne : bool),
  know_ok SEGS E M (kn cs) ->
  bv_unsigned (edenot E (am_base m)) <= bv_unsigned (edenot E (reg cs 10)) ->
  bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  lne = (bv_unsigned (edenot E (am_base m)) <? bv_unsigned (edenot E (reg cs 10))) ->
  rne = (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <? bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))) ->
  In (lne, rne) (dest_cases cs ne m).
Proof.
  intros E M cs ne m lne rne HK Hin1 Hin2 Hl Hr. unfold dest_cases.
  set (a := reg cs 10) in *. set (mb := am_base m) in *. set (ml := am_len m) in *.
  apply in_flat_map. exists lne. split.
  - destruct (lin_ge0 (kn cs) [(a, -1)] [(mb, 0)]) eqn:H1.
    + pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HK H1) as X. cbn [xt_den] in X. left. rewrite Hl. symmetry. apply Z.ltb_lt. lia.
    + destruct (expr_eqb a mb || lin_ge0 (kn cs) [(mb, 0)] [(a, 0)])%bool eqn:H2.
      * left. rewrite Hl. symmetry. apply Z.ltb_ge. apply orb_prop in H2 as [H2|H2].
        -- apply expr_eqb_eq in H2. rewrite H2. lia.
        -- pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HK H2) as X. cbn [xt_den] in X. lia.
      * destruct lne; [left | right; left]; reflexivity.
  - apply in_map_iff. exists rne. split; [reflexivity|].
    destruct (lin_ge0 (kn cs) [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)]) eqn:H1.
    + pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HK H1) as X. cbn [xt_den] in X. left. rewrite Hr. symmetry. apply Z.ltb_lt. lia.
    + destruct (lin_ge0 (kn cs) [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)]) eqn:H2.
      * pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HK H2) as X. cbn [xt_den] in X. left. rewrite Hr. symmetry. apply Z.ltb_ge. lia.
      * destruct rne; [left | right; left]; reflexivity.
Qed.

Lemma mmap_fixed_in_sound1 : forall cs arm b off ne nlo nhi m csO E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
  reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  fixed_in_args cs arm = Some (b, off, ne, nlo, nhi, m) ->
  mmap_fixed_in A LIMIT cs arm = Some csO ->
  (plain A = true -> match arm with ArmF => False | _ => True end) ->     (* [comment removed for export] *)
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csO R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc csO) FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs arm b off ne nlo nhi m csO E R FULL model TB HC Hec H17 H12 H13 H14 H15 HFI Hn HplainA HKB.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  (* [comment removed for export] *)
  rewrite fixed_in_args_eq in HFI. (* [comment removed for export] *) unfold fixed_in_args_ref in HFI.
  destruct (fixed_args_in cs) as [[[[[b0 off0] ne0] nlo0] nhi0]|] eqn:HFA; [|discriminate].   (* [comment removed for export] *)
  destruct (find_containing (kn cs) (a_maps cs) _ b0 off0 ne0) as [m0|] eqn:Hfind; [|discriminate].
  match type of HFI with (if ?c then _ else _) = _ => destruct c eqn:Hvars; [|discriminate] end.
  injection HFI as -> -> -> -> -> ->.
  rewrite mmap_fixed_in_eq in Hn. (* [comment removed for export] *) unfold mmap_fixed_in_ref in Hn. rewrite fixed_in_args_eq in Hn. unfold fixed_in_args_ref in Hn. rewrite HFA, Hfind, Hvars in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hbud; [|discriminate] end.
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (u64_range addr) as Ra.
  (* [comment removed for export] *)
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model)) by (fold nZ; lia).
  assert (Htop64 : alloc_top (m_vmmaps model) + 8388608 < 2 ^ 64)
    by (unfold alloc_top, stack_max_size; pose proof (u64_range (vm_init_sp (m_vmmaps model))); lia).
  (* [comment removed for export] *)
  assert (ATOP : alloc_top (m_vmmaps model) <= ATOP_MAX /\ forall x : word, bv_unsigned x < alloc_top (m_vmmaps model) -> argH E x = false).
  { pose proof (SINV_sp _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as [_ Shi]. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as I.
    unfold alloc_top, stack_max_size, ATOP_MAX. rewrite I. unfold APS.uE, sp_window_hi in Shi. split; [lia|].
    intros x Hx. destruct (argH E x) eqn:Ea; [|reflexivity]. exfalso.
    pose proof (argH_sp _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) Ea) as SP. unfold APS.uE in SP. lia. }
  destruct ATOP as [ATOP ARGH].
  assert (HF : slarm_of arm = SlF -> am_kind m = KRWLAZY).
  { intros Hs. destruct arm; try discriminate. cbn in Hkind. destruct Hkind as [<-|[]]. reflexivity. }
  assert (HnF : slarm_of arm <> SlF -> am_kind m <> KRWLAZY).
  { intros Hs Hk. destruct arm; [|exact (Hs eq_refl)|]; cbn in Hkind; rewrite Hk in Hkind; destruct Hkind as [|[|[|[]]]]; discriminate. }
  set (prot := match arm with ArmG => 0 | _ => 3 end) in *.
  set (flg := match arm with ArmF => 16434 | _ => 50 end) in *.
  assert (Hprot : prot = 0 \/ prot = 3) by (destruct arm; cbn; lia).
  assert (Hcore : mmap_flags_core (Z_to_bv 64 flg) = 50) by (destruct arm; [apply mmap_flags_core_32 | apply mmap_flags_core_4032 | apply mmap_flags_core_32]).
  (* [comment removed for export] *)
  assert (CONTB : forall model' FULL',
            slice_post (slarm_of arm) addr n model model' -> slice_mem (slarm_of arm) addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' SPo SM Hfs.
    assert (SH : slice_hyps E cs R FULL model (slarm_of arm) m addr n nZ model' FULL') by (constructor; assumption).
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    assert (Hpc : pc csO = pc cs + 4).
    { destruct arm; try (injection Hn as <-; reflexivity). destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HKB E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HKB. rewrite Hpc in HKB. apply HKB; [|exact Hfs]. clear HKB.
    assert (Hregs' : regs_ok E (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)).
    { apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | rewrite <- bv5_10; exact R10]. }
    assert (MROUT := fun x => sl_MR_out E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH cs x eq_refl).
    assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
                      MR E cs model' FULL' x = MR E cs model FULL x).
    { intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
    pose proof (slice_cs1_ok E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)) as CS1.
    assert (HplainF : plain A = true -> match slarm_of arm with SlF => False | _ => True end) by (intros HP; specialize (HplainA HP); destruct arm; exact HplainA).
    destruct arm; cbn [slarm_of sl_charge] in *.
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
      { eapply kn_unfill_clip_ok_hd; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; lia | exact MROUT']. }
      unfold budget_ok in Hbud. apply Z.leb_le in Hbud.   (* [comment removed for export] *)
      pose proof (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud) ltac:(intros _; exact I)) as HC1.
      eapply (vis_add_slice_ok E _ csO (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
      + exact Hn.
      + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
      + reflexivity.
      + exact Hest.
      + unfold elenZ. rewrite Hne. exact Un.
      + lia.
      + lia.
      + lia.
      + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
        split; [exact (sl_in_maps E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [exact (sl_noacc_in E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [apply ARGH; lia|].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_rezero (kn cs) b off ne))).
      { eapply kn_rezero_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; lia | exact MROUT' |].
        intros x Hx Hdef. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx.
        unfold Mr, mrestrict, hid in Hdef |- *.
        rewrite (sl_vis_in_F E cs R FULL model SlF m addr n nZ model' FULL' SH eq_refl cs x eq_refl Hx).
        destruct (argH E x); [exfalso; apply Hdef; reflexivity|]. cbn [orb] in *.
        destruct (VIS E cs model x); [|exfalso; apply Hdef; reflexivity]. cbn [negb].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH) HplainF).
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_cutout (kn cs) b off ne))).
      { apply know_ok_filter. eapply (APS.know_ok_cutout SEGS); [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | exact MROUT']. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH) ltac:(intros _; exact I)). }
  (* [comment removed for export] *)
  unfold cfg_of.
  assert (R12' : getr R 12 = Z_to_bv 64 prot) by (destruct arm; exact R12).
  assert (R13' : getr R 13 = Z_to_bv 64 flg) by (destruct arm; exact R13).
  eapply (srz_mmap_fixedin_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w prot (Z_to_bv 64 flg) addr len TB
            Hf He Hhalt R17 Hprot Hcore R10 Hal Hpos R11 ltac:(lia) Hce R12' R13' R14 R15 Hrfres Hmc).
  - (* [comment removed for export] *) intros Hp3. fold nZ n. destruct arm; cbn in Hp3; try discriminate Hp3; subst flg.
    + apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact Hwf |].
      pose proof (budget_slack E cs R FULL model nhi HC Hbud). lia.
    + (* [comment removed for export] *)
      apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact Hwf | exact Hal | unfold page_size; rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; lia |].
      eapply vm_backing_used_limit; [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | apply A_wf_allowA'].
  - fold nZ. fold n. destruct arm; subst prot flg; cbn [Z.eqb slarm_of] in CONTB |- *.
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_4032.
      apply CONTB; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing, m_vm_lazy_vm_forget_range.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Theorem node_mmapin_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmapin A LIMIT).
Proof.
  intros cs csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mmapin in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & _).
  destruct isnull; [discriminate|]. cbv zeta in Hn.
  assert (CASES : forall arm,
     reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
     reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
     (plain A = true -> match arm with ArmF => False | _ => True end) ->
     match fixed_in_args cs arm with
     | Some _ => mmap_fixed_in A LIMIT cs arm
     | None => None
     end = Some csb ->
     srealizes SEGS (cfg R (pc cs) FULL model) TB).
  { intros arm H12' H13' HPA Hn'.
    destruct (fixed_in_args cs arm) as [[[[[[b off] ne] nlo] nhi] m]|] eqn:HFI; [|discriminate].
    eapply (mmap_fixed_in_sound1 cs arm b off ne nlo nhi m csb); eauto. }
  (* [comment removed for export] *)
  destruct (Bool.bool_dec (plain A) true) as [EP|EP]; [|apply Bool.not_true_is_false in EP]; rewrite EP in Hn;
  destruct prot as [|p|p]; try discriminate Hn; try (repeat (destruct p as [p|p|]; try discriminate Hn));
  destruct flags as [|q|q]; try discriminate Hn; try (repeat (destruct q as [q|q|]; try discriminate Hn));
  refine (CASES _ _ _ _ Hn); first [exact H12 | exact H13 | intros HP; first [exact I | rewrite HP in EP; discriminate EP]].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kwritable_x_sound_mm : forall segs E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable_x allkn k b off n = true ->
  (forall m, Z.of_nat m <= elenZ E n ->
     store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros segs E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable_x] in H.
  destruct K; try exact (IH Hrest H).
  lazymatch type of HKK with kentry_ok _ _ _ (KWr ?a ?n) => destruct a as [wb wk]; rename n into wn end.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 (forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros HA0 HB0. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [HA0 HB0].
    unfold estart in HA0, HB0. cbn [a_base a_off] in HA0, HB0. apply CORE; lia.
Qed.
Lemma pageup_pagedown_gap_mm : forall a b, a <= b -> pageup b - pagedown a <= b - a + 8190.
Proof.
  intros a b H. unfold pageup, pagedown.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). (first [solve [try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H0; try pose proof I as H; try pose proof I as HULL_ok'; clear - H6 H5 H1 H0 H HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H0; try pose proof I as H; try pose proof I as HULL_ok'; clear - H6 H5 H1 H0 H HULL_ok'; xlia zchecker] | lia]).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma Forall_kimg_clip : forall (P : kentry -> Prop) k, Forall P k -> Forall P (kimg_clip A k).
Proof. intros P k H. apply Forall_forall. intros K HK. apply (proj1 (Forall_forall _ _) H). eapply APS.kimg_clip_incl. exact HK. Qed.

Lemma vis_foot_ok : forall E cs B n cs2 R FULL model,
  CSOK E cs R FULL model -> vis_foot A LIMIT cs B n = Some cs2 -> CSOK E cs2 R FULL model /\ pc cs2 = pc cs /\ nxt cs2 = nxt cs.
Proof.
  intros E cs B n cs2 R FULL model HC Hv. unfold vis_foot in Hv.
  destruct (Bool.bool_dec (plain A) true) as [NP|NP]; [rewrite NP in Hv; discriminate | apply Bool.not_true_is_false in NP; rewrite NP in Hv].
  destruct (split_lit B) as [bb bk] eqn:Hsplit.
  destruct (shadow_of A (kn cs) B (ELit n)) as [[sb sk] sn] eqn:Hsh.
  destruct (shadow_of A (kn cs) stack_vis_base (ELit 8)) as [[hb hk] hn] eqn:Hhd.
  destruct (xlo (kn cs) B) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) B) as [bhi|] eqn:Hbhi; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hv as <-.
  apply andb_prop in Hc as [Hc Hbudget]. apply andb_prop in Hc as [Hc Hgh]. apply andb_prop in Hc as [Hc Hvis].
  apply andb_prop in Hc as [Hc Hwit]. apply andb_prop in Hc as [Hc HflW]. apply andb_prop in Hc as [Hc Hexs].
  apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hc Hfoot]. apply andb_prop in Hc as [Hc Hvars].
  apply andb_prop in Hc as [Hc HflS]. apply andb_prop in Hc as [Hc HflB]. apply andb_prop in Hc as [Hc Hnw].
  apply andb_prop in Hc as [Hc Hblo0]. apply andb_prop in Hc as [Hc Hnmod]. apply andb_prop in Hc as [Hc Hnhi].
  apply andb_prop in Hc as [Hal Hnpos].
  apply Z.leb_le in Hbudget. apply Z.ltb_lt in Hnpos. apply Z.leb_le in Hnhi. apply Z.eqb_eq in Hnmod.
  apply Z.leb_le in Hblo0. apply Z.ltb_lt in Hnw.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xlo_sound SEGS E _ (kn cs) B blo HK Hblo) as Hblo'. pose proof (xhi_sound SEGS E _ (kn cs) B bhi HK Hbhi) as Hbhi'.
  destruct (APS.flat_x_sound SEGS E _ (kn cs) bb bk (ELit n) HK HflB) as (Fb1 & Fb2 & Fb3).
  rewrite edenot_lit, u64_lit in Fb2, Fb3 by (unfold two64 in Hnw; lia).
  pose proof (APS.u_of_split E B bb bk Hsplit ltac:(lia)) as Ub.
  pose proof (APS.pow2_divide_4096 SEGS (kn cs) B E _ HK Hal) as [qB QB].
  pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK Hfoot) as FOOT. cbn [xt_den] in FOOT.
  pose proof SHADOW_ok as SO. unfold shadow_ok in SO.
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as ISP.
  pose proof (SINV_sp _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as [Slo Shi]. unfold sp_window_lo, sp_window_hi, APS.uE in Slo, Shi.
  set (usp := bv_unsigned (edenot E e_sp0)) in *.
  set (uB := bv_unsigned (edenot E B)) in *.
  (* [comment removed for export] *)
  destruct (APS.flat_x_sound SEGS E _ (kn cs) sb sk sn HK HflS) as (Fs1 & Fs2 & Fs3).
  destruct (APS.shadow_of_denot SEGS A HS XN XE XB SHADOW_ok 0%nat E _ (kn cs) B (ELit n) sb sk sn HK Hsh) as [HS0 Usn].
  { unfold APS.uE. fold uB. unfold two64 in Hnw. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). (first [solve [try pose proof I as H15; try pose proof I as H14; try pose proof I as H0; try pose proof I as H; try pose proof I as SO; try pose proof I as Hbhi'; try pose proof I as Hnw; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H15 H14 H0 H SO Hbhi' Hnw Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H15; try pose proof I as H14; try pose proof I as H0; try pose proof I as H; try pose proof I as __sat12; try pose proof I as SO; try pose proof I as Hbhi'; try pose proof I as Hnw; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H15 H14 H0 H __sat12 SO Hbhi' Hnw Hnpos HULL_ok'; xlia zchecker] | lia]).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  { pose proof (u64_range (edenot E sn)). lia. }
  unfold APS.uE in HS0, Usn. fold uB in HS0. rewrite edenot_lit, u64_lit in Usn by (unfold two64 in Hnw; lia). unfold elenZ in Usn.
  set (S0 := estart E (SA sb sk)) in *.
  assert (Hn8 : 512 <= n / 8 /\ 8 * (n / 8) = n).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). (first [solve [try pose proof I as H19; try pose proof I as H0; try pose proof I as H; try pose proof I as Usn; try pose proof I as Ub; try pose proof I as Fb3; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnmod; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H19 H0 H Usn Ub Fb3 Fb1 Hbhi' Hnmod Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H19; try pose proof I as H0; try pose proof I as H; try pose proof I as Usn; try pose proof I as Ub; try pose proof I as Fb3; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnmod; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H19 H0 H Usn Ub Fb3 Fb1 Hbhi' Hnmod Hnpos HULL_ok'; xlia zchecker] | lia]).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  assert (TOP : S0 + n / 8 <= usp - STK_BELOW).
  { destruct (APS.lit_rwlazy_cover_sound E (a_maps cs) _ _ (S0 + n / 8 - 1) Hcov) as (m & Hmin & Hnf & Hkind & Zin).
    { rewrite HS0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). split; [(first [solve [try pose proof I as H5; try pose proof I as H4; try pose proof I as H0; try pose proof I as H; try pose proof I as Hn8; try pose proof I as QB; try pose proof I as Hbhi'; try pose proof I as Hblo'; try pose proof I as Hblo0; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H5 H4 H0 H Hn8 QB Hbhi' Hblo' Hblo0 Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H5; try pose proof I as H4; try pose proof I as H0; try pose proof I as H; try pose proof I as Hn8; try pose proof I as QB; try pose proof I as Hbhi'; try pose proof I as Hblo'; try pose proof I as Hblo0; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H5 H4 H0 H Hn8 QB Hbhi' Hblo' Hblo0 Hnpos HULL_ok'; xlia zchecker] | lia])|].
      assert (X : uB / 8 + n / 8 <= (bhi + n) / 8) by (first [solve [try pose proof I as H10; try pose proof I as H9; try pose proof I as H0; try pose proof I as H; try pose proof I as Hn8; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H10 H9 H0 H Hn8 Ub Fb1 Hbhi' Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H10; try pose proof I as H9; try pose proof I as H0; try pose proof I as H; try pose proof I as Hn8; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H10 H9 H0 H Hn8 Ub Fb1 Hbhi' Hnpos HULL_ok'; xlia zchecker] | lia]). (first [solve [try pose proof I as X; clear - X; lia] | solve [Zify.zify; try pose proof I as X; clear - X; xlia zchecker] | lia]).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (Hmv : In (APS.amap_den E m) (vm_maps (m_vmmaps model))) by (eapply APS.maps_match_In; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hmin | exact Hnf]).
    pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hmv) as (_ & _ & _ & BT & _). cbn [APS.amap_den fst snd] in BT.
    unfold alloc_top, stack_max_size in BT. rewrite ISP in BT. fold usp in BT. unfold APS.uE in Zin. unfold STK_BELOW. lia. }
  pose proof (u64_range (edenot E e_sp0)) as Rsp. fold usp in Rsp.
  (* [comment removed for export] *)
  destruct (APS.flat_x_sound SEGS E _ (kn cs) hb hk _ HK HflW) as (Fw1 & Fw2 & Fw3).
  assert (Ustk : bv_unsigned (edenot E stack_vis_base) = usp - STK_BELOW).
  { unfold stack_vis_base, eaddz. rewrite mkAlu_denot, u_add64, edenot_lit. fold usp.
    rewrite (u_lit64 (- STK_BELOW)). replace ((- STK_BELOW) mod two64) with (two64 - STK_BELOW) by reflexivity.
    unfold two64, STK_BELOW in *. rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small; lia. }
  destruct (APS.shadow_of_denot SEGS A HS XN XE XB SHADOW_ok 0%nat E _ (kn cs) stack_vis_base (ELit 8) hb hk hn HK Hhd) as [HH0 _].
  { unfold APS.uE. rewrite Ustk. unfold STK_BELOW. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). (first [solve [try pose proof I as H20; try pose proof I as H19; try pose proof I as H0; try pose proof I as H; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Shi; try pose proof I as Slo; try pose proof I as SO; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H20 H19 H0 H TOP Hn8 HS0 Shi Slo SO FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H20; try pose proof I as H19; try pose proof I as H0; try pose proof I as H; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Shi; try pose proof I as Slo; try pose proof I as SO; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H20 H19 H0 H TOP Hn8 HS0 Shi Slo SO FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok'; xlia zchecker] | lia]).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  { pose proof (u64_range (edenot E (esub (eaddz sb (sk + n / 8)) (eaddz hb hk)))). lia. }
  unfold APS.uE in HH0. rewrite Ustk in HH0. set (H0 := estart E (SA hb hk)) in *.
  destruct (kwritable_x_sound_mm SEGS E _ (kn cs) (kn cs) hb hk (esub (eaddz sb (sk + n / 8)) (eaddz hb hk)) HK HK Hwit) as (Wst & Wlo & Whi).
  fold H0 in Wst, Wlo, Whi.
  assert (Uw : elenZ E (esub (eaddz sb (sk + n / 8)) (eaddz hb hk)) = S0 + n / 8 - H0).
  { (* [comment removed for export] *)
    unfold elenZ, esub, eaddz. rewrite !mkAlu_denot, u_sub64, !u_add64, !edenot_lit.
    assert (E1 : (bv_unsigned (edenot E sb) + bv_unsigned (Z_to_bv 64 (sk + n / 8))) mod 2 ^ 64 = S0 + n / 8).
    { rewrite (u_lit64 (sk + n / 8)). unfold S0, estart; cbn [a_base a_off]. pose proof (u64_range (edenot E sb)) as Rsb. unfold two64.
      unfold S0, estart in Fs1, Fs2, TOP; cbn [a_base a_off] in Fs1, Fs2, TOP. unfold STK_BELOW in TOP.
      assert (K1 : ((sk + n / 8) mod 2 ^ 64 = sk + n / 8 /\ 0 <= sk + n / 8) \/ ((sk + n / 8) mod 2 ^ 64 = sk + n / 8 + 2 ^ 64 /\ sk + n / 8 < 0)).
      { destruct (Z_lt_le_dec (sk + n / 8) 0) as [Hn'|Hp'].
        - right. split; [|lia]. rewrite <- (Z.mod_add (sk + n / 8) 1 (2 ^ 64)) by lia. rewrite Z.mod_small; lia.
        - left. split; [|lia]. apply Z.mod_small. lia. }
      destruct K1 as [[-> Hk]|[-> Hk]].
      - rewrite Z.mod_small; lia.
      - rewrite Z.add_assoc. rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small; lia. }
    assert (E2 : (bv_unsigned (edenot E hb) + bv_unsigned (Z_to_bv 64 hk)) mod 2 ^ 64 = H0).
    { rewrite (u_lit64 hk). unfold H0, estart; cbn [a_base a_off]. pose proof (u64_range (edenot E hb)) as Rhb. unfold two64.
      unfold H0, estart in Fw1, Fw2; cbn [a_base a_off] in Fw1, Fw2.
      assert (K1 : (hk mod 2 ^ 64 = hk /\ 0 <= hk) \/ (hk mod 2 ^ 64 = hk + 2 ^ 64 /\ hk < 0)).
      { destruct (Z_lt_le_dec hk 0) as [Hn'|Hp'].
        - right. split; [|lia]. rewrite <- (Z.mod_add hk 1 (2 ^ 64)) by lia. rewrite Z.mod_small; lia.
        - left. split; [|lia]. apply Z.mod_small. lia. }
      destruct K1 as [[-> Hk]|[-> Hk]].
      - apply Z.mod_small. pose proof (u64_range (edenot E (esub (eaddz sb (sk + n / 8)) (eaddz hb hk)))). lia.
      - rewrite Z.add_assoc. rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small; [lia|].
        pose proof (u64_range (edenot E (esub (eaddz sb (sk + n / 8)) (eaddz hb hk)))). lia. }
    rewrite E1, E2.
    (* [comment removed for export] *)
    rewrite HS0, HH0. unfold STK_BELOW in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Z.mod_small; [lia|]. unfold S0, H0 in *. pose proof (u64_range (edenot E B)). fold uB in H. (first [solve [try pose proof I as H36; try pose proof I as H12; try pose proof I as H11; try pose proof I as H2; try pose proof I as H1; try pose proof I as E2; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Fs1; try pose proof I as Slo; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H36 H12 H11 H2 H1 E2 HH0 TOP Hn8 HS0 Fs1 Slo FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H36; try pose proof I as H12; try pose proof I as H11; try pose proof I as H2; try pose proof I as H1; try pose proof I as heq_S0; try pose proof I as E2; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Fs1; try pose proof I as Slo; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H36 H12 H11 H2 H1 heq_S0 E2 HH0 TOP Hn8 HS0 Fs1 Slo FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok'; xlia zchecker] | lia]).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  rewrite Uw in Wst, Whi.
  set (cs2 := ACS _ _ _ _ _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (SUB : forall a, HID E cs2 model a = true -> HID E cs model a = true).
  { intros a. apply APS.hid_cons_sub. }
  (* [comment removed for export] *)
  assert (HA : ALLOW E cs2 = APS.allow1 A E (B, ELit n) ++ ALLOW E cs) by reflexivity.
  assert (Hcost : A_bytes (APS.allow1 A E (B, ELit n)) <= vis_cost n).
  { unfold APS.allow1, vis_cost. cbn [A_bytes fst snd]. unfold APS.sh_lo, APS.sh_hi. cbn [fst snd]. unfold APS.uE. fold uB.
    rewrite edenot_lit, u64_lit by (unfold two64 in Hnw; lia).
    pose proof (pageup_pagedown_gap_mm uB (uB + n) ltac:(lia)) as G1.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof (pageup_pagedown_gap_mm (shadow_off A + uB / 8) (shadow_off A + (uB + n) / 8) ltac:((first [solve [try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H; try pose proof I as Uw; try pose proof I as Hn8; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H6 H5 H1 H Uw Hn8 QB Ub Fb1 Hbhi' Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as Uw; try pose proof I as Hn8; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H6 H5 H1 H heq_S0 heq_H0 Uw Hn8 QB Ub Fb1 Hbhi' Hnpos HULL_ok'; xlia zchecker] | lia]))) as G2.
    assert (G3 : (uB + n) / 8 - uB / 8 <= n / 8 + 1) by (first [solve [try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H; try pose proof I as Uw; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Fs1; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H6 H5 H1 H Uw HH0 TOP Hn8 HS0 Fs1 QB Ub Fb1 Hbhi' Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as Uw; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Fs1; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H6 H5 H1 H heq_S0 heq_H0 Uw HH0 TOP Hn8 HS0 Fs1 QB Ub Fb1 Hbhi' Hnpos HULL_ok'; xlia zchecker] | lia]).
    (first [solve [try pose proof I as G3; try pose proof I as G2; try pose proof I as G1; try pose proof I as Uw; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Fs1; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - G3 G2 G1 Uw TOP Hn8 Fs1 QB Ub Fb1 Hbhi' Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as G3; try pose proof I as G2; try pose proof I as G1; try pose proof I as Uw; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Fs1; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - heq_S0 heq_H0 G3 G2 G1 Uw TOP Hn8 Fs1 QB Ub Fb1 Hbhi' Hnpos HULL_ok'; xlia zchecker] | lia]).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  assert (GROWS : mem_grows (MR E cs model FULL) (MR E cs2 model FULL)).
  { intros x Hx. unfold APS.Mr, mrestrict in *. destruct (HID E cs2 model x) eqn:H2.
    - rewrite (SUB x H2) in Hx. exact Hx.
    - destruct (HID E cs model x); [exfalso; exact (Hx eq_refl) | exact Hx]. }
  assert (BYTE : forall i, 0 <= i < n / 8 -> wview SEGS (MR E cs2 model FULL) (Z_to_bv 64 (S0 + i)) <> None).
  { intros i Hi.
    set (z := S0 + i) in *.
    assert (Hz64 : 0 <= z < 2 ^ 64) by (unfold z; rewrite Usn in Fs2; lia).
    (* [comment removed for export] *)
    destruct (APS.lit_rwlazy_cover_sound E (a_maps cs) _ _ z Hcov) as (m & Hmin & Hnf & Hkind & Zin).
    { unfold z. rewrite HS0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). split; [(first [solve [try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H; try pose proof I as H30; try pose proof I as H32; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as QB; try pose proof I as Hbhi'; try pose proof I as Hblo'; try pose proof I as Hblo0; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - H6 H5 H1 H H30 H32 HH0 TOP Hn8 HS0 QB Hbhi' Hblo' Hblo0 Hnpos HULL_ok' HULL_tight; lia] | solve [Zify.zify; try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as heq_z; try pose proof I as H30; try pose proof I as H32; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as QB; try pose proof I as Hbhi'; try pose proof I as Hblo'; try pose proof I as Hblo0; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - H6 H5 H1 H heq_S0 heq_H0 heq_z H30 H32 HH0 TOP Hn8 HS0 QB Hbhi' Hblo' Hblo0 Hnpos HULL_ok' HULL_tight; xlia zchecker] | lia])|].
      assert (X : uB / 8 + n / 8 <= (bhi + n) / 8) by (first [solve [try pose proof I as H16; try pose proof I as H15; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hblo'; try pose proof I as Hblo0; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H16 H15 H11 H10 H1 H Wlo HH0 TOP Hn8 HS0 Ub Fb1 Hbhi' Hblo' Hblo0 Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H16; try pose proof I as H15; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hblo'; try pose proof I as Hblo0; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H16 H15 H11 H10 H1 H Wlo HH0 TOP Hn8 HS0 Ub Fb1 Hbhi' Hblo' Hblo0 Hnpos HULL_ok'; xlia zchecker] | lia]). (first [solve [try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as X; try pose proof I as H33; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hblo'; try pose proof I as Hblo0; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H11 H10 H1 H X H33 Wlo HH0 TOP Hn8 HS0 QB Ub Fb1 Hbhi' Hblo' Hblo0 Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as X; try pose proof I as H33; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hblo'; try pose proof I as Hblo0; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - H11 H10 H1 H heq_S0 heq_H0 X H33 Wlo HH0 TOP Hn8 HS0 QB Ub Fb1 Hbhi' Hblo' Hblo0 Hnpos HULL_ok'; xlia zchecker] | lia]).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    unfold APS.uE in Zin.
    assert (Hmv : In (APS.amap_den E m) (vm_maps (m_vmmaps model))) by (eapply APS.maps_match_In; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hmin | exact Hnf]).
    pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hmv) as (B1 & B2 & B3 & BT & BH). cbn [APS.amap_den fst snd] in B1, B2, B3, BT, BH.
    set (a := Z_to_bv 64 z). assert (Ua : bv_unsigned a = z) by (unfold a; apply u64_lit; exact Hz64).
    assert (Hm1 : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
    { eapply APS.in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hmin | exact Hnf |]. rewrite Ua. exact Zin. }
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hmin Hkind a ltac:(rewrite Ua; exact Zin)) as [Hna Hlz].
    unfold alloc_top, stack_max_size in BT. rewrite ISP in BT. fold usp in BT.
    assert (Hargh : argH E a = false).
    { destruct (argH E a) eqn:Ha; [|reflexivity]. exfalso.
      pose proof (argH_sp _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) Ha) as SP. unfold APS.uE in SP. fold usp in SP. lia. }
    assert (Hh : in_hull A (bv_unsigned a) = false).
    { unfold in_hull. rewrite Ua. apply andb_false_iff. destruct BH as [BH'|BH']; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
    assert (Hc2 : ((CEIL <=? bv_unsigned a) && (alloc_top (m_vmmaps model) <=? bv_unsigned a))%bool = false).
    { apply andb_false_iff. right. apply Z.leb_gt. rewrite Ua. unfold alloc_top, stack_max_size. rewrite ISP. fold usp. lia. }
    (* [comment removed for export] *)
    assert (Hvis2 : HID E cs2 model a = false).
    { unfold APS.hid. rewrite Hargh. cbn [orb]. apply negb_false_iff. unfold APS.vis.
      rewrite Hm1, Hna, Hlz, Hh, Hc2. cbn [negb andb orb].
      assert (Hsh2 : APS.in_sh A E cs2 (bv_unsigned a) = true).
      { unfold APS.in_sh. cbn [cs2 a_vis existsb]. unfold APS.sh_lo, APS.sh_hi. cbn [fst snd]. unfold APS.uE. fold uB.
        rewrite edenot_lit, u64_lit by (unfold two64 in Hnw; lia).
        rewrite Ua. apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
        - unfold z. rewrite HS0. lia.
        - unfold z. rewrite HS0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). (first [solve [try pose proof I as H16; try pose proof I as H15; try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H; try pose proof I as B1; try pose proof I as Zin; try pose proof I as H48; try pose proof I as Uw; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Fs1; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - H16 H15 H6 H5 H1 H B1 Zin H48 Uw Wlo HH0 TOP Hn8 HS0 Fs1 QB Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight; lia] | solve [Zify.zify; try pose proof I as H16; try pose proof I as H15; try pose proof I as H6; try pose proof I as H5; try pose proof I as H1; try pose proof I as H; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as heq_z; try pose proof I as B1; try pose proof I as Zin; try pose proof I as H48; try pose proof I as Uw; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Fs1; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - H16 H15 H6 H5 H1 H heq_S0 heq_H0 heq_z B1 Zin H48 Uw Wlo HH0 TOP Hn8 HS0 Fs1 QB Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight; xlia zchecker] | lia]).
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      unfold APS.in_allow. rewrite Hsh2. rewrite !orb_true_r. reflexivity. }
    (* [comment removed for export] *)
    destruct (HID E cs model a) eqn:Hhid.
    - (* [comment removed for export] *)
      assert (Hngh : APS.in_ghost E cs (bv_unsigned a) = false).
      { unfold APS.in_ghost. apply APS.existsb_false_forall. intros p Hp.
        pose proof (proj1 (forallb_forall _ _) Hgh p Hp) as Hpp. cbv beta in Hpp.
        destruct (split_lit (fst p)) as [pb pk] eqn:Hps. apply andb_prop in Hpp as [Hpf Hap2].
        destruct (APS.flat_x_sound SEGS E _ (kn cs) pb pk (snd p) HK Hpf) as (Fp1 & Fp2 & Fp3).
        pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
        pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap2) as A2. fold S0 in A2. unfold elenZ in A2. rewrite Usn in A2.
        unfold APS.uE. rewrite Up, Ua. unfold z. apply andb_false_iff. destruct A2 as [A2|A2]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; (first [solve [try pose proof I as A2; try pose proof I as BH; try pose proof I as B1; try pose proof I as Zin; try pose proof I as Hi; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Fs1; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as Fp3; try pose proof I as Fp1; try pose proof I as Hblo'; try pose proof I as Hblo0; clear - A2 BH B1 Zin Hi TOP Hn8 Fs1 QB Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight Fp3 Fp1 Hblo' Hblo0; lia] | solve [Zify.zify; try pose proof I as heq_z; try pose proof I as A2; try pose proof I as BH; try pose proof I as B1; try pose proof I as Zin; try pose proof I as Hi; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Fs1; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as Fp3; try pose proof I as Fp1; try pose proof I as Hblo'; try pose proof I as Hblo0; clear - heq_z A2 BH B1 Zin Hi TOP Hn8 Fs1 QB Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight Fp3 Fp1 Hblo' Hblo0; xlia zchecker] | lia]). }
      unfold wview, APS.Mr, mrestrict. rewrite Hvis2. rewrite (co_zero _ _ _ _ _ _ _ _ _ _ _ HC a Hhid Hm1 Hna Hlz Hngh). discriminate.
    - (* [comment removed for export] *)
      unfold APS.hid in Hhid. rewrite Hargh in Hhid. cbn [orb] in Hhid. apply negb_false_iff in Hhid. unfold APS.vis in Hhid.
      rewrite Hm1, Hna, Hlz, Hh, Hc2 in Hhid. cbn [negb andb orb] in Hhid.
      unfold APS.in_allow in Hhid. apply orb_prop in Hhid.
      (* [comment removed for export] *)
      assert (P : forall p, In p (a_vis cs) -> is_stack_vis p = false ->
                ((APS.uE E (fst p) <=? bv_unsigned a) && (bv_unsigned a <? APS.uE E (fst p) + APS.uE E (snd p)))%bool = false
                /\ ((APS.sh_lo A E p <=? bv_unsigned a) && (bv_unsigned a <? APS.sh_hi A E p))%bool = false).
      { intros p Hp Hns. pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hpp. cbv beta in Hpp. rewrite Hns in Hpp. cbn [orb] in Hpp.
        destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
        apply andb_prop in Hpp as [Hpp Hap2]. apply andb_prop in Hpp as [Hpf Hap1].
        destruct (APS.flat_x_sound SEGS E _ (kn cs) pb pk (snd p) HK Hpf) as (Fp1 & Fp2 & Fp3).
        pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
        pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap2) as A2. fold S0 in A2. unfold elenZ in A2. rewrite Usn in A2.
        (* [comment removed for export] *)
        assert (A1 : S0 + n / 8 <= shadow_off A + estart E (SA pb pk) / 8 \/ shadow_off A + (estart E (SA pb pk) + bv_unsigned (edenot E (snd p))) / 8 <= S0).
        { apply orb_prop in Hap1 as [Hap1|Hap1].
          - pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap1) as X. unfold elenZ in X. rewrite edenot_lit, u64_lit in X by (unfold two64 in Hnw; lia).
            rewrite <- Ub in X. fold uB in X. rewrite HS0.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
            destruct X as [X|X]; [left | right]; (first [solve [try pose proof I as H30; try pose proof I as H21; try pose proof I as H20; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as X; try pose proof I as Fp3; try pose proof I as BH; try pose proof I as B2; try pose proof I as B1; try pose proof I as Zin; try pose proof I as H47; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as SO; try pose proof I as FOOT; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as H6; try pose proof I as H5; try pose proof I as A2; try pose proof I as Fp1; try pose proof I as Fs1; try pose proof I as QB; clear - H30 H21 H20 H11 H10 H1 H X Fp3 BH B2 B1 Zin H47 Wlo HH0 TOP Hn8 HS0 SO FOOT Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight H6 H5 A2 Fp1 Fs1 QB; lia] | solve [Zify.zify; try pose proof I as H30; try pose proof I as H21; try pose proof I as H20; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as heq_z; try pose proof I as X; try pose proof I as Fp3; try pose proof I as BH; try pose proof I as B2; try pose proof I as B1; try pose proof I as Zin; try pose proof I as H47; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as SO; try pose proof I as FOOT; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as H6; try pose proof I as H5; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as A2; try pose proof I as Fp1; try pose proof I as Fs1; try pose proof I as QB; clear - H30 H21 H20 H11 H10 H1 H heq_z X Fp3 BH B2 B1 Zin H47 Wlo HH0 TOP Hn8 HS0 SO FOOT Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight H6 H5 heq_S0 heq_H0 A2 Fp1 Fs1 QB; xlia zchecker] | lia]).
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          - (* [comment removed for export] *)
            unfold below_foot in Hap1. match type of Hap1 with (if ?c then _ else _) = _ => destruct c eqn:E12; [|discriminate] end.
            apply andb_prop in E12 as [E1 E2].
            pose proof (APS.pow2_divide_4096 SEGS (kn cs) _ E _ HK E1) as [q1 Q1]. pose proof (APS.pow2_divide_4096 SEGS (kn cs) _ E _ HK E2) as [q2 Q2].
            pose proof (APS.ends_below_stack_sound SEGS E _ (kn cs) pb pk (snd p) HK Hap1 Fp1) as G3. unfold APS.uE, elenZ in G3. fold usp in G3.
            unfold estart in G3; cbn [a_base a_off] in G3.
            assert (Ue : bv_unsigned (edenot E (eaddz pb pk)) = estart E (SA pb pk)).
            { unfold eaddz. rewrite mkAlu_denot, u_add64, edenot_lit, (u_lit64 pk). unfold estart in *; cbn [a_base a_off] in *. unfold two64.
              pose proof (u64_range (edenot E pb)) as Rpb.
              assert (K1 : (pk mod 2 ^ 64 = pk /\ 0 <= pk) \/ (pk mod 2 ^ 64 = pk + 2 ^ 64 /\ pk < 0)).
              { destruct (Z_lt_le_dec pk 0) as [Hn'|Hp'].
                - right. split; [|lia]. rewrite <- (Z.mod_add pk 1 (2 ^ 64)) by lia. rewrite Z.mod_small; (first [solve [try pose proof I as Hn'; try pose proof I as Rpb; try pose proof I as Fp1; try pose proof I as B1; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Fs1; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - Hn' Rpb Fp1 B1 TOP Hn8 Fs1 Ub Fb1 Hbhi' Hnpos HULL_ok'; lia] | solve [Zify.zify; try pose proof I as Hn'; try pose proof I as Rpb; try pose proof I as Fp1; try pose proof I as B1; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Fs1; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; clear - Hn' Rpb Fp1 B1 TOP Hn8 Fs1 Ub Fb1 Hbhi' Hnpos HULL_ok'; xlia zchecker] | lia]).
                - left. split; [|lia]. apply Z.mod_small. (first [solve [try pose proof I as Hp'; try pose proof I as Rpb; try pose proof I as G3; try pose proof I as Q2; try pose proof I as Fp3; try pose proof I as BT; try pose proof I as B1; try pose proof I as Zin; try pose proof I as Hi; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Shi; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - Hp' Rpb G3 Q2 Fp3 BT B1 Zin Hi TOP Hn8 Shi FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok' HULL_tight; lia] | solve [Zify.zify; try pose proof I as heq_z; try pose proof I as Hp'; try pose proof I as Rpb; try pose proof I as G3; try pose proof I as Q2; try pose proof I as Fp3; try pose proof I as BT; try pose proof I as B1; try pose proof I as Zin; try pose proof I as Hi; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Shi; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - heq_z Hp' Rpb G3 Q2 Fp3 BT B1 Zin Hi TOP Hn8 Shi FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok' HULL_tight; xlia zchecker] | lia]). }
              destruct K1 as [[-> Hk]|[-> Hk]]; [apply Z.mod_small; (first [solve [try pose proof I as G3; try pose proof I as Q2; try pose proof I as Fp3; try pose proof I as Fp1; try pose proof I as BT; try pose proof I as B1; try pose proof I as Zin; try pose proof I as Hi; try pose proof I as Hn8; try pose proof I as Shi; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - G3 Q2 Fp3 Fp1 BT B1 Zin Hi Hn8 Shi FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok' HULL_tight; lia] | solve [Zify.zify; try pose proof I as heq_z; try pose proof I as G3; try pose proof I as Q2; try pose proof I as Fp3; try pose proof I as Fp1; try pose proof I as BT; try pose proof I as B1; try pose proof I as Zin; try pose proof I as Hi; try pose proof I as Hn8; try pose proof I as Shi; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - heq_z G3 Q2 Fp3 Fp1 BT B1 Zin Hi Hn8 Shi FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok' HULL_tight; xlia zchecker] | lia])|].
              rewrite Z.add_assoc. rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small; (first [solve [try pose proof I as G3; try pose proof I as Q2; try pose proof I as Fp3; try pose proof I as Fp1; try pose proof I as BT; try pose proof I as B1; try pose proof I as Zin; try pose proof I as Hi; try pose proof I as Hn8; try pose proof I as Shi; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - G3 Q2 Fp3 Fp1 BT B1 Zin Hi Hn8 Shi FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok' HULL_tight; lia] | solve [Zify.zify; try pose proof I as heq_z; try pose proof I as G3; try pose proof I as Q2; try pose proof I as Fp3; try pose proof I as Fp1; try pose proof I as BT; try pose proof I as B1; try pose proof I as Zin; try pose proof I as Hi; try pose proof I as Hn8; try pose proof I as Shi; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb2; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; clear - heq_z G3 Q2 Fp3 Fp1 BT B1 Zin Hi Hn8 Shi FOOT QB Ub Fb2 Hbhi' Hnpos HULL_ok' HULL_tight; xlia zchecker] | lia]). }
            rewrite Ue in Q1. right. rewrite HS0. unfold STK_BELOW in *.
            assert (LE : bv_unsigned (edenot E pb) + pk + bv_unsigned (edenot E (snd p)) <= uB).
            { unfold estart in Q1; cbn [a_base a_off] in Q1. clear - Q1 Q2 QB G3 FOOT. lia. }
            clear - LE SO Fp1. unfold estart in *; cbn [a_base a_off] in *.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
        unfold APS.sh_lo, APS.sh_hi, APS.uE. rewrite Up, Ua. unfold z.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        split; apply andb_false_iff.
        + destruct A2 as [A2'|A2']; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; (first [solve [try pose proof I as A2'; try pose proof I as Fp3; try pose proof I as B1; try pose proof I as Zin; try pose proof I as H53; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Fs1; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as H35; try pose proof I as H26; try pose proof I as H25; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as Fp1; try pose proof I as BH; try pose proof I as B2; try pose proof I as H50; try pose proof I as H52; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as HS0; try pose proof I as FOOT; try pose proof I as QB; clear - A2' Fp3 B1 Zin H53 TOP Hn8 Fs1 Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight H35 H26 H25 H11 H10 H1 H Fp1 BH B2 H50 H52 Wlo HH0 HS0 FOOT QB; lia] | solve [Zify.zify; try pose proof I as heq_z; try pose proof I as A2'; try pose proof I as Fp3; try pose proof I as B1; try pose proof I as Zin; try pose proof I as H53; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as Fs1; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as H35; try pose proof I as H26; try pose proof I as H25; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as __sat78; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as Fp1; try pose proof I as BH; try pose proof I as B2; try pose proof I as H50; try pose proof I as H52; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as HS0; try pose proof I as FOOT; try pose proof I as QB; clear - heq_z A2' Fp3 B1 Zin H53 TOP Hn8 Fs1 Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight H35 H26 H25 H11 H10 H1 H __sat78 heq_S0 heq_H0 Fp1 BH B2 H50 H52 Wlo HH0 HS0 FOOT QB; xlia zchecker] | lia]).
        + destruct A1 as [A1'|A1']; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; (first [solve [try pose proof I as H26; try pose proof I as H25; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as A1'; try pose proof I as Fp3; try pose proof I as B1; try pose proof I as Zin; try pose proof I as H48; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Fs1; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as H30; try pose proof I as A2; try pose proof I as Fp1; try pose proof I as BH; try pose proof I as B2; try pose proof I as H45; try pose proof I as H47; try pose proof I as SO; clear - H26 H25 H11 H10 H1 H A1' Fp3 B1 Zin H48 Wlo HH0 TOP Hn8 HS0 Fs1 FOOT QB Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight H30 A2 Fp1 BH B2 H45 H47 SO; lia] | solve [Zify.zify; try pose proof I as H26; try pose proof I as H25; try pose proof I as H11; try pose proof I as H10; try pose proof I as H1; try pose proof I as H; try pose proof I as heq_S0; try pose proof I as heq_H0; try pose proof I as heq_z; try pose proof I as A1'; try pose proof I as Fp3; try pose proof I as B1; try pose proof I as Zin; try pose proof I as H48; try pose proof I as Wlo; try pose proof I as HH0; try pose proof I as TOP; try pose proof I as Hn8; try pose proof I as HS0; try pose proof I as Fs1; try pose proof I as FOOT; try pose proof I as QB; try pose proof I as Ub; try pose proof I as Fb1; try pose proof I as Hbhi'; try pose proof I as Hnpos; try pose proof I as HULL_ok'; try pose proof I as HULL_tight; try pose proof I as H30; try pose proof I as __sat77; try pose proof I as A2; try pose proof I as Fp1; try pose proof I as BH; try pose proof I as B2; try pose proof I as H45; try pose proof I as H47; try pose proof I as SO; clear - H26 H25 H11 H10 H1 H heq_S0 heq_H0 heq_z A1' Fp3 B1 Zin H48 Wlo HH0 TOP Hn8 HS0 Fs1 FOOT QB Ub Fb1 Hbhi' Hnpos HULL_ok' HULL_tight H30 __sat77 A2 Fp1 BH B2 H45 H47 SO; xlia zchecker] | lia]).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      (* [comment removed for export] *)
      assert (Hge : H0 <= z).
      { destruct Hhid as [Hv|Hv].
        - unfold APS.in_vis in Hv. apply existsb_exists in Hv as [p [Hp Hb]].
          destruct (is_stack_vis p) eqn:Hst; [|rewrite (proj1 (P p Hp Hst)) in Hb; discriminate].
          exfalso. unfold is_stack_vis in Hst. apply expr_eqb_eq in Hst. rewrite Hst in Hb. unfold APS.uE in Hb. rewrite Ustk, Ua in Hb.
          apply andb_prop in Hb as [Hb _]. apply Z.leb_le in Hb. unfold STK_BELOW in *. lia.
        - unfold APS.in_sh in Hv. apply existsb_exists in Hv as [p [Hp Hb]].
          destruct (is_stack_vis p) eqn:Hst; [|rewrite (proj2 (P p Hp Hst)) in Hb; discriminate].
          unfold is_stack_vis in Hst. apply expr_eqb_eq in Hst. unfold APS.sh_lo, APS.sh_hi in Hb. rewrite Hst in Hb. unfold APS.uE in Hb. rewrite Ustk, Ua in Hb.
          apply andb_prop in Hb as [Hb _]. apply Z.leb_le in Hb. rewrite HH0. lia. }
      (* [comment removed for export] *)
      assert (WW : wview SEGS (MR E cs model FULL) a <> None).
      { apply (store_ok_all SEGS (MR E cs model FULL) (Z.to_nat (S0 + n / 8 - H0)) (Z_to_bv 64 H0)).
        - rewrite u64_lit by lia. rewrite Z2Nat.id by lia. lia.
        - apply Wst. rewrite Z2Nat.id by lia. lia.
        - rewrite u64_lit by lia. rewrite Z2Nat.id by lia. rewrite Ua. unfold z in *. lia. }
      exact (wview_grows SEGS _ _ a GROWS WW). }
  (* [comment removed for export] *)
  assert (Hfl : flat E (SA sb sk) (elenZ E sn)) by (unfold flat, elenZ; fold S0; rewrite Usn; lia).
  assert (HKW : kentry_ok SEGS E (MR E cs2 model FULL) (KWr (SA sb sk) sn)).
  { cbn [kentry_ok]. split; [exact Hfl|]. intros d w Hd Hdw. fold S0. unfold elenZ in Hdw. rewrite Usn in Hdw.
    destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    replace x with (Z_to_bv 64 (S0 + (bv_unsigned x - S0))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); lia).
    apply (BYTE (bv_unsigned x - S0)). lia. }
  assert (HKold : know_ok SEGS E (MR E cs2 model FULL) (kimg_clip A (kn cs))).
  { unfold APS.Mr. eapply know_ok_unhide'; [apply H_off_segments_cs' | apply APS.kimg_clip_in_hull | | |].
    - intros y Hy. exact (SUB y Hy).
    - intros y Hy. apply hid_hull'. exact Hy.
    - apply Forall_kimg_clip. exact HK. }
  split; [|split; reflexivity].
  destruct HC. constructor; cbn [cs2 a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
    try assumption; try reflexivity.
  - (* [comment removed for export] *) constructor; [exact HKW | exact HKold].
  - (* [comment removed for export] *) rewrite HA, APS.A_bytes_app. lia.
  - (* [comment removed for export] *) rewrite HA. apply APS.MInv_app; [exact co_minv0|]. rewrite APS.A_bytes_app, co_limit0. lia.
  - (* [comment removed for export] *) intros a Ha. apply co_zero0. apply SUB. exact Ha.
Qed.



(* [comment removed for export] *)
Theorem xn_visfoot_sound : forall args, APS.node1_stmt SEGS A nx0 LIMIT SINV argH FS0 APS.always (xn_visfoot A LIMIT args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_visfoot in Hn.
  destruct args as [|B [|n0 rest]]; [discriminate| discriminate|]. destruct n0 as [n| | | | | | |]; try discriminate.
  destruct rest; [|discriminate].
  destruct (vis_foot_ok E cs B n cs' R FULL model HC Hn) as (HC' & Hpc & Hnx).
  rewrite <- Hpc. apply (Hk E R FULL model); [| exact HC' | reflexivity].
  split; apply env_agree_refl'.
Qed.

End Nodes.
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
Definition OBL_hyps (SEGS : list Segment) (A : atable) (nx0 : nat) (SINV : env -> (word -> option byte) -> Prop)
           (argH : env -> word -> bool) (P : Prop) : Prop :=
  (forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  res_len_ok SEGS A ->
  Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS) ->
  hull_ok A -> shadow_ok A ->
  APS.nx0_min_ok nx0 ->
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
  (forall E M (a : word), SINV E M -> argH E a = true -> APS.uE E e_sp0 <= bv_unsigned a) ->
  (forall E M, SINV E M -> sp_window_lo <= APS.uE E e_sp0 <= sp_window_hi) ->
  (hull_tight_b (segments_reserved SEGS) (img_lo A) (img_hi A) = true /\ img_lo A < img_hi A) ->
  P.

Theorem node_mmap_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  OBL_hyps SEGS A nx0 SINV argH (OBL_mmap SEGS A nx0 LIMIT SINV argH FS0).
Proof. intros *. unfold OBL_hyps. intros. unfold OBL_mmap. eapply node_mmap_sound; eauto. Qed.

Theorem node_mprotect_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  OBL_hyps SEGS A nx0 SINV argH (OBL_mprotect SEGS A nx0 LIMIT SINV argH FS0).
Proof. intros *. unfold OBL_hyps. intros. unfold OBL_mprotect. eapply node_mprotect_sound; eauto. Qed.

Theorem node_mmapin_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  OBL_hyps SEGS A nx0 SINV argH (OBL_mmapin SEGS A nx0 LIMIT SINV argH FS0).
Proof. intros *. unfold OBL_hyps. intros. unfold OBL_mmapin. eapply node_mmapin_sound; eauto. Qed.

(* [comment removed for export] *)
Theorem xn_visfoot_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  OBL_hyps SEGS A nx0 SINV argH (forall args, APS.node1_stmt SEGS A nx0 LIMIT SINV argH FS0 APS.always (xn_visfoot A LIMIT args)).
Proof. intros *. unfold OBL_hyps. intros. eapply xn_visfoot_sound; eauto. Qed.

End WithFP1.
