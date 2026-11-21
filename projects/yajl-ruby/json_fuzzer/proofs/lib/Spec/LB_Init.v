(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the in_channel_reader premise of QI_init; QI_init's initial reserved ledger ends with the vDSO/vvar pair, kept apart from the brk window by its mmap-base and brk-gap premises (init_resv_apart', after Agent/MallocKown.v's init_resv_apart and KL_init), with kl_metas_resv and kl_vdso). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Nodes NodesMat Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl RawAlloc KInv KLink KStep
  MI_Tree MI_Inv MI_Contracts LB_Tables LB_Inv LB_Sum LB_Kernel LB_QM LB_StmtA LB_Raw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma zsum_nonneg' l : (forall x, In x l -> 0 <= x) -> 0 <= zsum l.
Proof. induction l as [|a l IH]; intros H; cbn; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)). unfold zsum in IH. lia. Qed.

Lemma CAP_lower P c : (forall c, 0 <= P c) -> 0 <= c -> 1 <= CAP P c.   (* [comment removed for export] *)
Proof.
  intros HP Hc.
  assert (0 <= HOSTSTD P c).
  { unfold HOSTSTD. apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc').
    assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia). cbn beta.
    destruct (bighost c' =? c); [| apply Z.le_refl]. pose proof (tab_basic_ok c' G) as (_ & CM & _).
    apply Z.div_pos; [| lia]. unfold CAP0. pose proof (HP 0). destruct (c' <=? 23); lia. }
  unfold CAP, CAP0. pose proof (HP 0). destruct (c <=? 23); lia.
Qed.

Lemma NCAP_lower P : (forall c, 0 <= P c) -> 4 <= NCAP P.
Proof.
  intros HP. unfold NCAP, NG.
  assert (0 <= zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes)).
  { apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c & <- & Hc). apply In_classes in Hc. cbn beta.
    pose proof (tab_basic_ok c Hc) as (_ & CM & _). pose proof (CAP_lower P c HP ltac:(lia)).
    assert (0 <= (CAP P c + 32) / cmax c) by (apply Z.div_pos; lia). lia. }
  pose proof (HP 63). lia.
Qed.

Lemma SINV_minit secret resv : SINV x0 (minit secret resv) [].
Proof.
  constructor; cbn -[Z.mul Z.add Z.le Z.lt]; try (intros *; intros HH; rewrite lookup_empty in HH; discriminate).
  - intros k [].
  - intros c Hc. unfold nsc, gmetas, groups_l. cbn [s_groups minit]. rewrite map_to_list_empty. cbn. lia.
  - unfold apages, ncarved, regions_l. cbn [s_regions s_metas minit]. rewrite !map_to_list_empty. unfold zlen. cbn. lia.
  - intros H. lia.
Qed.

Lemma gcnt_minit secret resv c : gcnt (minit secret resv) c = 0.
Proof. unfold gcnt. cbn [s_groups minit]. rewrite map_to_list_empty. reflexivity. Qed.

Lemma AQ_minit P secret resv : (forall c, 0 <= P c) -> AQ (minit secret resv) [] P.
Proof.
  intros HP. constructor.
  - intros c Hc. unfold LR, zcount, zlen. cbn. apply HP.
  - intros c Hc. rewrite gcnt_minit. pose proof (CAP_lower P c HP ltac:(lia)). lia.
  - unfold n63, zcount, zlen. cbn. apply HP.
  - unfold ncarved. cbn [s_metas minit]. rewrite map_to_list_empty. pose proof (NCAP_lower P HP). unfold zlen. cbn. lia.
  - exact HP.
  - unfold zlen. cbn. apply HP.
Qed.

Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

(* LPS 727298f3: the initial reserved ledger is [reserved ++ vdso_reserved ..] (State.v [init_reserved],
   [m_vmmaps_init_model]); the vDSO/vvar pair sits under the page below [min mbase (sp - stack_max_size)], and
   [mmap_base_min] is far above the brk window, so each entry is below the brk start or four pages above it
   (a copy of Agent/MallocKown.v's init_resv_apart). *)
Lemma init_resv_apart' : forall segs brk0 mbase sp lim inp,
  bv_unsigned sp = rc_sp -> sp_window_lo <= rc_sp ->
  valid_brk segs brk0 -> mmap_base_min <= bv_unsigned mbase ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 32 * PGSZ <= mmap_base_min ->
  forall e, In e (vm_reserved (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))) ->
  ehi e <= bv_unsigned brk0 \/ bv_unsigned brk0 + 4 * PGSZ <= elo e.
Proof.
  intros segs brk0 mbase sp lim inp Hsp Hspw (Hlo & Hhi & Hal) Hmb Hgap e Hin.
  rewrite m_vmmaps_init_model in Hin.
  change (In e (init_reserved (segments_reserved segs) mbase sp (in_kernel inp))) in Hin.
  unfold init_reserved in Hin.
  apply in_app_or in Hin as [Hin | Hin].
  - left. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. lia.
  - right. destruct e as [a n].
    pose proof (vdso_len_bounds (in_kernel inp)) as VL.
    assert (Hsw : mmap_base_min + 32 * PGSZ <= bv_unsigned sp - stack_max_size)
      by (rewrite Hsp; unfold sp_window_lo, stack_max_size, mmap_base_min, PGSZ in *; lia).
    set (x := Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)) in Hin.
    assert (Hx : mmap_base_min <= x) by (unfold x; unfold PGSZ in Hsw; lia).
    assert (Hxm : x <= bv_unsigned mbase) by (unfold x; lia).
    assert (Hd : x - page_size < page_round_down_Z x <= x).
    { unfold page_round_down_Z, page_size. Z.div_mod_to_equations. lia. }
    assert (Htop : page_round_down_Z x < two_pow_64).
    { pose proof (bv_unsigned_in_range 64 mbase) as R. unfold bv_modulus in R. unfold two_pow_64. lia. }
    destruct (vdso_reserved_above _ _ a n Htop Hin) as [Ha _].
    unfold elo. cbn [fst]. unfold PGSZ, page_size in *. lia.
Qed.

(* [comment removed for export] *)
Theorem QI_init : forall P segs brk0 mbase sp lim inp,
  bv_unsigned sp = rc_sp -> sp_window_lo <= rc_sp <= sp_window_hi ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  in_channel_reader inp = true ->
  mmap_base_min <= bv_unsigned mbase ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 32 * PGSZ <= mmap_base_min ->
  (forall c, 0 <= P c) -> PHI P <= LBUDGET ->
  QI [] P (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros P segs brk0 mbase sp lim inp Hsp Hspw (Hlo & Hhi & Hal) Hpos Hceil Hch Hmb Hgap HP HPHI. split; [| unfold R63X, zsum; cbn; lia].
  (* LPS 727298f3: the vDSO/vvar pair is the tail of the initial reserved ledger (as Agent/MallocKown.v's KL_init). *)
  assert (Kvd0 : forall e, In e (vdso_of (init_model (segments_reserved segs) brk0 mbase sp lim inp)) ->
                   In e (vm_reserved (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)))).
  { intros e He. rewrite vm_reserved_init_model. apply in_or_app. right.
    unfold vdso_of in He. rewrite m_kernel_init_model in He. exact He. }
  exists (minit rc_secret (reservedZ segs)), (led_init (reservedZ segs)), [], (fun _ => []).
  split; [reflexivity|]. split; [apply INVL_init; exact rc_secret_range|]. split; [apply SINV_minit|]. split; [apply AQ_minit; exact HP|].
  split; [| split; [| split; [apply Permutation_refl| reflexivity]]].
  - constructor; rewrite ?m_vmmaps_init_model; cbn -[Z.pow Z.mul Z.add init_model].
    + apply minv_init; assumption.
    + apply m_halted_init_model.
    + split; [intros e []| apply pwdisj_nil].
    + first [unfold init_reserved; rewrite map_app; eexists; reflexivity | eexists; rewrite ?app_nil_r; reflexivity].
    + intros e Hin. exact (init_resv_apart' segs brk0 mbase sp lim inp Hsp (proj1 Hspw) (conj Hlo (conj Hhi Hal)) Hmb Hgap e Hin).
    + unfold PGSZ in *. unfold page_size in Hal. lia.
    + intros b l [].
    + intros b l k [].
    + apply List.NoDup_nil.
    + intros b l H. discriminate.
    + split; reflexivity.
    + intros b l [].
    + intros e [].
    + apply m_vm_materialized_init.
    + intros e [].
    + intros b l k [].
    + exact Kvd0.
  - unfold LI, gm, BB, vm_live_bytes. rewrite m_vmmaps_init_model. cbn. lia.
Qed.
End RC__1.
