(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Image.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import STree Malloc MallocCtrl KInv KStep KLink KEv Prog
  MI_Tree MI_Inv MI_Contracts LB_Tables LB_Inv LB_Sum LB_Kernel LB_KCount LB_QM LB_StmtA LB_Raw Gap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma zsum_nonneg' l : (forall x, In x l -> 0 <= x) -> 0 <= zsum l.
Proof. induction l as [|a l IH]; intros H; cbn; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)). unfold zsum in IH. lia. Qed.

Lemma CAP_lower P c : (forall c, 0 <= P c) -> 0 <= c -> 14 <= CAP P c.
Proof.
  intros HP Hc.
  assert (0 <= HOSTSTD P c).
  { unfold HOSTSTD. apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc').
    assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia). cbn beta.
    destruct (bighost c' =? c); [| apply Z.le_refl]. pose proof (tab_basic_ok c' G) as (_ & CM & _).
    apply Z.div_pos; [| lia]. unfold CAP0. pose proof (HP c'). destruct (c' <=? 23); lia. }
  unfold CAP, CAP0. pose proof (HP c). destruct (c <=? 23); lia.
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

Lemma SINV_minit secret resv atop : SINV x0 (minit secret resv atop) [].
Proof.
  constructor; cbn -[Z.mul Z.add Z.le Z.lt]; try (intros *; intros HH; rewrite lookup_empty in HH; discriminate).
  - intros k [].
  - intros c. unfold MIS, zcount, zlen. cbn. lia.
  - intros c Hc. unfold nsc, gmetas, groups_l. cbn [s_groups minit]. rewrite map_to_list_empty. cbn. lia.
  - unfold apages, ncarved, regions_l. cbn [s_regions s_metas minit]. rewrite !map_to_list_empty. unfold zlen. cbn. lia.
  - intros H. lia.
Qed.

Lemma gcnt_minit secret resv atop c : gcnt (minit secret resv atop) c = 0.
Proof. unfold gcnt. cbn [s_groups minit]. rewrite map_to_list_empty. reflexivity. Qed.

Lemma AQ_minit P secret resv atop : (forall c, 0 <= P c) -> PQOK P -> AQ (minit secret resv atop) [] P.
Proof.
  intros HP PQ. constructor.
  - intros c Hc. unfold LR, zcount, zlen. cbn. apply HP.
  - intros c Hc. rewrite gcnt_minit. pose proof (CAP_lower P c HP ltac:(lia)). lia.
  - unfold n63, zcount, zlen. cbn. apply HP.
  - unfold ncarved. cbn [s_metas minit]. rewrite map_to_list_empty. pose proof (NCAP_lower P HP). unfold zlen. cbn. lia.
  - exact HP.
  - exact PQ.
Qed.

Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

(* the start model is with_vdso of init_model (TopLevel mo0 at
   ), for any vDSO run v; + the image bound and mmap_base_min <= mbase (APPENDED; the facts KLink KL_init
   and LB_KCount LNstat need). The KL launch proof is KLink KL_init, as Spec/ModelInv GI_init. *)
Theorem QI_init : forall P segs brk0 mbase sp lim inp atop v,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  atop = bv_unsigned sp - stack_max_size ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  (forall c, 0 <= P c) -> PQOK P -> PHI P <= LBUDGET ->
  in_channel_reader inp = true ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 -> mmap_base_min <= bv_unsigned mbase ->
  QI [] P (ps_init (reservedZ segs) atop) (with_vdso v (init_model (segments_reserved segs) brk0 mbase sp lim inp)).
Proof.
  intros P segs brk0 mbase sp lim inp atop v Hvb Hpos Hsp Eatop Hceil Hfloor Hresv Hlim HP PQ HPHI Hrdr Hlow Hmb.
  pose proof Hvb as (Hlo & Hhi & Hal).
  split; [| unfold R63X, zsum; cbn; lia].
  pose proof alloc_ceiling_lo_val as Hclo.
  assert (Hat : 0 < atop <= atop_hi) by (unfold atop_hi, sp_window_lo, sp_window_hi, stack_max_size in *; lia).
  exists (minit 0 (reservedZ segs) atop), (led_init (reservedZ segs) atop), [], (fun _ => []).
  split; [reflexivity|]. split; [apply INVL_init; [lia| exact Hat]|]. split; [apply SINV_minit|]. split; [apply AQ_minit; [exact HP| exact PQ]|].
  assert (Evm : m_vmmaps (with_vdso v (init_model (segments_reserved segs) brk0 mbase sp lim inp))
                = mkVmMapsFull (init_reserved (segments_reserved segs) mbase sp (in_kernel inp)) [] [] brk0 brk0 lim mbase sp)
    by reflexivity.
  destruct (KL_resv_init segs brk0 mbase sp lim inp Hvb Hlow Hmb (proj1 Hsp)) as (_ & _ & Hlb).
  assert (Hlb' : live_bytes (init_reserved (segments_reserved segs) mbase sp (in_kernel inp))
                 <= live_bytes (segments_reserved segs) + 0x14000) by exact Hlb.
  split; [| split; [| split; [| apply Permutation_refl]]].
  - apply KL_with_vdso.
    exact (KL_init segs brk0 mbase sp lim inp (reservedZ segs) atop _ eq_refl Hvb Hpos Hsp Eatop Hceil Hlow Hmb Hrdr).
  - unfold LI, gm, BB. rewrite Evm. cbn [vm_maps vm_brk vm_start_brk]. cbn. lia.
  - split; [| split].
    + rewrite Evm. unfold kcnt, lcnt. cbn [vm_maps]. cbn. lia.
    + unfold LNstat. rewrite Evm. cbn [vm_start_brk vm_limit vm_reserved vm_mmap_base]. unfold PGSZ in *.
      do 2 (split; [lia|]). split; [lia| exact Hmb].
    + intros b l H. discriminate.
Qed.
