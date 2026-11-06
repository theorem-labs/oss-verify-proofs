(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Image.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep KLink KEv Prog
  MI_Tree MI_Inv MI_Contracts LB_Tables LB_Inv LB_Sum LB_Kernel LB_KCount LB_QM LB_StmtA LB_Raw Gap.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem QI_init : forall P segs brk0 mbase sp lim inp atop,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->            (* [comment removed for export] *)
  atop = bv_unsigned sp - stack_max_size ->                     (* [comment removed for export] *)
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> KLIM <= lim ->
  (forall c, 0 <= P c) -> PQOK P -> PHI P <= LBUDGET ->
  QI [] P (ps_init (reservedZ segs) atop) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros P segs brk0 mbase sp lim inp atop (Hlo & Hhi & Hal) Hpos Hsp Eatop Hceil Hfloor Hresv Hlim HP PQ HPHI. split; [| unfold R63X, zsum; cbn; lia].
  pose proof alloc_ceiling_lo_val as Hclo.
  assert (Hat : 0 < atop <= atop_hi) by (unfold atop_hi, sp_window_lo, sp_window_hi, stack_max_size in *; lia).
  exists (minit 0 (reservedZ segs) atop), (led_init (reservedZ segs) atop), [], (fun _ => []).
  split; [reflexivity|]. split; [apply INVL_init; [lia| exact Hat]|]. split; [apply SINV_minit|]. split; [apply AQ_minit; [exact HP| exact PQ]|].
  assert (Evm : m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)
                = mkVmMapsFull (segments_reserved segs) [] [] brk0 brk0 lim mbase sp) by reflexivity.
  assert (Eh : m_halted (init_model (segments_reserved segs) brk0 mbase sp lim inp) = None) by reflexivity.
  split; [| split; [| split; [| apply Permutation_refl]]].
  - constructor; rewrite ?Evm; cbn -[Z.pow Z.mul Z.add Z.sub init_model alloc_top].
    + apply minv_init. exact Hsp.
    + exact Eh.
    + split; [intros e []| apply pwdisj_nil].
    + reflexivity.
    + intros e Hin. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. lia.
    + unfold PGSZ in *. unfold page_size in Hal. unfold alloc_ceiling_lo, sp_window_lo, stack_max_size in *. lia.
    + intros b l [].
    + intros b l k [].
    + apply List.NoDup_nil.
    + intros b l H. discriminate.
    + split; reflexivity.
    + unfold alloc_top. cbn [vm_init_sp]. exact Eatop.
  - unfold LI, gm, BB. rewrite Evm. cbn. lia.
  - split; [| split].
    + rewrite Evm. unfold kcnt, lcnt. cbn. lia.
    + unfold LNstat. rewrite Evm. cbn -[Z.pow Z.mul Z.add]. unfold PGSZ in *. split; [lia|]. split; [lia| exact Hresv].
    + intros b l H. discriminate.
Qed.
