(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep Prog
  MI_Tree MI_Inv MI_Contracts LB_Tables LB_Inv LB_Sum LB_Kernel LB_QM LB_StmtA LB_Raw.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Unforced.
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

Lemma SINV_minit secret resv : SINV x0 (minit secret resv) [].
Proof.
  constructor; cbn -[Z.mul Z.add Z.le Z.lt]; try (intros *; intros HH; rewrite lookup_empty in HH; discriminate).
  - intros k [].
  - intros c. unfold MIS, zcount, zlen. cbn. lia.
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
Qed.

Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

Section WithCeiling. Context {CE__ : Ceiling}.

Theorem QI_init : forall P segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  bv_unsigned sp - stack_max_size = alloc_ceiling ->
  (forall c, 0 <= P c) -> PHI P <= LBUDGET ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 -> KLIM + SMALLREQ <= lim ->
  QI [] P (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros P segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hpos Hceil Htop HP HPHI Hlow Hroom. split; [| unfold R63X, zsum; cbn; lia].
  exists (minit 0 (reservedZ segs)), (led_init (reservedZ segs)), [], (fun _ => []).
  split; [reflexivity|]. split; [apply INVL_init; lia|]. split; [apply SINV_minit|]. split; [apply AQ_minit; exact HP|].
  split; [| split; [| apply Permutation_refl]].
  - constructor; rewrite ?m_vmmaps_init_model, ?m_halted_init_model; cbn -[Z.pow Z.mul Z.add].
    + apply minv_init.
    + reflexivity.
    + split; [intros e []| apply pwdisj_nil].
    + reflexivity.
    + intros e Hin. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. lia.
    + unfold PGSZ in *. unfold page_size in Hal. lia.
    + intros b l [].
    + intros b l k [].
    + apply List.NoDup_nil.
    + intros b l H. discriminate.
    + split; reflexivity.
    + exact Htop.
  - split.
    + unfold gm, BB. rewrite m_vmmaps_init_model. cbn. lia.
    +
      rewrite m_vmmaps_init_model. split; [intros e []|]. cbn [vm_limit vm_start_brk]. split; [exact Hroom| lia].
Qed.

End WithCeiling.
