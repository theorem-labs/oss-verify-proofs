(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ACells LJ PEnv APrimSpec2 APrimLem APrimQ ASec ASecD AQuar AHeap.
Import ListNotations.
Open Scope Z_scope.

Notation zb := (Z_to_bv 8 0).

Lemma rw_zeros_sub : forall (m : mem) A (N off n : nat), rw_cells asegs m A [CB N (repeat zb N)] -> (off + n <= N)%nat ->
  rw_cells asegs m (A + Z.of_nat off) [CB n (repeat zb n)].
Proof.
  intros m A N off n [[WF (B0 & B1 & BY)] (W0 & W1 & WR)] LE. cbn [cells_bytes cbytes cells_size csize Nat.add] in *.
  rewrite !app_nil_r, !repeat_length in B1, BY. rewrite Nat.add_0_r in W1, WR.
  split; [split; [cbn; split; [apply repeat_length| exact I]|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold bytes_at. rewrite repeat_length. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat off + Z.of_nat i) with (A + Z.of_nat (off + i)) by lia. rewrite (BY (off + i)%nat ltac:(lia)).
    rewrite !nth_error_repeat by lia. reflexivity.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat off + i) with (A + (Z.of_nat off + i)) by lia. apply WR. lia.
Qed.

Lemma rw_zeros_cells : forall (m : mem) A (N off : nat) cs, rw_cells asegs m A [CB N (repeat zb N)] -> cells_wf cs ->
  cells_bytes cs = repeat zb (cells_size cs) -> (off + cells_size cs <= N)%nat -> rw_cells asegs m (A + Z.of_nat off) cs.
Proof.
  intros m A N off cs RZ WF EB LE. pose proof (rw_zeros_sub m A N off (cells_size cs) RZ LE) as R.
  eapply rw_cells_rebytes; [exact R| exact WF| |].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact EB.
  - cbn [cells_size csize]. lia.
Qed.

Lemma get_cls_prim0 : forall c, get_cls prim0 c = pclass0.
Proof.
  intros c. unfold get_cls, prim0. cbn [pr_cls].
  destruct (nth_in_or_default (Z.to_nat c) (repeat pclass0 32) pclass0) as [IN| ->]; [apply repeat_spec in IN; exact IN| reflexivity].
Qed.

Section IR.
Context {HC : HasCeiling}.
Variable AL : alayout.
Hypothesis AO : alayout_ok AL.
Notation THR := (at_thr (al_thread AL)).

#[using="Type"] Lemma pclass0_wf : forall c, 1 <= c <= 31 -> pclass_wf c pclass0.
Proof.
  intros c Hc. pose proof (class_size_pos c Hc) as CS. pose proof (max_count_range c Hc) as (MR & _).
  unfold pclass_wf, pclass0. cbn [p_nf p_mfa p_au p_mu p_nalloc p_nfreed p_fa p_cnt p_chunks app length Z.of_nat].
  repeat split; try lia; try reflexivity; try apply NoDup_nil_2; try constructor.
Qed.

#[using="HC AO"] Lemma RPRIM_init : forall (m : mem),
  prim_env AL m ->
  rw_cells asegs m (RIB AL) [CB 4096 (repeat zb 4096)] ->
  rw_cells asegs m (THR + CACHE_OFF) [CB 2960 (repeat zb 2960)] ->
  RPRIM AL prim0 m.
Proof.
  intros m PE RI TC. layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold RPRIM. split; [reflexivity|]. split; [exact PE|]. split; [| split].
  - intros c Hc. rewrite get_cls_prim0. cbn [pr_inited prim0]. pose proof (region_range AL c Hc) as [RR1 RR2].
    split; [exact (pclass0_wf c Hc)|]. split; [| split; [| split; [| split]]].
    + exists (wz 0), (wz 0), (wz 0), (wz 0), (wz 0), (wz 0), (repeat zb 3). unfold ri_addr.
      replace (RIB AL + 128 * c) with (RIB AL + Z.of_nat (Z.to_nat (128 * c))) by lia.
      apply (rw_zeros_cells m (RIB AL) 4096 _ _ RI); [cbn; tauto| vm_compute; reflexivity| cbn [cells_size csize ri_cells Nat.add]; lia].
    + unfold pcl_rep, pcl_addr. cbn [p_cnt p_chunks pclass0 length firstn map]. split.
      * replace (THR + CACHE_OFF + 80 * c) with (THR + CACHE_OFF + Z.of_nat (Z.to_nat (80 * c))) by lia.
        apply (rw_zeros_cells m _ 2960 _ _ TC); [cbn; tauto| vm_compute; reflexivity| cbn [cells_size csize Nat.add]; lia].
      * exists (repeat (wz 0) 16). split; [| split; reflexivity].
        pose proof (rw_zeros_sub m _ 2960 (Z.to_nat (80 * c + 16)) 64 TC ltac:(lia)) as [[_ BY] WR].
        replace (THR + CACHE_OFF + Z.of_nat (Z.to_nat (80 * c + 16))) with (THR + CACHE_OFF + 80 * c + 16) in * by lia.
        split; [exact BY| exact WR].
    + unfold fa_rep. exists []. cbn [p_mfa p_fa pclass0 length firstn map]. split; [| split; reflexivity].
      unfold fa_base, u32arr, bytes_at, wr_at. change (u32s []) with (@nil byte). cbn [length Z.of_nat]. repeat split; try lia; intros i Hi; lia.
    + unfold tail_rep. cbn [p_mu p_au pclass0]. rewrite Z.sub_diag, Z.add_0_r. change (0 / 8) with 0. change (Z.to_nat 0) with 0%nat. cbn [repeat].
      assert (SH : 0 <= sh (region AL c) <= 2^63) by (unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
      split; [exists []|]; (unfold rw_cells, cells_at, bytes_at, wr_at; cbn [cells_bytes cbytes cells_size csize app length Z.of_nat Nat.add cells_wf]; repeat split; try lia; intros i Hi; lia).
    + intros v [].
  - cbn [pr_calloc pr_cmapped prim0]. replace (THR + CSTATS_OFF + 16) with (THR + CACHE_OFF + Z.of_nat 2576) by lia.
    apply (rw_zeros_cells m _ 2960 _ _ TC); [cbn; tauto| vm_compute; reflexivity| cbn [cells_size csize Nat.add]; lia].
  - exists (repeat zb 368). replace (THR + TSTATS_OFF) with (THR + CACHE_OFF + Z.of_nat 2592) by lia. exact (rw_zeros_sub m _ 2960 2592 368 TC ltac:(lia)).
Qed.

#[using="AO"] Lemma RSEC_init : forall (m : mem) nres0,
  sec_env AL m -> sec_vars (mkSEC [] nres0) m -> nres0 = 0 -> RSEC AL (mkSEC [] nres0) m.
Proof.
  intros m nres0 SE SV ->. layout_facts AO 1%nat LP. destruct LP as (_ & P2 & _ & P4 & _).
  unfold RSEC. split; [| split; [exact SE| split; [exact SV| split]]].
  - unfold sec_wf. cbn [se_nres se_n se_chunks]. unfold se_n. cbn [se_chunks length Z.of_nat].
    repeat split; try lia; try reflexivity; try constructor.
  - unfold parr_rep. exists []. cbn [se_nres se_chunks length firstn map Z.of_nat]. split; [| split; reflexivity].
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold u64arr, bytes_at, wr_at. change (u64s []) with (@nil byte). cbn [length Z.of_nat]. repeat split; try lia; intros i Hi; lia.
  - intros i c NTH. destruct i; discriminate.
Qed.

End IR.

Lemma a0_wview_seg : forall (m : mem) (x : word),
  (match find_segment asegs (bv_unsigned x) 1 with
   | Some seg => if seg_writable seg then segment_byte_at seg.(seg_bytes) (Z.to_N (bv_unsigned x - Z.of_N seg.(seg_base))) else None
   | None => None end) <> None ->
  wview asegs m x <> None.
Proof. intros m x H. unfold wview. destruct (m x); [discriminate| exact H]. Qed.

Lemma a0_canary_wr : forall m : mem, wr_at asegs m 6321648 8.
Proof.
  intros m. split; [lia|]. split; [lia|]. intros i Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  apply a0_wview_seg.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma canary_cell : forall (m : mem) (w : word), bytes_at asegs m 6321648 (le8 w) -> rw_cells asegs m 6321648 [C8 w].
Proof.
  intros m w BY. split; [split; [cbn; tauto|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY.
  - cbn [cells_size csize Nat.add Z.of_nat]. exact (a0_canary_wr m).
Qed.
