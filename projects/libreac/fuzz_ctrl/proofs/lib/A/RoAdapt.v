(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 866 of its 1005 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R3.v; 39 of its 124 lines of code are new or changed and 920 lines of the source are left out. *)
(* Frame v3 (ro_agree) transfers for image A (asan): the memory facts a segment hands to a callee contract, moved
   across lib.A.MemNorm's mem_rel rsegs m m0 (m0 = normalize rsegs m, which has mem_inv by construction; see
   MemNorm.evt_normalize). A cut carries ro_agree, not mem_inv (push 5b), but every callee contract asks for
   mem_inv, so a segment runs the call on the normalized memory and brings the post back.
   bytes_at, mrd and so asan_cells and addressable cross mem_rel in both directions unchanged; a cell that is
   written (wr_at, stk, shadow_rw, rw_cells) crosses to m0 when it is at no read-only address (rel_*_norm), and
   back to m always (rel_*_back). Every segment of the image ends below 6283264 (ro_rsegs_low), so every address
   at or above it, the shadow included, is not read-only (ro_addr_false_hi, ro_addr_false_w,
   ro_addr_false_shadow); the stack, the frame and the heap all lie above it.
   The canonical copies of the R3/R4 segments' local r3_* / r4_* (a working branch). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
Import ListNotations.
Open Scope Z_scope.

(* ---- the read-only image of rsegs lies below 6283264 ---- *)

Definition ro_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma ro_rsegs_low : ro_tops rsegs 6283264 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ro_find_below : forall segs top x n s,
  ro_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold ro_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma ro_addr_false_hi : forall a, 6283264 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [exfalso|reflexivity].
  unfold ro_addr in E.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:Es; [|discriminate E].
  destruct (ro_find_below rsegs 6283264 (bv_unsigned (wa a)) 1 s ro_rsegs_low Es ltac:(lia)) as [L|L];
    [|discriminate L].
  rewrite wa_unsigned in L by lia. lia.
Qed.

Lemma ro_addr_false_w : forall x : word, 6283264 <= bv_unsigned x -> ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:Es; [|reflexivity].
  destruct (ro_find_below rsegs 6283264 (bv_unsigned x) 1 s ro_rsegs_low Es ltac:(lia)) as [L|L];
    [lia | discriminate L].
Qed.

Lemma ro_addr_false_shadow : forall a, in_shadow a -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. apply ro_addr_false_hi. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia.
Qed.

(* ---- ro_agree across a run ---- *)

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

(* ro_agree survives a run whose write set is at no read-only address (with ro_addr_false_w: a write set at or
   above 6283264, e.g. the frame shadow, a callee's stack window, a frame record). *)
Lemma ro_agree_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> ro_addr rsegs x = false) -> ro_agree rsegs m'.
Proof.
  intros W m m' HRO MU HW a Ha.
  destruct (outside_dec W (bv_unsigned a)) as [Ho|Hno].
  - unfold mrd. rewrite (MU a Ho). exact (HRO a Ha).
  - rewrite (HW a Hno) in Ha. discriminate Ha.
Qed.

(* ---- the transfers across mem_rel rsegs m m0 ---- *)

Lemma rel_stk_norm : forall m m0 lo hi, mem_rel rsegs m m0 ->
  (forall x, lo <= x < hi -> ro_addr rsegs (wa x) = false) -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi REL HR (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 _ REL (HR a Ha)). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma rel_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma rel_sw_norm : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 REL HS a Ha. destruct (HS a Ha) as (Hv & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 _ REL (ro_addr_false_shadow a Ha)). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma rel_sw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL HS a Ha. destruct (HS a Ha) as (Hv & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL (ro_addr_false_shadow a Ha)). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma rel_ac_norm : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 REL H. unfold asan_cells in H |- *.
  do 16 (destruct H as (? & H)).
  do 16 (split; [apply (proj1 (bytes_at_rel rsegs m m0 _ _ REL)); assumption|]).
  apply (proj1 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

Lemma rel_ac_back : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 REL H. unfold asan_cells in H |- *.
  do 16 (destruct H as (? & H)).
  do 16 (split; [apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption|]).
  apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

Lemma rel_rw_norm : forall m m0 A cs, mem_rel rsegs m m0 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs m A cs -> rw_cells rsegs m0 A cs.
Proof.
  intros m m0 A cs REL HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj1 (bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (wr_at_norm rsegs m m0 A _ REL Hw HR).
Qed.

Lemma rel_rw_back : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs REL ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (wr_at_rel rsegs m m0 A _ REL Hw).
Qed.

Lemma rel_addr_norm : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n REL (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma rel_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n REL (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.
