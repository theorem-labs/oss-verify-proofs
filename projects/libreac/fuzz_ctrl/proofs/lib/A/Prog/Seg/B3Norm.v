(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths changed; 39 of its 100 lines of code are new or changed and 1441 lines of the source are left out. *)
(* Batch-B3 helper for the asan slot segment lemmas of fuzz_ctrl LLVMFuzzerTestOneInput (rule 24: no function
   proved): the mem_rel transports a segment uses when its callee's contract asks for mem_inv.  Push 5b's FRA carries
   ro_agree, not mem_inv, so such a segment runs on the normalized memory `MemNorm.normalize rsegs m`
   (MemNorm.evt_normalize from FRA's ro_agree; mem_inv of it is MemNorm.mem_inv_normalize): each premise crosses
   mem_rel forward and each part of the post crosses it back.  Every byte such a run reads or writes outside the image
   lies at or above 0x5fe000, where no byte is read-only, or is read through mrd, which mem_rel keeps.  These are
   Seg/R14.v's r14_* transports (the worked pattern), stated once for R18, R19 and R21. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm BzBridge.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

(* Every segment of the image ends below 0x5fe000. *)
Lemma b3n_segs_below : BzBridge.seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

(* Above the image there is no read-only byte. *)
Lemma b3n_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (BzBridge.find_segment_below sg 0x5fe000 x n s b3n_segs_below E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib.MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

(* A write set whose ranges all start at or above 0x5fe000 writes no read-only byte. *)
Lemma b3n_W_ro : forall (W : list ivl) (x : word), (forall p, In p W -> 6283264 <= fst p) ->
  ro_addr rsegs x = true -> outside W (bv_unsigned x).
Proof.
  intros W x LOS E.
  assert (Hx : bv_unsigned x < 0x5fe000).
  { destruct (Z_lt_le_dec (bv_unsigned x) 0x5fe000) as [L|L]; [exact L|].
    exfalso. pose proof (u64_range x) as Hu.
    pose proof (b3n_ro_hi (bv_unsigned x) ltac:(lia)) as Hf. unfold wa in Hf.
    rewrite Z_to_bv_bv_unsigned in Hf. rewrite Hf in E. discriminate E. }
  revert LOS. induction W as [|[lo hi] W IH]; intros LOS; cbn [outside]; [exact I|].
  split.
  - pose proof (LOS (lo, hi) (or_introl eq_refl)) as Hp. cbn [fst] in Hp. lia.
  - apply IH. intros p Hp. apply LOS. right. exact Hp.
Qed.

Lemma b3n_wv : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof. intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (b3n_ro_hi a Ha)). tauto. Qed.

Lemma b3n_rel_stk : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi.
  split; intros (H0 & H1 & H); (split; [lia|]); (split; [lia|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb); (split; [apply (b3n_wv m m0 a HR ltac:(lia)); exact Hw|]);
    exists b; [rewrite <- (mrd_rel rsegs m m0 (wa a) HR) | rewrite (mrd_rel rsegs m m0 (wa a) HR)]; exact Hb.
Qed.

Lemma b3n_rel_sw : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 HR. split; intros H a Ha; pose proof (in_shadow_range a Ha) as Hr;
    assert (Hhi : 0x5fe000 <= a < 2 ^ 64)
      by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha; lia);
    destruct (H a Ha) as (Hw & b & Hb); (split; [apply (b3n_wv m m0 a HR Hhi); exact Hw|]);
    exists b; [rewrite <- (mrd_rel rsegs m m0 (wa a) HR) | rewrite (mrd_rel rsegs m m0 (wa a) HR)]; exact Hb.
Qed.

Lemma b3n_rel_ad : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n HR.
  split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]); (split; [exact H2|]);
    intros i Hi; destruct (H i Hi) as (Hap & b & Hb & Hok); (split; [exact Hap|]); exists b;
    [rewrite <- (mrd_rel rsegs m m0 _ HR) | rewrite (mrd_rel rsegs m m0 _ HR)]; split; assumption.
Qed.

Lemma b3n_cells_gen : forall m m1, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m1 a bs) ->
  asan_cells m -> asan_cells m1.
Proof.
  intros m m1 Fb H. unfold asan_cells in *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => apply Fb; assumption end.
Qed.

Lemma b3n_rel_cells : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 HR. split; apply b3n_cells_gen; intros a bs Hb;
    [exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb) | exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) Hb)].
Qed.

(* A writable range above the image reads the same on both sides of mem_rel. *)
Lemma b3n_rel_wr : forall m m0 a n, mem_rel rsegs m m0 -> 0x5fe000 <= a ->
  (wr_at rsegs m a n <-> wr_at rsegs m0 a n).
Proof.
  intros m m0 a n HR Ha.
  split; intros (H0 & H1 & H); (split; [exact H0|]); (split; [exact H1|]); intros i Hi;
    apply (b3n_wv m m0 (a + i) HR ltac:(lia)); exact (H i Hi).
Qed.

(* The writes of the normalized run, read back on the real memory: a byte outside W is unchanged (read-only bytes
   by ro_same, the others through the two normalizations). *)
Lemma b3n_rel_munch : forall W m m0 mf m0', mem_rel rsegs m m0 -> mem_rel rsegs mf m0' ->
  munch W m0 m0' -> ro_same rsegs m mf -> munch W m mf.
Proof.
  intros W m m0 mf m0' R1 R2 MU RS x Hx.
  destruct (ro_addr rsegs x) eqn:E; [exact (RS x E)|].
  rewrite <- (mem_rel_rw rsegs mf m0' x R2 E). rewrite (MU x Hx). exact (mem_rel_rw rsegs m m0 x R1 E).
Qed.

(* Writability is kept: a writable byte of the real memory either lies outside W, so is unchanged, or is not
   read-only and crosses both normalizations. *)
Lemma b3n_rel_wmono : forall W m m0 mf m0', mem_rel rsegs m m0 -> mem_rel rsegs mf m0' ->
  munch W m mf -> wmono rsegs m0 m0' ->
  (forall x : word, ro_addr rsegs x = true -> outside W (bv_unsigned x)) ->
  wmono rsegs m mf.
Proof.
  intros W m m0 mf m0' R1 R2 MU WM Hro x Hx.
  destruct (ro_addr rsegs x) eqn:E.
  - unfold wview in *. rewrite (MU x (Hro x E)). exact Hx.
  - rewrite <- (wview_rel_rw rsegs mf m0' x R2 E). apply WM.
    rewrite (wview_rel_rw rsegs m m0 x R1 E). exact Hx.
Qed.

(* A machine state with no pending supervisor call is its MS. *)
Lemma b3n_ms_eta : forall s, ms_svc_pending s = None ->
  s = MS (ms_regs s) (ms_fregs s) (ms_pc_val s) (ms_fcsr s) (ms_resv s) (ms_mem s) (ms_rom s).
Proof. intros [] H; cbn in H; subst; reflexivity. Qed.
