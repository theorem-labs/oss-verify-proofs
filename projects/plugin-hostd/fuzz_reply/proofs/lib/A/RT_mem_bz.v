(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 142 of its 194 lines of code are new or changed and 691 lines of the source are left out. *)
(* GXA's memcpy and memset call contracts need the musl bodies' walks in the relocated Bz tree's words: I_amemcpy.v's
   memcpy_stmt (musl memcpy, 0x964cc) and F_memset.v's memset_callZ_stmt (musl memset, 0x96900).  The bodies are proved
   in lib/Lib's words by the relocated c-libc walks lib/A/Prog/memcpy.v (memcpy_holds), memcpy_same.v
   (memcpy_same_holds) and memset.v (memset_holds); this file moves them across, exactly as the donor does.

   This file proves no new function.  Every lemma is copied, with only the module path changed, from
   origin/cold/c-asan-rt-stateio-n 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib:
     lib/A/BzBridge.v:40-63      seg_tops_below, rsegs_below_task, find_segment_below, seg_addr_below
     lib/A/BzCallBridge.v:17-147 msteps_bz .. rw_cells_CB0_ours, memset_callZ_of_contract (:109)
     lib/A/Prog/asan_memcpy.v:36-108  msteps_to_bz, evt_to_bz, bytes_at_same, mc_post, mc_proof (:87)
   The donor files themselves are not copied: BzBridge.v and BzCallBridge.v import AsanRT.v (117 fuzz_state.asan
   numerals, the asan_cells record of the donor's own call forms), which none of the lemmas below uses.
   No address numeral occurs here. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog Require Import memset_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog.memcpy_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog.memcpy.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog.memcpy_same.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog.memset.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_amemcpy.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.F_memset.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Module BzI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Module BzCl := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Module BzFr := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Module BzA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_amemcpy.
Module BzF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.F_memset.
Module MCc := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog.memcpy_c.
Module MCp := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog.memcpy.
Module MCs := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog.memcpy_same.
Module MSp := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog.memset.

(* ---- lib/A/BzBridge.v:40-63 ---- *)
Definition seg_tops_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma rsegs_below_task : seg_tops_below rsegs TASK_SIZE = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_below : forall segs top x n s,
  seg_tops_below segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma seg_addr_below : forall a, BzM.seg_addr rsegs a = true -> bv_unsigned a < BzM.UTOP.
Proof.
  intros a H. unfold BzM.seg_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (find_segment_below rsegs TASK_SIZE (bv_unsigned a) 1 s rsegs_below_task E ltac:(lia)) as [L|L];
    [unfold BzM.UTOP, TASK_SIZE in *; lia | discriminate L].
Qed.

(* ---- lib/A/BzCallBridge.v ---- *)
Lemma msteps_bz : forall s s', msteps rsegs s s' -> BzE.msteps BzI.asegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BzE.msteps_refl.
  - eapply BzE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma evt_bz : forall (Q : machine_state -> Prop) ms, evt rsegs Q ms -> BzE.evt BzI.asegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [exact (msteps_bz ms ms' H) | exact HQ].
Qed.

Lemma rw_cb_to_bz : forall m a k bs, rw_cells rsegs m a [CB k bs] -> BzSt.rw_cells BzI.asegs m a [BzCl.CB k bs].
Proof. intros m a k bs [[Hwf Hb] Hw]. split; [split|]; [exact Hwf | exact Hb | exact Hw]. Qed.

Lemma rw_cb_of_bz : forall m a k bs, BzSt.rw_cells BzI.asegs m a [BzCl.CB k bs] -> rw_cells rsegs m a [CB k bs].
Proof. intros m a k bs [[Hwf Hb] Hw]. split; [split|]; [exact Hwf | exact Hb | exact Hw]. Qed.

Lemma munch_to_bz : forall W m m', munch W m m' -> BzFr.munch W m m'.
Proof. intros W m m' H. exact H. Qed.

Lemma wmono_to_bz : forall m m', wmono rsegs m m' -> BzFr.wmono BzI.asegs m m'.
Proof. intros m m' H. exact H. Qed.

Lemma mem_inv_of_bz : forall m, BzM.mem_inv BzI.asegs m -> mem_inv rsegs m.
Proof. intros m H a b E. exact (BzM.mem_inv_ro BzI.asegs m a b H E). Qed.

Lemma bz_wview_below : forall m a, BzM.mem_inv BzI.asegs m -> wview rsegs m a <> None -> bv_unsigned a < BzM.UTOP.
Proof.
  intros m a H Hw. destruct (m a) as [b|] eqn:E; [exact (BzM.mem_inv_ov_below BzI.asegs m a b H E)|].
  apply seg_addr_below. unfold BzM.seg_addr. unfold wview in Hw. rewrite E in Hw.
  change BzI.asegs with rsegs.
  destruct (find_segment rsegs (bv_unsigned a) 1); [reflexivity | exfalso; apply Hw; reflexivity].
Qed.

Lemma bz_mem_inv_after : forall m m' D N, BzM.mem_inv BzI.asegs m -> wr_at rsegs m D N -> mem_inv rsegs m' ->
  munch [(D, D + N)] m m' -> BzM.mem_inv BzI.asegs m'.
Proof.
  intros m m' D N HB (HD & HN & HW) HM MU. apply BzM.mem_inv_intro; [exact seg_addr_below|].
  intros a b E. split; [exact (HM a b E)|].
  destruct (Z_lt_le_dec (bv_unsigned a) D) as [L|L];
    [|destruct (Z_lt_le_dec (bv_unsigned a) (D + N)) as [L2|L2]].
  - rewrite (MU a) in E by (cbn; split; [lia | exact I]). exact (BzM.mem_inv_ov_below BzI.asegs m a b HB E).
  - pose proof (HW (bv_unsigned a - D) ltac:(lia)) as Hw.
    replace (wa (D + (bv_unsigned a - D))) with a in Hw
      by (unfold wa; rewrite Z.add_comm, Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
    exact (bz_wview_below m a HB Hw).
  - rewrite (MU a) in E by (cbn; split; [lia | exact I]). exact (BzM.mem_inv_ov_below BzI.asegs m a b HB E).
Qed.

Lemma rw_cells_CB0_ours : forall m A, 0 <= A <= 2^64 -> rw_cells rsegs m A [CB 0 []].
Proof. intros m A HA. apply rw_cb_of_bz. exact (BzF.rw_cells_CB0 m A HA). Qed.

Lemma memset_callZ_of_contract : memset_contract -> BzF.memset_callZ_stmt.
Proof.
  intros MSC. unfold BzF.memset_callZ_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D C N junk
    RW MI HD HN HDN HC.
  pose proof RW as (_ & WR). cbn [BzCl.cells_size BzCl.csize Nat.add] in WR. rewrite Nat.add_0_r, Z2Nat.id in WR by lia.
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  destruct (Z.eq_dec D (2^64)) as [ED|ND].
  - assert (N0 : N = 0) by lia. subst N.
    assert (EW : Z_to_bv 64 D = Z_to_bv 64 0) by (apply bv_eq; rewrite !Z_to_bv_unsigned, ED; reflexivity).
    rewrite EW. apply evt_bz.
    eapply evt_mono.
    { apply (MSC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 C) (Z_to_bv 64 0) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m []).
      - rewrite !unsigned_lit by lia. apply rw_cells_CB0_ours. lia.
      - exact (mem_inv_of_bz m MI). }
    intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RW').
    rewrite !unsigned_lit in MU by lia.
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
    split; [rewrite EW; exact E|]. split.
    { intros x Hx. apply MU. cbn. split; [lia | exact I]. }
    split; [exact (wmono_to_bz m m' WM)|]. split.
    { apply (bz_mem_inv_after m m' 0 0 MI); [split; [lia|]; split; [lia|]; intros; lia | exact MI' | exact MU]. }
    cbn [Z.to_nat repeat]. apply BzF.rw_cells_CB0. lia.
  - assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
    apply evt_bz.
    eapply evt_mono.
    { apply (MSC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk).
      - rewrite ED, EN. exact (rw_cb_of_bz m D _ junk RW).
      - exact (mem_inv_of_bz m MI). }
    intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RW').
    rewrite ED, EC, EN in *.
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
    split; [exact E|]. split; [exact (munch_to_bz _ m m' MU)|]. split; [exact (wmono_to_bz m m' WM)|]. split.
    { exact (bz_mem_inv_after m m' D N MI WR MI' MU). }
    exact (rw_cb_to_bz m' D _ _ RW').
Qed.

(* ---- lib/A/Prog/asan_memcpy.v ---- *)
Lemma msteps_to_bz : forall s s', msteps rsegs s s' -> BzE.msteps BzI.asegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BzE.msteps_refl.
  - eapply BzE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma evt_to_bz : forall (Q : machine_state -> Prop) ms, evt rsegs Q ms -> BzE.evt BzI.asegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [exact (msteps_to_bz ms ms' H) | exact HQ].
Qed.

Lemma bytes_at_same : forall m a bs bs', bytes_at rsegs m a bs -> bytes_at rsegs m a bs' ->
  length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (_ & _ & H) (_ & _ & H') L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi), (proj2 (nth_error_None bs' i) ltac:(lia)). reflexivity.
Qed.

Lemma mc_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (a0 a1 a2 : word) src m st,
  BzM.mem_inv BzI.asegs m -> bv_unsigned a0 + bv_unsigned a2 <= 2^47 ->
  MCc.memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m st ->
  BzA.memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m st.
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m st MI H47
    (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MU & WM & MI' & RW & B).
  unfold BzA.memcpy_post.
  exists t0, t1, t2, a1', a2', a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|].
  split; [|split; [exact (rw_cb_to_bz _ _ _ _ RW) | exact B]].
  apply BzM.mem_inv_intro; [intros x; exact (BzM.mem_inv_seg_below _ _ _ MI)|].
  intros x b Hx. split; [exact (MI' x b Hx)|].
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a0)) as [L|L];
    [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a0 + bv_unsigned a2)) as [L2|L2]].
  - rewrite (MU x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (BzM.mem_inv_ov_below _ _ _ _ MI Hx).
  - unfold BzM.UTOP. lia.
  - rewrite (MU x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (BzM.mem_inv_ov_below _ _ _ _ MI Hx).
Qed.

Lemma mc_proof : BzA.memcpy_stmt.
Proof.
  unfold BzA.memcpy_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk
    SRC LEN DST OV H47 MI.
  apply evt_to_bz.
  pose proof (rw_cb_of_bz _ _ _ _ DST) as DST'. pose proof (mem_inv_of_bz m MI) as MI'.
  apply (evt_mono rsegs (MCc.memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)).
  - destruct OV as [E|OV].
    + assert (EA : a1 = a0) by (apply bv_eq; symmetry; exact E). subst a1.
      assert (EJ : junk = src).
      { destruct DST' as ((Hwf & HB) & _). cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, HB.
        rewrite app_nil_r in HB. destruct Hwf as [Hl _].
        apply (bytes_at_same m (bv_unsigned a0)); [exact HB | exact SRC | lia]. }
      subst junk.
      exact (MCs.memcpy_same_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m src eq_refl LEN DST' MI').
    + exact (MCp.memcpy_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m src junk SRC LEN DST' OV MI').
  - intros st H. exact (mc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m st MI H47 H).
Qed.

(* the two statements the interceptor walks take as Section hypotheses *)
Theorem ms_callZ_proof : BzF.memset_callZ_stmt.
Proof. exact (memset_callZ_of_contract MSp.memset_holds). Qed.
