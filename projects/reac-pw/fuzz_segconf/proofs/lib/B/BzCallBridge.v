(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 142 of its 194 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/RT_mem_bz.v, with its module paths changed; 36 of its 129 lines of code are new or changed and 101 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/BzCallBridge.v: ported from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/BzCallBridge.v, which equals the A->B relocation (asan-kit elfmap.py + remap.py) of lib/A/BzCallBridge.v at cold/port-fm-int 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_segconf Require Import lib.MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import Img0 AsanRT BzBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import memset_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.F_memset.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_m2s.
Import ListNotations.
Open Scope Z_scope.

Module BzFr := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Frame.
Module BzF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.F_memset.
Module BzR := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_m2s.

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

Lemma rw_cb_of_normalized : forall m' m0' a k bs, mem_rel_cj rsegs m' m0' ->
  BzSt.rw_cells BzI.asegs m0' a [BzCl.CB k bs] -> rw_cells rsegs m' a [CB k bs].
Proof.
  intros m' m0' a k bs REL H. apply rw_cb_of_bz in H. destruct H as [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (bytes_at_rel_cj rsegs m' m0' a _ REL Hb)] | exact (wr_at_rel_cj rsegs m' m0' a _ REL Hw)].
Qed.

Lemma ro_c8_to_bz : forall m a v, bytes_at rsegs m a (le8 v) -> BzSt.ro_cells BzI.asegs m a [BzCl.C8 v].
Proof. intros m a v H. split; [cbn; tauto|]. cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma ro_c1_to_bz : forall m a b, bytes_at rsegs m a [b] -> BzSt.ro_cells BzI.asegs m a [BzCl.C1 b].
Proof. intros m a b H. split; [cbn; tauto|]. cbn [BzCl.cells_bytes BzCl.cbytes app]. exact H. Qed.

Lemma ro_c4_to_bz : forall m a v, bytes_at rsegs m a (le4 v) -> BzSt.ro_cells BzI.asegs m a [BzCl.C4 v].
Proof. intros m a v H. split; [cbn; tauto|]. cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma bytes_at_cat8 : forall m a v bs,
  bytes_at rsegs m a (le8 v) -> bytes_at rsegs m (a + 8) bs -> bytes_at rsegs m a (le8 v ++ bs).
Proof. intros m a v bs H1 H2. apply bytes_at_app. split; [exact H1|]. rewrite length_le8. exact H2. Qed.

Lemma m2s_cells_normalize : forall m, mem_inv rsegs m -> asan_cells m -> BzR.m2s_cells (normalize_cj rsegs m).
Proof.
  intros m HMI HC. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  destruct HC as (HK & HGK & _ & _ & _ & _ & _ & _ & HHI & HGHI & HMB & HGMB & HME & HGME & _ & _ & _).
  unfold BzR.m2s_cells. split; [|split].
  - apply rw_cells_of_bytes; [cbn; tauto | | reflexivity | vm_compute; reflexivity].
    apply bytes_normalize_low; [exact RO | vm_compute; intro Hc; discriminate Hc |].
    cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r.
    apply bytes_at_cat8; [exact HGK|]. apply bytes_at_cat8; [exact HGMB|]. apply bytes_at_cat8; [exact HGME|].
    exact HGHI.
  - apply rw_cells_of_bytes; [cbn; tauto | | reflexivity | vm_compute; reflexivity].
    apply bytes_normalize_low; [exact RO | vm_compute; intro Hc; discriminate Hc |].
    cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r. exact HK.
  - apply rw_cells_of_bytes; [cbn; tauto | | reflexivity | vm_compute; reflexivity].
    apply bytes_normalize_low; [exact RO | vm_compute; intro Hc; discriminate Hc |].
    cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r.
    apply bytes_at_cat8; [exact HHI|]. apply bytes_at_cat8; [exact HMB|]. exact HME.
Qed.

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
