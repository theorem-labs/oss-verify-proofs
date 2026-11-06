(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 142 of its 194 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/RT_mem_bz.v, with its module paths and module names changed; 204 of its 281 lines of code are new or changed and 117 lines of the source are left out. *)
(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/asan_memcpy.v, unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf Require Import lib.MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import asan_memcpy_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec.StrFun.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcpy_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcpy.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcpy_same.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.asan_region_is_poisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_amemcpy.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memcpyw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.R_isPoisoned.
Import ListNotations.
Open Scope Z_scope.

Module SF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec.StrFun.
Module MCc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcpy_c.
Module MCp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcpy.
Module MCs := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcpy_same.
Module ARP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.asan_region_is_poisoned.
Module BzA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_amemcpy.
Module BzW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memcpyw.
Module BzQ := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_qck.
Module BzC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_consts.
Module BzR := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.R_m2s.
Module BzP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.R_isPoisoned.

(* Runs and memory facts in the moved tree's words, from ours (same image, same memory). *)

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

Lemma mem_inv_of_bz : forall m, BzM.mem_inv BzI.asegs m -> mem_inv rsegs m.
Proof. intros m H a b E. exact (BzM.mem_inv_ro BzI.asegs m a b H E). Qed.

Lemma rw_cb_of_bz : forall m a n bs, BzSt.rw_cells BzI.asegs m a [BzCl.CB n bs] -> rw_cells rsegs m a [CB n bs].
Proof. intros m a n bs ((Hwf & HB) & HW). split; [split|]; [exact Hwf | exact HB | exact HW]. Qed.

Lemma rw_cb_to_bz : forall m a n bs, rw_cells rsegs m a [CB n bs] -> BzSt.rw_cells BzI.asegs m a [BzCl.CB n bs].
Proof. intros m a n bs ((Hwf & HB) & HW). split; [split|]; [exact Hwf | exact HB | exact HW]. Qed.

Lemma bytes_at_same : forall m a bs bs', bytes_at rsegs m a bs -> bytes_at rsegs m a bs' ->
  length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (_ & _ & H) (_ & _ & H') L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi), (proj2 (nth_error_None bs' i) ltac:(lia)). reflexivity.
Qed.

(* The plain copy routine at 0x925a4 in the moved tree's words: c-libc's memcpy and memcpy_same proofs. *)

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

(* The helper's premises on the normalized memory, from ours. *)

Lemma le8_of_len8 : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with (bytes_le_to_Z bs mod 2^64).
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- L. apply SF.Z_to_le_bytes_to_Z.
Qed.

Lemma bytes_exist : forall m k A, 0 <= A -> A + Z.of_nat k <= 2^64 ->
  (forall j, 0 <= j < Z.of_nat k -> exists b, mrd rsegs m (wa (A + j)) = Some b) ->
  exists bs, length bs = k /\ bytes_at rsegs m A bs.
Proof.
  intros m k. induction k as [|k IH]; intros A H0 H1 H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & L & B).
    { intros j Hj. replace (A + 1 + j) with (A + (j + 1)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn; lia|]. destruct B as (_ & _ & B).
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
    + rewrite Z.add_0_r. exact Hb.
    + cbn [nth_error]. rewrite <- (B i ltac:(cbn [length] in Hi; lia)).
      replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. reflexivity.
Qed.

Lemma shadow_word : forall m x, mem_inv rsegs m -> shadow_rw m -> app_mem x ->
  exists w, BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) (BzQ.al8 (BzS.shad x)) [BzCl.C8 w].
Proof.
  intros m x HMI HSR Hx. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  assert (HA : forall j, 0 <= j < 8 -> in_shadow (BzQ.al8 (BzS.shad x) + j)).
  { intros j Hj. unfold BzQ.al8, BzS.shad, BzS.SHB, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx.
    Z.div_mod_to_equations. destruct Hx as [Hx|Hx]; [left|right]; lia. }
  pose proof (in_shadow_range _ (HA 0 ltac:(lia))) as R0.
  pose proof (HA 7 ltac:(lia)) as R7.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in R7.
  destruct (bytes_exist m 8 (BzQ.al8 (BzS.shad x)) ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)) as (bs & L & B).
  { intros j Hj. change (Z.of_nat 8) with 8 in Hj. destruct (HSR _ (HA j Hj)) as [_ Hb]. exact Hb. }
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [cbn; tauto|].
  assert (E : BzCl.cells_bytes [BzCl.C8 (Z_to_bv 64 (bytes_le_to_Z bs))] = bs).
  { cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r. exact (le8_of_len8 bs L). }
  rewrite E.
  assert (HL : BzQ.al8 (BzS.shad x) + Z.of_nat (length bs) <= TASK_SIZE)
    by (rewrite L; change (Z.of_nat 8) with 8; unfold TASK_SIZE; lia).
  exact (bytes_normalize_low m _ bs RO HL B).
Qed.

Lemma rng_of_ours : forall m p n, addressable m p n -> end_in_app p n -> (n = 0 \/ app_mem (p + 7)) -> n <= 2^40 ->
  BzQ.rng_ok p n.
Proof.
  intros m p n AD EA A7 HN Hn. split; [|exact HN].
  pose proof (addressable_app m p n AD) as AI. pose proof AD as (P0 & N0 & PE & _).
  pose proof (AI p ltac:(lia)) as A0.
  destruct EA as [E|EA]; [lia|]. destruct A7 as [E|A7]; [lia|].
  unfold BzC.region_in_mem, BzR.kLowMemEnd, BzR.kHighShadowEnd, BzR.kHighMemEnd.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A0, EA, A7, PE.
  destruct A0 as [A0|A0].
  - left. destruct (Z_le_gt_dec (p + n) 0x7fff8000) as [L|L]; [lia|].
    exfalso. pose proof (AI 0x7fff8000 ltac:(lia)) as X. unfold app_mem, LOWMEM_END, HIGHMEM_BEG in X. lia.
  - right. lia.
Qed.

Lemma chk_ok_of_ours : forall m p n, mem_inv rsegs m -> shadow_rw m -> addressable m p n -> end_in_app p n ->
  (n = 0 \/ app_mem (p + 7)) -> n <= 2^40 -> BzQ.chk_ok (normalize_cj rsegs m) p n.
Proof.
  intros m p n HMI HSR AD EA A7 HN. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  split; [exact (acc_normalize m p n RO AD)|]. split.
  - intros Hn. pose proof AD as (P0 & N0 & PE & H).
    destruct (H 0 ltac:(lia)) as (A0 & _). destruct (H (n - 1) ltac:(lia)) as (A1 & _).
    rewrite Z.add_0_r in A0. replace (p + (n - 1)) with (p + n - 1) in A1 by lia.
    destruct (shadow_word m p HMI HSR A0) as [w1 W1].
    destruct (shadow_word m (p + n - 1) HMI HSR A1) as [w2 W2].
    exists w1, w2. split; assumption.
  - exact (rng_of_ours m p n AD EA A7 HN).
Qed.

Lemma ro_c8_norm : forall m A v, ro_agree rsegs m -> A + 8 <= TASK_SIZE -> bytes_at rsegs m A (le8 v) ->
  BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) A [BzCl.C8 v].
Proof.
  intros m A v RO HA H. split; [cbn; tauto|]. cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r.
  exact (bytes_normalize_low m A (le8 v) RO ltac:(rewrite length_le8; exact HA) H).
Qed.

Lemma ro_c1_norm : forall m A b, ro_agree rsegs m -> A + 1 <= TASK_SIZE -> bytes_at rsegs m A [b] ->
  BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) A [BzCl.C1 b].
Proof.
  intros m A b RO HA H. split; [cbn; tauto|]. cbn [BzCl.cells_bytes BzCl.cbytes app].
  exact (bytes_normalize_low m A [b] RO HA H).
Qed.

Lemma icells_normalize : forall m, mem_inv rsegs m -> asan_cells m -> BzW.icells (normalize_cj rsegs m).
Proof.
  intros m HMI HC. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  destruct HC as (HK & HGK & _ & HR & HGR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRM & _ & _).
  unfold BzW.icells. split; [|split; [|split; [|split]]].
  - apply (ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HGK].
  - apply (ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HGR].
  - apply (ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HRM].
  - apply (ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HK].
  - apply (ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HR].
Qed.

Lemma rw_cb_normalize : forall m a n bs, mem_inv rsegs m -> a + Z.of_nat n <= TASK_SIZE ->
  rw_cells rsegs m a [CB n bs] -> BzSt.rw_cells BzI.asegs (normalize_cj rsegs m) a [BzCl.CB n bs].
Proof.
  intros m a n bs HMI HT ((Hwf & HB) & HW). pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (mem_rel_cj_normalize rsegs m RO) as REL.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in Hwf, HB, HW.
  rewrite app_nil_r in HB. rewrite Nat.add_0_r in HW. destruct Hwf as [Hl _].
  split; [split|].
  - cbn. tauto.
  - cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r.
    exact (bytes_normalize_low m a bs RO ltac:(rewrite Hl; exact HT) HB).
  - cbn [BzCl.cells_size BzCl.csize]. rewrite Nat.add_0_r.
    apply (wr_at_norm_cj rsegs m _ a (Z.of_nat n) REL HW).
    intros i Hi. destruct HW as (H0 & H1 & HW').
    apply cj_drop_false_intro; [exact (ro_false_of_wview m _ HMI (HW' i Hi)) |].
    right. rewrite wa_unsigned by (unfold TASK_SIZE in HT; lia). lia.
Qed.

Lemma rw_cb_of_normalized : forall m' m0' a n bs, mem_rel_cj rsegs m' m0' ->
  BzSt.rw_cells BzI.asegs m0' a [BzCl.CB n bs] -> rw_cells rsegs m' a [CB n bs].
Proof.
  intros m' m0' a n bs REL H. destruct (rw_cb_of_bz _ _ _ _ H) as ((Hwf & HB) & HW).
  split; [split|].
  - exact Hwf.
  - exact (bytes_at_rel_cj rsegs m' m0' a _ REL HB).
  - exact (wr_at_rel_cj rsegs m' m0' a _ REL HW).
Qed.

Theorem asan_memcpy_holds : asan_memcpy_contract.
Proof.
  unfold asan_memcpy_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk lo.
  cbv zeta. intros SRC LEN DST OV HN AS AD ES ED H7 HRT HSD HSS HST HK HLO HSP HC HSR HMI.
  unfold ASAN_MEMCPY_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (mem_rel_cj_normalize rsegs m RO) as REL0.
  pose proof AS as (S0 & N0 & SE & _). pose proof AD as (D0 & _ & DE & _).
  assert (EN : Z.of_nat (length src) = bv_unsigned a2) by (rewrite LEN; apply Z2Nat.id; lia).
  assert (S7 : bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a1 + 7)) by (destruct H7 as [?|[? ?]]; [left|right]; assumption).
  assert (D7 : bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) by (destruct H7 as [?|[? ?]]; [left|right]; assumption).
  apply (evt_mono rsegs (fun st => exists st0,
            BzA.amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a1) src lo
              (normalize_cj rsegs m) st0
            /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))).
  - apply (evt_normalize_cj rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply (BzA.amemcpy_spec BzP.rip_proof mc_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc (normalize_cj rsegs m) (bv_unsigned a0) (bv_unsigned a1) src junk lo); rewrite ?EN.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + exact (stk_normalize m lo (bv_unsigned sp) HMI HST ltac:(unfold TASK_SIZE, APPMEM_END in *; lia)).
    + lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + unfold APPMEM_END in *. lia.
    + exact D0.
    + exact S0.
    + unfold APPMEM_END in *. lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + right. exact HSS.
    + right. exact HSD.
    + assert (HL : bv_unsigned a1 + Z.of_nat (length src) <= TASK_SIZE)
        by (rewrite EN; unfold TASK_SIZE, APPMEM_END in *; lia).
      exact (bytes_normalize_low m (bv_unsigned a1) src RO HL SRC).
    + rewrite LEN.
      assert (HL : bv_unsigned a0 + Z.of_nat (Z.to_nat (bv_unsigned a2)) <= TASK_SIZE)
        by (rewrite Z2Nat.id by lia; unfold TASK_SIZE, APPMEM_END in *; lia).
      exact (rw_cb_normalize m (bv_unsigned a0) (Z.to_nat (bv_unsigned a2)) junk HMI HL DST).
    + exact (chk_ok_of_ours m (bv_unsigned a1) (bv_unsigned a2) HMI HSR AS ES S7 HN).
    + exact (chk_ok_of_ours m (bv_unsigned a0) (bv_unsigned a2) HMI HSR AD ED D7 HN).
    + exact (ARP.m2s_cells_normalize m HMI HC).
    + exact (icells_normalize m HMI HC).
    + exact (bz_mem_inv_normalize m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST & RW & B).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    rewrite EN in MU. rewrite LEN in RW.
    assert (MU' : munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 2224, bv_unsigned sp)]
                    m (ms_mem st))
      by (eapply munch_rel_cj; [exact REL0 | exact E8 | exact SAME | exact MU]).
    assert (WM' : wmono rsegs m (ms_mem st)) by (eapply wmono_rel_cj; [exact REL0 | exact E8 | exact SAME | exact WM]).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [exact MU'|split; [exact WM'|split; [|split; [|split; [|split; [|split]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + exact (mem_inv_of_normalized m _ HMI SAME).
    + exact (stk_of_normalized _ _ lo _ E8 ST).
    + exact (rw_cb_of_normalized _ _ _ _ _ E8 RW).
    + exact (bytes_at_rel_cj rsegs _ _ _ _ E8 B).
    + apply (asan_cells_kept _ m _ HC MU'). cbn [disjoint_from].
      split; [|split; [|exact I]]; unfold RT_LO, RT_HI, HIGHMEM_BEG in *; lia.
    + apply (shadow_rw_kept m _ HSR); [|exact WM']. apply (munch_meta _ m _ MU'). cbn [all_app].
      split; [exact (addressable_app m _ _ AD)|]. split; [|exact I].
      intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
Qed.
