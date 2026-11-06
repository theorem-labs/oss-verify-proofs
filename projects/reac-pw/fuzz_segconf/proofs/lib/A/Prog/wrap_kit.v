(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 142 of its 194 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/RT_mem_bz.v; 31 of its 62 lines of code are new or changed and 163 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/FRsl.v, with its module paths changed; 201 of its 242 lines of code are new or changed and 21 lines of the source are left out. *)
(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/wrap_kit.v, unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf Require Import lib.MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strlen_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strlen.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memchr_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memchr.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.asan_memcpy.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_musl.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Spec.StrFun.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcmp_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcmp.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memcmpw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_strncmpw.
Import ListNotations.
Open Scope Z_scope.

Module AMC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.asan_memcpy.
Module BzU := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_musl.
Module BzN := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_strnlenw.
Module SLc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strlen_c.
Module SLp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strlen.
Module MHc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memchr_c.
Module MHp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memchr.
Module BzSF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Spec.StrFun.
Module BzMC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memchrw.
Module MCc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcmp_c.
Module MCp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.memcmp.
Module BzMW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_memcmpw.
Module BzSW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_strncmpw.

(* Shared steps of the wrapper proofs: the walks of the moved tree run on the normalized memory; these lemmas meet
   their premises from the wrapper statements and carry their posts back. *)

(* The plain routines in the moved tree's words, from c-libc's proved contracts (same image, same memory). *)

Lemma bz_mem_inv_same : forall m m', BzM.mem_inv BzI.asegs m -> munch [] m m' -> BzM.mem_inv BzI.asegs m'.
Proof. intros m m' H MU a. unfold BzM.mem_ok_at. rewrite (MU a I). exact (H a). Qed.

Lemma sl_proof : BzU.strlen_stmt.
Proof.
  unfold BzU.strlen_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack
    BUF NZ PAD MI.
  apply AMC.evt_to_bz.
  apply (evt_mono rsegs (SLc.strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)).
  - exact (SLp.strlen_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m str slack BUF NZ PAD (AMC.mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ & B).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact (bz_mem_inv_same m m' MI MU) | exact B].
Qed.

Lemma mch_proof : BzU.memchr_stmt.
Proof.
  unfold BzU.memchr_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
    BUF OK MI.
  apply AMC.evt_to_bz.
  apply (evt_mono rsegs (MHc.memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)).
  - exact (MHp.memchr_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m buf BUF OK (AMC.mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ & B).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact (bz_mem_inv_same m m' MI MU) | exact B].
Qed.

Lemma mcmp_proof : BzU.memcmp_stmt.
Proof.
  unfold BzU.memcmp_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v
    LS RS HM MI.
  apply AMC.evt_to_bz.
  apply (evt_mono rsegs (MCc.memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m)).
  - exact (MCp.memcmp_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m ls rs v LS RS HM (AMC.mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ & _ & _).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|]. exact (bz_mem_inv_same m m' MI MU).
Qed.

Lemma memcmp_model_firstn : forall n l r, BzSF.memcmp_model (firstn n l) (firstn n r) n = BzSF.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* Cells of the runtime on the normalized memory. *)

Lemma rw_c1_norm : forall m A b, mem_inv rsegs m -> A + 1 <= TASK_SIZE -> ro_free A 1 = true -> bytes_at rsegs m A [b] ->
  BzSt.rw_cells BzI.asegs (normalize_cj rsegs m) A [BzCl.C1 b].
Proof.
  intros m A b HMI HA HF H. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  apply rw_cells_of_bytes; [cbn; tauto | | reflexivity | exact HF].
  cbn [BzCl.cells_bytes BzCl.cbytes app]. exact (bytes_normalize_low m A [b] RO HA H).
Qed.

Lemma inited_norm : forall m, mem_inv rsegs m -> asan_cells m ->
  BzSt.rw_cells BzI.asegs (normalize_cj rsegs m) INITED [BzCl.C1 (Z_to_bv 8 1)].
Proof.
  intros m HMI HC. destruct HC as (_ & _ & HI & _).
  apply (rw_c1_norm m _ _ HMI); [unfold INITED, TASK_SIZE; lia | vm_compute; reflexivity | exact HI].
Qed.

Lemma icells_sn_norm : forall m, mem_inv rsegs m -> asan_cells m ->
  bytes_at rsegs m 0xa2a40 (le8 (wa 0x13db28)) -> bytes_at rsegs m (0x13db28 + 251) [Z_to_bv 8 1] ->
  BzN.icells_sn (normalize_cj rsegs m).
Proof.
  intros m HMI HC HG HF. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (inited_norm m HMI HC) as HI.
  destruct HC as (HK & HGK & _).
  unfold BzN.icells_sn. split; [|split; [|split; [|split]]].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HG].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HGK].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HK].
  - exact HI.
  - apply (AMC.ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HF].
Qed.

Lemma icells_mc_norm : forall m, mem_inv rsegs m -> asan_cells m ->
  bytes_at rsegs m 0xa47a8 (le8 (wa MHc.MEMCHR)) -> BzMC.icells_mc (normalize_cj rsegs m).
Proof.
  intros m HMI HC HR. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (inited_norm m HMI HC) as HI.
  destruct HC as (HK & HGK & _).
  unfold BzMC.icells_mc. split; [|split; [|split]].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HGK].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HR].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HK].
  - exact HI.
Qed.

Lemma icells_mcmp_norm : forall m, mem_inv rsegs m -> asan_cells m ->
  bytes_at rsegs m 0xa2a40 (le8 (wa 0x13db28)) ->
  bytes_at rsegs m 0xa4798 (le8 (wa MCc.MEMCMP)) ->
  bytes_at rsegs m (0x13db28 + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (0x13db28 + 255) [Z_to_bv 8 1] ->
  BzMW.icells_mcmp (normalize_cj rsegs m).
Proof.
  intros m HMI HC HG HRM HF4 HF5. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (inited_norm m HMI HC) as HI.
  destruct HC as (HK & HGK & _).
  unfold BzMW.icells_mcmp. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HG].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HGK].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HRM].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HK].
  - exact HI.
  - apply (AMC.ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HF4].
  - apply (AMC.ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HF5].
Qed.

Lemma icells_sc_norm : forall m, mem_inv rsegs m -> asan_cells m ->
  bytes_at rsegs m 0xa2a40 (le8 (wa 0x13db28)) -> bytes_at rsegs m (0x13db28 + 245) [Z_to_bv 8 0] ->
  BzSW.icells_sc (normalize_cj rsegs m).
Proof.
  intros m HMI HC HG HF. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (inited_norm m HMI HC) as HI.
  destruct HC as (HK & HGK & _).
  unfold BzSW.icells_sc. split; [|split; [|split; [|split]]].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HG].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HGK].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HK].
  - exact HI.
  - apply (AMC.ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HF].
Qed.

(* Runs on the normalized memory, and their posts in the wrapper statements' words. *)

Lemma bz_run : forall (Q : machine_state -> Prop) R F pc fc m,
  mem_inv rsegs m ->
  BzE.evt BzI.asegs Q (MS R F pc fc None (normalize_cj rsegs m) (seg_rom rsegs)) ->
  evt rsegs (fun st => exists st0, Q st0 /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))
    (MS R F pc fc None m (seg_rom rsegs)).
Proof.
  intros Q R F pc fc m HMI H.
  apply (evt_normalize_cj rsegs Q R F pc fc None m (seg_rom rsegs) wx_apart_asan (ro_agree_of_mem_inv m HMI)).
  apply bz_evt. exact H.
Qed.

Lemma wrap_post : forall W m m' m0' lo hi,
  mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
  mem_rel_cj rsegs m' m0' -> cj_same rsegs m m' ->
  munch W (normalize_cj rsegs m) m0' -> wmono rsegs (normalize_cj rsegs m) m0' -> stk rsegs m0' lo hi ->
  all_app W -> disjoint_from W RT_LO (RT_HI - RT_LO) ->
  munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo hi /\ asan_cells m' /\ shadow_rw m'.
Proof.
  intros W m m' m0' lo hi HMI HC HSR E8 SAME MU WM ST AW DJ.
  pose proof (mem_rel_cj_normalize rsegs m (ro_agree_of_mem_inv m HMI)) as REL0.
  assert (MU' : munch W m m') by (eapply munch_rel_cj; [exact REL0 | exact E8 | exact SAME | exact MU]).
  assert (WM' : wmono rsegs m m') by (eapply wmono_rel_cj; [exact REL0 | exact E8 | exact SAME | exact WM]).
  split; [exact MU'|]. split; [exact WM'|]. split; [exact (mem_inv_of_normalized m m' HMI SAME)|].
  split; [exact (stk_of_normalized _ _ lo hi E8 ST)|].
  split; [exact (asan_cells_kept W m m' HC MU' DJ)|].
  exact (shadow_rw_kept m m' HSR (munch_meta W m m' MU' AW) WM').
Qed.

Lemma stack_W_ok : forall lo hi, HIGHMEM_BEG <= lo -> lo <= hi -> hi <= APPMEM_END ->
  all_app [(lo, hi)] /\ disjoint_from [(lo, hi)] RT_LO (RT_HI - RT_LO).
Proof.
  intros lo hi H1 H2 H3. cbn [all_app disjoint_from]. split; [split; [|exact I] | split; [|exact I]].
  - intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
  - unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
Qed.

Lemma bytes_at_prefix : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m a l1.
Proof. intros m a l1 l2 H. apply bytes_at_app in H. exact (proj1 H). Qed.

(* The next multiple of 8 at or above an address of the application range stays in it. *)
Lemma round8_le : forall x, x <= 2^47 -> x + (- x) mod 8 <= 2^47.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

(* The part of a buffer below the end of the application range: the walks see the normalized memory, which keeps
   the bytes below TASK_SIZE. *)
Definition cut47 (A : Z) (buf : list byte) : list byte := firstn (Z.to_nat (2^47 - A)) buf.

Lemma cut47_bytes : forall m A buf, bytes_at rsegs m A buf -> bytes_at rsegs m A (cut47 A buf).
Proof.
  intros m A buf H. apply (bytes_at_prefix m _ _ (skipn (Z.to_nat (2^47 - A)) buf)).
  unfold cut47. rewrite firstn_skipn. exact H.
Qed.

Lemma cut47_len : forall A buf, 0 <= A <= 2^47 ->
  A + Z.of_nat (length (cut47 A buf)) <= 2^47 /\ Z.of_nat (length (cut47 A buf)) <= Z.of_nat (length buf).
Proof. intros A buf H. unfold cut47. rewrite length_firstn. lia. Qed.

Lemma find_byte_firstn_lt : forall c l k i, BzSF.find_byte c l = Some i -> (i < k)%nat ->
  BzSF.find_byte c (firstn k l) = Some i.
Proof.
  intros c l. induction l as [|b l IH]; intros k i H Hi; [discriminate|].
  destruct k as [|k]; [lia|]. cbn [firstn BzSF.find_byte] in H |- *.
  destruct (bv_unsigned b =? c); [exact H|].
  destruct (BzSF.find_byte c l) as [j|] eqn:E; [|discriminate].
  injection H as <-. rewrite (IH k j eq_refl ltac:(lia)). reflexivity.
Qed.

Lemma find_byte_firstn_None : forall c l k, BzSF.find_byte c l = None -> BzSF.find_byte c (firstn k l) = None.
Proof.
  intros c l. induction l as [|b l IH]; intros k H; destruct k as [|k]; try reflexivity.
  cbn [firstn BzSF.find_byte] in H |- *.
  destruct (bv_unsigned b =? c); [discriminate|].
  destruct (BzSF.find_byte c l) as [j|] eqn:E; [discriminate|]. rewrite (IH k eq_refl). reflexivity.
Qed.

(* memchr on the cut buffer: the same result and the same reads, when the checked length stays in the range. *)
Lemma memchr_cut : forall A c n buf, 0 <= A -> 0 <= n ->
  A + (if BzSF.memchr_res A c n buf =? 0 then n else BzSF.memchr_res A c n buf - A + 1) <= 2^47 ->
  BzSF.memchr_ok A c n buf ->
  BzSF.memchr_ok A c n (cut47 A buf) /\ BzSF.memchr_res A c n (cut47 A buf) = BzSF.memchr_res A c n buf.
Proof.
  intros A c n buf HA Hn HL OK. unfold BzSF.memchr_ok, BzSF.memchr_res, cut47 in *.
  rewrite firstn_firstn, Nat.min_comm, <- firstn_firstn. rewrite length_firstn.
  destruct (BzSF.find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB;
    try rewrite FB in HL; try rewrite FB in OK; cbv beta iota in HL, OK.
  - destruct (BzSF.find_byte_Some _ _ _ FB) as (Hj & _ & _). rewrite length_firstn in Hj.
    assert (Aj : A + Z.of_nat j + 1 <= 2^47) by (revert HL; destruct (Z.eqb_spec (A + Z.of_nat j) 0); intros; lia).
    pose proof (round8_le (A + Z.of_nat j + 1) Aj) as R8.
    rewrite (find_byte_firstn_lt c _ (Z.to_nat (2^47 - A)) j FB ltac:(lia)).
    split; [cbv beta iota; lia | reflexivity].
  - rewrite (find_byte_firstn_None c _ (Z.to_nat (2^47 - A)) FB).
    split; [cbv beta iota; cbn in HL; lia | reflexivity].
Qed.

(* The search memchr and strnlen make sees the same bytes in the cut buffer. *)
Lemma find_cut : forall A c n buf, 0 <= A -> 0 <= n ->
  A + (if BzSF.memchr_res A c n buf =? 0 then n else BzSF.memchr_res A c n buf - A + 1) <= 2^47 ->
  BzSF.find_byte c (firstn (Z.to_nat n) (cut47 A buf)) = BzSF.find_byte c (firstn (Z.to_nat n) buf).
Proof.
  intros A c n buf HA Hn HL. unfold BzSF.memchr_res, cut47 in *.
  rewrite firstn_firstn, Nat.min_comm, <- firstn_firstn.
  destruct (BzSF.find_byte c (firstn (Z.to_nat n) buf)) as [j|] eqn:FB;
    try rewrite FB in HL; cbv beta iota in HL.
  - destruct (BzSF.find_byte_Some _ _ _ FB) as (Hj & _ & _). rewrite length_firstn in Hj.
    assert (Aj : A + Z.of_nat j + 1 <= 2^47) by (revert HL; destruct (Z.eqb_spec (A + Z.of_nat j) 0); intros; lia).
    exact (find_byte_firstn_lt c _ (Z.to_nat (2^47 - A)) j FB ltac:(lia)).
  - exact (find_byte_firstn_None c _ (Z.to_nat (2^47 - A)) FB).
Qed.
