(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 116 of its 175 lines of code are new or changed and 684 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/BzBridge.v: ported from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/BzBridge.v, which equals the A->B relocation (asan-kit elfmap.py + remap.py) of lib/A/BzBridge.v at cold/port-fm-int 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_segconf Require Import lib.MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import Img0 AsanRT.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.Shadow.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Step.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Mem.
Module BzI := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.ImageA.
Module BzS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.Shadow.
Module BzCl := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Step.

Lemma asegs_rsegs : BzI.asegs = rsegs.
Proof. reflexivity. Qed.

Lemma bz_msteps : forall s s', BzE.msteps rsegs s s' -> msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply msteps_refl.
  - eapply msteps_cons; [exact Hs | exact IH].
Qed.

Lemma bz_evt : forall (Q : machine_state -> Prop) ms, BzE.evt BzI.asegs Q ms -> evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [exact (bz_msteps ms ms' H) | exact HQ].
Qed.

Lemma wx_apart_asan : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

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

Lemma bz_mem_inv_normalize : forall m, BzM.mem_inv BzI.asegs (normalize_cj rsegs m).
Proof.
  intros m. apply BzM.mem_inv_intro.
  - exact seg_addr_below.
  - intros a b H. destruct (mem_inv_cj_normalize rsegs m a b H) as [R [S|T]]; split.
    + exact R.
    + destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|congruence].
      apply seg_addr_below. unfold BzM.seg_addr. rewrite E. reflexivity.
    + exact R.
    + unfold BzM.UTOP, TASK_SIZE in *. lia.
Qed.

Lemma ro_agree_of_mem_inv : forall m, mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m H a E. unfold mrd. destruct (m a) as [b|] eqn:Em; [|reflexivity].
  rewrite (H a b Em) in E. discriminate E.
Qed.

Lemma ro_false_of_wview : forall m x, mem_inv rsegs m -> wview rsegs m x <> None -> ro_addr rsegs x = false.
Proof.
  intros m x HMI Hw. destruct (m x) as [b|] eqn:E; [exact (HMI x b E)|].
  unfold wview in Hw. rewrite E in Hw. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|]; [|reflexivity].
  destruct (seg_writable s); [reflexivity | exfalso; apply Hw; reflexivity].
Qed.

Lemma wview_of_mrd : forall m x b, mrd rsegs m x = Some b -> ro_addr rsegs x = false -> wview rsegs m x <> None.
Proof.
  intros m x b H R. unfold wview. destruct (m x) as [c|] eqn:E; [discriminate|].
  unfold mrd in H. rewrite E in H. unfold ro_addr in R. unfold seg_rom, memory_read in H.
  change (Z.of_N 1) with 1 in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|]; [|discriminate H].
  apply negb_false_iff in R. rewrite R.
  destruct (seg_readable s); [|discriminate H].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (bv_unsigned x - Z.of_N (seg_base s)))) eqn:Eb; [discriminate|].
  exfalso. simpl in H. rewrite Eb in H. discriminate H.
Qed.

Lemma byte_signed_nonneg : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
  revert H. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[bv_unsigned Z.modulo Z.add Z.sub Z.ltb Z.mul Z.div Z.pow].
  change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256. intros H.
  pose proof (Z.div_mod (bv_unsigned b + 128) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (bv_unsigned b + 128) 256 ltac:(lia)). lia.
Qed.

Lemma shad_eq : forall a, BzS.shad a = shadow_addr a.
Proof. reflexivity. Qed.

Lemma acc_normalize : forall m p n, ro_agree rsegs m -> addressable m p n ->
  BzS.acc BzI.asegs (normalize_cj rsegs m) p n.
Proof.
  intros m p n RO (H0 & H1 & H2 & H) i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). exists b. split.
  - assert (Hs : 0 <= shadow_addr (p + i) < TASK_SIZE).
    { unfold shadow_addr, ASAN_K, TASK_SIZE, APPMEM_END in *.
      pose proof (Z.div_pos (p + i) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (p + i) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    rewrite shad_eq. split; [lia|]. split; [cbn [length Z.of_nat]; unfold TASK_SIZE in Hs; lia|].
    intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth_error].
    change (mrd rsegs (normalize_cj rsegs m) (wa (shadow_addr (p + i) + Z.of_nat 0)) = Some b).
    rewrite Z.add_0_r. rewrite mrd_normalize_cj; [exact Hb | exact RO |].
    right. right. rewrite wa_unsigned by (unfold TASK_SIZE in Hs; lia). lia.
  - unfold BzS.sh_ok. unfold shadow_ok in Hok. destruct Hok as [E|[E1 E2]].
    + left. rewrite byte_signed_nonneg by lia. exact E.
    + right. pose proof (Z.mod_pos_bound (p + i) 8 ltac:(lia)).
      rewrite byte_signed_nonneg by lia. lia.
Qed.

Fixpoint ro_free (a : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => negb (ro_addr rsegs (wa a)) && ro_free (a + 1) n'
  end.

Lemma ro_free_at : forall n a i, ro_free a n = true -> 0 <= i < Z.of_nat n -> ro_addr rsegs (wa (a + i)) = false.
Proof.
  induction n as [|n IH]; intros a i H Hi; [lia|].
  cbn [ro_free] in H. apply andb_prop in H as [H0 H1].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r. apply negb_true_iff. exact H0.
  - replace (a + i) with (a + 1 + (i - 1)) by lia. apply IH; [exact H1 | lia].
Qed.

Lemma wr_at_of_bytes : forall m a bs, bytes_at rsegs m a bs -> ro_free a (length bs) = true ->
  wr_at rsegs m a (Z.of_nat (length bs)).
Proof.
  intros m a bs (H0 & H1 & H) Hf. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (H (Z.to_nat i) ltac:(lia)) as Hr. rewrite Z2Nat.id in Hr by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E.
  - exact (wview_of_mrd m _ b Hr (ro_free_at _ a i Hf Hi)).
  - apply nth_error_None in E. lia.
Qed.

Lemma bytes_normalize_low : forall m a bs, ro_agree rsegs m -> a + Z.of_nat (length bs) <= TASK_SIZE ->
  bytes_at rsegs m a bs -> bytes_at rsegs (normalize_cj rsegs m) a bs.
Proof. intros m a bs RO Hl H. exact (bytes_at_normalize_cj_low rsegs m a bs RO Hl H). Qed.

Lemma rw_cells_of_bytes : forall m a cs, BzCl.cells_wf cs -> bytes_at rsegs m a (BzCl.cells_bytes cs) ->
  length (BzCl.cells_bytes cs) = BzCl.cells_size cs -> ro_free a (BzCl.cells_size cs) = true ->
  BzSt.rw_cells BzI.asegs m a cs.
Proof.
  intros m a cs Hwf Hb Hl Hf. split; [split; [exact Hwf | exact Hb]|].
  rewrite <- Hl. apply wr_at_of_bytes; [exact Hb | rewrite Hl; exact Hf].
Qed.

Lemma stk_normalize : forall m lo hi, mem_inv rsegs m -> stk rsegs m lo hi -> hi <= TASK_SIZE ->
  stk rsegs (normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi HMI (H0 & H1 & H) Hhi. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (mem_rel_cj_normalize rsegs m RO) as REL.
  split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as (Hw & b & Hb).
  assert (Ea : bv_unsigned (wa a) = a) by (apply wa_unsigned; unfold TASK_SIZE in Hhi; lia).
  assert (K : cj_drop rsegs (wa a) = false).
  { apply cj_drop_false_intro; [exact (ro_false_of_wview m _ HMI Hw)|]. right. rewrite Ea. lia. }
  split.
  - rewrite (wview_rel_cj rsegs m _ _ REL K). exact Hw.
  - exists b. rewrite mrd_normalize_cj; [exact Hb | exact RO |]. right. right. rewrite Ea. lia.
Qed.

Lemma stk_of_normalized : forall m' m0' lo hi, mem_rel_cj rsegs m' m0' -> stk rsegs m0' lo hi -> stk rsegs m' lo hi.
Proof.
  intros m' m0' lo hi REL (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_cj rsegs m' m0' _ REL (keep_of_wview_cj rsegs m' m0' _ REL Hw)). exact Hw.
  - exists b. exact (mrd_rel_cj rsegs m' m0' _ b REL Hb).
Qed.

Lemma mem_inv_of_normalized : forall m m', mem_inv rsegs m -> cj_same rsegs m m' -> mem_inv rsegs m'.
Proof.
  intros m m' HMI SAME a b H. destruct (cj_drop rsegs a) eqn:D.
  - rewrite (SAME a D) in H. exact (HMI a b H).
  - exact (proj1 (cj_drop_false rsegs a D)).
Qed.
