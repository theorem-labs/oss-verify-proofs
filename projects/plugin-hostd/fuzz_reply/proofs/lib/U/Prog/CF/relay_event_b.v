(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and addresses changed; 578 of its 650 lines of code are new or changed and 1157 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  strlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Open Scope Z_scope.

Lemma ev_bytes_at_trunc : forall m A (s t : list byte) n,
  bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A (s ++ firstn n t).
Proof.
  intros m A s t n H. apply bytes_at_app in H. destruct H as [H1 H2]. apply bytes_at_app. split; [exact H1|].
  rewrite <- (firstn_skipn n t) in H2. apply bytes_at_app in H2. exact (proj1 H2).
Qed.

Lemma ev_bytes_at_pre : forall m A (s t : list byte), bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A s.
Proof. intros m A s t H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma ev_bytes_at_str : forall m A (s t : list byte) (b : byte), bytes_at rsegs m A (s ++ b :: t) ->
  bytes_at rsegs m A (s ++ [b]).
Proof. intros m A s t b H. apply (ev_bytes_at_pre _ _ _ t). rewrite <- app_assoc. exact H. Qed.

Lemma ev_rw_cells_cut : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma ev_rw_cells_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Definition ev_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (e : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (j : list byte) m',
    ms' = MS (mkR (Z_to_bv 64 0x13310) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a0 (Z_to_bv 64 203000)
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x13328) fc None m' (seg_rom rsegs)
    /\ a1 = Z_to_bv 64 (Z.of_nat (length e) + 1)
    /\ munch [(bv_unsigned sp + -32, bv_unsigned sp); (203004, 203008)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]
    /\ rw_cells rsegs m' 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]
    /\ bytes_at rsegs m' (bv_unsigned a0) (e ++ [Z_to_bv 8 0]).

Lemma ev_run1 : pthread_mutex_lock_contract -> strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (e slack : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 203040 <= lo ->
  mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned a0) (e ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) e ->
  (- (bv_unsigned a0 + Z.of_nat (length e) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (bv_unsigned a0 + (Z.of_nat (length e) + 1) <= 202912 \/ 203040 <= bv_unsigned a0) ->
  (bv_unsigned a0 + (Z.of_nat (length e) + 1) <= bv_unsigned sp - 128 \/ bv_unsigned sp <= bv_unsigned a0) ->
  rw_cells rsegs m 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  evt rsegs (ev_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc e m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x132d8) fc None m (seg_rom rsegs)).
Proof.
  intros SPL SLEN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e slack ST LO LOG MI HX NZ PAD SEPR SEPS GL.
  pose proof (bytes_at_bound _ _ _ _ HX) as XB. rewrite length_app in XB. cbn [length] in XB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (Z.mod_pos_bound (- (bv_unsigned a0 + Z.of_nat (length e) + 1)) 8 ltac:(lia)) as R8.
  remember (Z.to_nat ((- (bv_unsigned a0 + Z.of_nat (length e) + 1)) mod 8)) as k eqn:Ek.
  assert (KZ : Z.of_nat k = (- (bv_unsigned a0 + Z.of_nat (length e) + 1)) mod 8) by (rewrite Ek; apply Z2Nat.id; lia).
  clear Ek.
  assert (HS : bytes_at rsegs m (bv_unsigned a0) (e ++ Z_to_bv 8 0 :: firstn k slack)).
  { replace (e ++ Z_to_bv 8 0 :: firstn k slack) with ((e ++ [Z_to_bv 8 0]) ++ firstn k slack)
      by (rewrite <- app_assoc; reflexivity).
    apply ev_bytes_at_trunc. rewrite <- app_assoc. exact HX. }
  assert (KL : length (firstn k slack) = k) by (apply firstn_length_le; lia).
  clear HX.
  destruct (ev_rw_cells_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (ev_rw_cells_cut _ _ [_] [_] GL12) as [GL1 GL2]. clear GL12.
  assert (TB : bytes_at rsegs m 203000 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. exact (ev_bytes_at_pre _ _ _ _ B). }
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (203004, 203008)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  step. step. step. step. step. step. step. step. step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            203000 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
  1: reflexivity.
  1: exact TB.
  1: reflexivity.
  1: exact GL1.
  1: assumption.
  cbv delta [mkR].
  match goal with H : rw_cells _ _ _ [C4 (Z_to_bv 64 16)] |- _ => rename H into L16 end.
  step. step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e (firstn k slack)).
  1: eassumption.
  1: exact NZ.
  1: rewrite KL; lia.
  1: assumption.
  cbv delta [mkR].
  pose proof (ev_bytes_at_str _ _ _ _ _ HS) as LB.
  step. step. step.
  apply evt_done. unfold ev_mid.
  do 16 eexists. split; [reflexivity|].
  split; [rewrite ?unsigned_lit by lia; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [exact (ev_rw_cells_join _ _ _ [_] [_; _] GL0 (ev_rw_cells_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl)|].
  exact LB.
Qed.

Lemma ev_run2 : pthread_mutex_unlock_contract ->
  forall x1 gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 ra0 s00 s01 : word) (j : list byte) (lo : Z),
  rw_cells rsegs m (bv_unsigned sp0 + -32) [CB 8 j; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] ->
  stk rsegs m lo (bv_unsigned sp0) -> lo + 96 <= bv_unsigned sp0 -> 203040 <= lo ->
  mem_inv rsegs m ->
  evt rsegs (pthread_mutex_unlock_post ra0 sp0 gp tp s00 s01 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 203000 lo m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp0 + -32)) gp tp x5 x6 x7 x8 (Z_to_bv 64 203000) x10 x11 x12 x13 x14 x15
             x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13310) fc None m (seg_rom rsegs)).
Proof.
  intros SPU x1 gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
    F fc m sp0 ra0 s00 s01 j lo FR GL ST LO LOG MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  step. step. step. step. step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -32 + 32)) with sp0
    by (replace (bv_unsigned sp0 + -32 + 32) with (bv_unsigned sp0) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  step.
  eapply (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 203000 lo);
    [reflexivity | exact GL | exact ST | lia | lia | exact MI].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c relay_event_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c relay_event_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Local Open Scope Z_scope.

Lemma ev_bytes_at_transfer : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) E. split; [exact H1|]. split; [exact H2|].
  intros i Hi. change (mbyte segs m' (a + Z.of_nat i) = nth_error bs i).
  rewrite E by lia. exact (H i Hi).
Qed.

Lemma ev_rw_cells_transfer : forall segs m m' a cs, rw_cells segs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte segs m' (a + i) = mbyte segs m (a + i) /\
     (writable_at segs m (a + i) -> writable_at segs m' (a + i))) ->
  rw_cells segs m' a cs.
Proof.
  intros segs m m' a cs [[Hwf Hb] (Ha & Hn & Hw)] E.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - apply (ev_bytes_at_transfer segs m); [exact Hb|]. intros i Hi. apply E. rewrite <- L. exact Hi.
  - split; [exact Ha|]. split; [exact Hn|]. intros i Hi. apply (proj2 (E i Hi)). exact (Hw i Hi).
Qed.

Lemma ev_munch_mbyte : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  mbyte segs m' a = mbyte segs m a.
Proof.
  intros segs W m m' a H R O. unfold mbyte. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma ev_munch_writable : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros segs W m m' a H R O. unfold writable_at, wview. rewrite (H (Z_to_bv 64 a)); [tauto|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma ev_munch_present : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  present m a -> present m' a.
Proof.
  intros W m m' a H R O [b E]. exists b. rewrite (H (Z_to_bv 64 a)); [exact E|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma ev_find_segment_none_above : forall segs top a n,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true -> top <= a -> 0 < n ->
  find_segment segs a n = None.
Proof.
  induction segs as [|s segs IH]; intros top a n H Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - apply IH with top; assumption.
Qed.

Lemma ev_rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 20) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ev_rsegs_res_top :
  forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 21) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ev_writable_hi_present : forall m a, 2 ^ 20 <= a < 2 ^ 64 -> writable_at rsegs m a -> present m a.
Proof.
  intros m a Ha. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite unsigned_lit by lia.
  rewrite (ev_find_segment_none_above rsegs (2 ^ 20) a 1 ev_rsegs_top) by lia.
  intros W. exfalso. apply W. reflexivity.
Qed.

Lemma ev_ro_addr_hi : forall a, 2 ^ 20 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr, wa. rewrite unsigned_lit by lia.
  rewrite (ev_find_segment_none_above rsegs (2 ^ 20) a 1 ev_rsegs_top) by lia. reflexivity.
Qed.

Lemma ev_ro_glob_check : forallb (fun i => negb (ro_addr rsegs (wa (202912 + Z.of_nat i)))) (seq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ev_ro_addr_glob : forall a, 202912 <= a < 203040 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. pose proof (proj1 (forallb_forall _ _) ev_ro_glob_check (Z.to_nat (a - 202912))) as H.
  rewrite in_seq in H. specialize (H ltac:(lia)). rewrite Z2Nat.id in H by lia.
  replace (202912 + (a - 202912)) with a in H by lia.
  destruct (ro_addr rsegs (wa a)); [discriminate H | reflexivity].
Qed.

Lemma ev_wx_rsegs : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ev_stk_norm : forall m lo hi, ro_agree rsegs m -> stk rsegs m lo hi -> 2 ^ 20 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RA (H1 & H2 & H) Hlo Hhi. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [W [b Eb]].
  pose proof (mem_rel_normalize rsegs m RA) as MRL.
  assert (E : ro_addr rsegs (wa a) = false) by (apply ev_ro_addr_hi; lia).
  split; [rewrite (wview_rel_rw rsegs m _ _ MRL E); exact W|].
  exists b. rewrite <- (mrd_rel rsegs m _ _ MRL). exact Eb.
Qed.

Lemma ev_rw_cells_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs RA [[W B] WR] Hro. pose proof (mem_rel_normalize rsegs m RA) as MRL.
  split; [split; [exact W | exact (bytes_at_normalize rsegs m _ _ RA B)] |].
  exact (wr_at_norm rsegs m _ A _ MRL WR Hro).
Qed.

Lemma ev_rw_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[W B] WR].
  split; [split; [exact W | exact (proj2 (bytes_at_rel rsegs m m0 _ _ HR) B)] |].
  exact (wr_at_rel rsegs m m0 _ _ HR WR).
Qed.

Lemma ev_ret_pc_of_ok : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
  pose proof (bv_unsigned_in_range 64 k) as R. unfold bv_modulus in R.
  assert (T : Z.testbit (bv_unsigned k) 0 = false).
  { rewrite <- H at 1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec. apply Bool.andb_false_r. }
  assert (E : bv_unsigned k mod 2 = 0) by (rewrite Zmod_odd, <- Z.bit0_odd, T; reflexivity).
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [exact R | exact E].
Qed.

Lemma ev_blk_out : forall (P : Z -> Prop) q k, (forall i, 0 <= i < k -> ~ P (q + i)) ->
  (forall a, 202912 <= a < 203040 -> P a) -> q + k <= 202912 \/ 203040 <= q \/ k <= 0.
Proof.
  intros P q k H G.
  destruct (Z_le_gt_dec (q + k) 202912) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec 203040 q) as [D'|D']; [right; left; exact D'|].
  destruct (Z_le_gt_dec k 0) as [D''|D'']; [right; right; exact D''|].
  exfalso. apply (H (Z.max q 202912 - q)); [lia|].
  replace (q + (Z.max q 202912 - q)) with (Z.max q 202912) by lia. apply G. lia.
Qed.

Section Regs.
Context {fx : YK11.FPState}.

Lemma ev_canon_mkst : forall regs pc mem rom,
  RegisterBridge.canonical_register_state (mkst regs pc mem rom) =
  MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem rom.
Proof using. reflexivity. Qed.

Lemma ev_getr_of_eqv : forall M R (r : bv 5), Regs6ss.xregs_eqv M R -> bv_eqb r 0 = false -> getr R r = reg_get M r.
Proof using. intros M R r H NZ. unfold getr. rewrite NZ. symmetry. apply H. exact NZ. Qed.

Lemma ev_preserved_chain : forall (own : Z -> bool) regs R1 R2 R3 M1 M3,
  Regs6ss.xregs_eqv M1 R1 -> regs_preserved R1 R2 -> Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> own r = false ->
     reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r) /\ reg_get M1 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> own r = true -> reg_get M3 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  regs_preserved regs R3.
Proof using.
  intros own regs R1 R2 R3 M1 M3 X1 P X3 K1 K2 r Hr.
  assert (Hk : 0 < r < 32) by (unfold callee_saved in Hr; lia).
  assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
  rewrite (ev_getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ.
  destruct (own r) eqn:O; [exact (K2 r Hr O)|].
  destruct (K1 r Hr O) as [E1 E2]. rewrite E1, <- E2.
  pose proof (P r Hr) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3. symmetry. apply X1. exact NZ.
Qed.

Lemma ev_unpack : forall (Q : machine_state -> Prop) mem ms',
  (exists can, (exists s0, Q s0 /\ ms_rel rsegs can s0 /\ ro_same rsegs mem (ms_mem can)) /\
     Regs6ss.ms_eqv can ms') ->
  exists s0 R' m', Q s0 /\
    ms' = {| ms_regs := R'; ms_fregs := ms_fregs s0; ms_pc_val := ms_pc_val s0; ms_svc_pending := ms_svc_pending s0;
             ms_resv := ms_resv s0; ms_fcsr := ms_fcsr s0; ms_mem := m'; ms_rom := ms_rom s0 |} /\
    Regs6ss.xregs_eqv (ms_regs s0) R' /\ mem_rel rsegs m' (ms_mem s0) /\ ro_same rsegs mem m'.
Proof.
  intros Q mem ms' (can & (s0 & HQ & HR & HO) & HE).
  destruct ms' as [r f p sv rv c mm o], can as [cr cf cp csv crv cc cmm co], s0 as [zr zf zp zsv zrv zc zmm zo].
  destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct HE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *. subst.
  do 3 eexists. split; [exact HQ|]. split; [reflexivity|]. split; [exact E1|]. split; [exact R8 | exact HO].
Qed.

End Regs.

Ltac ev_win := cbn [disjoint_from outside]; simpl_sizes;
  repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.

Section EvB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).

Lemma ev_in_img_low : forall a, ms_segs Bm = rsegs -> in_img Bm a -> 0 <= a < 2 ^ 21.
Proof using.
  intros a SEGS (_ & s & Hin & H1 & H2). rewrite SEGS in Hin.
  pose proof (proj1 (forallb_forall _ _) ev_rsegs_res_top s Hin) as T. apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma ev_not_owned : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> img_plain Bm a -> ~ owned Bm L0 A0 a.
Proof using AX.
  intros L0 A0 m0 md0 a HM (Hi & Hs & Hc & He) [Ho|Ho].
  - exact (Hc (ax_img AX L0 A0 m0 md0 a HM Hi Ho)).
  - exact (Hs Ho).
Qed.

Lemma ev_mr_munch : forall L0 A0 m0 m0' md0 lo0 hi0, aa_MR API L0 A0 m0 md0 ->
  munch [(lo0, hi0); (203004, 203008)] m0 m0' -> alloc_ceiling <= lo0 ->
  (forall a, 203004 <= a < 203008 -> img_plain Bm a) ->
  aa_MR API L0 A0 m0' md0.
Proof using AX.
  intros L0 A0 m0 m0' md0 lo0 hi0 HM MU HLO IMG.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_lt as AC.
  destruct (mr_model _ _ LAWS _ _ _ _ HM) as (Hh & Hl & Hmat).
  assert (OUT : forall x, 0 <= x < alloc_ceiling -> ~ (203004 <= x < 203008) -> outside [(lo0, hi0); (203004, 203008)] x).
  { intros x Hx Hn. cbn [outside]. split; [lia|]. split; [exact Hn | exact I]. }
  assert (NOW : forall x, owned Bm L0 A0 x -> ~ (203004 <= x < 203008)).
  { intros x Ho Hx. exact (ev_not_owned L0 A0 m0 md0 x HM (IMG x Hx) Ho). }
  eapply (mr_frame Bm _ LAWS L0 A0 m0 m0' md0 md0 HM).
  - intros a Ho. pose proof (mr_owned_low Bm _ LAWS _ _ _ _ a HM Ho) as Ha.
    eapply ev_munch_mbyte; [exact MU | lia | apply OUT; [lia | exact (NOW a Ho)]].
  - intros a Ho Hp. pose proof (mr_owned_low Bm _ LAWS _ _ _ _ a HM Ho) as Ha.
    eapply ev_munch_present; [exact MU | lia | apply OUT; [lia | exact (NOW a Ho)] | exact Hp].
  - intros p n i Hin Hi. destruct (mr_blocks Bm _ LAWS L0 A0 m0 md0 p n i HM Hin Hi) as (Hp & H4 & Hc & _).
    eapply ev_munch_present; [exact MU | lia | apply OUT; [lia|] | exact Hp].
    intros Hx. apply (ax_blocks_img AX L0 A0 m0 md0 p n i HM Hin Hi). exact (proj1 (IMG _ Hx)).
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hmat.
Qed.

Theorem relay_event_holds (F : ResFormT) : pthread_mutex_lock_contract -> pthread_mutex_unlock_contract ->
  strlen_contract -> send_line_contract Bm API F -> relay_event_contract Bm API F.
Proof using AX.
  intros SPL SPU SLEN SL.
  unfold relay_event_contract.
  intros L A regs mem md bnd e slack O junk cl br dd ei mx nout cap out ev.
  cbv zeta.
  intros SEGS PRE INIT TPE ERR4 HERR RA HX NZ PAD SEPR SEPE SEPS IMGR IMGC IMGE HOME GL Hcl Hbr Hdd Hei
    CCL CBR CDD CEI COUT CERR HOUT REQ RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERRW & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold RELAY_EVENT_K, RELAY_EVENT_FRAME, SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK,
    G_RELAY_LO, G_LOCK_HI, G_LOCK, G_CLIENT, G_BROKEN, G_DEAD, G_EINTR, G_OUTV, ERRNO_OFF, RELAY_EVENT in *.
  rewrite SEGS in *.
  change (PropExec.getr regs 2) with (reg_get regs 2) in *.
  change (PropExec.getr regs 10) with (reg_get regs 10) in *.
  change (PropExec.getr regs 1) with (reg_get regs 1) in *.
  unfold spZ in HAL, HCEIL, H63, HWS.
  change (getr regs 2) with (reg_get regs 2) in HAL, HCEIL, H63, HWS.
  set (sp := reg_get regs 2) in *.
  set (lpw := reg_get regs 10) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ HX) as XB. rewrite length_app in XB. cbn [length] in XB.
  assert (ERRL : 0 <= errno_addr Bm /\ errno_addr Bm + 4 <= 2 ^ 21).
  { pose proof (ev_in_img_low (errno_addr Bm) SEGS (IMGE (errno_addr Bm) ltac:(lia))) as E1.
    pose proof (ev_in_img_low (errno_addr Bm + 3) SEGS (IMGE (errno_addr Bm + 3) ltac:(lia))) as E2. lia. }
  assert (OUTB : bv_unsigned out + bv_unsigned cap <= alloc_ceiling).
  { destruct HOUT as [(C0 & O0 & _) | (_ & _ & _ & (_ & FB & _) & _)]; lia. }
  assert (OUTG : bv_unsigned out + bv_unsigned cap <= 202912 \/ 203040 <= bv_unsigned out \/ bv_unsigned cap <= 0).
  { destruct HOUT as [(C0 & O0 & _) | (_ & _ & _ & (_ & _ & FI) & _)]; [right; right; lia|].
    apply (ev_blk_out (in_img Bm) _ _ FI). intros a Ha. exact (proj1 (IMGR a Ha)). }
  assert (ST : stk rsegs mem (bv_unsigned sp - 8400) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (ev_writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (mem_rel_normalize rsegs mem RA) as MRL0.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite ev_canon_mkst. unfold Regs6ss.mkR_of. fold sp. fold lpw.
    eapply evt_normalize; [exact ev_wx_rsegs | exact RA |].
    eapply (ev_run1 SPL SLEN) with (lo := bv_unsigned sp - 8400) (e := e) (slack := slack).
    - apply ev_stk_norm; [exact RA | exact ST | lia | lia].
    - lia.
    - lia.
    - apply mem_inv_normalize.
    - apply bytes_at_normalize; [exact RA | exact HX].
    - exact NZ.
    - exact PAD.
    - lia.
    - lia.
    - apply ev_rw_cells_norm; [exact RA | exact GL |]. intros i Hi. cbn in Hi. apply ev_ro_addr_glob. lia. }
  intros ms1 PK1.
  destruct (ev_unpack _ _ _ PK1) as (s1 & R1 & m1 & Q1 & -> & X1 & MR1 & RS1). clear PK1.
  unfold ev_mid in Q1.
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j & m1n
    & -> & EA1 & MU1 & WM1 & MI1 & FR1 & GL1 & LB1).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in X1, MR1 |- *.
  pose proof (munch_rel rsegs _ mem _ m1 m1n MRL0 MR1 RS1 MU1) as MU1r.
  pose proof (wmono_rel rsegs mem _ m1 m1n MRL0 MR1 RS1 WM1) as WM1r.
  pose proof (ev_rw_cells_rel _ _ _ _ MR1 FR1) as FR1r.
  pose proof (ev_rw_cells_rel _ _ _ _ MR1 GL1) as GL1r.
  pose proof (proj2 (bytes_at_rel rsegs m1 m1n _ _ MR1) LB1) as LB1r.
  pose proof (ro_agree_same rsegs mem m1 RA RS1) as RA1.
  clear MU1 WM1 FR1 GL1 LB1 MI1.
  assert (G1_1 : getr R1 1 = Z_to_bv 64 0x13310)
    by (rewrite (ev_getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (G1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -32))
    by (rewrite (ev_getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (G1_4 : getr R1 4 = reg_get regs 4)
    by (rewrite (ev_getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (G1_9 : getr R1 9 = Z_to_bv 64 203000)
    by (rewrite (ev_getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (G1_10 : getr R1 10 = lpw)
    by (rewrite (ev_getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (G1_11 : getr R1 11 = Z_to_bv 64 (Z.of_nat (length e) + 1))
    by (rewrite (ev_getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; exact EA1).
  assert (SP1 : bv_unsigned (getr R1 2) = bv_unsigned sp + -32) by (rewrite G1_2; apply unsigned_lit; lia).
  assert (MR1A : aa_MR API L A m1 md)
    by exact (ev_mr_munch L A mem m1 md _ _ HMR MU1r ltac:(lia) (fun a Ha => IMGR a ltac:(lia))).
  assert (PRE1 : call_pre_k Bm (aa_MR API) (112 + (8192 + 64)) L A R1 m1 md).
  { split; [exact MR1A|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite G1_1; apply bv_eq; vm_compute; reflexivity|].
    unfold spZ. rewrite SP1.
    split; [replace (bv_unsigned sp + -32) with (bv_unsigned sp + (-2) * 16) by ring; rewrite Z.mod_add by lia;
            exact HAL|].
    split; [lia|]. split; [lia|].
    split; [intros a Ha; rewrite SEGS; apply WM1r; apply HWS; lia|].
    split; [rewrite G1_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; apply WM1r; apply HERRW; exact Ha|].
    intros HI. rewrite INIT in HI. discriminate HI. }
  assert (CCL1 : rw_cells rsegs m1 136740 [C4 (Z_to_bv 64 cl)])
    by (apply (rw_cells_transport rsegs _ mem m1 _ _ CCL MU1r WM1r); ev_win).
  assert (CBR1 : rw_cells rsegs m1 202916 [C1 (Z_to_bv 8 br)])
    by (apply (rw_cells_transport rsegs _ mem m1 _ _ CBR MU1r WM1r); ev_win).
  assert (CDD1 : rw_cells rsegs m1 202924 [C1 (Z_to_bv 8 dd)])
    by (apply (rw_cells_transport rsegs _ mem m1 _ _ CDD MU1r WM1r); ev_win).
  assert (CEI1 : rw_cells rsegs m1 202928 [C1 (Z_to_bv 8 ei)])
    by (apply (rw_cells_transport rsegs _ mem m1 _ _ CEI MU1r WM1r); ev_win).
  assert (COUT1 : rw_cells rsegs m1 202968 [C8 mx; C8 nout; C8 cap; C8 out])
    by (apply (rw_cells_transport rsegs _ mem m1 _ _ COUT MU1r WM1r); ev_win).
  assert (CERR1 : rw_cells rsegs m1 (errno_addr Bm) [C4 ev])
    by (apply (rw_cells_transport rsegs _ mem m1 _ _ CERR MU1r WM1r); ev_win).
  assert (HOUT1 : (bv_unsigned cap = 0 /\ bv_unsigned out = 0 /\ bv_unsigned nout = 0 /\ O = []) \/
     (0 < bv_unsigned cap /\ bv_unsigned nout <= bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L A) /\
      fresh_block Bm (bv_unsigned out) (bv_unsigned cap) /\ bytes_at rsegs m1 (bv_unsigned out) (O ++ junk) /\
      Z.of_nat (length O) = bv_unsigned nout /\ Z.of_nat (length junk) = bv_unsigned cap - bv_unsigned nout /\
      (bv_unsigned lpw + (Z.of_nat (length e) + 1) <= bv_unsigned out \/
       bv_unsigned out + bv_unsigned cap <= bv_unsigned lpw))).
  { destruct HOUT as [H|(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)]; [left; exact H|right].
    do 4 (split; [assumption|]). split; [|split; [assumption | split; assumption]].
    destruct H4 as (F1 & F2 & F3).
    apply (bytes_at_transport rsegs _ mem m1 _ _ H5 MU1r). rewrite length_app, Nat2Z.inj_add, H6, H7. ev_win. }
  pose proof (SL L A R1 m1 md bnd (e ++ [Z_to_bv 8 0]) O junk cl br dd ei mx nout cap out ev) as SLc.
  cbv zeta in SLc.
  unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK, G_RELAY_LO, G_RELAY_HI, G_CLIENT, G_BROKEN,
    G_DEAD, G_EINTR, G_OUTV, ERRNO_OFF, SEND_LINE in SLc.
  rewrite SEGS in SLc.
  change (PropExec.getr R1 1) with (getr R1 1) in SLc.
  change (PropExec.getr R1 2) with (getr R1 2) in SLc.
  change (PropExec.getr R1 10) with (getr R1 10) in SLc.
  change (PropExec.getr R1 11) with (getr R1 11) in SLc.
  rewrite G1_10, G1_11, G1_1, (unsigned_lit (Z.of_nat (length e) + 1)) in SLc by lia.
  rewrite SP1 in SLc.
  specialize (SLc eq_refl PRE1 INIT TPE ERR4 ltac:(lia) RA1 LB1r ltac:(rewrite length_app; cbn [length]; lia)
    ltac:(lia) ltac:(lia) ltac:(lia) (fun a Ha => IMGR a ltac:(lia)) IMGC IMGE).
  specialize (SLc ltac:(right; destruct HOME as (q & kq & H1 & _ & H3 & H4 & H5); exists q, kq; tauto)
    Hcl Hbr Hdd Hei CCL1 CBR1 CDD1 CEI1 COUT1 CERR1 HOUT1 REQ RES ROOM).
  eapply SR_bind; [exact SLc|]. clear SLc.
  intros c2 RET.
  destruct RET as (L' & A' & R2 & m2 & md' & OUT' & CAP' & junk' & -> & RP & INIT' & RES' & RA2 & LB2
    & CCL2 & CBR2 & CDD2 & CEI2 & DEAD2 & LIVE2).
  unfold relay_post in RP. rewrite SEGS in RP.
  destruct RP as (HMR2 & HWF2 & HBD2 & HLE2 & HREG2 & HPA2 & HUB2 & HZB2 & HOWN2 & HPRES2 & HVM2 & HFR2 & HBK2 & HSCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  assert (G2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -32))
    by exact (eq_trans (HPRES2 2 ltac:(unfold callee_saved; lia)) G1_2).
  assert (G2_9 : reg_get R2 9 = Z_to_bv 64 203000)
    by exact (eq_trans (HPRES2 9 ltac:(unfold callee_saved; lia)) G1_9).
  assert (NSC1 : forall a, ~ (bv_unsigned sp - 8400 <= a < bv_unsigned sp + -32) ->
            ~ (errno_addr Bm <= a < errno_addr Bm + 4) -> ~ scratch_k Bm (112 + (8192 + 64)) R1 a).
  { intros a H1 H2. unfold scratch_k, spZ. rewrite SP1. intros [H|H]; [apply H1; lia | exact (H2 H)]. }
  assert (KEEPS : forall a, bv_unsigned sp + -32 <= a < bv_unsigned sp ->
            mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
  { intros a Ha. apply HFR2.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low Bm _ LAWS _ _ _ _ a HMR Ho). lia.
    - intros Ho. pose proof (mr_owned_low Bm _ LAWS _ _ _ _ a HMR2 Ho). lia.
    - apply NSC1; lia.
    - unfold send_writes, G_BROKEN, G_EINTR, G_OUTV. intros [X|[X|[X|[_ X]]]]; lia. }
  assert (KEEPG : forall a, 203000 <= a < 203012 ->
            mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
  { intros a Ha. apply HFR2.
    - right. exact (proj1 (IMGR a ltac:(lia))).
    - exact (ev_not_owned L A m1 md a MR1A (IMGR a ltac:(lia))).
    - exact (ev_not_owned L' A' m2 md' a HMR2 (IMGR a ltac:(lia))).
    - apply NSC1; lia.
    - unfold send_writes, G_BROKEN, G_EINTR, G_OUTV. intros [X|[X|[X|[_ X]]]]; lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32)
                  [CB 8 j; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (ev_rw_cells_transfer rsegs m1); [exact FR1r|]. intros i Hi. cbn in Hi.
    destruct (KEEPS (bv_unsigned sp + -32 + i) ltac:(lia)) as [E W]. split; [exact E | apply W]. }
  assert (GL2r : rw_cells rsegs m2 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]).
  { apply (ev_rw_cells_transfer rsegs m1); [exact GL1r|]. intros i Hi. cbn in Hi.
    destruct (KEEPG (203000 + i) ltac:(lia)) as [E W]. split; [exact E | apply W]. }
  assert (ST2 : stk rsegs m2 (bv_unsigned sp - 96) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs m2 a).
    { destruct (Z_lt_ge_dec a (bv_unsigned sp + -32)) as [D|D].
      - apply HSCR2. unfold scratch_k, spZ. rewrite SP1. left. lia.
      - pose proof FR2 as [_ (_ & _ & Hw)].
        replace a with (bv_unsigned sp + -32 + (a - (bv_unsigned sp + -32))) by lia. apply Hw. cbn. lia. }
    split; [exact W|].
    destruct (ev_writable_hi_present m2 a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (mem_rel_normalize rsegs m2 RA2) as MRL2.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite ev_canon_mkst. unfold Regs6ss.mkR_of. rewrite G2_2, G2_9.
    eapply evt_normalize; [exact ev_wx_rsegs | exact RA2 |].
    eapply (ev_run2 SPU) with (sp0 := sp) (lo := bv_unsigned sp - 96).
    - apply ev_rw_cells_norm; [exact RA2 | exact FR2 |]. intros i Hi. cbn in Hi. apply ev_ro_addr_hi. lia.
    - apply ev_rw_cells_norm; [exact RA2 | exact GL2r |]. intros i Hi. cbn in Hi. apply ev_ro_addr_glob. lia.
    - apply ev_stk_norm; [exact RA2 | exact ST2 | lia | lia].
    - lia.
    - lia.
    - apply mem_inv_normalize. }
  intros ms3 PK3.
  destruct (ev_unpack _ _ _ PK3) as (s3 & R3 & m3 & Q3 & -> & X3 & MR3 & RS3). clear PK3.
  unfold pthread_mutex_unlock_post in Q3.
  destruct Q3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3n
    & -> & MU3 & WM3 & MI3 & ST3 & GL3).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in X3, MR3 |- *.
  pose proof (munch_rel rsegs _ m2 _ m3 m3n MRL2 MR3 RS3 MU3) as MU3r.
  pose proof (wmono_rel rsegs m2 _ m3 m3n MRL2 MR3 RS3 WM3) as WM3r.
  pose proof (ev_rw_cells_rel _ _ _ _ MR3 GL3) as GL3r.
  pose proof (ro_agree_same rsegs m2 m3 RA2 RS3) as RA3.
  clear MU3 WM3 GL3 ST3 MI3.
  assert (RP1 : ret_pc (reg_get regs 1) = reg_get regs 1) by exact (ev_ret_pc_of_ok _ HRA).
  rewrite RP1.
  apply SR_ret.
  exists L', A', R3, m3, md', OUT', CAP', junk'.
  split; [reflexivity|].
  split.
  { unfold relay_post. rewrite SEGS.
    split; [exact (ev_mr_munch L' A' m2 m3 md' _ _ HMR2 MU3r ltac:(lia) (fun a Ha => IMGR a ltac:(lia)))|].
    split; [exact HWF2|]. split; [exact HBD2|]. split; [exact HLE2|]. split; [exact HREG2|].
    split; [exact HPA2|]. split; [exact HUB2|]. split; [exact HZB2|]. split; [exact HOWN2|].
    split.
    { eapply (ev_preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9)) regs R1 R2 R3 _ _ X1 HPRES2 X3).
      - intros r Hr Ow. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate Ow | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr Ow. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate Ow | reflexivity]|]).
        subst r. discriminate Ow. }
    split; [exact HVM2|].
    split.
    { intros a HA NO1 NO2 NS NE.
      assert (AR : 0 <= a < 2 ^ 64)
        by (destruct HA as [HA|HA]; [lia | pose proof (ev_in_img_low a SEGS HA); lia]).
      unfold scratch_k, spZ in NS. change (getr regs 2) with sp in NS.
      unfold event_writes, G_LOCK in NE.
      assert (NSP : ~ (bv_unsigned sp - 8400 <= a < bv_unsigned sp)) by (intro H; apply NS; left; lia).
      assert (NER : ~ (errno_addr Bm <= a < errno_addr Bm + 4)) by (intro H; apply NS; right; exact H).
      assert (NLK : ~ (203004 <= a < 203008)) by (intro H; apply NE; right; lia).
      assert (NSW : ~ send_writes (send_live cl br dd (Z.of_nat (length e) + 1)) (bv_unsigned out) (bv_unsigned cap) a)
        by (intro H; apply NE; left; exact H).
      assert (O1 : outside [(bv_unsigned sp + -32, bv_unsigned sp); (203004, 203008)] a)
        by (cbn [outside]; split; [lia|]; split; [exact NLK | exact I]).
      assert (O3 : outside [(bv_unsigned sp - 96, bv_unsigned sp); (203000 + 4, 203000 + 8)] a)
        by (cbn [outside]; split; [lia|]; split; [lia | exact I]).
      pose proof (ev_munch_mbyte rsegs _ _ _ a MU1r AR O1) as E01.
      pose proof (ev_munch_writable rsegs _ _ _ a MU1r AR O1) as W01.
      destruct (HFR2 a HA NO1 NO2 ltac:(apply NSC1; lia) NSW) as [E12 W12].
      pose proof (ev_munch_mbyte rsegs _ _ _ a MU3r AR O3) as E23.
      pose proof (ev_munch_writable rsegs _ _ _ a MU3r AR O3) as W23.
      split; [rewrite E23, E12, E01; reflexivity | rewrite W01, W12, W23; tauto]. }
    split.
    { intros p n i Hin Hin' NF Hi NE.
      destruct (mr_blocks Bm _ LAWS L A mem md p n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
      unfold event_writes, G_LOCK in NE.
      assert (NSW : ~ send_writes (send_live cl br dd (Z.of_nat (length e) + 1)) (bv_unsigned out) (bv_unsigned cap)
                        (ptr_addr L p + i)) by (intro H; apply NE; left; exact H).
      assert (O1 : outside [(bv_unsigned sp + -32, bv_unsigned sp); (203004, 203008)] (ptr_addr L p + i))
        by (cbn [outside]; split; [lia|]; split; [intro H; apply NE; right; lia | exact I]).
      assert (O3 : outside [(bv_unsigned sp - 96, bv_unsigned sp); (203000 + 4, 203000 + 8)] (ptr_addr L p + i))
        by (cbn [outside]; split; [lia|]; split; [intro H; apply NE; right; lia | exact I]).
      rewrite (ev_munch_mbyte rsegs _ _ _ (ptr_addr L p + i) MU3r ltac:(lia) O3), (HBK2 p n i Hin Hin' NF Hi NSW).
      exact (ev_munch_mbyte rsegs _ _ _ (ptr_addr L p + i) MU1r ltac:(lia) O1). }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    apply WM3r.
    assert (W1 : writable_at rsegs m1 a)
      by (apply WM1r; destruct Ha as [Ha|Ha]; [apply HWS; lia | apply HERRW; exact Ha]).
    destruct Ha as [Ha|Ha].
    - destruct (Z_lt_ge_dec a (bv_unsigned sp + -32)) as [D|D].
      + apply HSCR2. unfold scratch_k, spZ. rewrite SP1. left. lia.
      + exact (proj1 (proj2 (KEEPS a ltac:(lia))) W1).
    - apply HSCR2. right. exact Ha. }
  split; [exact INIT'|]. split; [exact RES'|]. split; [exact RA3|].
  split.
  { apply (bytes_at_transport rsegs _ m2 m3 _ _ LB2 MU3r). ev_win. }
  split; [exact GL3r|].
  split; [apply (rw_cells_transport rsegs _ m2 m3 _ _ CCL2 MU3r WM3r); ev_win|].
  split; [apply (rw_cells_transport rsegs _ m2 m3 _ _ CBR2 MU3r WM3r); ev_win|].
  split; [apply (rw_cells_transport rsegs _ m2 m3 _ _ CDD2 MU3r WM3r); ev_win|].
  split; [apply (rw_cells_transport rsegs _ m2 m3 _ _ CEI2 MU3r WM3r); ev_win|].
  split.
  { intros HL. destruct (DEAD2 HL) as (BE & ER2 & OV2).
    split; [exact BE|].
    split; [apply (rw_cells_transport rsegs _ m2 m3 _ _ ER2 MU3r WM3r); ev_win|].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ OV2 MU3r WM3r); ev_win. }
  intros HL. destruct (LIVE2 HL) as (NL & ECAP & FB & (ev2 & ER2) & NEQ & BL & BO & JL & OV2).
  split; [exact NL|]. split; [exact ECAP|]. split; [exact FB|].
  split; [exists ev2; apply (rw_cells_transport rsegs _ m2 m3 _ _ ER2 MU3r WM3r); ev_win|].
  split; [exact NEQ|]. split; [exact BL|].
  split.
  { rewrite <- app_assoc in BO. destruct FB as (FB1 & FB2 & FB3).
    pose proof (ev_blk_out (in_img Bm) _ _ FB3 (fun a Ha => proj1 (IMGR a Ha))) as BG.
    assert (LO : Z.of_nat (length O) = bv_unsigned nout).
    { destruct HOUT as [(C0 & _ & N0 & OE) | (_ & _ & _ & _ & _ & H6 & _)]; [subst O; cbn; lia | exact H6]. }
    apply (bytes_at_transport rsegs _ m2 m3 _ _ BO MU3r).
    rewrite !length_app. cbn [length]. ev_win. }
  split; [exact JL|].
  apply (rw_cells_transport rsegs _ m2 m3 _ _ OV2 MU3r WM3r); ev_win.
Qed.

End EvB.
