(* Case 4 of the op loop of LLVMFuzzerTestOneInput in the plain image (fuzz_transport.c:1187-1189
   `case 4: op_submit(&in); break;`, op_submit at :1065-1119 inlined): what the segment files share. The frame as
   cells (op4_mem and its carriers), the tail 0x14280 -> latch (llvm_op4_tail), the model split at `if (g_raw)`
   (op4_raw_m, op4_tagged_m), the o4_* names of the model's values, the program points op4_j / op4_t1 .. op4_t4 and
   the statements of the segments (op4_entry_stmt, op4_raw_stmt, op4_tag1_stmt .. op4_tag5_stmt). The segments are
   LLVMFuzzerTestOneInput_op4{e,r,t1,t2,t3,t4,t5}.v; LLVMFuzzerTestOneInput_op4.v chains them into llvm_op4. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* ---- the frame as a list of cells, split and joined at a cell boundary ---- *)

Lemma op4_wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & Hw). split; (split; [lia|]); (split; [lia|]).
    + intros i Hi. apply Hw. lia.
    + intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply Hw. lia.
  - intros [(Ha & Hb & Hw1) (Ha2 & Hb2 & Hw2)]. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z_lt_le_dec i n1) as [L|L]; [apply Hw1; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply Hw2. lia.
Qed.

Lemma op4_rw_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app, Nat2Z.inj_add.
  rewrite (op4_wr_at_app m A) by lia.
  split.
  - intros [[[W1 W2] [B1 B2]] [R1 R2]].
    assert (L1 : length (cells_bytes cs1) = cells_size cs1) by (apply cells_bytes_length; exact W1).
    rewrite L1 in B2. tauto.
  - intros [[[W1 B1] R1] [[W2 B2] R2]].
    assert (L1 : length (cells_bytes cs1) = cells_size cs1) by (apply cells_bytes_length; exact W1).
    rewrite L1. tauto.
Qed.

(* the same bytes in other cells *)
Lemma op4_rw_rebytes : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. unfold rw_cells, cells_at.
  assert (S : cells_size cs' = cells_size cs).
  { rewrite <- (cells_bytes_length cs' W'), <- (cells_bytes_length cs W), E. reflexivity. }
  rewrite S, E. tauto.
Qed.

Lemma op4_rw_mid : forall m A pre mid mid' post, rw_cells rsegs m A (pre ++ mid ++ post) ->
  cells_wf mid' -> cells_bytes mid' = cells_bytes mid -> rw_cells rsegs m A (pre ++ mid' ++ post).
Proof.
  intros m A pre mid mid' post H W E. apply (op4_rw_rebytes m A _ _ H).
  - pose proof (proj1 (proj1 H)) as WH. rewrite !cells_wf_app in WH |- *. tauto.
  - rewrite !cells_bytes_app, E. reflexivity.
Qed.

(* the first k bytes of a cell list at a cell boundary, and the rest *)
Fixpoint op4_take (k : nat) (cs : list cell) {struct cs} : list cell :=
  match cs with
  | [] => []
  | c :: cs' => match k with O => [] | S _ => c :: op4_take (k - csize c) cs' end
  end.
Fixpoint op4_drop (k : nat) (cs : list cell) {struct cs} : list cell :=
  match cs with
  | [] => []
  | c :: cs' => match k with O => cs | S _ => op4_drop (k - csize c) cs' end
  end.

Lemma op4_take_drop : forall cs k, op4_take k cs ++ op4_drop k cs = cs.
Proof. induction cs as [|c cs IH]; intros [|k]; cbn [op4_take op4_drop app]; try reflexivity. f_equal. apply IH. Qed.

(* Regroup a run of cells into one CB cell: the cells at positions [k, k+n) of fr become a single CB cell, so the
   kit's store tactic can split them for a sub-word store. k and n are BYTE offsets into the cell list. *)
Lemma op4_cells_wf_take_drop : forall fr k, cells_wf fr -> cells_wf (op4_take k fr) /\ cells_wf (op4_drop k fr).
Proof.
  intros fr k H. rewrite <- (op4_take_drop fr k) in H. apply cells_wf_app in H. exact H.
Qed.

Lemma op4_regroup : forall m A fr k n, rw_cells rsegs m A fr ->
  rw_cells rsegs m A
    (op4_take k fr ++
     [CB (cells_size (op4_take n (op4_drop k fr))) (cells_bytes (op4_take n (op4_drop k fr)))] ++
     op4_drop n (op4_drop k fr)).
Proof.
  intros m A fr k n H.
  pose proof (proj1 (proj1 H)) as WF.
  destruct (op4_cells_wf_take_drop fr k WF) as [WFk WFd].
  destruct (op4_cells_wf_take_drop (op4_drop k fr) n WFd) as [WFn _].
  eapply (op4_rw_mid m A (op4_take k fr) (op4_take n (op4_drop k fr))).
  - rewrite (op4_take_drop (op4_drop k fr) n), (op4_take_drop fr k). exact H.
  - cbn [cells_wf cell_wf]. split; [apply cells_bytes_length; exact WFn | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
Qed.

(* The compiler's w % 25 for a 16-bit w (0x13e90-0x13ebc): q = (((w * 0x47af) >> 16) +
   (((w - ((w * 0x47af) >> 16)) mod 2^16) >> 1)) >> 4 is w / 25, checked on every 16-bit w. *)
Definition op4_q25 (w : Z) : Z :=
  Z.shiftr (Z.shiftr (w * 18351) 16 + Z.shiftr ((w - Z.shiftr (w * 18351) 16) mod 65536) 1) 4.

Fixpoint op4_q25_chk (fuel : nat) (w : Z) : bool :=
  match fuel with
  | O => true
  | S f => (Z.eqb (op4_q25 w) (w / 25) && op4_q25_chk f (w + 1))%bool
  end.

Lemma op4_q25_chk_sound : forall fuel w0 w, op4_q25_chk fuel w0 = true ->
  w0 <= w < w0 + Z.of_nat fuel -> op4_q25 w = w / 25.
Proof.
  induction fuel as [|f IH]; intros w0 w H Hw.
  - cbn [Z.of_nat] in Hw. lia.
  - cbn [op4_q25_chk] in H. apply andb_true_iff in H. destruct H as [H1 H2].
    rewrite Nat2Z.inj_succ in Hw.
    destruct (Z.eq_dec w w0) as [->|Hne]; [apply Z.eqb_eq; exact H1|].
    apply (IH (w0 + 1) w H2). lia.
Qed.

Lemma op4_q25_ok : forall w, 0 <= w < 65536 -> op4_q25 w = w / 25.
Proof.
  intros w Hw. apply (op4_q25_chk_sound (Z.to_nat 65536) 0 w); [vm_compute; reflexivity|].
  rewrite Z2Nat.id by lia. lia.
Qed.

(* 0x13e90-0x13ec4 is w mod 25: this is the sequence up to the wrap of q * 25, which the kit also leaves
   ((q * 25) mod 2^64; _op4r.v o4r_mod25 states the kit's exact form from this lemma). *)
Lemma op4_mod25 : forall W, 0 <= W < 65536 ->
  Z.land ((W - Z.shiftr ((Z.shiftr (Z.shiftl (bv_swrap 32 (W - Z.shiftr ((W * 18351)
                            mod 18446744073709551616) 16) mod 18446744073709551616) 48
                            mod 18446744073709551616) 49
                          + Z.shiftr ((W * 18351) mod 18446744073709551616) 16)
                         mod 18446744073709551616) 4 * 25)
          mod 18446744073709551616) 65535
  = W mod 25.
Proof.
  intros W HW.
  assert (HP : (W * 18351) mod 18446744073709551616 = W * 18351) by (apply Z.mod_small; lia).
  rewrite HP.
  rewrite (Z.shiftr_div_pow2 (W * 18351) 16) by lia. change (2 ^ 16) with 65536.
  assert (Hq0 : 0 <= W * 18351 / 65536 <= W).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  assert (HS : bv_swrap 32 (W - W * 18351 / 65536) = W - W * 18351 / 65536).
  { apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. }
  rewrite HS.
  rewrite (Z.mod_small (W - W * 18351 / 65536) 18446744073709551616) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small ((W - W * 18351 / 65536) * 2 ^ 48) 18446744073709551616)
    by (change (2 ^ 48) with 281474976710656; lia).
  rewrite (Z.shiftr_div_pow2 ((W - W * 18351 / 65536) * 2 ^ 48) 49) by lia.
  replace ((W - W * 18351 / 65536) * 2 ^ 48 / 2 ^ 49) with ((W - W * 18351 / 65536) / 2)
    by (replace ((W - W * 18351 / 65536) * 2 ^ 48) with (2 ^ 48 * (W - W * 18351 / 65536)) by ring;
        replace (2 ^ 49) with (2 ^ 48 * 2) by (vm_compute; reflexivity);
        rewrite Z.div_mul_cancel_l by (vm_compute; discriminate); reflexivity).
  rewrite (Z.mod_small ((W - W * 18351 / 65536) / 2 + W * 18351 / 65536) 18446744073709551616)
    by (pose proof (Z.div_pos (W - W * 18351 / 65536) 2 ltac:(lia) ltac:(lia));
        pose proof (Z.div_le_upper_bound (W - W * 18351 / 65536) 2 W ltac:(lia) ltac:(lia)); lia).
  rewrite (Z.shiftr_div_pow2 ((W - W * 18351 / 65536) / 2 + W * 18351 / 65536) 4) by lia.
  change (2 ^ 4) with 16.
  assert (HQ : ((W - W * 18351 / 65536) / 2 + W * 18351 / 65536) / 16 = W / 25).
  { pose proof (op4_q25_ok W HW) as E. unfold op4_q25 in E.
    rewrite !(Z.shiftr_div_pow2 (W * 18351) 16) in E by lia.
    change (2 ^ 16) with 65536 in E.
    rewrite (Z.mod_small (W - W * 18351 / 65536) 65536) in E by lia.
    rewrite (Z.shiftr_div_pow2 (W - W * 18351 / 65536) 1) in E by lia.
    change (2 ^ 1) with 2 in E.
    rewrite (Z.shiftr_div_pow2 (W * 18351 / 65536 + (W - W * 18351 / 65536) / 2) 4) in E by lia.
    change (2 ^ 4) with 16 in E.
    rewrite <- E. f_equal. lia. }
  rewrite HQ.
  pose proof (Z.div_mod W 25 ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound W 25 ltac:(lia)) as MB.
  replace (W - W / 25 * 25) with (W mod 25) by lia.
  rewrite (Z.mod_small (W mod 25) 18446744073709551616) by lia.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 16) with 65536. lia.
Qed.

(* a sub-range of the input buffer, as memcpy's source argument *)
Lemma op4_bytes_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k ->
  (Z.to_nat k + n <= length bs)%nat -> bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n H Hk Hn. destruct H as (Ha & Hl & Hb).
  assert (LS : length (sub bs k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite LS; lia|].
  intros i Hi. rewrite LS in Hi.
  rewrite ne_sub by lia.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply Hb. lia.
Qed.

Section OP4.
Context (data : Z) (D : list byte).

(* llvm_mem with the frame as any cell list of the frame's size: the form the case's stores keep. m0 is the
   reference memory of the evt segment; the footprint munch is carried from it as in llvm_mem. *)
Definition op4_mem (Sp lo : Z) (B : list byte) (m0 m : word -> option byte) (fr : list cell) : Prop :=
  munch (LLVM_FP Sp) m0 m /\ wmono rsegs m0 m /\
  bytes_at rsegs m data D /\
  Sp mod 16 = 0 /\ stk rsegs m lo Sp /\ lo + LLVM_LOOP_K <= Sp /\ Sp + LLVM_FRAME < 2 ^ 63 /\
  w_off_stack W_BASE_PLAIN (Z_to_bv 64 Sp) LLVM_LOOP_K /\ W_BASE_PLAIN + W_LEN <= lo /\
  off_world data (Z.of_nat (length D)) /\
  off_window (Z_to_bv 64 (Sp + LLVM_FRAME)) (LLVM_LOOP_K + LLVM_FRAME) data (Z.of_nat (length D)) /\
  mem_inv rsegs m /\ relro_img m /\ wmem rsegs m B /\ g_fail_next B <= 1 /\
  rw_cells rsegs m Sp fr /\ cells_size fr = 224%nat.

Lemma op4_of_llvm : forall Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28,
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  op4_mem Sp lo B m0 m
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s));
      CB 8 j10; C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); CB 80 j28;
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Proof.
  intros Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 H.
  unfold llvm_mem, llvm_frame_consts, llvm_saved in H. unfold op4_mem.
  destruct H as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2 & HRW).
  cbn [app] in HRW. repeat (split; [assumption|]). first [reflexivity | split; [exact HRW | reflexivity]].
Qed.

Lemma op4_to_llvm : forall Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m10 m28,
  op4_mem Sp lo B m0 m
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] ++ m10 ++
     [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++ m28 ++
     [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  cells_size m10 = 8%nat -> cells_size m28 = 80%nat ->
  llvm_mem data D Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (cells_bytes m10) (cells_bytes m28).
Proof.
  intros Sp lo B m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m10 m28 H S10 S28.
  unfold op4_mem in H. unfold llvm_mem, llvm_frame_consts, llvm_saved.
  destruct H as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  pose proof (proj1 (proj1 HRW)) as WF. rewrite !cells_wf_app in WF.
  destruct WF as (_ & W10 & _ & W28 & _).
  repeat (split; [assumption|]).
  split; [rewrite cells_bytes_length by exact W10; exact S10|].
  split; [rewrite cells_bytes_length by exact W28; exact S28|].
  pose proof (rw_cells_merge rsegs m Sp
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] ++ m10 ++
     [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)]) m28
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) as M1.
  rewrite <- !app_assoc in M1. specialize (M1 HRW). rewrite S28 in M1.
  cbn [app] in M1.
  pose proof (rw_cells_merge rsegs m Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] m10
    ([C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++
     CB 80 (cells_bytes m28) ::
     [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) as M2.
  cbn [app] in M2. specialize (M2 M1). rewrite S10 in M2.
  cbn [app] in M2 |- *. exact M2.
Qed.

(* the invariant after a stretch whose stores and calls stay in the callee window, the frame and the world *)
Lemma op4_mem_after : forall Sp lo K B B' m0 m m' fr fr',
  op4_mem Sp lo B m0 m fr ->
  0 <= K <= LLVM_LOOP_K ->
  munch [(Sp - K, Sp + LLVM_FRAME); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp -> wmem rsegs m' B' -> g_fail_next B' <= 1 ->
  rw_cells rsegs m' Sp fr' -> cells_size fr' = 224%nat ->
  op4_mem Sp lo B' m0 m' fr'.
Proof.
  intros Sp lo K B B' m0 m m' fr fr' HM HK MU WMO MI ST WM HFN' HRW' HSZ'.
  unfold op4_mem in HM |- *.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold off_window in HOWIN. rewrite unsigned_lit in HOWIN by lia.
  unfold off_world in HOW.
  split; [ eapply munch_trans; [exact HMU0|];
    intros x Hx; apply MU; unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in Hx; cbn [outside] in Hx |- *;
    destruct Hx as (Hx1 & Hx2 & _);
    split; [lia | split; [exact Hx2 | exact I]] |].
  split; [eapply wmono_trans; [exact HWMO0 | exact WMO]|].
  split; [eapply bytes_at_transport; [exact HD | exact MU |];
          cbn [disjoint_from]; split; [lia | split; [lia | exact I]]|].
  split; [exact HSP|]. split; [exact ST|]. split; [exact HLO|]. split; [exact HSP2|].
  split; [exact HWOS|]. split; [exact HOWS|]. split; [exact HOW|].
  split; [unfold off_window; rewrite unsigned_lit by lia; exact HOWIN|].
  split; [exact MI|].
  split; [eapply relro_munch_hi; [exact HRO | exact MU | lia]|].
  split; [exact WM|]. split; [exact HFN'|]. split; [exact HRW'|]. exact HSZ'.
Qed.

(* a callee confined to its window and the world: the frame is carried *)
Lemma op4_mem_after_call : forall Sp lo K B B' m0 m m' fr,
  op4_mem Sp lo B m0 m fr -> 0 <= K <= LLVM_LOOP_K ->
  munch [(Sp - K, Sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp -> wmem rsegs m' B' -> g_fail_next B' <= 1 ->
  op4_mem Sp lo B' m0 m' fr.
Proof.
  intros Sp lo K B B' m0 m m' fr HM HK MU WMO MI ST WM HFN'.
  pose proof HM as HM1. unfold op4_mem in HM1.
  destruct HM1 as (_ & _ & _ & _ & _ & HLO & HSP2 & _ & HOWS & _ & _ & _ & _ & _ & _ & HRW & HSZ).
  unfold LLVM_LOOP_K in HLO.
  eapply (op4_mem_after Sp lo K B B' m0 m m' fr fr); [exact HM | exact HK | | exact WMO | exact MI | exact ST
    | exact WM | exact HFN' | | exact HSZ].
  - intros x Hx. apply MU. cbn [outside] in *. unfold LLVM_FRAME in Hx.
    destruct Hx as (H1 & H2 & _). split; [lia | split; [exact H2 | exact I]].
  - eapply rw_cells_transport; [exact HRW | exact MU | exact WMO |].
    rewrite HSZ. cbn [disjoint_from]. unfold W_BASE_PLAIN, W_LEN in *. split; [lia | split; [lia | exact I]].
Qed.

(* a world memset / memcpy that fills one span inside the world: the frame is carried, the world is upd B k src *)
Lemma op4_mem_after_fill : forall Sp lo B m0 m m' k n src fr,
  op4_mem Sp lo B m0 m fr ->
  munch [(W_BASE_PLAIN + k, W_BASE_PLAIN + k + n)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' (W_BASE_PLAIN + k) [CB (Z.to_nat n) src] ->
  0 <= k -> 0 <= n -> k + n <= W_LEN ->
  g_fail_next (upd B k src) <= 1 ->
  op4_mem Sp lo (upd B k src) m0 m' fr.
Proof.
  intros Sp lo B m0 m m' k n src fr HM MU WMO MI CZ Hk Hn Hkn HFN'.
  pose proof HM as HM1. unfold op4_mem in HM1.
  destruct HM1 as (_ & _ & _ & _ & HSTK & HLO & _ & _ & HOWS & _ & _ & _ & _ & HWM & _ & HRW & HSZ).
  unfold LLVM_LOOP_K in HLO.
  assert (MUw : munch [(Sp - 0, Sp + LLVM_FRAME); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m').
  { intros x Hx. apply MU. cbn [outside] in Hx |- *. destruct Hx as (_ & Hw & _).
    unfold W_BASE_PLAIN, W_LEN in *. split; [lia | exact I]. }
  eapply (op4_mem_after Sp lo 0 B (upd B k src) m0 m m' fr fr);
    [exact HM | unfold LLVM_LOOP_K; lia | exact MUw | exact WMO | exact MI | | | exact HFN' | | exact HSZ].
  - eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |].
    cbn [disjoint_from]. unfold W_BASE_PLAIN, W_LEN in *. split; [lia | exact I].
  - exact (wm_fill rsegs W_BASE_PLAIN m m' B (W_BASE_PLAIN + k) k n src HWM MU WMO CZ eq_refl Hk Hn Hkn).
  - eapply rw_cells_transport; [exact HRW | exact MU | exact WMO |].
    rewrite HSZ. cbn [disjoint_from]. unfold W_BASE_PLAIN, W_LEN in *. split; [lia | exact I].
Qed.

(* writes that keep the length and the g_fail_next byte, for threading op_begin's world facts *)
Lemma op4_len_put : forall (u : list byte) k n v, Z.of_nat (length u) = W_LEN -> 0 <= k ->
  k + Z.of_nat n <= W_LEN -> Z.of_nat (length (upd u k (put n v))) = W_LEN.
Proof. intros u k n v Hu Hk Hn. rewrite length_upd_put; [exact Hu | lia | rewrite Hu; lia]. Qed.

Lemma op4_fn_put : forall (u : list byte) k n v, Z.of_nat (length u) = W_LEN -> 0 <= k ->
  k + Z.of_nat n <= W_LEN -> (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd u k (put n v)) = g_fail_next u.
Proof.
  intros u k n v Hu Hk Hn Hd. unfold g_fail_next.
  rewrite u_at_upd_out; [reflexivity | lia | unfold OFF_g_fail_next; lia
    | rewrite length_put; cbn [Z.of_nat]; lia | rewrite length_put, Hu; lia].
Qed.

(* op_begin (fuzz_transport.c:388-394) as case 4 runs it: memset OW, memset GOT, OW.desk_off = -1, M.fail =
   g_fail_next (the binary's store order; the model's too). *)
Lemma op4_begin_world : forall (Bx Bz : list byte), Z.of_nat (length Bx) = W_LEN ->
  Bz = upd (upd Bx 65312 (repeat (Z_to_bv 8 0) 304)) 65084 (repeat (Z_to_bv 8 0) 224) ->
  op_begin_m Bx = Some (upd (upd Bz 65544 (put 4 (-1))) 88 (put 4 (u_at Bz OFF_g_fail_next 1)), tt).
Proof.
  intros Bx Bz HL EZ.
  assert (EWL : W_LEN = 65616) by reflexivity.
  assert (R304 : Z.of_nat (length (repeat (Z_to_bv 8 0) 304)) = 304) by (rewrite repeat_length; lia).
  assert (R224 : Z.of_nat (length (repeat (Z_to_bv 8 0) 224)) = 224) by (rewrite repeat_length; lia).
  assert (P4 : forall v : Z, Z.of_nat (length (put 4 v)) = 4) by (intros; rewrite length_put; lia).
  assert (L1 : Z.of_nat (length (upd Bx 65312 (repeat (Z_to_bv 8 0) 304))) = W_LEN)
    by (rewrite length_upd; [exact HL | lia | rewrite R304; lia]).
  assert (LZ : Z.of_nat (length Bz) = W_LEN)
    by (rewrite EZ, length_upd; [exact L1 | lia | rewrite R224, L1; lia]).
  unfold op_begin_m, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off, OFF_M, OFF_OW, OFF_GOT.
  change (Z.to_nat SZ_OW) with 304%nat. change (Z.to_nat SZ_GOT) with 224%nat.
  change (b8 0) with (Z_to_bv 8 0).
  rewrite <- EZ.
  replace (65312 + 232) with 65544 by lia. replace (0 + 88) with 88 by lia.
  assert (EFN : g_fail_next (upd Bz 65544 (put 4 (-1))) = u_at Bz OFF_g_fail_next 1).
  { change (u_at Bz OFF_g_fail_next 1) with (g_fail_next Bz).
    apply op4_fn_put; [exact LZ | lia | cbn [Z.of_nat]; lia | unfold OFF_g_fail_next; lia]. }
  rewrite EFN. reflexivity.
Qed.

(* 0x14280-0x14288 and the latch: a0 = 0, settle(0), mv s3, s0, then 0x1428c. s0 = the cursor after the op,
   s6 = its count; s1 / s2 / s8 were restored by the caller. The frame is back in its llvm_mem shape. *)
Lemma llvm_op4_tail : forall Sp lo ops cout Bf Bf' m0 m m10 m28
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    rz gp tp e0 e1 e2 q0 q1 q2 q3 q4 q5 q6 q7 r8 x4 x7 e3 e4 e5 e6,
  settle_contract ->
  op4_mem Sp lo Bf m0 m
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] ++ m10 ++
     [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++ m28 ++
     [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  cells_size m10 = 8%nat -> cells_size m28 = 80%nat ->
  llvm_cursor D cout -> 0 <= ops < OPS_MAX ->
  settle_m Bf 0 = Some (Bf', tt) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops cout Bf'
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 (Z_to_bv 64 (data + fi_off cout)) (Z_to_bv 64 7)
             q0 q1 q2 q3 q4 q5 q6 q7 (Z_to_bv 64 0x39) x4 x7 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (fi_n cout)) r8 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x14280) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops cout Bf Bf' m0 m m10 m28 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q
    rz gp tp e0 e1 e2 q0 q1 q2 q3 q4 q5 q6 q7 r8 x4 x7 e3 e4 e5 e6 STC HM S10 S28 HC HOPS HB HK.
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold LLVM_LOOP_K, LLVM_FRAME in HLO, HSP2. wk_facts. wk_eq_fact OFF_g_s.
  do 2 zstep.
  eapply evt_cut.
  { eapply STC with (B := Bf) (ticked := 0) (lo := lo).
    - reflexivity.
    - lia.
    - exact HWM.
    - exact HB.
    - rewrite unsigned_lit by lia. exact HSP.
    - rewrite unsigned_lit by lia. exact HSTK.
    - rewrite unsigned_lit by lia. unfold settle_FRAME. lia.
    - unfold w_off_stack. rewrite unsigned_lit by lia. unfold settle_FRAME. lia.
    - exact HMI. }
  intros ms' Hpost.
  destruct Hpost as (g0 & g1 & g2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & i3 & i4 & i5 & i6 & m5 &
                     -> & MU5 & WMO5 & MI5 & ST5 & EB & WM5).
  rewrite unsigned_lit in MU5, ST5 by lia. subst Bf'.
  assert (HM5 : op4_mem Sp lo Bf m0 m5
    ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))] ++ m10 ++
     [C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff)] ++ m28 ++
     [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { eapply (op4_mem_after_call Sp lo settle_FRAME Bf Bf m0 m m5);
      [ exact HM | unfold settle_FRAME, LLVM_LOOP_K; lia | apply munch_add_world; exact MU5
      | exact WMO5 | exact MI5 | exact ST5 | exact WM5 | exact HFN ]. }
  rewrite (ret_pc_even 0x14288) by (first [lia | reflexivity]).
  zstep.
  apply HK. unfold llvm_latch. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC|].
  eapply op4_to_llvm; [exact HM5 | exact S10 | exact S28].
Qed.

(* The 32 bytes the raw path leaves at sp + 0x50 are the model's cmd_struct: the n copied input bytes,
   zeros up to 24, the length byte, the display byte, two pad zeros, the key. *)
Lemma op4_struct_raw : forall (src : list byte) (n display key : Z),
  src ++ repeat (b8 0) (Z.to_nat (24 - n)) ++ [b8 n] ++ ([b8 display] ++ repeat (b8 0) 2 ++ put 4 key)
  = cmd_struct (src ++ repeat (b8 0) (Z.to_nat (24 - n))) n display key.
Proof. intros. unfold cmd_struct. cbn [repeat app]. rewrite <- !app_assoc. reflexivity. Qed.

End OP4.

(* ================================================================ the model's two arms *)

(* the option monad of TOps.v *)
Local Notation "'let?' p ':=' e 'in' b" :=
  (match e with Some p => b | None => None end)
  (at level 200, p pattern, e at level 100, b at level 200, right associativity).

(* op_submit_m (TOps.v:218-275) after op_begin and the three bytes kb, ab, db, split at `if (g_raw)` (:1075).
   Copied from the ubsan twin
   (lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_mid.v op4_raw_m / op4_tagged_m / op_submit_split): build-independent. *)
Definition op4_raw_m (B1 D : list byte) (c3 : fuzz_in) (before display key : Z) : option (list byte * fuzz_in) :=
    let (c4, w) := fuzz_u16_m D c3 in
    let '(c5, off, t) := fuzz_take_m c4 (w mod (SPEC_CMD_MAX + 1)) in
    let len := t mod 2^8 in
    let cbytes := sub D off (Z.to_nat len) ++ repeat (b8 0) (Z.to_nat (24 - len)) in
    let cs := cmd_struct cbytes len display key in
    let? (B2, rc) := diginet_session_submit_m B1 cs in
    let? (B3, _) := check_refusal_submit_m B2 cs rc before in
    let? (B4, _) := settle_m B3 0 in
    Some (B4, c5).

Definition op4_tagged_m (B1 D : list byte) (c3 : fuzz_in) (before display key : Z) : option (list byte * fuzz_in) :=
    let serial := g_ncmd B1 in
    if CMDS_MAX <=? serial then None
    else
    let B2 := upd B1 (A_Cmd_st serial) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) in
    let (c4, lb) := fuzz_u8_m D c3 in
    let len := lb mod 22 + 3 in
    let '(c5, off, n) := fuzz_take_m c4 (len - 3) in
    let cbytes := [b8 TAG; b8 (Z.land serial 0x7f); b8 (Z.land (Z.shiftr serial 7) 0x7f)]
                  ++ sub D off (Z.to_nat n) ++ repeat (b8 0) (Z.to_nat (21 - n)) in
    let sys := system_at (firstn (Z.to_nat len) cbytes) in
    let? at_ :=
      if negb (h_coalescable_m key =? 0)
      then submit_find_at (S (Z.to_nat CMDS_MAX)) B2 key 0
      else Some (-1) in
    let want := if sys then SPEC_E_REFUSED
                else if (at_ <? 0) && (g_nq B2 =? QUEUE_MAX) then SPEC_E_SPACE
                else SPEC_OK in
    let cs := cmd_struct cbytes len display key in
    let? (B3, rc) := diginet_session_submit_m B2 cs in
    let? (B4, _) := check_refusal_submit_m B3 cs rc before in
    let? (B5, _) := if sys then Some (B4, tt) else check_latest_submit_m B4 rc want in
    let? B6 :=
      if want =? SPEC_OK then
        let Bw := set_Cmd_bytes
                    (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 serial PENDING) serial key)
                                    serial display) serial len)
                    serial (firstn (Z.to_nat len) cbytes) in
        if 0 <=? at_ then
          let q := Q_at Bw at_ in
          if CMDS_MAX <=? q then None
          else Some (set_Q_at (set_Cmd_st Bw q REPLACED) at_ serial)
        else
          let nq := g_nq Bw in
          if CMDS_MAX <=? nq then None
          else Some (set_g_nq (set_Q_at Bw nq serial) ((nq + 1) mod 2^32))
      else Some B5 in
    let B7 := set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2^32) in
    let? (B8, _) := settle_m B7 0 in
    Some (B8, c5).

Lemma op_submit_split : forall B D c, op_submit_m B D c =
  match op_begin_m B with
  | Some (B1, _) =>
      let (c1, kb) := fuzz_u8_m D c in
      let (c2, ab) := fuzz_u8_m D c1 in
      let (c3, db) := fuzz_u8_m D c2 in
      if negb (g_raw B1 =? 0) then op4_raw_m B1 D c3 (S_queued B) (Z.land db 1) (KEY (kb mod 9 + 1) ab)
      else op4_tagged_m B1 D c3 (S_queued B) (Z.land db 1) (KEY (kb mod 9 + 1) ab)
  | None => None
  end.
Proof. intros B D c. reflexivity. Qed.

(* The two scan loops of TR6Op4Scan's LLVMFuzzerTestOneInput_op4scan.v, as statements (its lemmas op4_sys_scan,
   op4_sys_short and op4_find_scan, verbatim); _op4.v discharges them with its lemmas. *)
Definition op4_sys_scan_stmt : Prop :=
  forall (cs : list byte) (p len : Z) (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bytes_at rsegs m p cs -> 4 <= len <= Z.of_nat (length cs) -> len < 2 ^ 63 ->
  (forall a0' a2' a3' a4' : word,
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (len - 3)) a2' a3' a4' a5 a6 a7
                (Z_to_bv 64 0xf0) s3 s4 (Z_to_bv 64 (b2z (system_at (firstn (Z.to_nat len) cs))))
                s6 (Z_to_bv 64 0x13) s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1400c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (len - 3)) (Z_to_bv 64 (p + 1))
             a3 a4 a5 a6 a7 (Z_to_bv 64 0xf0) s3 s4 s5 s6 (Z_to_bv 64 0x13) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fd0) fc None m (seg_rom rsegs)).

Definition op4_sys_short_stmt : Prop :=
  forall (cs : list byte) (len : Z), len < 4 -> system_at (firstn (Z.to_nat len) cs) = false.

Definition op4_find_scan_stmt : Prop :=
  forall (B : list byte) (key : Z) (f : nat) (i at_ : Z) (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  wmem rsegs m B -> 0 <= key < 2 ^ 32 -> 0 <= i < g_nq B ->
  submit_find_at f B key i = Some at_ ->
  (forall a2' a3' a4' a5' a6' : word,
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 key) (Z_to_bv 64 (g_nq B)) a2' a3' a4' a5' a6' a7
                (Z_to_bv 64 (at_ mod 2 ^ 32)) s3 (Z_to_bv 64 0x37558) s5 s6 s7 (Z_to_bv 64 0x28)
                s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1408c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 key) (Z_to_bv 64 (g_nq B)) (Z_to_bv 64 i) (Z_to_bv 64 (i + 1))
             (Z_to_bv 64 (0x41558 + 4 * i)) (Z_to_bv 64 0xffffffff) a6 a7
             s2 s3 (Z_to_bv 64 0x37558) s5 s6 s7 (Z_to_bv 64 0x28) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14054) fc None m (seg_rom rsegs)).

(* ================================================================ the program points of case 4 *)

Section OP4D.
Context (data : Z) (D : list byte).

(* the three bytes after the op byte (:1073-1074), from the cursor c1 after it *)
Definition o4_c3 (c1 : fuzz_in) : fuzz_in := fst (fuzz_u8_m D (fst (fuzz_u8_m D (fst (fuzz_u8_m D c1))))).
Definition o4_display (c1 : fuzz_in) : Z :=
  Z.land (snd (fuzz_u8_m D (fst (fuzz_u8_m D (fst (fuzz_u8_m D c1)))))) 1.
Definition o4_key (c1 : fuzz_in) : Z :=
  KEY (snd (fuzz_u8_m D c1) mod 9 + 1) (snd (fuzz_u8_m D (fst (fuzz_u8_m D c1)))).

(* the tagged arm's model values (op4_tagged_m), from the cursor c3 after the three bytes *)
Definition o4_B2 (B1 : list byte) : list byte := upd B1 (A_Cmd_st (g_ncmd B1)) (repeat (b8 0) (Z.to_nat Cmd_ESZ)).
Definition o4_c4 (c3 : fuzz_in) : fuzz_in := fst (fuzz_u8_m D c3).
Definition o4_len (c3 : fuzz_in) : Z := snd (fuzz_u8_m D c3) mod 22 + 3.
Definition o4_tk (c3 : fuzz_in) : fuzz_in * Z * Z := fuzz_take_m (o4_c4 c3) (o4_len c3 - 3).
Definition o4_c5 (c3 : fuzz_in) : fuzz_in := fst (fst (o4_tk c3)).
Definition o4_off (c3 : fuzz_in) : Z := snd (fst (o4_tk c3)).
Definition o4_n (c3 : fuzz_in) : Z := snd (o4_tk c3).
Definition o4_cb (B1 : list byte) (c3 : fuzz_in) : list byte :=
  [b8 TAG; b8 (Z.land (g_ncmd B1) 0x7f); b8 (Z.land (Z.shiftr (g_ncmd B1) 7) 0x7f)]
  ++ sub D (o4_off c3) (Z.to_nat (o4_n c3)) ++ repeat (b8 0) (Z.to_nat (21 - o4_n c3)).
Definition o4_cs (B1 : list byte) (c3 : fuzz_in) (display key : Z) : list byte :=
  cmd_struct (o4_cb B1 c3) (o4_len c3) display key.
Definition o4_sys (B1 : list byte) (c3 : fuzz_in) : bool := system_at (firstn (Z.to_nat (o4_len c3)) (o4_cb B1 c3)).
Definition o4_atopt (B1 : list byte) (key : Z) : option Z :=
  if negb (h_coalescable_m key =? 0) then submit_find_at (S (Z.to_nat CMDS_MAX)) (o4_B2 B1) key 0 else Some (-1).
Definition o4_want (B1 : list byte) (c3 : fuzz_in) (at_ : Z) : Z :=
  if o4_sys B1 c3 then SPEC_E_REFUSED
  else if (at_ <? 0) && (g_nq (o4_B2 B1) =? QUEUE_MAX) then SPEC_E_SPACE else SPEC_OK.
(* :1104-1115, the record of the command when want = SPEC_OK, from the world B5 after the calls *)
Definition o4_rec (B5 B1 : list byte) (c3 : fuzz_in) (display key at_ : Z) : option (list byte) :=
  let serial := g_ncmd B1 in
  let Bw := set_Cmd_bytes
              (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 serial PENDING) serial key)
                              serial display) serial (o4_len c3))
              serial (firstn (Z.to_nat (o4_len c3)) (o4_cb B1 c3)) in
  if 0 <=? at_ then
    let q := Q_at Bw at_ in
    if CMDS_MAX <=? q then None else Some (set_Q_at (set_Cmd_st Bw q REPLACED) at_ serial)
  else
    let nq := g_nq Bw in
    if CMDS_MAX <=? nq then None else Some (set_g_nq (set_Q_at Bw nq serial) ((nq + 1) mod 2^32)).

(* The frame of case 4, in cells: sp+0x00 / 0x08 the loop's constants, sp+0x10 the cell x10 (scratch; the tagged
   arm parks the cursor's n there, 0x13fa4), sp+0x18 / 0x20 = 0x610f / 0xffff, sp+0x28 the 8 bytes of
   (int)s->queued (0x1391c), sp+0x30 32 bytes of scratch, sp+0x50 the struct diginet_cmd c (32 bytes,
   fuzz_transport.c:1067), sp+0x70 8 bytes of scratch, sp+0x78 the 13 saved registers. *)
Definition op4_fr (x10 : cell) (bf : word) (j30 cs j70 : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); x10;
   C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30; CB 32 cs; CB 8 j70;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition o4_ok (ops : Z) (c3 : fuzz_in) (before display key : Z) : Prop :=
  0 <= ops < OPS_MAX /\ llvm_cursor D c3 /\ 0 <= before < 2 ^ 32 /\ 0 <= display <= 1 /\ 0 <= key < 2 ^ 32.

Definition o4_tok (ops : Z) (c3 : fuzz_in) (B1 : list byte) (before display key : Z) : Prop :=
  o4_ok ops c3 before display key /\ 0 <= g_ncmd B1 < CMDS_MAX.

(* 0x13df4 (`lw a1, 4(s9)`, g_raw), the join of the four key-byte subcases: op_begin done (world B1), the cursor
   after the three bytes in s3 / s7, the display bit in a0, the struct at sp+0x50 zero but its key (0x13998,
   0x13b34, 0x13bf4 `sw 0x6c(sp)`). *)
Definition op4_j (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c3 : fuzz_in) (B1 : list byte)
    (before display key : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x20 x22 t3 t4 t5 t6 : word) (m : word -> option byte)
         (j10 j30 j70 : list byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 x8 (Z_to_bv 64 7) (Z_to_bv 64 display) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c3)) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                 x22 (Z_to_bv 64 (fi_n c3)) (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x13df4) fc None m (seg_rom rsegs) /\
    o4_ok ops c3 before display key /\
    op4_mem data D Sp lo B1 m0 m
      (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 before)) j30 (cmd_struct (repeat (b8 0) 24) 0 0 key) j70
              ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

(* The tagged arm's frame and invariant: world Bx, sp+0x10 = the cursor's n after lb (0x13fa4 `sd a4`), the struct
   = the model's cmd_struct (0x13f8c-0x13f98 stores, 0x13fb4 memcpy). *)
Definition o4_tmem (Sp lo : Z) (c3 : fuzz_in) (B1 : list byte) (before display key : Z) (Bx : list byte)
    (m0 m : word -> option byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  exists j30 j70 : list byte,
    op4_mem data D Sp lo Bx m0 m
      (op4_fr (C8 (Z_to_bv 64 (fi_n (o4_c4 c3)))) (Z_to_bv 64 (bv_swrap 32 before)) j30
              (o4_cs B1 c3 display key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

(* 0x1400c (`lwu a0, 0x6c(sp)`, the key): g_cmd[serial] zeroed (world o4_B2 B1), the struct built, s5 = sys.
   s0 = &g_cmd[serial] (0x13e30), s1 = serial (0x13e1c), s2 = 0xf0 (0x13f64), s3 = the cursor after lb, s4 = &g_cmd
   (0x13e20 + 0x13e2c: 0x37558 = W_BASE_PLAIN + OFF_g_cmd), s6 = n (0x13f7c-0x13fa0), s7 = 0x13 (0x13f68),
   s8 = 0x28 (0x13e24). *)
Definition op4_t1 (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c3 : fuzz_in) (B1 : list byte)
    (before display key : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2
                 (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))) (Z_to_bv 64 (g_ncmd B1))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0xf0) (Z_to_bv 64 (data + fi_off (o4_c4 c3))) (Z_to_bv 64 0x37558)
                 (Z_to_bv 64 (b2z (o4_sys B1 c3))) (Z_to_bv 64 (o4_n c3)) (Z_to_bv 64 0x13) (Z_to_bv 64 0x28)
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
                 (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1400c) fc None m (seg_rom rsegs) /\
    o4_tok ops c3 B1 before display key /\
    o4_tmem Sp lo c3 B1 before display key (o4_B2 B1) m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

(* 0x1408c (`beqz s5`): s2 = at_ as the 32-bit value (0xffffffff for -1), from 0x1401c or the queue scan. *)
Definition op4_t2 (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c3 : fuzz_in) (B1 : list byte)
    (before display key at_ : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2
                 (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))) (Z_to_bv 64 (g_ncmd B1))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (at_ mod 2 ^ 32)) (Z_to_bv 64 (data + fi_off (o4_c4 c3))) (Z_to_bv 64 0x37558)
                 (Z_to_bv 64 (b2z (o4_sys B1 c3))) (Z_to_bv 64 (o4_n c3)) (Z_to_bv 64 0x13) (Z_to_bv 64 0x28)
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
                 (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1408c) fc None m (seg_rom rsegs) /\
    o4_tok ops c3 B1 before display key /\
    o4_tmem Sp lo c3 B1 before display key (o4_B2 B1) m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

(* 0x140ec (`ld s5, 8(sp)`): the three calls done, world B5; s7 = want (0x14090 / 0x14098-0x140b4). *)
Definition op4_t3 (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c3 : fuzz_in) (B1 : list byte)
    (before display key at_ : Z) (B5 : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x24 t3 t4 t5 t6 : word) (m : word -> option byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2
                 (Z_to_bv 64 (W_BASE_PLAIN + A_Cmd_st (g_ncmd B1))) (Z_to_bv 64 (g_ncmd B1))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (at_ mod 2 ^ 32)) (Z_to_bv 64 (data + fi_off (o4_c4 c3))) (Z_to_bv 64 0x37558)
                 x21 (Z_to_bv 64 (o4_n c3)) (Z_to_bv 64 (o4_want B1 c3 at_)) x24
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
                 (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x140ec) fc None m (seg_rom rsegs) /\
    o4_tok ops c3 B1 before display key /\
    o4_tmem Sp lo c3 B1 before display key B5 m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

(* 0x14260 (`lw a0, 0x10(s9)`, g_ncmd): the command recorded (or not), world B6; s5 = &g_s (0x140ec), s8 = 1
   (0x140f0), s1 = serial, s3 / s6 the cursor after lb and n. *)
Definition op4_t4 (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c3 : fuzz_in) (B1 : list byte)
    (before display key : Z) (B6 : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x23 t3 t4 t5 t6 : word) (m : word -> option byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 x8 (Z_to_bv 64 (g_ncmd B1))
                 a0 a1 a2 a3 a4 a5 a6 a7
                 x18 (Z_to_bv 64 (data + fi_off (o4_c4 c3))) x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                 (Z_to_bv 64 (o4_n c3)) x23 (Z_to_bv 64 1)
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
                 (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x14260) fc None m (seg_rom rsegs) /\
    o4_tok ops c3 B1 before display key /\
    o4_tmem Sp lo c3 B1 before display key B6 m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

(* ---------------------------------------------------------------- the segment statements *)

(* 0x13910 -> 0x13df4: op_begin, the struct zeroed, before saved, the three bytes *)
Definition op4_entry_stmt : Prop :=
  forall Sp lo ops c c1 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms (Q : machine_state -> Prop),
    memset_contract ->
    llvm_case data D m0 gp tp 4 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    op_begin_m B = Some (B1, tt) ->
    (forall ms', op4_j m0 gp tp Sp lo ops (o4_c3 c1) B1 (S_queued B) (o4_display c1) (o4_key c1)
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

(* 0x13df4 -> the latch, g_raw != 0: the u16, w % 25, the take, memcpy, submit, check_refusal, settle *)
Definition op4_raw_stmt : Prop :=
  forall Sp lo ops c3 B1 before display key B' cout m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms
    (Q : machine_state -> Prop),
    memcpy_contract -> diginet_session_submit_contract -> check_refusal_submit_contract -> settle_contract ->
    op4_j m0 gp tp Sp lo ops c3 B1 before display key ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    g_raw B1 <> 0 ->
    op4_raw_m B1 D c3 before display key = Some (B', cout) ->
    (forall ms', llvm_latch data D m0 gp tp Sp lo ops cout B'
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

(* 0x13df4 -> 0x1400c, g_raw = 0: memset(&g_cmd[serial]), lb, the struct's stores, memcpy, the F0 13 xx 70 scan *)
Definition op4_tag1_stmt : Prop :=
  forall Sp lo ops c3 B1 before display key m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms
    (Q : machine_state -> Prop),
    memset_contract -> memcpy_contract -> op4_sys_scan_stmt -> op4_sys_short_stmt ->
    op4_j m0 gp tp Sp lo ops c3 B1 before display key ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    g_raw B1 = 0 -> g_ncmd B1 < CMDS_MAX ->
    (forall ms', op4_t1 m0 gp tp Sp lo ops c3 B1 before display key
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

(* 0x1400c -> 0x1408c: the coalescable test (:1094 h_coalescable(c.key)), g_nq = 0, the queue scan *)
Definition op4_tag2_stmt : Prop :=
  forall Sp lo ops c3 B1 before display key at_ m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms
    (Q : machine_state -> Prop),
    op4_find_scan_stmt ->
    op4_t1 m0 gp tp Sp lo ops c3 B1 before display key ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    o4_atopt B1 key = Some at_ ->
    (forall ms', op4_t2 m0 gp tp Sp lo ops c3 B1 before display key at_
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

(* 0x1408c -> 0x140ec: want, diginet_session_submit, check_refusal_submit, check_latest_submit unless sys *)
Definition op4_tag3_stmt : Prop :=
  forall Sp lo ops c3 B1 before display key at_ B3 B4 B5 rc m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc ms (Q : machine_state -> Prop),
    diginet_session_submit_contract -> check_refusal_submit_contract -> check_latest_submit_contract ->
    op4_t2 m0 gp tp Sp lo ops c3 B1 before display key at_
      ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    (at_ = -1 \/ 0 <= at_ < CMDS_MAX) ->
    diginet_session_submit_m (o4_B2 B1) (o4_cs B1 c3 display key) = Some (B3, rc) ->
    check_refusal_submit_m B3 (o4_cs B1 c3 display key) rc before = Some (B4, tt) ->
    (if o4_sys B1 c3 then Some (B4, tt) else check_latest_submit_m B4 rc (o4_want B1 c3 at_))
      = Some (B5, tt) ->
    (forall ms', op4_t3 m0 gp tp Sp lo ops c3 B1 before display key at_ B5
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

(* 0x140ec -> 0x14260: the record of the command (:1104-1115) when want = SPEC_OK *)
Definition op4_tag4_stmt : Prop :=
  forall Sp lo ops c3 B1 before display key at_ B5 B6 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc ms (Q : machine_state -> Prop),
    memcpy_contract ->
    op4_t3 m0 gp tp Sp lo ops c3 B1 before display key at_ B5
      ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    (at_ = -1 \/ 0 <= at_ < CMDS_MAX) ->
    (if o4_want B1 c3 at_ =? SPEC_OK then o4_rec B5 B1 c3 display key at_ else Some B5) = Some B6 ->
    (forall ms', op4_t4 m0 gp tp Sp lo ops c3 B1 before display key B6
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

(* 0x14260 -> the latch: g_ncmd++ (:1117), the cursor after the take, settle(0) (:1118) *)
Definition op4_tag5_stmt : Prop :=
  forall Sp lo ops c3 B1 before display key B6 B8 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc ms (Q : machine_state -> Prop),
    settle_contract ->
    op4_t4 m0 gp tp Sp lo ops c3 B1 before display key B6
      ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    settle_m (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) 0 = Some (B8, tt) ->
    (forall ms', llvm_latch data D m0 gp tp Sp lo ops (o4_c5 c3) B8
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

End OP4D.
