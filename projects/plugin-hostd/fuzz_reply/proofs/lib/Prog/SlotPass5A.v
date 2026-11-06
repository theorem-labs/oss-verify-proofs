(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names, addresses and numbers changed; 655 of its 764 lines of code are new or changed and 1120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_instance_gone_b_seg.v, with its module paths and module names changed; 158 of its 206 lines of code are new or changed and 716 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotPass1 SlotPass9G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import printf_facts_c snprintf_c relay_remove_b_c
  relay_instance_gone_b_c SlotPass2Run SlotPass5Run SlotPass5Check.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
Import ListNotations.
Local Open Scope Z_scope.

Definition g5_W (SP : Z) : list (Z * Z) := [(SP - SNPRINTF_K, SP); (SP + 16, SP + 88)].

Lemma g5a_stk_cj : forall m lo hi, 2 ^ 20 <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs (MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi Hlo Hhi HW. unfold TASK_SIZE in Hhi. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (writable_hi_present m a ltac:(lia) (HW a Ha)) as [bb E].
  assert (NE : MemNorm.normalize_cj rsegs m (wa a) = m (wa a)).
  { unfold MemNorm.normalize_cj. rewrite (MemNorm.cj_drop_false_intro rsegs (wa a)); [reflexivity | |].
    - unfold wa. apply ro_addr_hi. lia.
    - right. unfold wa. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia. }
  unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity].
Qed.

Lemma g5a_rw_cj : forall m a cs, MemNorm.ro_agree rsegs m -> rw_cells rsegs m a cs -> 2 ^ 20 <= a ->
  a + Z.of_nat (cells_size cs) <= TASK_SIZE -> rw_cells rsegs (MemNorm.normalize_cj rsegs m) a cs.
Proof.
  intros m a cs RO [[Hwf Hb] Hw] Ha Hlt. unfold TASK_SIZE in Hlt. split; [split; [exact Hwf|]|].
  - apply (MemNorm.bytes_at_normalize_cj_low rsegs m a _ RO); [|exact Hb].
    rewrite cells_bytes_length by exact Hwf. unfold TASK_SIZE. lia.
  - apply (MemNorm.wr_at_norm_cj rsegs m _ a _ (MemNorm.mem_rel_cj_normalize rsegs m RO) Hw).
    intros i Hi. apply (MemNorm.cj_drop_false_intro rsegs).
    + unfold wa. apply ro_addr_hi. lia.
    + right. unfold wa. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
Qed.

Lemma g5a_cb_after : forall W m m' A n (junk bs : list byte),
  rw_cells rsegs m A [CB n junk] -> munch W m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' A bs -> (length bs <= n)%nat ->
  disjoint_from W (A + Z.of_nat (length bs)) (Z.of_nat n - Z.of_nat (length bs)) ->
  rw_cells rsegs m' A [CB n (bs ++ skipn (length bs) junk)].
Proof.
  intros W m m' A n junk bs [[Wf Bj] Wr] MU WM Hb Hl Hd.
  destruct Wf as [Wf _]. cbn [cell_wf] in Wf.
  cbn [cells_bytes cbytes] in Bj. rewrite app_nil_r in Bj.
  rewrite <- (firstn_skipn (length bs) junk) in Bj. apply bytes_at_app in Bj. destruct Bj as [_ B2].
  rewrite firstn_length_le in B2 by lia.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_app, length_skipn. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact Hb|].
    eapply bytes_at_transport; [exact B2 | exact MU |].
    rewrite length_skipn. replace (Z.of_nat (length junk - length bs)) with (Z.of_nat n - Z.of_nat (length bs)) by lia.
    exact Hd.
  - eapply wr_at_transport; [|exact WM]. cbn [cells_size csize] in Wr |- *. exact Wr.
Qed.

Lemma g5a_img_free : forall D n, 2 ^ 21 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs.
  match type of Hs with In _ ?L =>
    assert (H : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 21) L = true)
      by (vm_compute; reflexivity) end.
  rewrite forallb_forall in H. specialize (H s Hs). apply Z.leb_le in H. lia.
Qed.

Lemma g5a_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma g5a_le_byte_bv : forall v k, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v k Hv. unfold le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Mem.Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

Lemma g5a_word_le8 : forall segs m a v, word_mem segs m a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  bytes_at segs m a (le8 (Z_to_bv 64 v)).
Proof.
  intros segs m a v Hw Hv Ha Hb. split; [exact Ha|]. rewrite length_le8. split; [lia|].
  intros j Hj. unfold le8, word_to_le_bytes. rewrite g5a_nth_le_bytes by exact Hj.
  rewrite unsigned_lit by lia. rewrite <- g5a_le_byte_bv by exact Hv. exact (Hw j Hj).
Qed.

Lemma g5a_ro_hi : forall W m m', munch W m m' -> (forall x, 0 <= x < 2 ^ 20 -> outside W x) ->
  MemNorm.ro_agree rsegs m -> MemNorm.ro_agree rsegs m'.
Proof.
  intros W m m' MU HW RO. apply (g9_ro_munch W m m' MU); [|exact RO].
  intros a HA. pose proof (bv_unsigned_in_range 64 a) as AR. change (bv_modulus 64) with (2 ^ 64) in AR.
  apply HW. split; [lia|]. destruct (Z_lt_le_dec (bv_unsigned a) (2 ^ 20)) as [HL|HL]; [exact HL|].
  exfalso. pose proof (ro_addr_hi (bv_unsigned a) ltac:(lia)) as HN. rewrite Z_to_bv_bv_unsigned in HN. congruence.
Qed.

Definition g5_snp_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SP id : Z) (junk : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) Ft (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ munch [(SP - SNPRINTF_K, SP); (SP + 40, SP + 88)] m m' /\ wmono rsegs m m' /\
    MemNorm.ro_agree rsegs m' /\
    rw_cells rsegs m' (SP + 40)
      [CB 48 (pf_bytes (instance_prefix id ++ [0]) ++ skipn (length (instance_prefix id) + 1) junk)].

Lemma g5a_snp : snprintf_contract ->
  forall (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP id : Z) (junk : list byte) (canary : word),
  0 <= id < 256 -> IMG_END + SNPRINTF_K <= SP -> 2 ^ 21 + SNPRINTF_K <= SP -> SP + 88 <= TASK_SIZE ->
  (forall a, SP - SNPRINTF_K <= a < SP -> writable_at rsegs m a) ->
  rw_cells rsegs m (SP + 40) [CB 48 junk] -> MemNorm.ro_agree rsegs m -> frm0 fc ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (g5_snp_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP id junk m)
    (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SP + 40)) (Z_to_bv 64 48) (Z_to_bv 64 0x102a2)
             (Z_to_bv 64 0x103e6) (Z_to_bv 64 id) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP id junk canary
    HID HIMG H21 HTS WST CBJ RO FRM GG GU.
  unfold snprintf_contract in SNP. unfold IMG_END, SNPRINTF_K in *.
  assert (TSV : TASK_SIZE < 2 ^ 63) by (unfold TASK_SIZE; lia).
  pose proof (g5_pre_ok id) as [PNZ PLEN].
  assert (SPv : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; lia).
  assert (DPv : bv_unsigned (Z_to_bv 64 (SP + 40)) = SP + 40) by (apply unsigned_lit; lia).
  assert (MIJ : MemNorm.mem_inv_cj rsegs (MemNorm.normalize_cj rsegs m)) by apply MemNorm.mem_inv_cj_normalize.
  pose proof (MemNorm.mem_inv_cj_inv rsegs _ MIJ) as MI0.
  pose proof (MemNorm.mem_inv_cj_task rsegs _ MIJ) as TM0.
  pose proof (MemNorm.mem_rel_cj_normalize rsegs m RO) as REL.
  pose proof (ro_cells_image rsegs (MemNorm.normalize_cj rsegs m) 66210 (pf_bytes ([37; 115; 32; 37; 100; 32] ++ [0]))
    MI0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity)) as [_ HF].
  cbn [cells_bytes cbytes] in HF. rewrite app_nil_r in HF.
  pose proof (ro_cells_image rsegs (MemNorm.normalize_cj rsegs m) 66534
    (pf_bytes (K_GESTURE ++ [0]) ++ pf_bytes [47; 100; 101; 118]) MI0 ltac:(vm_compute; reflexivity) ltac:(lia)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)) as [_ HKY].
  cbn [cells_bytes cbytes] in HKY. rewrite app_nil_r in HKY.
  eapply evt_mono.
  { apply (MemNorm.evt_normalize_cj rsegs); [vm_compute; reflexivity|exact RO|].
    eapply SNP with (lo := SP - 5936) (canary := canary) (fmt := [37; 115; 32; 37; 100; 32])
      (ps := [Ps; PLit 32; Pd; PLit 32]) (args := [APtr K_GESTURE; AInt id]) (T := instance_prefix id) (junk := junk).
    - rewrite (unsigned_lit 66210) by lia. exact HF.
    - apply Z.leb_le. vm_compute. reflexivity.
    - apply Z.leb_le. vm_compute. reflexivity.
    - reflexivity.
    - rewrite SPv, DPv. cbn [pf_args_ok pf_arg_ok].
      split; [split|split; [|exact I]].
      + unfold K_GESTURE. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
      + exists (pf_bytes [47; 100; 101; 118]). rewrite (unsigned_lit 66534) by lia.
        split; [exact HKY|]. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [lia|].
        change (Z.of_nat (length K_GESTURE)) with 13.
        change (Z.of_nat (length (pf_bytes [47; 100; 101; 118]))) with 4.
        split; left; lia.
      + split; [lia|]. rewrite unsigned_lit by lia. reflexivity.
    - reflexivity.
    - rewrite DPv, (unsigned_lit 48) by lia. change (Z.to_nat 48) with 48%nat.
      apply g5a_rw_cj; [exact RO|exact CBJ|lia|cbn [cells_size csize]; lia].
    - rewrite (unsigned_lit 48) by lia. lia.
    - lia.
    - rewrite DPv. lia.
    - rewrite SPv, DPv. right. lia.
    - rewrite DPv. apply g5a_img_free. lia.
    - rewrite SPv. apply g5a_stk_cj; [lia|lia|intros a Ha; apply WST; lia].
    - rewrite SPv. unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - rewrite SPv. lia.
    - exact FRM.
    - exact MI0.
    - exact TM0.
    - apply (MemNorm.bytes_at_normalize_cj_low rsegs m _ _ RO); [rewrite length_le8; unfold GOT_GUARD, TASK_SIZE; lia|exact GG].
    - apply (MemNorm.bytes_at_normalize_cj_low rsegs m _ _ RO); [rewrite length_le8; unfold GUARD, TASK_SIZE; lia|exact GU]. }
  intros s (s0' & HP & HR & HO).
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m0' &
    E & MU & WM & _ & _ & FR & _ & _ & BY).
  subst s0'.
  rewrite SPv, DPv in MU. rewrite DPv in BY.
  replace (Z.to_nat (bv_unsigned (Z_to_bv 64 48) - 1)) with 47%nat in MU, BY by reflexivity.
  rewrite firstn_all2 in MU, BY by lia.
  destruct s as [r f pv sv rv c mm o].
  destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  cbn in R1, R2, R3, R4, R5, R6, R7, R8, HO.
  pose proof (MemNorm.munch_rel_cj rsegs _ m _ mm m0' REL R8 HO MU) as MUr.
  pose proof (MemNorm.wmono_rel_cj rsegs m _ mm m0' REL R8 HO WM) as WMr.
  pose proof (MemNorm.bytes_at_rel_cj rsegs mm m0' _ _ R8 BY) as BYr.
  unfold g5_snp_post.
  exists t0', t1', t2', (Z_to_bv 64 (Z.of_nat (length (instance_prefix id)))), a1', a2', a3', a4', a5', a6', a7',
    t3', t4', t5', t6', Ft, fc', mm.
  split; [unfold MS; subst; reflexivity|].
  split; [exact FR|].
  split.
  { eapply munch_weaken; [|exact MUr]. unfold sub_fp, SNPRINTF_K. cbn [outside]. intros x (H1 & H2 & _).
    split; [lia|]. split; [lia|exact I]. }
  split; [exact WMr|].
  split; [exact (MemNorm.ro_agree_same_cj rsegs m mm RO HO)|].
  replace (length (instance_prefix id) + 1)%nat with (length (pf_bytes (instance_prefix id ++ [0])))
    by (unfold pf_bytes; rewrite length_map, length_app; reflexivity).
  eapply (g5a_cb_after _ m); [exact CBJ|exact MUr|exact WMr|exact BYr| |].
  - unfold pf_bytes. rewrite length_map, length_app. cbn [length]. lia.
  - unfold pf_bytes. rewrite length_map, length_app. cbn [length disjoint_from]. split; [lia|split; [lia|exact I]].
Qed.
