(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths and module names changed; 182 of its 246 lines of code are new or changed and 511 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/M03_cells.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/*.v, as libreac/fuzz_ctrl's
   released U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg ->
   SegCF, the segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the
   allocator contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Cells beside the frame that headamp_check_contract (segment M03) and headamp_plain_contract (segment M04) of
   reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan) read, and the input bounds both segments use. Every lemma is
   stated over plain inputs (bytes, numbers, a memory and the allocator's model); the segments use them at the
   ghost's values and at a cut's FR.
   - errno (tp - 164 = 0x306bc) lies in a writable image segment that holds its four bytes (vm_compute on the image),
     so four writable errno bytes are a C4 cell, of the memory and of its normalized forms (normalize for M04,
     MemNorm.normalize_cj for M03).
   - strtol's SSP cells: the GOT slot 0x1f3e8 holds the guard's address 0x509d0 and the guard holds some word, by
     AllocExtra's ax_statics (both are the allocator's statics).
   - The three lie in the image, so apart from every live block (AllocExtra's ax_blocks_img).
   - The input bounds: null = b & 1 in [0, 1], cap = x mod 10 in [0, 9], the record's buffer of 8 to 5440 bytes, and
     the answer's rc is -1 with no cells or the cell count in [0, cap] (Pod/Headamp.v parse_props_total).
   No function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1 Tac_errno.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(* The record is well formed, so its buffer is 8 to 5440 bytes (Pod/Spa.v buf_header). *)
Lemma mc_rec_wf : forall inp, pod_rec_wf (head_rec inp).
Proof.
  intros inp. unfold head_rec. apply (pod_build_wf inp _ (snd (pod_build inp))). apply surjective_pairing.
Qed.

Lemma mc_len_bound : forall inp, 8 <= head_len inp <= 5440.
Proof. intros inp. destruct (buf_header (head_rec inp) (mc_rec_wf inp)) as (_ & _ & _ & H). exact H. Qed.

(* ---- The input bounds ---- *)
Lemma mc_cap_rng : forall x, 0 <= x mod 10 <= 9.
Proof. intros x. pose proof (Z.mod_pos_bound x 10 ltac:(lia)). lia. Qed.

Lemma mc_null_rng : forall b, 0 <= Z.land b 1 <= 1.
Proof.
  intros b. assert (E : Z.land b 1 = b mod 2).
  { change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. }
  rewrite E. pose proof (Z.mod_pos_bound b 2 ltac:(lia)). lia.
Qed.

(* The answer of the parse: rc = -1 with no cells, or rc cells with 0 <= rc <= cap. *)
Lemma mc_ans : forall nl cap inp, 0 <= cap ->
  (ans_rc (head_ans nl cap inp) = -1 /\ ans_cells (head_ans nl cap inp) = []) \/
  (0 <= ans_rc (head_ans nl cap inp) <= cap /\
   ans_rc (head_ans nl cap inp) = Z.of_nat (length (ans_cells (head_ans nl cap inp)))).
Proof.
  intros nl cap inp Hcap.
  assert (H : answer_ok cap (head_ans nl cap inp)) by (unfold head_ans; apply parse_props_total; exact Hcap).
  destruct (answer_ok_parts cap (head_ans nl cap inp) H) as [[(H1 & H2 & _) | (H1 & H2 & _)] _].
  - left. split; assumption.
  - right. split; assumption.
Qed.

(* rc's range and first's request. *)
Lemma mc_rc_rng : forall nl cap inp, 0 <= cap -> -1 <= ans_rc (head_ans nl cap inp) <= cap.
Proof. intros nl cap inp Hc. destruct (mc_ans nl cap inp Hc) as [(Hr & _) | (Hr & _)]; lia. Qed.

Lemma mc_first_req : forall rc, -1 <= rc <= 9 ->
  1 <= first_req rc <= 27 /\ 3 * Z.max rc 0 <= first_req rc /\ (0 < rc -> first_req rc = 3 * rc).
Proof.
  intros rc Hrc. unfold first_req. destruct (0 <? rc) eqn:E.
  - apply Z.ltb_lt in E. split; [lia|]. split; [lia|]. intros _. reflexivity.
  - apply Z.ltb_ge in E. split; [lia|]. split; [lia|]. intros H. lia.
Qed.

(* The first parse's cells as bytes: 3 rc bytes for rc >= 0, none for rc = -1. *)
Lemma mc_cells_len : forall nl cap inp, 0 <= cap ->
  Z.of_nat (length (ha_cells_bytes (ans_cells (head_ans nl cap inp)))) = 3 * Z.max (ans_rc (head_ans nl cap inp)) 0.
Proof.
  intros nl cap inp Hc. rewrite length_ha_cells_bytes.
  destruct (mc_ans nl cap inp Hc) as [(H1 & H2) | (H1 & H2)]; [rewrite H2, H1; reflexivity | lia].
Qed.

(* No cells unless rc > 0. *)
Lemma mc_cells_nil : forall nl cap inp, 0 <= cap -> ans_rc (head_ans nl cap inp) <= 0 ->
  ans_cells (head_ans nl cap inp) = [].
Proof.
  intros nl cap inp Hc Hr. destruct (mc_ans nl cap inp Hc) as [(_ & E) | (_ & E)]; [exact E|].
  destruct (ans_cells (head_ans nl cap inp)); [reflexivity | cbn [length] in E; lia].
Qed.

(* out holds the first parse's cells, then the guard bytes: OUT_LEN cap bytes in all. *)
Lemma mc_out_len : forall nl cap inp, 0 <= cap ->
  Z.of_nat (length (out_after cap (head_ans nl cap inp))) = OUT_LEN cap.
Proof.
  intros nl cap inp Hcap. unfold out_after. rewrite length_app, repeat_length.
  pose proof (mc_cells_len nl cap inp Hcap) as Hc. pose proof (mc_rc_rng nl cap inp Hcap) as Hr.
  unfold OUT_LEN in *. lia.
Qed.

(* ---- The image facts (vm_compute on the UBSan image) ---- *)
(* errno's four bytes (0x306bc .. 0x306bf): not read-only, and the image holds them. *)
Lemma mc_errno_img_bytes : forall i, 0 <= i < 4 ->
  Mem.ro_addr rsegs (wa (0x306bc + i)) = false /\ seg_rom rsegs (wa (0x306bc + i)) <> None.
Proof.
  intros i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct E as [-> | [-> | [-> | ->]]];
    (split; [vm_compute; reflexivity | let H := fresh in intros H; vm_compute in H; discriminate H]).
Qed.

(* The GOT slot 0x1f3e8 (8 bytes) and the guard 0x509d0 (8 bytes) lie in reserved image segments. *)
Lemma mc_resv_got : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x1f3e8) &&
    (0x1f3e8 + 8 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mc_resv_guard : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x509d0) &&
    (0x509d0 + 8 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mc_in_img : forall B a n x, ms_segs B = rsegs ->
  existsb (fun s : word * word => (bv_unsigned (fst s) <=? a) &&
    (a + n <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true ->
  a <= x < a + n -> in_img B x.
Proof.
  intros B a n x HS H Hx. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite HS; intros Hn; rewrite Hn in Hs; cbn in Hs; destruct Hs|].
  exists s. rewrite HS. split; [exact Hs | lia].
Qed.

(* ---- A C4 cell from four readable, writable bytes ---- *)
Lemma mc_cell4 : forall m E, 0 <= E -> E + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 4 -> exists b, mrd rsegs m (wa (E + i)) = Some b) -> wr_at rsegs m E 4 ->
  exists ev, rw_cells rsegs m E [C4 ev].
Proof.
  intros m E H0 H1 HB HW.
  destruct (HB 0 ltac:(lia)) as (b0 & E0). destruct (HB 1 ltac:(lia)) as (b1 & E1).
  destruct (HB 2 ltac:(lia)) as (b2 & E2). destruct (HB 3 ltac:(lia)) as (b3 & E3).
  assert (L4 : le4 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])) = [b0; b1; b2; b3]).
  { unfold le4. rewrite MState.unsigned_lit.
    - exact (StrFun.Z_to_le_bytes_to_Z [b0; b1; b2; b3]).
    - pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]) as N0.
      pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as N1. cbn [length Z.of_nat] in N1. lia. }
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  split; [split|].
  - exact (conj I I).
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, L4.
    split; [exact H0|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error].
    + replace (E + Z.of_nat 0) with (E + 0) by lia. exact E0.
    + replace (E + Z.of_nat 1) with (E + 1) by lia. exact E1.
    + replace (E + Z.of_nat 2) with (E + 2) by lia. exact E2.
    + replace (E + Z.of_nat 3) with (E + 3) by lia. exact E3.
    + lia.
  - exact HW.
Qed.

(* A cell on the normalized memories. *)
Lemma mc_rw_norm : forall m E cs, ro_agree rsegs m -> rw_cells rsegs m E cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> Mem.ro_addr rsegs (wa (E + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) E cs.
Proof.
  intros m E cs Hro ((Hwf & Hb) & Hw) Hra.
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m E _ Hro Hb)]|].
  exact (wr_at_norm rsegs m (normalize rsegs m) E _ (mem_rel_normalize rsegs m Hro) Hw Hra).
Qed.

Lemma mc_rw_cj : forall m E cs, ro_agree rsegs m -> rw_cells rsegs m E cs ->
  E + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> Mem.ro_addr rsegs (wa (E + i)) = false) ->
  rw_cells rsegs (MemNorm.normalize_cj rsegs m) E cs.
Proof.
  intros m E cs Hro ((Hwf & Hb) & Hw) Ht Hra.
  split; [split; [exact Hwf|]|].
  - apply MemNorm.bytes_at_normalize_cj_low; [exact Hro | rewrite cells_bytes_length by exact Hwf; exact Ht | exact Hb].
  - apply (MemNorm.wr_at_norm_cj rsegs m _ E _ (MemNorm.mem_rel_cj_normalize rsegs m Hro) Hw).
    intros i Hi. apply MemNorm.cj_drop_false_intro; [exact (Hra i Hi)|]. right.
    destruct Hw as (Hw0 & Hw1 & _). unfold TASK_SIZE in *. rewrite wa_unsigned by lia. lia.
Qed.

Section MC.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Let API := APIf rc.

Lemma mc_errno_val : errno_addr B = 0x306bc.
Proof. rewrite (sl_errno_val B APIf ra empty FF). reflexivity. Qed.

(* ---- errno: four writable bytes (FR's errno clause) are a C4 cell ---- *)
Lemma mc_errno_rw : forall mem,
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a) ->
  exists ev, rw_cells rsegs mem (errno_addr B) [C4 ev].
Proof.
  intros mem Herr.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  rewrite mc_errno_val in *.
  apply mc_cell4; [lia | lia | |].
  - intros i Hi. unfold mrd. destruct (mem (wa (0x306bc + i))) as [b|] eqn:E; [exists b; reflexivity|].
    destruct (seg_rom rsegs (wa (0x306bc + i))) as [b|] eqn:E2; [exists b; reflexivity|].
    exfalso. exact (proj2 (mc_errno_img_bytes i Hi) E2).
  - split; [lia|]. split; [lia|]. intros i Hi. specialize (Herr (0x306bc + i) ltac:(lia)).
    unfold writable_at in Herr. rewrite SEGS in Herr. exact Herr.
Qed.

Lemma mc_errno_norm : forall mem, ro_agree rsegs mem ->
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a) ->
  exists ev, rw_cells rsegs (normalize rsegs mem) (errno_addr B) [C4 ev].
Proof.
  intros mem HMI Herr.
  destruct (mc_errno_rw mem Herr) as (ev & H). exists ev.
  apply mc_rw_norm; [exact HMI | exact H |].
  intros i Hi. cbn in Hi. rewrite mc_errno_val. exact (proj1 (mc_errno_img_bytes i ltac:(lia))).
Qed.

Lemma mc_errno_cj : forall mem, ro_agree rsegs mem ->
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a) ->
  exists ev, rw_cells rsegs (MemNorm.normalize_cj rsegs mem) (errno_addr B) [C4 ev].
Proof.
  intros mem HMI Herr.
  destruct (mc_errno_rw mem Herr) as (ev & H). exists ev.
  apply mc_rw_cj; [exact HMI | exact H | rewrite mc_errno_val; cbn; unfold TASK_SIZE; lia |].
  intros i Hi. cbn in Hi. rewrite mc_errno_val. exact (proj1 (mc_errno_img_bytes i ltac:(lia))).
Qed.

(* ---- strtol's SSP cells ---- *)
Lemma mc_ssp : forall L A mem md, aa_MR API L A mem md ->
  bytes_at rsegs mem 0x1f3e8 (le8 (Z_to_bv 64 0x509d0)) /\ exists can, bytes_at rsegs mem 0x509d0 (le8 can).
Proof.
  intros L A mem md HM.
  destruct (ax_statics (b1_ax B APIf ra empty FF) L A mem md HM) as (W1 & (gv & Hgv & W2) & _).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  rewrite (ff_got_guard B APIf ra empty FF), (ff_guard B APIf ra empty FF), SEGS in W1.
  rewrite (ff_guard B APIf ra empty FF), SEGS in W2.
  split.
  - exact (KindBGlue.word_mem_le8 rsegs mem 0x1f3e8 0x509d0 W1 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exists (Z_to_bv 64 gv). exact (KindBGlue.word_mem_le8 rsegs mem 0x509d0 gv W2 Hgv ltac:(lia) ltac:(lia)).
Qed.

Lemma mc_ssp_norm : forall L A mem md, aa_MR API L A mem md -> ro_agree rsegs mem ->
  bytes_at rsegs (normalize rsegs mem) 0x1f3e8 (le8 (Z_to_bv 64 0x509d0)) /\
  exists can, bytes_at rsegs (normalize rsegs mem) 0x509d0 (le8 can).
Proof.
  intros L A mem md HM HMI.
  destruct (mc_ssp L A mem md HM) as (H1 & can & H2).
  split; [exact (bytes_at_normalize rsegs mem _ _ HMI H1)|].
  exists can. exact (bytes_at_normalize rsegs mem _ _ HMI H2).
Qed.

Lemma mc_ssp_cj : forall L A mem md, aa_MR API L A mem md -> ro_agree rsegs mem ->
  bytes_at rsegs (MemNorm.normalize_cj rsegs mem) 0x1f3e8 (le8 (Z_to_bv 64 0x509d0)) /\
  exists can, bytes_at rsegs (MemNorm.normalize_cj rsegs mem) 0x509d0 (le8 can).
Proof.
  intros L A mem md HM HMI.
  destruct (mc_ssp L A mem md HM) as (H1 & can & H2).
  split.
  - apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia | exact H1].
  - exists can.
    apply MemNorm.bytes_at_normalize_cj_low; [exact HMI | rewrite length_le8; unfold TASK_SIZE; lia | exact H2].
Qed.

(* ---- Separation ---- *)
(* An image range and a live block are apart. *)
Lemma mc_apart : forall L A mem md phi n x k, aa_MR API L A mem md -> In (phi, n) (blocks L A) -> 0 < n -> 0 < k ->
  (forall y, x <= y < x + k -> in_img B y) -> x + k <= phi \/ phi + n <= x.
Proof.
  intros L A mem md phi n x k HM Hin Hn Hk Himg.
  destruct (Z_le_dec (x + k) phi) as [H|H]; [left; exact H|].
  destruct (Z_le_dec (phi + n) x) as [H'|H']; [right; exact H'|].
  exfalso. apply blocks_In in Hin as (p & Ep & Hp).
  apply (ax_blocks_img (b1_ax B APIf ra empty FF) L A mem md p n (Z.max x phi - phi) HM Hp ltac:(lia)).
  rewrite Ep. replace (phi + (Z.max x phi - phi)) with (Z.max x phi) by lia. apply Himg. lia.
Qed.

Lemma mc_errno_blk : forall L A mem md phi n, aa_MR API L A mem md -> In (phi, n) (blocks L A) -> 0 < n ->
  errno_addr B + 4 <= phi \/ phi + n <= errno_addr B.
Proof.
  intros L A mem md phi n HM Hin Hn.
  apply (mc_apart L A mem md phi n (errno_addr B) 4 HM Hin Hn ltac:(lia)).
  exact (te_errno_img B APIf ra empty FF).
Qed.

Lemma mc_got_blk : forall L A mem md phi n, aa_MR API L A mem md -> In (phi, n) (blocks L A) -> 0 < n ->
  0x1f3e8 + 8 <= phi \/ phi + n <= 0x1f3e8.
Proof.
  intros L A mem md phi n HM Hin Hn.
  apply (mc_apart L A mem md phi n 0x1f3e8 8 HM Hin Hn ltac:(lia)).
  intros y Hy. exact (mc_in_img B 0x1f3e8 8 y (sl_segs B APIf ra empty FF) mc_resv_got Hy).
Qed.

Lemma mc_guard_blk : forall L A mem md phi n, aa_MR API L A mem md -> In (phi, n) (blocks L A) -> 0 < n ->
  0x509d0 + 8 <= phi \/ phi + n <= 0x509d0.
Proof.
  intros L A mem md phi n HM Hin Hn.
  apply (mc_apart L A mem md phi n 0x509d0 8 HM Hin Hn ltac:(lia)).
  intros y Hy. exact (mc_in_img B 0x509d0 8 y (sl_segs B APIf ra empty FF) mc_resv_guard Hy).
Qed.

End MC.
