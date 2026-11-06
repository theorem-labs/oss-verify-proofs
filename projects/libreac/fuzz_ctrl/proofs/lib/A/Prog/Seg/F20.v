(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 540 of its 622 lines of code are new or changed and 2475 lines of the source are left out. *)
(* Segment F20 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the cut-to-cut range 0x82418 .. 0x824b4
   (slot-plan-asan section 2 row F20 plus the CKV call). From the F19 exit cut at 0x82418 (a0 = 0 on the BCMP
   fall-through) the block runs four one-byte instrumented checks on the record bytes phi+14..phi+17 (each loads
   the shadow byte at (a >> 3) + 0x7fff8000 and the `bnez shadow,errpath` is shown NOT taken from the zero shadow
   byte the cut carries), the two record comparisons at 0x8245c / 0x824a8 shown NOT taken (the field equalities the
   cut carries), `mv a0,s7` at 0x824ac and the call `jal reac_ctrl_checksum_verify` at 0x824b0 (Section Hypothesis
   CKV): a0 = phi, the 32 record bytes [phi+18, phi+50) are addressable, and the only memory the callee writes is
   its own 16-byte frame [sp - 16, sp) inside the slot's stack window. It returns 0 when the block sum of those 32
   bytes is 0 and -1 otherwise, which the exit cut at 0x824b4 carries in a0.
   The run is a Lib.Exec.evt (sl_run_lib, AsanLift.evt_SR_canon_lazy); FRA moves across the callee's window write
   by Tac_slot.sl_win_run (with Tac_slot.sl_win_stk for the slot window and Tac_slot.fsrec_munch_lo for the
   side-arm frame record), whose premises are read off the new FRA (fra_win for the callee window, fra_frame for
   the frame placement); FLSI moves by flsi_win. The cuts are the official SlotInv.v Inv_A82418_at (entry) and
   Inv_A824b4_at (exit, F21's entry). Push 12: the five FLS facts (s2 = len, the [A+152] tfill spill, the record
   bytes at phi) and LT = IFS g fr (S j) are not written by the segment, so both cuts carry them (ifs_keep).
   Tac_slot is only Require'd (not Imported) so the A.Tk.UL engine tactics do not shadow the Lib ones. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFragLib RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_checksum_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* ---- Byte / word helpers for the Lib engine (its loads consume `ov_read_bytes _ _ (wa a) n = Some bs`). ---- *)
Lemma rd1 : forall m a v, b8 m a v -> ov_read_bytes rsegs m (wa a) 1 = Some [Z_to_bv 8 v].
Proof.
  intros m a v H. unfold b8 in H.
  pose proof (bytes_at_ov_read rsegs m a [Z_to_bv 8 v] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma rd2 : forall m a v, u16 m a v -> ov_read_bytes rsegs m (wa a) 2 = Some (le2 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold u16 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 2 H ltac:(rewrite length_le2; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite length_le2; lia).
  exact HH.
Qed.
Lemma rd8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold q64 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite length_le8; lia).
  exact HH.
Qed.

Lemma ubv8 : forall v, 0 <= v < 256 -> bv_unsigned (zxb (Z_to_bv 8 v)) = v.
Proof.
  intros v Hv. unfold zxb. rewrite (unsigned_lit (bv_unsigned (Z_to_bv 8 v))).
  - rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - rewrite Z_to_bv_unsigned, (bv_wrap_small 8 v) by (unfold bv_modulus; cbn; lia). lia.
Qed.
Lemma zxb8 : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; cbn; lia.
Qed.
Lemma eqb0_false : forall v, 0 < v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal bv_unsigned) in HC. rewrite !unsigned_lit in HC by lia. lia.
Qed.
(* seqz (= sltiu _ 1) reduces to the 0/1 indicator, matching the carried booleans. *)
Lemma seqz_v17 : forall v17, 0 <= v17 < 256 ->
  Lib.PropExec.v_sltiu (zxb (Z_to_bv 8 v17)) 1 = Z_to_bv 64 (if v17 =? 0 then 1 else 0).
Proof.
  intros v17 Hv. unfold Lib.PropExec.v_sltiu. rewrite ubv8 by lia. change (bv_wrap 64 1) with 1%Z.
  replace (v17 <? 1) with (v17 =? 0) by
    (destruct (Z.eqb_spec v17 0); destruct (Z.ltb_spec v17 1); lia).
  destruct (v17 =? 0); reflexivity.
Qed.
Lemma seqz_vs8 : forall vs8, 0 <= vs8 < 2 ^ 64 ->
  Lib.PropExec.v_sltiu (Z_to_bv 64 (vs8 + -1)) 1 = Z_to_bv 64 (if vs8 =? 1 then 1 else 0).
Proof.
  intros vs8 Hv. unfold Lib.PropExec.v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eq_dec vs8 0) as [->|H0].
  - change ((0 + -1) mod 2 ^ 64 <? 1) with false. reflexivity.
  - rewrite (Z.mod_small (vs8 + -1) (2 ^ 64)) by lia.
    replace (vs8 + -1 <? 1) with (vs8 =? 1) by
      (destruct (Z.eqb_spec vs8 1); destruct (Z.ltb_spec (vs8 + -1) 1); lia).
    destruct (vs8 =? 1); reflexivity.
Qed.
(* Byte-combine for the is_8819 u16 compare at 0x8245c. *)
Lemma cmp16_eq : forall v14 v15 field16, 0 <= v14 < 256 -> 0 <= v15 < 256 -> field16 = v14 + 256 * v15 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (Z_to_bv 8 v15))) 8)))
                    (bv_unsigned (zxb (Z_to_bv 8 v14))))
  = zx16 (Z_to_bv 64 field16).
Proof.
  intros v14 v15 field16 H14 H15 Hf.
  rewrite (ubv8 v15), (ubv8 v14) by lia.
  rewrite (unsigned_lit (Z.shiftl v15 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia.
  unfold zx16. rewrite (unsigned_lit field16) by lia.
  rewrite Z.mod_small by lia. subst field16. reflexivity.
Qed.

(* The model facts the segment reads. *)
Lemma t_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.
Lemma t_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk, bsl. rewrite length_firstn, length_skipn, t_g_len. reflexivity. Qed.
Lemma t_g6_len : forall inp j, length (bsl (t_g inp j) 34 6) = 6%nat.
Proof. intros inp j. unfold bsl. rewrite length_firstn, length_skipn, t_g_len. reflexivity. Qed.

(* Push 12: the identity record (38 bytes at fr + 2688) and the fragment record (72 bytes at fr + 2768) of LT keep
   their lengths in every turn (SlotModel turn), so their bytes lie inside the frame. *)
Lemma fg_first_len : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold fg_first, fg_body.
  rewrite !length_app, length_skipn, (RcFragLib.rf_bsl_length g 6 6),
    (RcFragLib.rf_bsl_length g 27 (fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g HL HG. unfold fg_st, fcls.
  rewrite (RcFragLib.rf_class_nn 1 1 1 1 1) by lia.
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in FR. rewrite !andb_true_iff in FR.
    destruct FR as (FR & _). destruct FR as (FR & Hn2). destruct FR as (_ & Hn1).
    apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia. }
  destruct (bat g 19 =? 1); [cbn [fg_next]; apply fg_first_len; assumption|].
  destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply RcFragLib.rf_clear_length; exact HL].
  assert (HT : fg_T st g <= 64).
  { unfold fg_keep in KEEP. rewrite !andb_true_iff in KEEP. destruct KEEP as (_ & KEEP).
    apply Z.leb_le in KEEP. exact KEEP. }
  destruct (fg_close st g); cbn [negb fg_next];
    apply RcFragLib.rf_clear_length, RcFragLib.rf_fg_join_length; assumption.
Qed.

Lemma t_FG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold t_FG in *. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; apply fg_st_len; solve [exact IH | apply t_g_len].
Qed.

Lemma rp_id_len : forall idb len g, length idb = RcIdentModel.ID_SIZE ->
  length (rp_id idb len g) = RcIdentModel.ID_SIZE.
Proof.
  intros idb len g H. unfold rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply RcIdentModel.ING_length; exact H | exact H].
Qed.

Lemma fg_id_len : forall idb len st g, length idb = RcIdentModel.ID_SIZE ->
  length (fg_id idb len st g) = RcIdentModel.ID_SIZE.
Proof.
  intros idb len st g H. unfold fg_id.
  destruct (fg_rf len st g =? 1); [apply RcIdentModel.ING_length; exact H | exact H].
Qed.

Lemma t_ID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. change 38%nat with RcIdentModel.ID_SIZE. induction j as [|j IH]; [reflexivity|].
  unfold t_ID in *. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; apply fg_id_len, rp_id_len, IH.
Qed.

Ltac ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (unsigned_lit X) by lia
  end.
Ltac outW := let x := fresh "x" in let Hx := fresh "Hx" in let H1 := fresh "HW1" in let H2 := fresh "HW2" in
  intros x Hx; cbn [outside]; split; [|exact I]; intros [H1 H2].
Ltac subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* Read-only image addresses lie below HIGHMEM_BEG (every image segment ends below it). *)
Lemma rsegs_low : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? HIGHMEM_BEG) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CKV : reac_ctrl_checksum_verify_contract.

Lemma mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Lib-engine analogue of Tac_slot.sl_run: prove the segment run as a Lib.Exec.evt (so the Lib-form reac
   contracts compose), then bridge to SR via evt_SR_canon_lazy. *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (canonical_register_state (mkst regs pc mem (seg_rom rsegs))) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* A spill read through s1 = A (FRA's spill base, bounded by the entry sp): its base is A. *)
Lemma sl_spill_at : forall regs m A off v, rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA Ho0 Ho (A' & H9' & Hq).
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. cbn in Hq1.
    unfold rg in H9, H9'. rewrite H9 in H9'. apply (f_equal bv_unsigned) in H9'.
    rewrite (unsigned_lit A) in H9' by lia. rewrite Z_to_bv_unsigned in H9'. unfold bv_wrap, bv_modulus in H9'.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in H9'.
    pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)).
    lia. }
  subst A'. exact Hq.
Qed.

(* FLSI (SlotInv.v) moves across a run whose write set W is app memory (so no shadow byte changes and the
   addressable facts stay) and misses the spill area [A, A + 416) at s1 = A, the frame [fr, fr + 3136) and every
   block of the entry heap (the input block f1_IN names is one of them when n > 0). F21 uses it too. *)
Lemma flsi_win : forall g j fr regs regs' mem mem' W A,
  FLSI g j fr regs mem -> rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  munch W mem mem' -> wmono rsegs mem mem' -> all_app W ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x) ->
  (forall q n x, In (q, n) (g_H g) -> q <= x < q + n -> outside W x) ->
  FLSI g j fr regs' mem'.
Proof.
  intros g j fr regs regs' mem mem' W A
    (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pour & Pin & Pg & P184 & P256 & P264 & P272 &
       P32) &
      F128 & Fstk & F144 & Fid17) &
     F216 & F224 & F248 & (Fin1 & Fin2 & Fin3) &
     (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfa & Cid & C72 & C64 & C56 & C48))
    H9 HA0 HA E9 MU WM AW HWA HWfr HWblk.
  assert (Kq : forall off v, 0 <= off -> off + 8 <= 416 -> spill regs mem off v -> spill regs' mem' off v).
  { intros off v Ho0 Ho1 Hs. pose proof (sl_spill_at regs mem A off v H9 HA0 HA Ho0 Ho1 Hs) as Hq.
    exists A. split; [unfold rg in *; rewrite E9; exact H9|].
    unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8. intros x Hx. apply HWA. lia. }
  pose proof (munch_meta W mem mem' MU AW) as MK.
  split; [split|].
  { (* push 13B: PRO, the prologue spills, our[]'s 6 bytes and the input block *)
    unfold PRO.
    split; [apply Kq; [lia | lia | exact P40]|].
    split; [apply Kq; [lia | lia | exact P120]|].
    split; [apply Kq; [lia | lia | exact P136]|].
    split; [apply Kq; [lia | lia | exact P160]|].
    split; [apply Kq; [lia | lia | exact P168]|].
    split; [apply Kq; [lia | lia | exact P176]|].
    split; [apply Kq; [lia | lia | exact P208]|].
    split; [apply Kq; [lia | lia | exact P248]|].
    split; [exact (addressable_kept mem mem' _ _ Pour MK)|].
    split.
    { eapply fl_bytes; [exact Pin | exact MU |].
      intros x Hx. apply (HWblk (g_p g) (g_n g) x); [apply Fin1|]; rewrite g_n_len; lia. }
    split.
    { intros Hn. destruct (Pg Hn) as (PIn & Pad).
      split; [exact PIn | exact (addressable_kept mem mem' _ _ Pad MK)]. }
    (* push 14D: A4's [A + 184] / [A + 256] / [A + 264] / [A + 272]; v1.9: [A + 32] = fr + 2880 *)
    split; [apply Kq; [lia | lia | exact P184]|].
    split; [apply Kq; [lia | lia | exact P256]|].
    split; [apply Kq; [lia | lia | exact P264]|].
    split; [apply Kq; [lia | lia | exact P272]|].
    apply Kq; [lia | lia | exact P32]. }
  { split; [apply Kq; [lia | lia | exact F128]|].
    split.
    { apply (stk_transport rsegs W mem mem' fr (fr + FRAME_BYTES) Fstk MU WM).
      intros x Hx. left. exact (HWfr x Hx). }
    (* push 12A: [A + 144] = fr + 2688 and the 17 addressable bytes at fr + 2691 *)
    split; [apply Kq; [lia | lia | exact F144]|].
    exact (addressable_kept mem mem' _ _ Fid17 MK). }
  split; [apply Kq; [lia | lia | exact F216]|].
  split; [apply Kq; [lia | lia | exact F224]|].
  split; [apply Kq; [lia | lia | exact F248]|].
  split.
  { split; [exact Fin1|].
    split; [exact (addressable_kept mem mem' _ _ Fin2 MK)|].
    eapply fl_bytes; [exact Fin3 | exact MU |].
    intros x Hx. apply (HWblk (g_p g) (g_n g) x); [apply Fin1|]; rewrite g_n_len; lia. }
  (* push 14D / 14E: FLC, the loop-invariant spills and the two record ranges (v1.9: [A+56] / [A+48] last) *)
  unfold FLC.
  split; [apply Kq; [lia | lia | exact C256]|].
  split; [apply Kq; [lia | lia | exact C184]|].
  split; [apply Kq; [lia | lia | exact C192]|].
  split; [apply Kq; [lia | lia | exact C80]|].
  split; [apply Kq; [lia | lia | exact C88]|].
  split; [apply Kq; [lia | lia | exact C96]|].
  split; [apply Kq; [lia | lia | exact C272]|].
  split; [apply Kq; [lia | lia | exact C264]|].
  split; [exact (addressable_kept mem mem' _ _ Cfa MK)|].
  split; [exact (addressable_kept mem mem' _ _ Cid MK)|].
  split; [apply Kq; [lia | lia | exact C72]|].
  split; [apply Kq; [lia | lia | exact C64]|].
  split; [apply Kq; [lia | lia | exact C56] | apply Kq; [lia | lia | exact C48]].
Qed.

(* LT = IFS g fr i crosses a run that keeps s1, keeps the shadow map and misses the frame's identity / fragment
   records and the first-fragment state (v1.9: the spills [A+104, A+120) and the body [fr + 2880, fr + 2915),
   F13.fsj_keep). F21 uses it too. *)
Lemma ifs_keep : forall g fr i A regs regs' m m' W,
  IFS g fr i regs m -> rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  munch W m m' -> meta_kept m m' ->
  (forall x, fr + 2688 <= x < fr + 2840 -> outside W x) ->
  (forall x, A + 104 <= x < A + 120 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x) ->
  IFS g fr i regs' m'.
Proof.
  intros g fr i A regs regs' m m' W H H9 HA0 HA E9 MU MK Hofr HoA Hob.
  unfold IFS, IDj, IDb, IDBe, FGj, FGb, FGBe in *.
  destruct H as ((HI & HIok) & (HG & HGok) & HS).
  split; [split; [|exact HIok]|].
  { eapply fl_bytes; [exact HI | exact MU |]. rewrite t_ID_len. intros x Hx. apply Hofr. lia. }
  split; [split; [|exact HGok]|].
  { eapply fl_bytes; [exact HG | exact MU |]. rewrite t_FG_len. intros x Hx. apply Hofr. lia. }
  exact (F13.fsj_keep g fr i A regs regs' m m' W HS H9 HA0 HA E9 MU MK HoA Hob).
Qed.

(* ---- The call: from 0x824ac (`mv a0,s7`) through `jal reac_ctrl_checksum_verify` to 0x824b4. ---- *)
Lemma f20_call_evt :
  forall (ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi A lo sp : Z) (blk : list byte),
    0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    length blk = 32%nat -> bytes_at rsegs m (phi + 18) blk ->
    stk rsegs m lo sp ->
    asan_cells m -> shadow_rw m -> addressable m (phi + 18) 32 ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (if blocksum blk =? 0 then 0 else -1)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x824b4) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x824ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi A lo sp blk Rsp Hp0 HpE Hpsp Hlo Hlo16 Lblk Hblk Hstk HAC HSW Hadr.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  (* 0x824ac mv a0,s7 ; 0x824b0 jal reac_ctrl_checksum_verify *)
  step. step.
  eapply evt_cut.
  { eapply CKV with (p := phi) (lo := lo) (bs := blk);
      unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME; rewrite ?Esp.
    - lia.
    - unfold APPMEM_END in HpE. lia.
    - reflexivity.
    - exact Lblk.
    - exact Hblk.
    - exact Hstk.
    - lia.
    - left. lia.
    - exact HAC.
    - exact HSW.
    - exact Hadr.
    - outW. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & _ & ST'). subst ms'.
  unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME in MU, ST'. rewrite Esp in MU, ST'.
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
  apply evt_done.
  do 7 eexists. exists m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

(* The segment, on the official cuts of SlotInv.v: entry Inv_A82418_at (the F19/F20 interface; the is_8819 match
   data, s7 = phi, s4 = s6 = phi + 18, s8 = k, the [A+280] spill and the frame-pointer spills, the u16 at fr + 196),
   exit Inv_A824b4_at (a0 = the call's result, the record state unchanged; F21's entry). Both carry the live list
   hb1 phi (a_size len), which is hb1 phi len here (50 <= len). *)
Lemma seg_F20 : forall j : nat,
  Hat B APIf ra (Inv_A824b4_at B APIf ra) j -> Hat B APIf ra (Inv_A82418_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK &
    Hs7 & Hs4 & Hs6 & Hs8 & Ha0 & Hphi0 & Hphi50 & Hbig & Rtk & Hblk & Hrec & Hsp280 & Hb136 & Hb120 & Hb176 &
    (v14 & v15 & v16 & v17 & field16 &
     Hsp248 & Hfield & Hb14 & Hb15 & Hb16 & Hb17 & Rv14 & Rv15 & Rv16 & Rv17 &
     Hsh14 & Hsh15 & Hsh16 & Hsh17 & Heq1 & Heq2) &
    H18 & H152 & Hgb & Hpb & Hpl & HLT). subst c.
  assert (Esz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  rewrite Esz in HFRA, HENT.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill304 & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof HRT as (HAC0 & HSW0 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  assert (Hin : In (phi, flen g j) (hb1 phi (flen g j) ++ g_H g)) by (unfold hb1; cbn; left; reflexivity).
  pose proof (lw_blocks (APIf rc) _ mem md phi (flen g j) HAH Hin) as LWr1.
  pose proof (lwb_align _ _ _ _ _ _ LWr1) as Hal16.
  pose proof (lwb_end _ _ _ _ _ _ LWr1) as Hbelow.
  pose proof HHB as (Hphinz & Hadr).
  unfold AC.a_size in Hadr. rewrite Z.max_l in Hadr by lia.
  pose proof Hadr as (_ & _ & HadrE & _).
  pose proof Hwin as (HwS0 & HwS1 & _).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
  assert (Esp : bv_unsigned (getr regs 2) = sp) by exact Haspz.
  destruct (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hwlo & Hwstk).
  unfold AC.aspZ in Hwlo, Hwstk. rewrite Esp in Hwlo, Hwstk.
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hfrsep & HfrA & _ & _).
  unfold AC.aspZ in Hfrsep. rewrite Esp in Hfrsep.
  assert (HFN : FN_STACK = 1048576 - 4096) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof (sl_spill_at regs mem A 280 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp280) as Hq280.
  pose proof (sl_spill_at regs mem A 248 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp248) as Hq248.
  set (W := [(sp - 16, sp)]).
  apply (sl_run_lib regs (Z_to_bv 64 0x82418) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x824b4 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 26 = getr regs 26 /\
       getr R 20 = Z_to_bv 64 (phi + 18) /\ getr R 23 = Z_to_bv 64 phi /\
       getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\
       getr R 10 = Z_to_bv 64 (if blocksum (t_blk (g_in g) j) =? 0 then 0 else -1) /\
       getr R 18 = getr regs 18 /\
       munch W mem mem' /\ wmono rsegs mem mem' /\ stk rsegs mem' (sp - FN_STACK) sp)
    (Post B APIf ra g)).
  - exact Hhalt.
  - change (canonical_register_state (mkst regs (Z_to_bv 64 0x82418) mem (seg_rom rsegs)))
      with (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82418) fp_csr None mem (seg_rom rsegs)).
    rewrite mkR_of_expand.
    assert (CALL : forall (ra1 b0 b1 b2 b3 b4 b5 : word),
      evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                       (getr regs 8) (Z_to_bv 64 A)
                       (Z_to_bv 64 (if blocksum (t_blk (g_in g) j) =? 0 then 0 else -1)) a1' a2' a3' a4' a5' a6'
                       (getr regs 17) (getr regs 18) (getr regs 19) (Z_to_bv 64 (phi + 18)) (getr regs 21)
                       (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 phi) (Z_to_bv 64 (t_k (g_in g) j)) (getr regs 25)
                       (Z_to_bv 64 ASAN_K) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
                       (getr regs 31))
                  fp_regs (Z_to_bv 64 0x824b4) fp_csr None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] mem m' /\ wmono rsegs mem m' /\ stk rsegs m' (sp - FN_STACK) sp)
      (MS (mkR ra1 (Z_to_bv 64 sp) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
               (getr regs 8) (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (Z_to_bv 64 (phi + 18)) (getr regs 21) (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 phi)
               (Z_to_bv 64 (t_k (g_in g) j)) (getr regs 25) (Z_to_bv 64 ASAN_K) (getr regs 27) (getr regs 28)
               (getr regs 29) (getr regs 30) (getr regs 31))
          fp_regs (Z_to_bv 64 0x824ac) fp_csr None mem (seg_rom rsegs))).
    { intros ra1 b0 b1 b2 b3 b4 b5.
      eapply f20_call_evt with (lo := sp - FN_STACK) (blk := t_blk (g_in g) j) (sp := sp).
      - unfold APPMEM_END in *. lia.
      - lia.
      - unfold APPMEM_END in *. lia.
      - lia.
      - lia.
      - lia.
      - apply t_blk_len.
      - exact Hblk.
      - exact Hwstk.
      - exact HAC0.
      - exact HSW0.
      - exact (addressable_sub mem phi (flen g j) 18 32 Hadr ltac:(lia) ltac:(lia) ltac:(lia)). }
    rewrite Hr2.
    subst_slot Ha0. subst_slot Hs7. subst_slot Hr9. subst_slot Hs8. subst_slot Hr26. subst_slot Hs4.
    subst_slot Hs6.
    pose proof (rd1 mem _ _ Hsh14) as RD14. pose proof (rd1 mem _ _ Hsh15) as RD15.
    pose proof (rd1 mem _ _ Hsh16) as RD16. pose proof (rd1 mem _ _ Hsh17) as RD17.
    pose proof (rd1 mem _ _ Hb14) as RDb14. pose proof (rd1 mem _ _ Hb15) as RDb15.
    pose proof (rd1 mem _ _ Hb16) as RDb16. pose proof (rd1 mem _ _ Hb17) as RDb17.
    pose proof (rd8 mem _ _ Hq248) as RDkp.
    pose proof (rd2 mem _ _ Hfield) as RDfield.
    (* 0x82418 bnez a0 : a0 = 0, not taken *)
    step. if_false.
    (* 0x8241c addi ; srli ; add ; lb a2 shadow(phi+14) *)
    step. step. step. ush.
    step.
    (* 0x8242c ld a1,248(s1) ; 0x82430 lhu a1,20(a1) ; 0x82434 bnez a2 (=0) not taken *)
    step. step. step. if_false.
    (* 0x82438 addi ; srli ; add ; lb a3 shadow(phi+15) *)
    step. step. step. ush.
    step.
    (* 0x82448 lbu a2,14(s7)=v14 ; 0x8244c bnez a3 (=0) not taken ; 0x82450 lbu a0=v15 ; slli ; or *)
    step. step. if_false. step. step. step.
    (* 0x8245c bne a0,a1 : (v15<<8)|v14 = field16 (Heq1), not taken *)
    step. rewrite (cmp16_eq v14 v15 field16 Rv14 Rv15 Heq1), bv_eqb_refl; cbn [negb]; cbv iota.
    (* 0x82460 addi ; srli ; add ; lb a1 shadow(phi+16) *)
    step. step. step. ush.
    step.
    (* 0x82470 bnez a1 (=0) not taken ; 0x82474 lbu a0=v16 ; 0x82478 beqz a0 *)
    step. if_false. step. step. rewrite (zxb8 v16) by lia.
    destruct (Z.eq_dec v16 0) as [Hv16|Hv16].
    + (* v16 = 0 : beqz taken to 0x82484 *)
      subst v16. rewrite bv_eqb_refl. cbv iota.
      (* 0x82484 addi ; srli ; add ; lb a1 shadow(phi+17) *)
      step. step. step. ush.
      step.
      (* bnez a1 (=0) ; lbu a0=v17 ; seqz a0 ; addi a1,s8,-1 ; seqz a1 ; bne (Heq2) *)
      step. if_false. step. step. step. step. step.
      rewrite (seqz_v17 v17 Rv17), (seqz_vs8 (t_k (g_in g) j) Rtk).
      replace (0 =? 0) with true in Heq2 by reflexivity. cbv iota in Heq2.
      rewrite Heq2, bv_eqb_refl; cbn [negb]; cbv iota.
      (* 0x824ac mv a0,s7 ; 0x824b0 jal CKV ; land at 0x824b4 *)
      eapply evt_mono; [apply CALL|].
      intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & ST'). subst ms'.
      do 2 eexists. exists m'. split; [reflexivity|].
      split; [reflexivity|].
      do 14 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM | exact ST'].
    + (* v16 <> 0 : beqz not taken, fall to 0x8247c *)
      rewrite (eqb0_false v16) by lia. cbv iota.
      (* 0x8247c li a0,0 ; 0x82480 j 823f4 ; 0x824a0 addi a1,s8,-1 ; 0x824a4 seqz a1 ; 0x824a8 bne (Heq2) *)
      step. step. step. step. step.
      rewrite (seqz_vs8 (t_k (g_in g) j) Rtk).
      replace (v16 =? 0) with false in Heq2 by (symmetry; apply Z.eqb_neq; exact Hv16). cbv iota in Heq2.
      rewrite <- Heq2, bv_eqb_refl; cbn [negb]; cbv iota.
      eapply evt_mono; [apply CALL|].
      intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & ST'). subst ms'.
      do 2 eexists. exists m'. split; [reflexivity|].
      split; [reflexivity|].
      do 14 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM | exact ST'].
  - (* continuation: rebuild the exit cut Inv_A824b4_at and apply it *)
    intros R pc' mem' regs'' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E21 & E22 & E26 & E20 & E23 & E24 & E10 & E18 & MU & WM & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (OW : forall x, x < sp - 16 \/ sp <= x -> outside W x) by (subst W; outW; lia).
    assert (HroM : ro_agree rsegs mem').
    { apply (ro_agree_same rsegs mem mem' Hro). intros a Ha. apply MU. apply OW. left.
      unfold ro_addr in Ha. destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:Ef; [|discriminate].
      destruct (kb_find_segment rsegs (bv_unsigned a) 1 s Ef) as (Hs & _ & Hs2).
      pose proof (proj1 (forallb_forall _ rsegs) rsegs_low s Hs) as Hb. cbn beta in Hb. apply Z.leb_le in Hb.
      unfold HIGHMEM_BEG in *. lia. }
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (Hrtdj : rt_disjoint W).
    { assert (Hwlo2 : AC.GT <= sp - 16) by (unfold AC.GT, HIGHMEM_BEG in *; lia).
      subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN, AC.GT in *.
      cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite unsigned_lit by lia. subst W.
      cbn [outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. unfold APPMEM_END in *. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    pose proof (lw_store (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH HstoreC HwmL) as LWr2.
    pose proof (lws_ah _ _ _ _ _ LWr2) as HAH'.
    pose proof (lws_own _ _ _ _ _ LWr2) as Hownst.
    pose proof (lws_lo _ _ _ _ _ LWr2) as HSTKeq.
    pose proof (lws_hi _ _ _ _ _ LWr2) as HSTKHeq.
    assert (HWblk : forall q n x, In (q, n) (g_H g) -> q <= x < q + n -> outside W x).
    { intros q n x Hinq Hx.
      pose proof (lw_blocks (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem md q n HAH
        (in_or_app _ _ _ (or_intror Hinq))) as LWr3.
      pose proof (lwb_end _ _ _ _ _ _ LWr3) as Hqe.
      apply OW. left. unfold FN_STACK, AF.SLOT_STACK in *. lia. }
    assert (HSTKW : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { destruct (stk_split rsegs mem' (sp - FN_STACK) (sp - 16) sp ST' ltac:(lia)) as (_ & ST16).
      apply (Tac_slot.sl_win_stk B APIf ra g fr (hb1 phi (flen g j)) regs mem md mem' 16 HFRA ltac:(lia));
        [ rewrite Haspz; subst W; exact MU | exact WM | rewrite Haspz; exact ST16 ]. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs'' mem' md).
    { apply (Tac_slot.sl_win_run B APIf ra empty FF g fr (hb1 phi (flen g j)) regs regs'' mem mem' md W HFRA MU
        WM HroM Hallapp Hrtdj HAH' HSTKeq).
      - intros x Hx. apply OW. left. unfold HIGHMEM_BEG in *. lia.
      - intros x Hx. apply OW. destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
      - intros A' HA' HA'b x Hx. apply OW. right.
        assert (EA' : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in Hr9; rewrite <- HA'; exact Hr9).
          apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !unsigned_lit in E by lia. exact E. }
        subst A'. lia.
      - intros x Hx. apply OW. right. lia.
      - exact HSTKW.
      - intros HR. eapply Tac_slot.fsrec_munch_lo with (W := W);
          [exact HR | exact HAH | exact MU | |].
        + intros x Hx. apply OW. left. unfold HIGHMEM_BEG in *. lia.
        + intros x Hxa Hxf Hxs. apply OW. left. unfold FN_STACK, AF.SLOT_STACK in *. lia.
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs'' mem' md').
    { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs'' regs'' mem' md md' HFRA');
        try reflexivity; exact Hmat. }
    (* ENT: the callee wrote only its own 16 bytes inside the slot window, so no byte the entry relation
       speaks of changed; then the model step of sl_run_lib. *)
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { apply (Tac_slot.ent_store B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md W HENT HFRA MU).
      - intros x Hx.
        destruct (Z_lt_le_dec x (sp - 16)) as [Hd|Hd]; [left; apply OW; left; exact Hd|].
        destruct (Z_lt_le_dec x sp) as [Hd2|Hd2]; [right; left; lia | left; apply OW; right; exact Hd2].
      - exact HSTKeq.
      - exact HSTKHeq.
      - intros a Hia Ho. exact (proj2 (Hownst a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md').
    { exact (Tac_slot.ent_mat APIf g (hb1 phi (flen g j)) mem' md md' HENT' Hmat). }
    assert (OWA : forall off, 0 <= off -> forall x, A + off <= x -> outside W x)
      by (intros off Hoff x Hx; apply OW; right; lia).
    assert (Kq : forall off v, 0 <= off -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg; rewrite Fr9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU | rewrite length_le8; intros x Hx; apply (OWA off); lia]. }
    rewrite <- Esz in HFRA'', HENT''.
    rewrite <- SEGS. apply Hexit.
    exists phi, regs'', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA''|].
    split; [exact HENT''|].
    destruct HLK as (Hj255 & H21 & HOUR).
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { split; [exact Hphinz|]. unfold AC.a_size. rewrite Z.max_l by lia.
      exact (addressable_kept mem mem' phi (flen g j) Hadr (munch_meta W mem mem' MU Hallapp)). }
    split.
    { apply (flsi_win g j fr regs regs'' mem mem' W A HFLSI Hr9 ltac:(lia) ltac:(lia) Fr9 MU WM Hallapp).
      - intros x Hx. apply OW. right. lia.
      - intros x Hx. apply OW.
        destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
      - exact HWblk. }
    split.
    { split; [exact Hj255|]. split; [unfold rg; rewrite Hreg, E21; exact H21|].
      unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. apply OW.
      destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia. }
    split; [unfold rg; rewrite Hreg; exact E10|].
    split; [unfold rg; rewrite Hreg; exact E23|].
    split; [unfold rg; rewrite Hreg; exact E20|].
    split; [unfold rg in *; rewrite Hreg, E22; exact Hs6|].
    split; [unfold rg; rewrite Hreg; exact E24|].
    split; [exact Hphi0|].
    split; [exact Hphi50|].
    split; [exact Hbig|].
    split; [exact Rtk|].
    split.
    { eapply fl_bytes; [exact Hblk | exact MU |]. rewrite t_blk_len. intros x Hx. apply OW. left. lia. }
    split.
    { eapply fl_bytes; [exact Hrec | exact MU |]. rewrite t_g6_len. intros x Hx. apply OW. left. lia. }
    split; [apply Kq; [lia | exact Hq280]|].
    split.
    { apply Kq; [lia | exact (sl_spill_at regs mem A 136 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb136)]. }
    split.
    { apply Kq; [lia | exact (sl_spill_at regs mem A 120 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb120)]. }
    split.
    { apply Kq; [lia | exact (sl_spill_at regs mem A 176 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb176)]. }
    (* push 12: the five FLS facts and LT, which the segment does not write (the callee's 16 bytes are below sp,
       the frame and the spill area are not, and the record block ends below stklo) *)
    split; [unfold rg; rewrite Hreg, E18; exact H18|].
    split.
    { apply Kq; [lia | exact (sl_spill_at regs mem A 152 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H152)]. }
    split.
    { eapply fl_bytes; [exact Hgb | exact MU |]. rewrite t_g_len. intros x Hx. apply OW. left. lia. }
    split.
    { eapply fl_bytes; [exact Hpb | exact MU |]. intros x Hx. apply OW. left. lia. }
    split; [exact Hpl|].
    unfold LT in HLT |- *.
    eapply ifs_keep; [exact HLT | exact Hr9 | lia | lia | exact Fr9 | exact MU
                     | exact (munch_meta W mem mem' MU Hallapp) | | |].
    + intros x Hx. apply OW. destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
    + intros x Hx. apply OW. right. lia.
    + intros x Hx. apply OW. destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
Qed.

End S.
