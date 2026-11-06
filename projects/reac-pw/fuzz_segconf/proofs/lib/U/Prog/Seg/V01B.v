(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 348 of its 410 lines of code are new or changed and 512 lines of the source are left out. *)
(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c / pinned 1696d6c34ffd): the
   frame bridge from the inner walk's interface (lib/U/Prog/Seg/V01D.v) to SegEvt.evt_V01 at the cut record CPseg.
   No machine step is taken here. From a cut state at K13e90 (FR over hb_end, the permutation, seg_cuts.P_K13e90 and
   frm_zero of fcsr) the bridge
   - builds the context X = VCtx S c m tab mt inp gp tp F fcsr (normalize rsegs mem) of the inner walk;
   - proves V01D.V01_geo X from the slot kit (Tac_slot.sl_fr_bnd, Tac_b1.b1_hb, Tac_b1.b1_sep, the frame's GV and
     ff_tp) and P_K13e90's own conjuncts; an image cell (errno, __stack_chk_guard, its GOT cell, "enp1s0") lies in a
     reserved segment of rsegs (computed), a live block in none (blk_noimg), so the two are apart (v1b_apart_resv);
   - proves V01D.V01_env X on the normalized memory (mem_inv_normalize, the slot's stack window, the allocator's
     statics YL01.ax_statics for the stack protector, FR's writable errno cell, the read-only "enp1s0" bytes, and
     P_K13e90's rconf_at / mconf_at) and the frame cells, the mvlan buffer and the two tables V01_INNER reads
     (P_mcore's cells, the stack window, P_K13e90's zero bytes and b1_hb's block writability);
   - runs V01_INNER X and weakens V01_post into seg_evt_e's postcondition: V01_W X lies inside Tac_seg.seg_We, sp,
     gp and tp are kept, and P_K141ec names only s4 = mt, s2 = tab, s3 = m and s0 = c.
   The pure part (byte lists, cells, the reserved-segment separation) is the module V01BPure, build-independent.
   Part of the proof of LLVMFuzzerTestOneInput: this file is the frame bridge of segment V01 of its UBSan walk; no
   released proof of fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss RegisterBridge Bytes Image.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require MainBPure.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c
  SegEnd SegEvt seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_seg
  SegWalkMainA V01D.
Import ListNotations.
Open Scope Z_scope.

(* ---- Build-independent facts: byte lists, cells, a reserved-segment cell apart from a block ---- *)
Module V01BPure.

Lemma v1b_le_inv : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  pose proof (bytes_le_to_Z_nonneg bs) as Nn.
  rewrite Bytes.lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - transitivity (Z_to_le_bytes (length bs) (bytes_le_to_Z bs)); [|exact IH]. f_equal.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(* Any 8 (4) bytes are the little-endian bytes of a word. *)
Lemma v1b_le8_of : forall bs, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hl. pose proof (bytes_le_to_Z_nonneg bs) as N. pose proof (bytes_le_to_Z_bound bs) as Bd.
  rewrite Hl in Bd. change (8 * Z.of_nat 8) with 64 in Bd.
  rewrite <- le8_lit by lia. rewrite <- Hl at 1. apply v1b_le_inv.
Qed.

Lemma v1b_le4_of : forall bs, length bs = 4%nat -> le4 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hl. pose proof (bytes_le_to_Z_nonneg bs) as N. pose proof (bytes_le_to_Z_bound bs) as Bd.
  rewrite Hl in Bd. change (8 * Z.of_nat 4) with 32 in Bd.
  unfold le4. rewrite unsigned_lit by lia. rewrite <- Hl at 1. apply v1b_le_inv.
Qed.

(* A writable n-byte block of unknown bytes as a word cell, or as two 4-byte blocks. *)
Lemma v1b_cb8 : forall segs m A j, rw_cells segs m A [CB 8 j] -> exists v, rw_cells segs m A [C8 v].
Proof.
  intros segs m A j [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  exists (Z_to_bv 64 (bytes_le_to_Z j)). split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes] in *. rewrite (v1b_le8_of j Hl). exact Hb.
  - exact Hw.
Qed.

Lemma v1b_cb4 : forall segs m A j, rw_cells segs m A [CB 4 j] -> exists v, rw_cells segs m A [C4 v].
Proof.
  intros segs m A j [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  exists (Z_to_bv 64 (bytes_le_to_Z j)). split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes] in *. rewrite (v1b_le4_of j Hl). exact Hb.
  - exact Hw.
Qed.

Lemma v1b_cb44 : forall segs m A j, rw_cells segs m A [CB 8 j] ->
  rw_cells segs m A [CB 4 (firstn 4 j); CB 4 (skipn 4 j)].
Proof.
  intros segs m A j [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn, Hl.
    split; [reflexivity | split; [reflexivity | exact I]].
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb. rewrite app_nil_r, firstn_skipn. exact Hb.
  - exact Hw.
Qed.

Lemma v1b_ba_eq : forall segs m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros segs m a a' bs H <-. exact H. Qed.

(* A cell list, one word at a time. *)
Lemma v1b_ca8 : forall segs m A v cs, bytes_at segs m A (le8 v) -> cells_at segs m (A + 8) cs ->
  cells_at segs m A (C8 v :: cs).
Proof.
  intros segs m A v cs H [Hwf Hb]. split.
  - cbn [cells_wf cell_wf]. split; [exact I | exact Hwf].
  - cbn [cells_bytes cbytes]. apply (proj2 (bytes_at_app segs m A (le8 v) (cells_bytes cs))).
    split; [exact H|]. rewrite length_le8. exact Hb.
Qed.

Lemma v1b_ca_nil : forall segs m A, 0 <= A <= 2 ^ 64 -> cells_at segs m A [].
Proof. intros segs m A H. split; [exact I|]. apply bytes_at_nil. exact H. Qed.

(* Cells inside a stack region are writable. *)
Lemma v1b_rw_of_stk : forall segs m lo hi A cs, Frame.stk segs m lo hi -> lo <= A ->
  A + Z.of_nat (cells_size cs) <= hi -> cells_at segs m A cs -> rw_cells segs m A cs.
Proof.
  intros segs m lo hi A cs (H1 & H2 & H) HA HB HC. split; [exact HC|].
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (A + i) ltac:(lia))).
Qed.

(* A stack word of unknown bytes. *)
Lemma v1b_junk8 : forall segs m lo hi a, Frame.stk segs m lo hi -> lo <= a -> a + 8 <= hi ->
  exists v, bytes_at segs m a (le8 v).
Proof.
  intros segs m lo hi a (H1 & H2 & H) Ha Hb.
  assert (S8 : Frame.stk segs m a (a + 8)).
  { split; [lia|]. split; [lia|]. intros x Hx. apply H. lia. }
  destruct (stk_bytes segs m a (a + 8) S8 ltac:(lia)) as (bs & Hl & Hbs).
  replace (Z.to_nat (a + 8 - a)) with 8%nat in Hl by lia.
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite (v1b_le8_of bs Hl). exact Hbs.
Qed.

(* Every byte of [a, a + k) lies in a reserved segment (a computed check). *)
Definition v1b_resv_cover (segs : list Segment) (a k : Z) : bool :=
  forallb (fun i => existsb (fun s : word * word =>
              (bv_unsigned (fst s) <=? a + Z.of_nat i) && (a + Z.of_nat i <? bv_unsigned (fst s) + bv_unsigned (snd s)))
            (segments_reserved segs))
    (seq 0 (Z.to_nat k)).

Lemma v1b_resv_cover_ok : forall segs a k, v1b_resv_cover segs a k = true -> forall x, a <= x < a + k ->
  exists s, In s (segments_reserved segs) /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  intros segs a k H x Hx. unfold v1b_resv_cover in H. rewrite forallb_forall in H.
  assert (Hi : In (Z.to_nat (x - a)) (seq 0 (Z.to_nat k))) by (apply in_seq; lia).
  specialize (H _ Hi). apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  rewrite Z2Nat.id in C1, C2 by lia. exists s. split; [exact Hs | lia].
Qed.

(* A cell that lies in the reserved segments and a block that meets none of them are apart. *)
Lemma v1b_apart_resv : forall segs a k b n, v1b_resv_cover segs a k = true -> blk_noimg segs b n -> 0 < k -> 0 < n ->
  apart a k b (b + n).
Proof.
  intros segs a k b n HC HN Hk Hn. unfold apart.
  destruct (Z_le_gt_dec (a + k) b) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (b + n) a) as [H'|H']; [right; exact H'|].
  exfalso. destruct (v1b_resv_cover_ok segs a k HC (Z.max a b) ltac:(lia)) as (s & Hs & Hr).
  apply (HN (Z.max a b - b) ltac:(lia) s Hs). replace (b + (Z.max a b - b)) with (Z.max a b) by lia. exact Hr.
Qed.

(* `not` of a word literal (P_mcore's s2 = ~m). *)
Lemma v1b_not_lit : forall z, 0 <= z < 2 ^ 64 -> bv_not (Z_to_bv 64 z) = Z_to_bv 64 (18446744073709551615 - z).
Proof.
  intros z Hz. apply bv_eq. rewrite bv_not_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite (Z.mod_small z) by lia. rewrite (Z.mod_small (18446744073709551615 - z)) by lia.
  unfold Z.lnot. replace (Z.pred (- z)) with ((18446744073709551615 - z) + (-1) * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

End V01BPure.
Import V01BPure.

(* ---- The image cells V01's interface names (computed on the UBSan image) ---- *)
Lemma v01b_cov_errno : v1b_resv_cover rsegs V01_ERRNO 4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma v01b_cov_guard : v1b_resv_cover rsegs 0x53820 8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma v01b_cov_got : v1b_resv_cover rsegs 0x221b0 8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma v01b_cov_enp : v1b_resv_cover rsegs V01_ENP 7 = true.
Proof. vm_compute. reflexivity. Qed.

(* Every byte of [a, a + k) is an image byte of a writable segment. *)
Definition v01b_rwimg (a k : Z) : bool :=
  forallb (fun i => match PropExec.seg_rom rsegs (wa (a + Z.of_nat i)) with
                    | Some _ => negb (ro_addr rsegs (wa (a + Z.of_nat i)))
                    | None => false
                    end) (seq 0 (Z.to_nat k)).

Lemma v01b_rwimg_ok : forall a k, v01b_rwimg a k = true -> forall x, a <= x < a + k ->
  ro_addr rsegs (wa x) = false /\ PropExec.seg_rom rsegs (wa x) <> None.
Proof.
  intros a k H x Hx. unfold v01b_rwimg in H. rewrite forallb_forall in H.
  assert (Hi : In (Z.to_nat (x - a)) (seq 0 (Z.to_nat k))) by (apply in_seq; lia).
  specialize (H _ Hi). rewrite Z2Nat.id in H by lia. replace (a + (x - a)) with x in H by lia.
  destruct (PropExec.seg_rom rsegs (wa x)) as [b|]; [|discriminate].
  split; [apply negb_true_iff; exact H | discriminate].
Qed.

Lemma v01b_errno_rw : v01b_rwimg V01_ERRNO 4 = true.
Proof. vm_compute. reflexivity. Qed.

(* "enp1s0" and its NUL in .rodata. *)
Lemma v01b_enp : forall m, mem_inv rsegs m -> bytes_at rsegs m V01_ENP (seg_spec.zb (SegModel.S_enp ++ [0])).
Proof.
  intros m MI.
  assert (Hl : length (seg_spec.zb (SegModel.S_enp ++ [0])) = 7%nat) by reflexivity.
  apply (ro_bytes_at rsegs m); [exact MI | unfold V01_ENP; lia | rewrite Hl; unfold V01_ENP; lia |].
  apply Image.ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Section V01B.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis INNER : forall X : vctx, V01_geo X -> V01_INNER X.

(* Two blocks of hb are apart (Tac_b1.b1_sep). *)
Lemma v01b_sep : forall g hb1 x hb2 L A regs mem md y,
  FR B APIf ra empty g (hb1 ++ x :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ x :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In y (hb1 ++ hb2 ++ blocks (g_L g) (g_A g)) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros g hb1 x hb2 L A regs mem md y H1 H2 H3.
  first [ exact (b1_sep B APIf ra empty g hb1 x hb2 L A regs mem md y H1 H2 H3)
        | exact (b1_sep B APIf ra empty FF g hb1 x hb2 L A regs mem md y H1 H2 H3) ].
Qed.

(* ---- V01_geo of the context ---- *)
Lemma v01b_geo : forall g bc bm tab mt L A regs mem md (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte),
  FR B APIf ra empty g (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))) L A regs mem md ->
  Permutation (blocks L A) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g)) ++ blocks (g_L g) (g_A g)) ->
  bc mod 16 = 0 -> bm mod 16 = 0 -> tab mod 16 = 0 -> mt mod 16 = 0 ->
  blk_noimg rsegs bc SEG_C_SIZE -> blk_noimg rsegs bm SEG_M_SIZE ->
  blk_noimg rsegs tab (TAB_N (g_in g)) -> blk_noimg rsegs mt (MT_N (g_in g)) ->
  V01_geo (VCtx (g_S g) bc bm tab mt (g_in g) (YK11.getr regs 3) (YK11.getr regs 4) F fc m0).
Proof.
  intros g bc bm tab mt L A regs mem md F fc m0 HFR HP Hc16 Hm16 Ht16 Hmt16 HNIc HNIm HNIt HNImt.
  pose proof HFR as (HGV & _ & _ & HF4 & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _ & _ & HTP & _).
  pose proof (sl_ceil (rc:=rc)) as Hceil.
  pose proof (MainBPure.mb_cap (g_in g)) as Hcap.
  assert (Inmt : In (mt, MT_N (g_in g)) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))))
    by (left; reflexivity).
  assert (Intab : In (tab, TAB_N (g_in g)) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))))
    by (right; left; reflexivity).
  assert (Inm : In (bm, M_SIZE) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))))
    by (right; right; left; reflexivity).
  assert (Inc : In (bc, C_SIZE) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))))
    by (right; right; right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g _ mt _ L A regs mem md HFR HP Inmt) as (_ & Hmt4 & Hmtc).
  destruct (b1_hb B APIf ra empty FF g _ tab _ L A regs mem md HFR HP Intab) as (_ & Ht4 & Htc).
  destruct (b1_hb B APIf ra empty FF g _ bm _ L A regs mem md HFR HP Inm) as (_ & Hm4 & Hmc).
  destruct (b1_hb B APIf ra empty FF g _ bc _ L A regs mem md HFR HP Inc) as (_ & Hc4 & Hcc).
  assert (Htn : 0 < TAB_N (g_in g)) by (unfold TAB_N, RVLAN_SIZE; lia).
  assert (Hmn : 0 < MT_N (g_in g)) by (unfold MT_N, MVLAN_SIZE; lia).
  unfold TAB_N, MT_N, RVLAN_SIZE, MVLAN_SIZE in Htc, Hmtc.
  unfold SL_TOP in Hceil. unfold SLOT_K, SLOT_STACK in HSK. unfold C_SIZE in Hcc. unfold M_SIZE in Hmc.
  unfold V01_geo, v_lo, v_ntab, v_nmt, v_cap. cbn [v_S v_c v_mm v_tab v_mt v_inp v_tp].
  unfold SEG_C_SIZE, SEG_M_SIZE, RVLAN_SIZE, MVLAN_SIZE.
  split; [exact HS16|].
  split; [lia|].
  split; [exact HS47|].
  split; [rewrite HF4, HTP, (ff_tp B APIf ra empty FF); apply unsigned_lit; lia|].
  split; [exact Hcap|].
  split; [lia|]. split; [exact Hc16|]. split; [lia|].
  split; [lia|]. split; [exact Hm16|]. split; [lia|].
  split; [lia|]. split; [exact Ht16|]. split; [lia|].
  split; [lia|]. split; [exact Hmt16|]. split; [lia|].
  (* the four blocks, pairwise *)
  split.
  { exact (v01b_sep g [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g)); (bm, M_SIZE)] (bc, C_SIZE) [] L A regs mem md
             (bm, M_SIZE) HFR HP ltac:(apply in_or_app; left; cbn [In]; auto)). }
  split.
  { exact (v01b_sep g [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g)); (bm, M_SIZE)] (bc, C_SIZE) [] L A regs mem md
             (tab, TAB_N (g_in g)) HFR HP ltac:(apply in_or_app; left; cbn [In]; auto)). }
  split.
  { exact (v01b_sep g [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g)); (bm, M_SIZE)] (bc, C_SIZE) [] L A regs mem md
             (mt, MT_N (g_in g)) HFR HP ltac:(apply in_or_app; left; cbn [In]; auto)). }
  split.
  { exact (v01b_sep g [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g))] (bm, M_SIZE) [(bc, C_SIZE)] L A regs mem md
             (tab, TAB_N (g_in g)) HFR HP ltac:(apply in_or_app; left; cbn [In]; auto)). }
  split.
  { exact (v01b_sep g [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g))] (bm, M_SIZE) [(bc, C_SIZE)] L A regs mem md
             (mt, MT_N (g_in g)) HFR HP ltac:(apply in_or_app; left; cbn [In]; auto)). }
  split.
  { exact (v01b_sep g [(mt, MT_N (g_in g))] (tab, TAB_N (g_in g)) [(bm, M_SIZE); (bc, C_SIZE)] L A regs mem md
             (mt, MT_N (g_in g)) HFR HP ltac:(apply in_or_app; left; cbn [In]; auto)). }
  (* the image cells against the blocks *)
  split; [exact (v1b_apart_resv rsegs V01_ERRNO 4 bc SEG_C_SIZE v01b_cov_errno HNIc ltac:(lia)
                   ltac:(unfold SEG_C_SIZE; lia))|].
  split; [exact (v1b_apart_resv rsegs V01_ERRNO 4 bm SEG_M_SIZE v01b_cov_errno HNIm ltac:(lia)
                   ltac:(unfold SEG_M_SIZE; lia))|].
  split; [exact (v1b_apart_resv rsegs V01_ERRNO 4 tab _ v01b_cov_errno HNIt ltac:(lia) Htn)|].
  split; [exact (v1b_apart_resv rsegs V01_ERRNO 4 mt _ v01b_cov_errno HNImt ltac:(lia) Hmn)|].
  split; [exact (v1b_apart_resv rsegs 0x53820 8 tab _ v01b_cov_guard HNIt ltac:(lia) Htn)|].
  split; [exact (v1b_apart_resv rsegs 0x53820 8 mt _ v01b_cov_guard HNImt ltac:(lia) Hmn)|].
  split; [exact (v1b_apart_resv rsegs 0x221b0 8 tab _ v01b_cov_got HNIt ltac:(lia) Htn)|].
  split; [exact (v1b_apart_resv rsegs 0x221b0 8 mt _ v01b_cov_got HNImt ltac:(lia) Hmn)|].
  split; [exact (v1b_apart_resv rsegs V01_ENP 7 tab _ v01b_cov_enp HNIt ltac:(lia) Htn)|].
  split; [exact (v1b_apart_resv rsegs V01_ENP 7 mt _ v01b_cov_enp HNImt ltac:(lia) Hmn)|].
  split; [exact HNIt | exact HNImt].
Qed.

(* ---- V01_env of the context on the normalized memory ---- *)
Lemma v01b_env : forall g hb L A regs mem md bc bm tab mt (F : bvmap 5 word) (fc : bv 32),
  FR B APIf ra empty g hb L A regs mem md ->
  rconf_at rsegs mem bc (seg_rc (SegModel.run (seg_pay (g_in g)))) ->
  mconf_at rsegs mem bm (seg_mc (SegModel.run (seg_pay (g_in g)))) ->
  V01_env (VCtx (g_S g) bc bm tab mt (g_in g) (YK11.getr regs 3) (YK11.getr regs 4) F fc (normalize rsegs mem))
    (normalize rsegs mem).
Proof.
  intros g hb L A regs mem md bc bm tab mt F fc HFR HRC HMC.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (_ & _ & _ & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _ & _ & _ & _ & _ & _ & _ & Herr & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & _).
  pose proof (sl_ceil (rc:=rc)) as Hceil.
  unfold SL_TOP in Hceil. unfold SLOT_K, SLOT_STACK in HSK, ST.
  unfold V01_env, v_lo, v_sp, v_rc, v_mc, V01_FRAME. cbn [v_S v_c v_mm v_inp].
  split; [exact (mem_inv_normalize rsegs mem)|].
  split; [apply (b8_stk_sub _ _ _ _ _ _ ST); lia|].
  split; [intros a Ha; apply (b8_seg_rom_hi B APIf ra empty FF); lia|].
  destruct (ax_statics (b1_ax B APIf ra empty FF) L A mem md HM) as (Hgot & (gv & Hgv & Hguard) & _).
  rewrite (ff_guard B APIf ra empty FF), (ff_got_guard B APIf ra empty FF), SEGS in Hgot.
  rewrite (ff_guard B APIf ra empty FF), SEGS in Hguard.
  change (sa_got_guard V01D.SA) with 0x221b0. change (sa_guard V01D.SA) with 0x53820.
  split.
  { apply (bytes_at_normalize rsegs mem _ _ HMI).
    apply (KindBGlue.word_mem_le8 rsegs mem 0x221b0 0x53820 Hgot); lia. }
  split.
  { exists (Z_to_bv 64 gv). apply (bytes_at_normalize rsegs mem _ _ HMI).
    apply (KindBGlue.word_mem_le8 rsegs mem 0x53820 gv Hguard); lia. }
  split.
  { rewrite (sl_errno_val B APIf ra empty FF) in Herr. rewrite SEGS in Herr.
    assert (STe : Frame.stk rsegs (normalize rsegs mem) V01_ERRNO (V01_ERRNO + 4)).
    { split; [unfold V01_ERRNO; lia|]. split; [unfold V01_ERRNO; lia|].
      intros a Ha. destruct (v01b_rwimg_ok _ _ v01b_errno_rw a Ha) as [Hro Hsr].
      split.
      - rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) (wa a) (mem_rel_normalize rsegs mem HMI) Hro).
        exact (Herr a ltac:(unfold V01_ERRNO in Ha; lia)).
      - unfold Mem.mrd. destruct (normalize rsegs mem (wa a)) as [b|]; [exists b; reflexivity|].
        destruct (PropExec.seg_rom rsegs (wa a)) as [b|]; [exists b; reflexivity | contradiction]. }
    destruct (sl_rw_of_stk _ _ _ V01_ERRNO 4 STe ltac:(lia) ltac:(lia)) as (j & Hj).
    exact (v1b_cb4 rsegs _ _ _ Hj). }
  split; [exact (v01b_enp _ (mem_inv_normalize rsegs mem))|].
  split.
  { destruct HRC as (bs & HB & HEc). exists bs. split; [exact (bytes_at_normalize rsegs mem _ _ HMI HB) | exact HEc]. }
  { destruct HMC as (bs & HB & HEc). exists bs. split; [exact (bytes_at_normalize rsegs mem _ _ HMI HB) | exact HEc]. }
Qed.

(* ---- The segment ---- *)
Lemma v01b_evt : evt_V01 B APIf ra empty CPseg.
Proof.
  unfold evt_V01, seg_evt_e. intros g bc bm tab ntab mt nmt L A regs mem md HFR HP HPre Hfrm.
  unfold CPseg in HPre |- *. cbn [cp_K13e90 cp_K141ec] in HPre |- *.
  unfold P_K13e90, P_mcore, rgz, celz in HPre.
  destruct HPre as (Entab & Enmt & (H18 & H27 & K08 & K10 & K20 & K48 & K50 & Hc16 & Hm16 & HNIc & HNIm) &
                    H10 & H9 & H20 & H8 & HZt & HZm & Ht16 & Hmt16 & HNIt & HNImt & HRC & HMC).
  subst ntab nmt.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & _ & _ & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & _).
  pose proof (sl_ceil (rc:=rc)) as Hceil.
  pose proof (MainBPure.mb_cap (g_in g)) as Hcap.
  assert (Inmt : In (mt, MT_N (g_in g)) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))))
    by (left; reflexivity).
  assert (Intab : In (tab, TAB_N (g_in g)) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))))
    by (right; left; reflexivity).
  assert (Inm : In (bm, M_SIZE) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))))
    by (right; right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g _ mt _ L A regs mem md HFR HP Inmt) as (STmt & _ & _).
  destruct (b1_hb B APIf ra empty FF g _ tab _ L A regs mem md HFR HP Intab) as (STt & _ & _).
  destruct (b1_hb B APIf ra empty FF g _ bm _ L A regs mem md HFR HP Inm) as (_ & Hm4 & Hmc).
  assert (Htn : 0 <= TAB_N (g_in g)) by (unfold TAB_N, RVLAN_SIZE; lia).
  assert (Hmn : 0 <= MT_N (g_in g)) by (unfold MT_N, MVLAN_SIZE; lia).
  unfold SL_TOP in Hceil. unfold SLOT_K, SLOT_STACK in HSK, ST. unfold M_SIZE in Hmc.
  (* the context, its numbers and its environment *)
  pose proof (v01b_geo g bc bm tab mt L A regs mem md (@fp_regs fx) (@fp_csr fx) (normalize rsegs mem) HFR HP
                Hc16 Hm16 Ht16 Hmt16 HNIc HNIm HNIt HNImt) as HG.
  pose proof (INNER _ HG) as HIN.
  pose proof (v01b_env g _ L A regs mem md bc bm tab mt (@fp_regs fx) (@fp_csr fx) HFR HRC HMC) as HE.
  (* the frame cells [sp, sp + 0x58), the int cell, the mvlan buffer and the two tables *)
  destruct (v1b_junk8 rsegs _ _ _ (g_S g - 240) ST ltac:(lia) ltac:(lia)) as (j0 & J0).
  destruct (v1b_junk8 rsegs _ _ _ (g_S g - 240 + 0x18) ST ltac:(lia) ltac:(lia)) as (j18 & J18).
  destruct (v1b_junk8 rsegs _ _ _ (g_S g - 240 + 0x28) ST ltac:(lia) ltac:(lia)) as (j28 & J28).
  destruct (v1b_junk8 rsegs _ _ _ (g_S g - 240 + 0x30) ST ltac:(lia) ltac:(lia)) as (j30 & J30).
  destruct (v1b_junk8 rsegs _ _ _ (g_S g - 240 + 0x38) ST ltac:(lia) ltac:(lia)) as (j38 & J38).
  destruct (v1b_junk8 rsegs _ _ _ (g_S g - 240 + 0x40) ST ltac:(lia) ltac:(lia)) as (j40 & J40).
  pose proof (bytes_at_normalize rsegs mem _ _ HMI K08) as N08.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI K10) as N10.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI K20) as N20.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI K48) as N48.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI K50) as N50.
  unfold SEG_FRAME in N08, N10, N20, N48, N50.
  assert (HCF : rw_cells rsegs (normalize rsegs mem) (g_S g - 240)
     [C8 j0; C8 (Z_to_bv 64 (seg_flags (g_in g))); C8 (Z_to_bv 64 (seg_cap (g_in g))); C8 j18;
      C8 (Z_to_bv 64 (seg_cap (g_in g))); C8 j28; C8 j30; C8 j38; C8 j40; C8 (Z_to_bv 64 bc);
      C8 (Z_to_bv 64 bm)]).
  { apply (v1b_rw_of_stk rsegs _ _ _ _ _ ST); [lia | cbn [cells_size csize]; lia |].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ J0); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ N08); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ N10); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ J18); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ N20); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ J28); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ J30); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ J38); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ J40); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ N48); lia|].
    apply v1b_ca8; [apply (v1b_ba_eq _ _ _ _ _ N50); lia|].
    apply v1b_ca_nil. lia. }
  destruct (sl_rw_of_stk _ _ _ (g_S g - 240 + 0x58) 8 ST ltac:(lia) ltac:(lia)) as (j5 & J5).
  pose proof (v1b_cb44 rsegs _ _ _ J5) as J5'.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 240 + 0x60) 20 ST ltac:(lia) ltac:(lia)) as (jb & JB).
  destruct (sl_rw_of_stk _ _ _ tab (Z.to_nat (TAB_N (g_in g))) STt ltac:(lia) ltac:(lia)) as (ft & FT).
  destruct (sl_rw_of_stk _ _ _ mt (Z.to_nat (MT_N (g_in g))) STmt ltac:(lia) ltac:(lia)) as (fm & FM).
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HZt) as NZt.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HZm) as NZm.
  (* the entry registers: mkR_of regs with P_K13e90's values *)
  rewrite sl_mkR_of.
  rewrite Hsp, H8, H9, H10, H20, H27, H18, (v1b_not_lit bm) by lia.
  eapply evt_mono.
  { exact (HIN (normalize rsegs mem) (YK11.getr regs 1) (YK11.getr regs 5) (YK11.getr regs 6) (YK11.getr regs 7)
            (YK11.getr regs 11) (YK11.getr regs 12) (YK11.getr regs 13) (YK11.getr regs 14) (YK11.getr regs 15)
            (YK11.getr regs 16) (YK11.getr regs 17) (YK11.getr regs 19) (YK11.getr regs 21) (YK11.getr regs 22)
            (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 28)
            (YK11.getr regs 29) (YK11.getr regs 30) (YK11.getr regs 31)
            j0 (Z_to_bv 64 (seg_flags (g_in g))) j18 (Z_to_bv 64 (seg_cap (g_in g))) j28 j30 j38 j40 (skipn 4 j5)
            HE (munch_refl _ _) (wmono_refl rsegs _) HCF eq_refl eq_refl
            (ex_intro _ (firstn 4 j5) J5') (ex_intro _ jb JB) NZt NZm (ex_intro _ ft FT) (ex_intro _ fm FM)). }
  (* V01_post -> seg_evt_e's postcondition *)
  intros ms (x1' & x5' & x6' & x7' & x9' & x10' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x21' & x22' &
             x23' & x24' & x25' & x26' & x27' & x28' & x29' & x30' & x31' & m' & -> & MU & WM & _).
  do 4 eexists. split; [reflexivity|].
  split; [exact Hfrm|].
  split.
  { refine (munch_weaken _ _ _ _ _ MU). intros x Hx. unfold seg_We, seg_W in Hx.
    cbn [map fst snd Frame.outside] in Hx. destruct Hx as (O1 & O2 & _ & O4 & O5 & _).
    unfold V01_W, v_lo, v_ntab, v_nmt, v_cap. cbn [Frame.outside v_S v_tab v_mt v_inp].
    unfold ERRNO_CELL in O1. unfold SLOT_K, SLOT_STACK in O2. unfold TAB_N, RVLAN_SIZE in O5.
    unfold MT_N, MVLAN_SIZE in O4. unfold V01_ERRNO, RVLAN_SIZE, MVLAN_SIZE.
    split; [clear - O2; lia|]. split; [clear - O5; lia|]. split; [clear - O4; lia|].
    split; [clear - O1; lia | exact I]. }
  split; [exact WM|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros regs' m0 Hx _. unfold P_K141ec, rgz. rewrite !(sl_getr_eqv _ _ _ Hx).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity | reflexivity].
Qed.

End V01B.

Theorem v01_evt_of_inner :
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
         (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
    frame_facts_ubsan B APIf LS SH SK ra empty ->
    (forall X : V01D.vctx, V01D.V01_geo X -> V01D.V01_INNER X) ->
    SegEvt.evt_V01 (fx:=fx) (rc:=rc) B APIf ra empty SegWalkMainA.CPseg.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF INNER.
  exact (v01b_evt (fx:=fx) (rc:=rc) B APIf ra empty FF INNER).
Qed.
