(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/simdjson/fuzz_implementations/lib/B/Pj_ser_ckitA.v, with its module paths and module names changed; 246 of its 296 lines of code are new or changed and 682 lines of the source are left out. *)
(* Segment V01 (plain) of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (ELF 8dec0b814e6f = pinned 3776ca44d75c): the
   facts of the cut state at K13cac that V01_Inv.v's HEAD piece takes, on the normalized memory (v01_env).
   - v01_geo: the stack window [S - 65536, S) from GV (16-aligned, above the image's top SL_TOP = 0x60000 and the
     allocator's ceiling, so no image byte: Tac_b8.b8_seg_rom_hi); the four live blocks c, m, tab, mt of hb_end, each
     at 4096 or above and below the ceiling (Tac_b1.b1_hb), so below the window, pairwise apart (Tac_b1.b1_sep), and
     16-aligned and outside the reserved pages (seg_cuts.P_K13cac, P_mcore);
   - v01_base: c's and m's encodings (P_K13cac) carried to the normalized memory by ro_agree (FR's MI); the errno cell
     V01_ERRNO = errno_addr B (Tac_slot.sl_errno_val), a .bss cell of the image: writable and present in every memory
     (a computed check over the image's segments, Tac_slot.sl_wchk and Mem.mrd's seg_rom fallback); the
     stack-protector cells from the allocator's statics (Reusable/YL01.v ax_statics through Tac_b1.b1_ax: the GOT
     cell 0x21818 holds &__stack_chk_guard = 0x52e80, and the guard is a word);
   - v01_head_pre: mem_inv of the normalized memory, the stack below main's frame (Tac_slot.sl_fr_stk), main's frame
     cells with 8 = flags, 0x10 = cap and 0x30 = c (P_mcore's celz) and any word in the others, the cells of v, and
     both tables all zero (P_K13cac) and writable (b1_hb);
   - tp = 0x32c10: FR keeps tp, GV gives the entry tp = ms_tp B, frame_facts_plain gives ms_tp B (Tac_slot.ff_tp).
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 V01_Inv.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require MainBPure.
Import ListNotations.
Open Scope Z_scope.

(* ---- Build-independent: byte lists as words, cells from a present and writable region ---- *)
Module V01EnvPure.

Lemma bytes_range : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  assert (Hs : 0 <= Z.shiftl (bytes_le_to_Z bs) 8) by (apply Z.shiftl_nonneg; lia).
  split; [apply Z.lor_nonneg; lia|].
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs)))) with (2 ^ 8 * 2 ^ (8 * Z.of_nat (length bs))).
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. rewrite Nat2Z.inj_succ. unfold Z.succ. lia. }
  nia.
Qed.

Lemma bytes_roundtrip : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  pose proof (bytes_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8).
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HR.
  rewrite MState.unsigned_lit by lia. rewrite <- HL. apply bytes_roundtrip.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (bytes_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HR.
  rewrite MState.unsigned_lit by lia. rewrite <- HL. apply bytes_roundtrip.
Qed.

Section Cells.
Variable segs : list Segment.

Lemma ba_at : forall m a a' bs, a = a' -> bytes_at segs m a' bs -> bytes_at segs m a bs.
Proof. intros m a a' bs -> H. exact H. Qed.

Lemma ba_cons : forall m a k bs rest, bytes_at segs m a bs -> length bs = k ->
  bytes_at segs m (a + Z.of_nat k) rest -> bytes_at segs m a (bs ++ rest).
Proof.
  intros m a k bs rest H1 Hl H2. apply (proj2 (bytes_at_app segs m a bs rest)).
  split; [exact H1|]. rewrite Hl. exact H2.
Qed.

Lemma ba_nil : forall m a, 0 <= a <= 2 ^ 64 -> bytes_at segs m a [].
Proof. intros m a Ha. split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma wr_of_stk : forall m lo hi a n, stk segs m lo hi -> lo <= a -> a + n <= hi -> wr_at segs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hb. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma bytes_of_stk : forall m lo hi a n, stk segs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, length bs = n /\ bytes_at segs m a bs.
Proof.
  intros m lo hi a n ST H1 H2.
  destruct (stk_split segs m lo (a + Z.of_nat n) hi ST ltac:(lia)) as [ST1 _].
  destruct (stk_carve segs m lo (a + Z.of_nat n) n ST1 ltac:(lia)) as [_ (bs & [[Hwf Hb] _])].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  exists bs. split; [exact Hl|].
  replace (a + Z.of_nat n - Z.of_nat n) with a in Hb by lia. exact Hb.
Qed.

Lemma any8_of_stk : forall m lo hi a, stk segs m lo hi -> lo <= a -> a + 8 <= hi ->
  exists w, bytes_at segs m a (le8 w).
Proof.
  intros m lo hi a ST H1 H2.
  destruct (bytes_of_stk m lo hi a 8 ST H1 ltac:(change (Z.of_nat 8) with 8; lia)) as (bs & Hl & Hb).
  exists (le_bytes_to_word bs). rewrite (le8_of_bytes bs Hl). exact Hb.
Qed.

Lemma any4_of_stk : forall m lo hi a, stk segs m lo hi -> lo <= a -> a + 4 <= hi ->
  exists w, bytes_at segs m a (le4 w).
Proof.
  intros m lo hi a ST H1 H2.
  destruct (bytes_of_stk m lo hi a 4 ST H1 ltac:(change (Z.of_nat 4) with 4; lia)) as (bs & Hl & Hb).
  exists (le_bytes_to_word bs). rewrite (le4_of_bytes bs Hl). exact Hb.
Qed.

Lemma rw_cb : forall m a n bs, length bs = n -> bytes_at segs m a bs -> wr_at segs m a (Z.of_nat n) ->
  rw_cells segs m a [CB n bs].
Proof.
  intros m a n bs Hl Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite ?Nat.add_0_r. exact Hw.
Qed.

Lemma rw_c4 : forall m a w, bytes_at segs m a (le4 w) -> wr_at segs m a 4 -> rw_cells segs m a [C4 w].
Proof.
  intros m a w Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - exact Hw.
Qed.

(* Nine cells: seven 8-byte words, then two 4-byte words (64 bytes). *)
Lemma rw_frame9 : forall m A w00 w08 w10 w18 w20 w28 w30 w38 w3c,
  bytes_at segs m A (le8 w00) -> bytes_at segs m (A + 8) (le8 w08) -> bytes_at segs m (A + 16) (le8 w10) ->
  bytes_at segs m (A + 24) (le8 w18) -> bytes_at segs m (A + 32) (le8 w20) -> bytes_at segs m (A + 40) (le8 w28) ->
  bytes_at segs m (A + 48) (le8 w30) -> bytes_at segs m (A + 56) (le4 w38) -> bytes_at segs m (A + 60) (le4 w3c) ->
  wr_at segs m A 64 ->
  rw_cells segs m A [C8 w00; C8 w08; C8 w10; C8 w18; C8 w20; C8 w28; C8 w30; C4 w38; C4 w3c].
Proof.
  intros m A w00 w08 w10 w18 w20 w28 w30 w38 w3c K0 K1 K2 K3 K4 K5 K6 K7 K8 HW.
  pose proof HW as (HA0 & HA1 & _).
  split; [split|].
  - cbn [cells_wf cell_wf]. repeat split.
  - cbn [cells_bytes cbytes].
    apply (ba_cons _ _ 8); [exact K0 | apply length_le8 |]. change (Z.of_nat 8) with 8.
    apply (ba_cons _ _ 8); [exact K1 | apply length_le8 |]. change (Z.of_nat 8) with 8.
    apply (ba_cons _ _ 8); [apply (ba_at _ _ (A + 16)); [lia | exact K2] | apply length_le8 |].
    change (Z.of_nat 8) with 8.
    apply (ba_cons _ _ 8); [apply (ba_at _ _ (A + 24)); [lia | exact K3] | apply length_le8 |].
    change (Z.of_nat 8) with 8.
    apply (ba_cons _ _ 8); [apply (ba_at _ _ (A + 32)); [lia | exact K4] | apply length_le8 |].
    change (Z.of_nat 8) with 8.
    apply (ba_cons _ _ 8); [apply (ba_at _ _ (A + 40)); [lia | exact K5] | apply length_le8 |].
    change (Z.of_nat 8) with 8.
    apply (ba_cons _ _ 8); [apply (ba_at _ _ (A + 48)); [lia | exact K6] | apply length_le8 |].
    change (Z.of_nat 8) with 8.
    apply (ba_cons _ _ 4); [apply (ba_at _ _ (A + 56)); [lia | exact K7] | apply length_le4 |].
    change (Z.of_nat 4) with 4.
    apply (ba_cons _ _ 4); [apply (ba_at _ _ (A + 60)); [lia | exact K8] | apply length_le4 |].
    change (Z.of_nat 4) with 4.
    apply ba_nil. lia.
  - exact HW.
Qed.

End Cells.

End V01EnvPure.

(* ---- The errno cell: a .bss cell of the image, writable and present in every memory ---- *)
Definition v01e_chk (a : Z) : bool :=
  sl_wchk a && match mrd rsegs (fun _ => None) (wa a) with Some _ => true | None => false end.

Lemma v01e_errno_chk : forallb (fun k => v01e_chk (V01_ERRNO + Z.of_nat k)) (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma v01e_errno_stk : forall m, stk rsegs m V01_ERRNO (V01_ERRNO + 4).
Proof.
  intros m. unfold V01_ERRNO. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof v01e_errno_chk as H. rewrite forallb_forall in H.
  assert (Hin : In (Z.to_nat (a - 0x32b6c)) (seq 0 4)) by (apply in_seq; lia).
  specialize (H _ Hin). unfold V01_ERRNO in H.
  replace (0x32b6c + Z.of_nat (Z.to_nat (a - 0x32b6c))) with a in H by lia.
  unfold v01e_chk in H. apply andb_true_iff in H as [H1 H2].
  split; [exact (sl_wchk_ok m a H1)|].
  revert H2. destruct (mrd rsegs (fun _ => None) (wa a)) as [b0|] eqn:E; intros H2; [|cbn in H2; discriminate H2].
  destruct (m (wa a)) as [b|] eqn:Em.
  - exists b. unfold mrd. rewrite Em. reflexivity.
  - exists b0. unfold mrd in E |- *. rewrite Em. exact E.
Qed.

Section Env.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.

Lemma v01_env : forall g bc bm tab ntab mt nmt L A regs mem md,
  FR B APIf ra empty g (hb_end bc bm tab ntab mt nmt) L A regs mem md ->
  Permutation (blocks L A) (hb_end bc bm tab ntab mt nmt ++ blocks (g_L g) (g_A g)) ->
  P_K13cac (g_in g) (g_p g) (g_S g) bc bm tab ntab mt nmt regs mem ->
  v01_geo (g_in g) (g_S g) bc bm tab mt /\ v01_base (g_in g) bc bm (normalize rsegs mem) /\
  v01_head_pre (g_in g) (g_S g) bc tab mt (normalize rsegs mem) /\ bv_unsigned (YK11.getr regs 4) = 0x32c10.
Proof.
  intros g bc bm tab ntab mt nmt L A regs mem md HFR HP HK.
  destruct HK as (Hnt & Hnm & HMC & _ & _ & _ & _ & HZt & HZm & Ht16 & Hmt16 & HNIt & HNImt & HRC & HMCf).
  destruct HMC as (_ & _ & HCfl & HCcap & HCc & Hc16 & Hm16 & HNIc & HNIm).
  subst ntab nmt.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (_ & _ & HSKb & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _ & _ & E4 & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & _ & _ & _ & Htp & _).
  pose proof (MainBPure.mb_cap (g_in g)) as Hcap.
  pose proof alloc_ceiling_lt as HACl.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  (* the four live blocks *)
  assert (Inc : In (bc, C_SIZE) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g))))
    by (right; right; right; left; reflexivity).
  assert (Inm : In (bm, M_SIZE) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g)))) by (right; right; left; reflexivity).
  assert (Int : In (tab, TAB_N (g_in g)) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g)))) by (right; left; reflexivity).
  assert (Inmt : In (mt, MT_N (g_in g)) (hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g)))) by (left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g _ bc C_SIZE L A regs mem md HFR HP Inc) as (_ & Hc4096 & Hcc).
  destruct (b1_hb B APIf ra empty FF g _ bm M_SIZE L A regs mem md HFR HP Inm) as (_ & Hm4096 & Hmc).
  destruct (b1_hb B APIf ra empty FF g _ tab (TAB_N (g_in g)) L A regs mem md HFR HP Int) as (STt & Ht4096 & Htc).
  destruct (b1_hb B APIf ra empty FF g _ mt (MT_N (g_in g)) L A regs mem md HFR HP Inmt) as (STmt & Hmt4096 & Hmtc).
  assert (SEP : forall hb1 x hb2 y, hb_end bc bm tab (TAB_N (g_in g)) mt (MT_N (g_in g)) = hb1 ++ x :: hb2 ->
            In y hb1 -> fst x + snd x <= fst y \/ fst y + snd y <= fst x).
  { intros hb1 x hb2 y E Hy. rewrite E in HFR, HP.
    first [ apply (b1_sep B APIf ra empty g hb1 x hb2 L A regs mem md y HFR HP)
          | apply (b1_sep B APIf ra empty FF g hb1 x hb2 L A regs mem md y HFR HP) ].
    apply in_or_app. left. exact Hy. }
  pose proof (SEP [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g)); (bm, M_SIZE)] (bc, C_SIZE) [] (bm, M_SIZE) eq_refl
                ltac:(right; right; left; reflexivity)) as Dcm.
  pose proof (SEP [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g)); (bm, M_SIZE)] (bc, C_SIZE) [] (tab, TAB_N (g_in g)) eq_refl
                ltac:(right; left; reflexivity)) as Dct.
  pose proof (SEP [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g)); (bm, M_SIZE)] (bc, C_SIZE) [] (mt, MT_N (g_in g)) eq_refl
                ltac:(left; reflexivity)) as Dcmt.
  pose proof (SEP [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g))] (bm, M_SIZE) [(bc, C_SIZE)] (tab, TAB_N (g_in g)) eq_refl
                ltac:(right; left; reflexivity)) as Dmt.
  pose proof (SEP [(mt, MT_N (g_in g)); (tab, TAB_N (g_in g))] (bm, M_SIZE) [(bc, C_SIZE)] (mt, MT_N (g_in g)) eq_refl
                ltac:(left; reflexivity)) as Dmmt.
  pose proof (SEP [(mt, MT_N (g_in g))] (tab, TAB_N (g_in g)) [(bm, M_SIZE); (bc, C_SIZE)] (mt, MT_N (g_in g)) eq_refl
                ltac:(left; reflexivity)) as Dtmt.
  clear SEP. cbn [fst snd] in Dcm, Dct, Dcmt, Dmt, Dmmt, Dtmt.
  assert (HTN : TAB_N (g_in g) = 18 * (seg_cap (g_in g) + 1)) by reflexivity.
  assert (HMN : MT_N (g_in g) = 20 * (seg_cap (g_in g) + 1)) by reflexivity.
  unfold C_SIZE, M_SIZE in *.
  unfold celz, SEG_FRAME in HCfl, HCcap, HCc.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HCfl) as NFl.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HCcap) as NCap.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HCc) as NC.
  clear HCfl HCcap HCc.
  split; [|split; [|split]].
  - (* v01_geo *)
    unfold v01_geo, apart, SEG_C_SIZE, SEG_M_SIZE.
    split; [exact HS16|]. split; [lia|]. split; [exact HS47|].
    split; [intros a Ha; apply (b8_seg_rom_hi B APIf ra empty FF); lia|].
    split; [lia|]. split; [lia|]. split; [exact Hc16|]. split; [exact HNIc|].
    split; [lia|]. split; [lia|]. split; [exact Hm16|]. split; [exact HNIm|].
    split; [lia|]. split; [lia|]. split; [exact Ht16|]. split; [exact HNIt|].
    split; [lia|]. split; [lia|]. split; [exact Hmt16|]. split; [exact HNImt|].
    split; [exact Dcm|]. split; [exact Dct|]. split; [exact Dcmt|].
    split; [exact Dmt|]. split; [exact Dmmt | exact Dtmt].
  - (* v01_base *)
    unfold v01_base, rconf_at, mconf_at.
    split.
    { destruct HRC as (bs & Hb & He). exists bs. split; [exact (bytes_at_normalize rsegs mem _ _ HMI Hb) | exact He]. }
    split.
    { destruct HMCf as (bs & Hb & He). exists bs.
      split; [exact (bytes_at_normalize rsegs mem _ _ HMI Hb) | exact He]. }
    split.
    { pose proof (v01e_errno_stk (normalize rsegs mem)) as STe.
      destruct (V01EnvPure.any4_of_stk rsegs _ _ _ V01_ERRNO STe ltac:(lia) ltac:(lia)) as (ev & Bev).
      exists ev. apply (V01EnvPure.rw_c4 rsegs); [exact Bev|].
      apply (V01EnvPure.wr_of_stk rsegs _ _ _ _ _ STe); lia. }
    destruct (ax_statics (b1_ax B APIf ra empty FF) L A mem md HM) as (Hgot & (gw & Hgw & Hguard) & _).
    pose proof (sl_segs B APIf ra empty FF) as SEGS.
    pose proof (ff_guard B APIf ra empty FF) as Eg.
    pose proof (ff_got_guard B APIf ra empty FF) as Egg.
    rewrite SEGS, Eg, Egg in Hgot. rewrite SEGS, Eg in Hguard.
    unfold ssp_ok, seg_env.SA, SEG_PLAIN. cbn [sa_got_guard sa_guard].
    split.
    + apply (bytes_at_normalize rsegs mem _ _ HMI).
      apply (KindBGlue.word_mem_le8 rsegs mem 0x21818 0x52e80 Hgot); lia.
    + exists (Z_to_bv 64 gw). apply (bytes_at_normalize rsegs mem _ _ HMI).
      apply (KindBGlue.word_mem_le8 rsegs mem 0x52e80 gw Hguard); lia.
  - (* v01_head_pre *)
    unfold v01_head_pre.
    split; [exact (mem_inv_normalize rsegs mem)|].
    split; [apply (b8_stk_sub _ _ _ _ _ _ ST); lia|].
    split.
    { destruct (V01EnvPure.any8_of_stk rsegs _ _ _ (g_S g - 208) ST ltac:(lia) ltac:(lia)) as (w00 & K00).
      destruct (V01EnvPure.any8_of_stk rsegs _ _ _ (g_S g - 208 + 24) ST ltac:(lia) ltac:(lia)) as (w18 & K18).
      destruct (V01EnvPure.any8_of_stk rsegs _ _ _ (g_S g - 208 + 32) ST ltac:(lia) ltac:(lia)) as (w20 & K20).
      destruct (V01EnvPure.any8_of_stk rsegs _ _ _ (g_S g - 208 + 40) ST ltac:(lia) ltac:(lia)) as (w28 & K28).
      destruct (V01EnvPure.any4_of_stk rsegs _ _ _ (g_S g - 208 + 56) ST ltac:(lia) ltac:(lia)) as (w38 & K38).
      destruct (V01EnvPure.any4_of_stk rsegs _ _ _ (g_S g - 208 + 60) ST ltac:(lia) ltac:(lia)) as (w3c & K3c).
      exists w00, w18, w20, w28, w38, w3c. unfold v01_frame.
      apply (V01EnvPure.rw_frame9 rsegs); try assumption.
      apply (V01EnvPure.wr_of_stk rsegs _ _ _ _ _ ST); lia. }
    split.
    { destruct (sl_rw_of_stk _ _ _ (g_S g - 208 + 64) 20 ST ltac:(lia) ltac:(change (Z.of_nat 20) with 20; lia))
        as (vb & HVB).
      exists vb. exact HVB. }
    split.
    + apply (V01EnvPure.rw_cb rsegs); [apply repeat_length | exact (bytes_at_normalize rsegs mem _ _ HMI HZt) |].
      rewrite Z2Nat.id by lia.
      apply (V01EnvPure.wr_of_stk rsegs _ _ _ _ _ STt); lia.
    + apply (V01EnvPure.rw_cb rsegs); [apply repeat_length | exact (bytes_at_normalize rsegs mem _ _ HMI HZm) |].
      rewrite Z2Nat.id by lia.
      apply (V01EnvPure.wr_of_stk rsegs _ _ _ _ _ STmt); lia.
  - (* tp *)
    rewrite E4, Htp, (ff_tp B APIf ra empty FF). apply MState.unsigned_lit. lia.
Qed.

End Env.
