(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 228 of its 263 lines of code are new or changed and 539 lines of the source are left out. *)
(* Segment M01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): K138a4 -> K138e8 at turn 0,
   [0x138a4, 0x138e8), as SegEvt.evt_M01 at CPseg
   (Prog/Seg/SegWalkMainA.v) and its lift SegEnd.seg_M01_stmt CPseg reac_segconf_init_contract.
   The run on the normalized memory: `beqz s8` and `beqz a0` not taken (c and m are live blocks: 4096 <= c, m by
   Tac_b1.b1_hb), s0 = m, the cap stored at 0x18(sp) and (cap & 0xff = cap, cap < 40) at 0x10(sp), s10 = m + 0x2000,
   `jal reac_segconf_init` with a0 = c (reac_segconf_init_contract, a Section hypothesis, run with Exec.evt_cut as
   reac-pw/fuzz_role's Prog/Seg/M01.v runs role_build_contract: its premises are c's 16616 cells (the block is
   writable, Tac_slot.sl_rw_of_stk), the stack [S - 65536, S - 208) (Tac_slot.sl_fr_stk), c below it, mem_inv of
   the normalized memory; its post writes [c, c + 16616) and leaves rconf_at c rconf0), then s11 = 0, m + 0x10 at
   0x20(sp), the label format 0x1093b at 0x28(sp), s4 = 1 and c at 0x30(sp). The run writes [sp + 16, sp + 56) and
   c, inside Tac_seg.seg_W g [(c, 16616)]; it touches no FP state (fcsr kept, so frm = 0 from seg_evt's premise).
   At K138e8 with f = 0: nfiles = 1 + b2 mod 4 > 0 (SegModel.decode), seg_run inp 0 = (rconf0, mconf0, true), so
   s4 = 1, c holds rconf0 (init's post) and m still holds its 9236 zero bytes (K138a4, outside the write set), which
   encode mconf0 (seg_spec.mconf_enc_zero); the flags cell 8(sp) is kept the same way.
   Part of the proof of LLVMFuzzerTestOneInput: this file is segment M01 of its walk; no released proof exists;
   written new in the style of reac-pw/fuzz_role's Prog/Seg/M01.v and E01.v. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec reac_segconf_init_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c
  SegEnd SegEvt seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_seg
  SegWalkMainA.
Import ListNotations.
Open Scope Z_scope.

(* ---- The payload: at least one file, cap below 40 ---- *)
Lemma m01_dec_files_len : forall k l, length (SegModel.dec_files k l) = k.
Proof.
  induction k as [|k IH]; intros l; [reflexivity|].
  cbn [SegModel.dec_files].
  destruct (SegModel.fuzz_u8 l) as [lb i1]. destruct (SegModel.fuzz_u16 i1) as [len i2].
  destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [length]. rewrite IH. reflexivity.
Qed.

Lemma m01_nfiles_pos : forall inp, 0 < seg_nfiles inp.
Proof.
  intros inp. unfold seg_nfiles, seg_files, seg_pay, SegModel.decode.
  destruct (SegModel.fuzz_u8 (seg_in inp)) as [b0 i1]. destruct (SegModel.fuzz_u8 i1) as [fl i2].
  destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [SegModel.p_files]. rewrite m01_dec_files_len.
  pose proof (Z.mod_pos_bound b2 4 ltac:(lia)). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma m01_cap_rng : forall inp, 0 <= seg_cap inp < 40.
Proof.
  intros inp. unfold seg_cap, seg_pay, SegModel.decode.
  destruct (SegModel.fuzz_u8 (seg_in inp)) as [b0 i1]. destruct (SegModel.fuzz_u8 i1) as [fl i2].
  destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.

(* ---- Words and bytes ---- *)
Lemma m01_weq_l : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

(* 0x138b4 `andi a0,s1,0xff` on the cap (cap < 256). *)
Lemma m01_andi : forall cap, 0 <= cap < 256 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 cap)) 255) = Z_to_bv 64 cap.
Proof.
  intros cap H. rewrite unsigned_lit by lia. f_equal.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

Ltac m01_weq :=
  first [ reflexivity
        | apply m01_andi; lia
        | apply m01_weq_l; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Lemma m01_ba_eq : forall m a a' bs, bytes_at rsegs m a bs -> a = a' -> bytes_at rsegs m a' bs.
Proof. intros m a a' bs H <-. exact H. Qed.

(* The five frame cells [sp + 16, sp + 56) the run leaves, one 8-byte word each. *)
Lemma m01_cells5 : forall m A v1 v2 v3 v4 v5,
  bytes_at rsegs m A (cells_bytes [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5]) ->
  bytes_at rsegs m A (le8 v1) /\ bytes_at rsegs m (A + 8) (le8 v2) /\ bytes_at rsegs m (A + 16) (le8 v3) /\
  bytes_at rsegs m (A + 24) (le8 v4) /\ bytes_at rsegs m (A + 32) (le8 v5).
Proof.
  intros m A v1 v2 v3 v4 v5 H. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
  apply bytes_at_app in H as [H1 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H2 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H3 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H4 H5]. rewrite length_le8 in H5.
  split; [exact H1|].
  split; [apply (m01_ba_eq _ _ _ _ H2); lia|].
  split; [apply (m01_ba_eq _ _ _ _ H3); lia|].
  split; [apply (m01_ba_eq _ _ _ _ H4); lia|].
  apply (m01_ba_eq _ _ _ _ H5); lia.
Qed.

(* ---- The run: K138a4 (0x138a4) to K138e8 (0x138e8) ---- *)
Definition m01_post (sp gp tp s1 s2 s3 s5 s6 s7 s9 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (c mm cap : Z) (ms' : machine_state) : Prop :=
  exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s4' s8' s10' s11' t3' t4' t5' t6' : word)
         (w10 w20 w28 : word) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4' s5 s6 s7 s8' s9 s10' s11'
                  t3' t4' t5' t6') F (Z_to_bv 64 0x138e8) fc None m' (seg_rom rsegs) /\
    rw_cells rsegs m' (bv_unsigned sp + 16) [C8 w10; C8 s1; C8 w20; C8 w28; C8 s8'] /\
    Frame.munch [(bv_unsigned sp + 16, bv_unsigned sp + 56); (c, c + SEG_C_SIZE)] m m' /\
    Frame.wmono rsegs m m' /\
    rconf_at rsegs m' c SegModel.rconf0 /\
    s0' = Z_to_bv 64 mm /\ s4' = Z_to_bv 64 1 /\ s8' = Z_to_bv 64 c /\ s10' = Z_to_bv 64 (mm + 8192) /\
    s11' = Z_to_bv 64 0 /\ w10 = Z_to_bv 64 cap /\ w20 = Z_to_bv 64 (mm + 16) /\ w28 = Z_to_bv 64 LABEL_FMT.

Lemma m01_run : reac_segconf_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo c mm cap : Z) (jc jf : list byte),
    s8 = Z_to_bv 64 c -> a0 = Z_to_bv 64 mm -> s1 = Z_to_bv 64 cap -> s10 = Z_to_bv 64 8192 ->
    4096 <= c -> c mod 16 = 0 -> c + SEG_C_SIZE <= lo -> 4096 <= mm < 2 ^ 62 -> 0 <= cap < 256 ->
    rw_cells rsegs m c [CB (Z.to_nat SEG_C_SIZE) jc] ->
    rw_cells rsegs m (bv_unsigned sp + 16) [CB 40 jf] ->
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    bv_unsigned sp + 56 <= 2 ^ 64 ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs (m01_post sp gp tp s1 s2 s3 s5 s6 s7 s9 F fc m c mm cap)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138a4) fc None m (seg_rom rsegs)).
Proof.
  intros INIT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo c mm cap jc jf Ec Em Ecap E10 Hc Hc16 Hap Hm Hcap HRC HRF ST Hlosp Hsp16 Hsp56 HROM HMI.
  subst s8 a0 s1 s10.
  assert (Hcs : SEG_C_SIZE = 16616) by reflexivity.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (munch_refl [(bv_unsigned sp + 16, bv_unsigned sp + 56); (c, c + SEG_C_SIZE)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x138a4 beqz s8 (c <> 0); 0x138a8 mv s0,a0; 0x138ac beqz a0 (m <> 0) *)
  step. if_false_by (b1_beq0 c ltac:(lia)).
  step.
  step. if_false_by (b1_beq0 mm ltac:(lia)).
  (* 0x138b0 sd s1,0x18(sp); 0x138b4 andi a0,s1,0xff; 0x138b8 sd a0,0x10(sp); 0x138bc add s10,s0,s10;
     0x138c0 mv a0,s8; 0x138c4 jal reac_segconf_init *)
  do 6 step.
  eapply evt_cut.
  { eapply INIT with (lo := lo).
    unfold reac_segconf_init_pre, stack_ok, apart. rewrite (unsigned_lit c) by lia.
    split; [lia|]. split; [exact Hc16|]. split; [exists jc; exact HRC|].
    split; [split; [exact ST | split; [lia | split; [exact Hsp16 | exact HROM]]]|].
    split; [left; lia | exact HMI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & -> &
              MU2 & WM2 & MI2 & ST2 & HZ & HRC2).
  rewrite (unsigned_lit c) in MU2, HZ, HRC2 by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  assert (Hsub : sub_fp [(c, c + SEG_C_SIZE)]
                   [(bv_unsigned sp + 16, bv_unsigned sp + 56); (c, c + SEG_C_SIZE)]).
  { intros x Hx. cbn [Frame.outside] in *. tauto. }
  pose proof (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ Hsub MU2)) as MU3.
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
  match goal with
  | H : rw_cells rsegs _ (bv_unsigned sp + 16) _ |- _ =>
      apply (rw_cells_transport rsegs [(c, c + SEG_C_SIZE)] _ m5) in H;
      [| exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes; lia]
  end.
  clear MU WM MU2 WM2 Hsub HZ.
  destruct HRC2 as (bsr & HBR & HENC).
  pose proof (proj1 HENC) as Hlr.
  (* 0x138c8 mv s11,zero; 0x138cc addi a0,s0,0x10; 0x138d0 sd a0,0x20(sp); 0x138d4 auipc; 0x138d8 addi (the label
     format); 0x138dc sd a0,0x28(sp); 0x138e0 li s4,1; 0x138e4 sd s8,0x30(sp) *)
  do 8 step.
  apply evt_done. unfold m01_post.
  do 25 eexists.
  split; [reflexivity|].
  split; [eassumption|].
  split; [exact MU3|].
  split; [exact WM3|].
  split; [exists bsr; split; assumption|].
  split; [m01_weq|]. split; [m01_weq|]. split; [m01_weq|]. split; [m01_weq|].
  split; [m01_weq|]. split; [m01_weq|]. split; [m01_weq | m01_weq].
Qed.

(* ---- The segment ---- *)
Section M01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis INIT : reac_segconf_init_contract.

Lemma m01_evt : evt_M01 B APIf ra empty CPseg.
Proof.
  unfold evt_M01, seg_evt. intros g bc bm L A regs mem md HFR HP HPre Hfrm.
  unfold CPseg in HPre |- *. cbn [cp_K138a4 cp_K138e8] in HPre |- *.
  destruct HPre as (H10 & H24 & H9 & H18 & H19 & H21 & H26 & HC8 & _ & HZm & Hc16 & Hm16 & HNIc & HNIm).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & _).
  assert (Hinc : In (bc, C_SIZE) (hb_cm bc bm)) by (right; left; reflexivity).
  assert (Hinm : In (bm, M_SIZE) (hb_cm bc bm)) by (left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g (hb_cm bc bm) bc C_SIZE L A regs mem md HFR HP Hinc)
    as (STc & Hc4096 & Hcc).
  destruct (b1_hb B APIf ra empty FF g (hb_cm bc bm) bm M_SIZE L A regs mem md HFR HP Hinm)
    as (_ & Hm4096 & Hmc).
  assert (HD : bm + M_SIZE <= bc \/ bc + C_SIZE <= bm).
  { assert (Hy : In (bc, C_SIZE) ([] ++ [(bc, C_SIZE)] ++ blocks (g_L g) (g_A g))) by (cbn; left; reflexivity).
    first [ pose proof (b1_sep B APIf ra empty g [] (bm, M_SIZE) [(bc, C_SIZE)] L A regs mem md (bc, C_SIZE)
                          HFR HP Hy) as HD0
          | pose proof (b1_sep B APIf ra empty FF g [] (bm, M_SIZE) [(bc, C_SIZE)] L A regs mem md (bc, C_SIZE)
                          HFR HP Hy) as HD0 ].
    cbn [fst snd] in HD0. exact HD0. }
  pose proof alloc_ceiling_lt as HACl.
  pose proof (m01_cap_rng (g_in g)) as Hcap.
  pose proof (m01_nfiles_pos (g_in g)) as Hnf.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 208).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Hcs : SEG_C_SIZE = 16616) by reflexivity.
  assert (Hms : SEG_M_SIZE = 9236) by reflexivity.
  unfold C_SIZE, M_SIZE in *.
  (* c's cells and the frame cells [sp + 16, sp + 56) on the normalized memory *)
  destruct (sl_rw_of_stk _ _ _ bc (Z.to_nat SEG_C_SIZE) STc ltac:(lia) ltac:(rewrite Hcs; lia)) as (jc & HRC).
  assert (Hf1 : g_S g - 65536 <= bv_unsigned (YK11.getr regs 2) + 16) by lia.
  assert (Hf2 : bv_unsigned (YK11.getr regs 2) + 16 + Z.of_nat 40 <= g_S g) by (rewrite Hspu; lia).
  destruct (sl_rw_of_stk _ _ _ (bv_unsigned (YK11.getr regs 2) + 16) 40 ST Hf1 Hf2) as (jf & HRF).
  rewrite sl_mkR_of.
  eapply evt_mono.
  { apply (m01_run INIT) with (lo := g_S g - 65536) (c := bc) (mm := bm) (cap := seg_cap (g_in g))
                              (jc := jc) (jf := jf).
    - exact H24.
    - exact H10.
    - exact H9.
    - exact H26.
    - lia.
    - exact Hc16.
    - lia.
    - lia.
    - lia.
    - exact HRC.
    - exact HRF.
    - rewrite Hspu. apply (b8_stk_sub _ _ _ _ _ _ ST); lia.
    - lia.
    - rewrite Hspu. exact Hsp16.
    - lia.
    - rewrite Hspu. intros a Ha. apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    - exact (mem_inv_normalize rsegs mem). }
  intros ms (ra' & t0' & t1' & t2' & s0' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & s8' & s10' & s11' &
             t3' & t4' & t5' & t6' & w10 & w20 & w28 & m' & -> & HCF & MU & WM & HRCF &
             E8 & E20 & E24 & E26 & E27 & Ew10 & Ew20 & Ew28).
  do 4 eexists. split; [reflexivity|].
  split; [exact Hfrm|].
  split.
  { apply (munch_weaken [(bv_unsigned (YK11.getr regs 2) + 16, bv_unsigned (YK11.getr regs 2) + 56);
                         (bc, bc + SEG_C_SIZE)]); [|exact MU].
    intros x Hx. unfold seg_W in Hx. cbn [map fst snd Frame.outside] in Hx |- *.
    destruct Hx as (O1 & _ & O3 & _). unfold SLOT_K, SLOT_STACK in O1. rewrite Hspu.
    split; [lia|]. split; [lia | exact I]. }
  split; [exact WM|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros regs' m0 Hx Hrel.
  pose proof (sl_cells_bytes _ _ _ HCF) as HCB.
  pose proof (b1_out _ m0 _ _ Hrel HCB) as HCB0.
  destruct (m01_cells5 _ _ _ _ _ _ _ HCB0) as (K10 & K18 & K20 & K28 & K30).
  rewrite Hspu in K10, K18, K20, K28, K30.
  rewrite Ew10 in K10. rewrite H9 in K18. rewrite Ew20 in K20. rewrite Ew28 in K28. rewrite E24 in K30.
  destruct HRCF as (bsr & HBR & HENC).
  unfold P_K138e8, P_lcore, P_mcore, rgz, celz, SEG_FRAME.
  rewrite !(sl_getr_eqv _ _ _ Hx).
  split; [exact Hnf|].
  split.
  { split.
    { split; [exact E8|].
      split; [exact E26|].
      split.
      { apply (b1_keep _ mem _ m0 _ _ HMI MU Hrel); [|exact HC8].
        cbn [disjoint_from]. rewrite length_le8, Hspu. split; [lia | split; [lia | exact I]]. }
      split; [apply (m01_ba_eq _ _ _ _ K10); lia|].
      split; [apply (m01_ba_eq _ _ _ _ K30); lia|].
      split; [exact Hc16|]. split; [exact Hm16|]. split; [exact HNIc | exact HNIm]. }
    split; [exact H18|].
    split; [apply (m01_ba_eq _ _ _ _ K18); lia|].
    split; [apply (m01_ba_eq _ _ _ _ K20); lia | apply (m01_ba_eq _ _ _ _ K28); lia]. }
  split; [exact E27|].
  split; [exact H19|]. split; [exact H21|]. split; [exact E20|].
  split.
  - exists bsr. split; [exact (b1_out _ m0 _ _ Hrel HBR) | exact HENC].
  - exists (repeat ZERO (Z.to_nat SEG_M_SIZE)). split; [|exact mconf_enc_zero].
    apply (b1_keep _ mem _ m0 _ _ HMI MU Hrel); [|exact HZm].
    cbn [disjoint_from]. rewrite repeat_length, Z2Nat.id by (rewrite Hms; lia). rewrite Hspu.
    split; [lia | split; [lia | exact I]].
Qed.

End M01.

Theorem evt_M01_holds : forall fx rc B APIf LS SH SK ra empty, frame_facts_plain B APIf LS SH SK ra empty ->
  reac_segconf_init_contract -> evt_M01 (fx:=fx) (rc:=rc) B APIf ra empty CPseg.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF INIT.
  exact (m01_evt (fx:=fx) (rc:=rc) B APIf ra empty FF INIT).
Qed.

Theorem seg_M01_holds : seg_M01_stmt CPseg reac_segconf_init_contract.
Proof. apply seg_M01_of_evt. exact evt_M01_holds. Qed.
