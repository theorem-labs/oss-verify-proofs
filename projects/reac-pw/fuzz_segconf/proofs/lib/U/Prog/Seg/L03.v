(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 233 of its 281 lines of code are new or changed and 526 lines of the source are left out. *)
(* Segment L03 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c): [0x13c34, 0x13c38], the end
   of file turn f. K13c34 f -> K139e4 (S f) or K13c3c (U/Prog/LLVMFuzzerTestOneInput_c.v's S_L03 at the
   cut record CPseg, U/Prog/Seg/SegWalkMainA.v). The twin of Prog/Seg/L03.v.
   Part of the proof of LLVMFuzzerTestOneInput (its segment L03); no released proof of fuzz_segconf's
   LLVMFuzzerTestOneInput exists; written new in the style of reac-pw/fuzz_role's U/Prog/Seg/X01.v (commit
   cb8205fb6109).
   The cut is at its own FP state (Tac_b8.b8_cut_open): every step below runs at it. 0x13c34 `jal free` (ra 0x13c38;
   free at 0x173d8 = frame_facts_ubsan's ms_free; a0 = text from P_K13c34) through Tac_b8.b8_free_call with hb1 = [],
   the text block (t, nt) at the head and hb2 = [m; c]: its continuation gives FR with hb = [m; c], the callee-saved
   registers, the frame's bytes from sp up (the cells 8 .. 0x50) and the bytes of m and c. Then 0x13c38
   `bne s0,s10,-0x254` with s0 = f + 1 and s10 = nfiles (P_K13c34, kept through free): taken (f + 1 <> nfiles) to
   0x139e4, where the turn after f is the drop-in step, seg_after = seg_run (S f) (l03_after_next), and S f < 4 as
   nfiles = 1 + b2 mod 4 <= 4 (l03_nfiles); not taken (f + 1 = nfiles) to 0x13c3c, where the last turn ends
   SegModel.run of the payload (l03_after_last: run_files of the files is run_files of the files after k turns from
   seg_run k, for k < nfiles). Each cut is closed at the cut's FP state (CUTST). No other call, no UBSan check. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c SegEnd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_slot Tac_b8 SegWalkMainA.
Import ListNotations.
Open Scope Z_scope.

(* ---- The payload: the number of files, the turn after f, the loop's exit ---- *)
Lemma l03_dec_files_len : forall k l, length (dec_files k l) = k.
Proof.
  induction k as [|k IH]; intros l; [reflexivity|]. cbn [dec_files].
  destruct (fuzz_u8 l) as [lb i1]; cbv beta iota.
  destruct (fuzz_u16 i1) as [len i2]; cbv beta iota.
  destruct (fuzz_take i2 len) as [q i3]; cbv beta iota.
  cbn [length]. rewrite IH. reflexivity.
Qed.

(* decode makes 1 + b2 mod 4 file records (SegModel.decode). *)
Lemma l03_nfiles : forall inp, 1 <= seg_nfiles inp <= 4.
Proof.
  intros inp. unfold seg_nfiles, seg_files, seg_pay, decode.
  destruct (fuzz_u8 (seg_in inp)) as [b0 i1]; cbv beta iota.
  destruct (fuzz_u8 i1) as [flags i2]; cbv beta iota.
  destruct (fuzz_u8 i2) as [b2 i3]; cbv beta iota.
  cbn [p_files]. rewrite l03_dec_files_len.
  pose proof (Z.mod_pos_bound b2 4 ltac:(lia)). lia.
Qed.

(* A turn that is not the last is the drop-in step of seg_run. *)
Lemma l03_after_next : forall inp f, Z.of_nat (S f) <> seg_nfiles inp -> seg_after inp f = seg_run inp (S f).
Proof. intros inp f H. unfold seg_after. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma l03_skipn_nth : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hk. lia.
Qed.

(* The run of the payload is the run of the files after k turns, from the state after k drop-in turns. *)
Lemma l03_run_skip : forall inp k, (k < length (seg_files inp))%nat ->
  SegModel.run (seg_pay inp) = run_files (skipn k (seg_files inp))
    (seg_rc (seg_run inp k)) (seg_mc (seg_run inp k)) (seg_ret (seg_run inp k)).
Proof.
  intros inp k. induction k as [|k IH]; intros Hk; [reflexivity|].
  rewrite IH by lia.
  rewrite (l03_skipn_nth (seg_files inp) k (SegModel.File 0 [])) by lia.
  assert (Hne : skipn (S k) (seg_files inp) <> []).
  { intros E. pose proof (f_equal (@length SegModel.file) E) as E'. rewrite length_skipn in E'. cbn [length] in E'. lia. }
  destruct (skipn (S k) (seg_files inp)) as [|y r] eqn:Es; [congruence|].
  cbn [seg_run]. unfold seg_turn_step, seg_txt, seg_label, seg_lb, seg_file.
  destruct (seg_run inp k) as [[c0 m0] r0].
  cbn [seg_rc seg_mc seg_ret fst snd run_files].
  destruct (r_parse_file c0 _ _) as [c1 n]. reflexivity.
Qed.

(* The last turn ends the run of the payload. *)
Lemma l03_after_last : forall inp f, Z.of_nat (S f) = seg_nfiles inp -> seg_after inp f = SegModel.run (seg_pay inp).
Proof.
  intros inp f H.
  assert (Hl : length (seg_files inp) = S f) by (unfold seg_nfiles in H; lia).
  rewrite (l03_run_skip inp f) by lia.
  rewrite (l03_skipn_nth (seg_files inp) f (SegModel.File 0 [])) by lia.
  replace (skipn (S f) (seg_files inp)) with (@nil SegModel.file) by (symmetry; apply skipn_all2; lia).
  unfold seg_after. rewrite H, Z.eqb_refl.
  unfold seg_turn_step, seg_txt, seg_file.
  destruct (seg_run inp f) as [[c0 m0] r0].
  cbn [seg_rc seg_mc seg_ret fst snd run_files].
  reflexivity.
Qed.

(* ---- Registers and bytes across the free ---- *)
Lemma l03_cs : forall r, callee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
  r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27.
Proof. intros r Hr. unfold callee_saved in Hr. lia. Qed.

Ltac l03_rgz HR H r :=
  try unfold rgz; etransitivity; [exact (HR r ltac:(unfold callee_saved; lia))|]; exact H.

Lemma l03_celz : forall mem mem' Sp off v, 0 <= off -> off + 8 <= SEG_FRAME -> celz mem Sp off v ->
  (forall a, Sp - SEG_FRAME <= a < Sp -> mbyte rsegs mem' a = mbyte rsegs mem a) -> celz mem' Sp off v.
Proof.
  intros mem mem' Sp off v H0 H1 HC K. unfold celz, SEG_FRAME in *. apply (b8_ba_mbyte mem); [exact HC|].
  intros i Hi. rewrite length_le8 in Hi. apply K. lia.
Qed.

Lemma l03_rconf_keep : forall mem mem' c rc, rconf_at rsegs mem c rc ->
  (forall i, 0 <= i < SEG_C_SIZE -> mbyte rsegs mem' (c + i) = mbyte rsegs mem (c + i)) -> rconf_at rsegs mem' c rc.
Proof.
  intros mem mem' c rc (bs & Hb & He) K. exists bs. split; [|exact He].
  pose proof He as (Hl & _). apply (b8_ba_mbyte mem); [exact Hb|]. intros i Hi. apply K. lia.
Qed.

Lemma l03_mconf_keep : forall mem mem' a mc, mconf_at rsegs mem a mc ->
  (forall i, 0 <= i < SEG_M_SIZE -> mbyte rsegs mem' (a + i) = mbyte rsegs mem (a + i)) -> mconf_at rsegs mem' a mc.
Proof.
  intros mem mem' a mc (bs & Hb & He) K. exists bs. split; [|exact He].
  pose proof He as He'. unfold mconf_enc, mconf_encp in He'. destruct He' as (Hl & _).
  apply (b8_ba_mbyte mem); [exact Hb|]. intros i Hi. apply K. lia.
Qed.

Lemma l03_lcore : forall inp p Sp c mm regs mem regs' mem',
  P_lcore inp p Sp c mm regs mem ->
  (forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall a, Sp - SEG_FRAME <= a < Sp -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  P_lcore inp p Sp c mm regs' mem'.
Proof.
  intros inp p Sp c mm regs mem regs' mem'
    ((R18 & R27 & C8 & C10 & C20 & C48 & C50 & Hc16 & Hm16 & Hnc & Hnm) & R21 & C28 & C30 & C38 & C40) HR HM.
  assert (KC : forall off v, 0 <= off <= 0x50 -> celz mem Sp off v -> celz mem' Sp off v).
  { intros off v Ho HC. apply (l03_celz mem); [lia | unfold SEG_FRAME; lia | exact HC | exact HM]. }
  unfold P_lcore, P_mcore.
  split; [|split; [l03_rgz HR R21 21|]].
  - split; [l03_rgz HR R18 18|]. split; [l03_rgz HR R27 27|].
    split; [apply KC; [lia | exact C8]|]. split; [apply KC; [lia | exact C10]|].
    split; [apply KC; [lia | exact C20]|]. split; [apply KC; [lia | exact C48]|].
    split; [apply KC; [lia | exact C50]|].
    split; [exact Hc16|]. split; [exact Hm16|]. split; [exact Hnc | exact Hnm].
  - split; [apply KC; [lia | exact C28]|]. split; [apply KC; [lia | exact C30]|].
    split; [apply KC; [lia | exact C38] | apply KC; [lia | exact C40]].
Qed.

(* K13c34 f -> K139e4 (S f) across free and the taken `bne`. *)
Lemma l03_P_next : forall inp p Sp f c mm t nt regs mem regs' mem',
  P_K13c34 inp p Sp f c mm t nt regs mem -> Z.of_nat (S f) <> seg_nfiles inp ->
  (forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall a, Sp - SEG_FRAME <= a < Sp -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  (forall i, 0 <= i < SEG_C_SIZE -> mbyte rsegs mem' (c + i) = mbyte rsegs mem (c + i)) ->
  (forall i, 0 <= i < SEG_M_SIZE -> mbyte rsegs mem' (mm + i) = mbyte rsegs mem (mm + i)) ->
  P_K139e4 inp p Sp (S f) c mm regs' mem'.
Proof.
  intros inp p Sp f c mm t nt regs mem regs' mem'
    (Hf & _ & Hlc & _ & _ & H8 & H19 & H9 & H20 & _ & Hrc & Hmc) Hn HR HM HC HMm.
  rewrite (l03_after_next inp f Hn) in H20, Hrc, Hmc.
  unfold P_K139e4.
  split; [lia|].
  split; [exact (l03_lcore inp p Sp c mm regs mem regs' mem' Hlc HR HM)|].
  split; [l03_rgz HR H8 8|]. split; [l03_rgz HR H19 19|]. split; [l03_rgz HR H9 9|].
  split; [l03_rgz HR H20 20|].
  split; [exact (l03_rconf_keep mem mem' c _ Hrc HC) | exact (l03_mconf_keep mem mem' mm _ Hmc HMm)].
Qed.

(* K13c34 f -> K13c3c across free and the `bne` not taken (f + 1 = nfiles). *)
Lemma l03_P_exit : forall inp p Sp f c mm t nt regs mem regs' mem',
  P_K13c34 inp p Sp f c mm t nt regs mem -> Z.of_nat (S f) = seg_nfiles inp ->
  (forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall a, Sp - SEG_FRAME <= a < Sp -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  (forall i, 0 <= i < SEG_C_SIZE -> mbyte rsegs mem' (c + i) = mbyte rsegs mem (c + i)) ->
  (forall i, 0 <= i < SEG_M_SIZE -> mbyte rsegs mem' (mm + i) = mbyte rsegs mem (mm + i)) ->
  P_K13c3c inp p Sp c mm regs' mem'.
Proof.
  intros inp p Sp f c mm t nt regs mem regs' mem'
    (_ & _ & Hlc & _ & _ & _ & _ & _ & H20 & _ & Hrc & Hmc) Hl HR HM HC HMm.
  rewrite (l03_after_last inp f Hl) in H20, Hrc, Hmc.
  destruct (l03_lcore inp p Sp c mm regs mem regs' mem' Hlc HR HM) as (HMC & _ & _ & _ & C38 & _).
  unfold P_K13c3c.
  split; [exact HMC|]. split; [exact C38|].
  split; [l03_rgz HR H20 20|].
  split; [exact (l03_rconf_keep mem mem' c _ Hrc HC) | exact (l03_mconf_keep mem mem' mm _ Hmc HMm)].
Qed.

(* ---- The two instructions ---- *)
(* 0x13c34 `jal free` (ra 0x13c38). *)
Lemma kL03a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13c38) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x173d8) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13c34) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro.
  step. apply evt_done. reflexivity.
Qed.

(* A branch: keep the side the facts allow. *)
Ltac l03_if :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "EC" in if_cases H; zify_cond H; try (exfalso; lia)
  | _ => idtac
  end.

(* 0x13c38 `bne s0,s10,-0x254`, taken: s0 <> s10, back to the loop head 0x139e4. *)
Lemma kL03t : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  bv_unsigned x8 <> bv_unsigned x26 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x139e4) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13c38) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro H.
  step. l03_if. apply evt_done. reflexivity.
Qed.

(* 0x13c38 `bne s0,s10,-0x254`, not taken: s0 = s10, out of the loop to 0x13c3c. *)
Lemma kL03n : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  bv_unsigned x8 = bv_unsigned x26 ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13c3c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13c38) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro H.
  step. l03_if. apply evt_done. reflexivity.
Qed.

(* ---- The segment ---- *)
Section L03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.

Lemma seg_L03 : S_L03 B APIf ra empty CPseg.
(* The cut carries its own FP state, so this walk does not read the Section's fx; SegEnd.seg_L03_stmt binds it. *)
Proof using fx rc B APIf LS SH SK ra empty FF.
  unfold S_L03. intros f H139e4 H13c3c g c (bc & bm & t & nt & HC).
  pose proof (b8_segs B APIf ra empty FF) as SEGS.
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HF HP HPc.
  pose proof HPc as (Hf & _ & _ & H10 & _ & H8 & _ & _ & _ & H26 & _).
  unfold rgz in H10, H8, H26.
  destruct (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (_ & _ & HSK & HS47).
  pose proof alloc_ceiling_value as HAC.
  pose proof (l03_nfiles (g_in g)) as HNF.
  unfold hb_tcm in HF, HP.
  assert (Hin : In (t, nt) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kL03a | intros regs_c HG].
  rewrite <- Ep in HF, HP.
  apply (b8_free_call B APIf ra empty FF g [] (hb_cm bc bm) L A regs mem md regs_c p nt).
  - exact HF.
  - exact HP.
  - exact Hp.
  - b8rg HG.
  - b8rg HG.
  - b8rg HG.
  - rewrite HG. apply ret_ok_even. reflexivity.
  - rewrite HG. transitivity (getr regs 10); [reflexivity|]. rewrite Ep. exact H10.
  - intros L' A' regs' mem' md' HF' HP' RP' HKS HKB.
    replace (getr regs_c 1) with (Z_to_bv 64 0x13c38) by (rewrite HG; reflexivity).
    cbn [app] in HF', HP', HKB.
    (* The callee-saved registers, the frame cells, c's and m's bytes through free. *)
    assert (R' : forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. etransitivity; [exact (RP' r Hr)|].
      destruct (l03_cs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        rewrite HG; reflexivity. }
    assert (HM : forall a, g_S g - SEG_FRAME <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a).
    { intros a Ha. rewrite <- SEGS. apply HKS. unfold SEG_FRAME in Ha. lia. }
    assert (HCk : forall i, 0 <= i < SEG_C_SIZE -> mbyte rsegs mem' (bc + i) = mbyte rsegs mem (bc + i)).
    { intros i Hi. rewrite <- SEGS. apply (HKB bc C_SIZE i); [right; left; reflexivity|].
      unfold C_SIZE, SEG_C_SIZE in *. lia. }
    assert (HMk : forall i, 0 <= i < SEG_M_SIZE -> mbyte rsegs mem' (bm + i) = mbyte rsegs mem (bm + i)).
    { intros i Hi. rewrite <- SEGS. apply (HKB bm M_SIZE i); [left; reflexivity|].
      unfold M_SIZE, SEG_M_SIZE in *. lia. }
    assert (U8 : bv_unsigned (getr regs' 8) = Z.of_nat (S f)).
    { transitivity (bv_unsigned (getr regs 8)); [f_equal; exact (R' 8 ltac:(unfold callee_saved; lia))|].
      rewrite H8. apply b8_unsigned. lia. }
    assert (U26 : bv_unsigned (getr regs' 26) = seg_nfiles (g_in g)).
    { transitivity (bv_unsigned (getr regs 26)); [f_equal; exact (R' 26 ltac:(unfold callee_saved; lia))|].
      rewrite H26. apply b8_unsigned. lia. }
    destruct (Z.eq_dec (Z.of_nat (S f)) (seg_nfiles (g_in g))) as [Hlast | Hnext].
    + (* f + 1 = nfiles: out of the loop, K13c3c. *)
      eapply (b8_run_to B APIf ra empty FF);
        [exact HF' | unfold rmk; apply kL03n; rewrite U8, U26; exact Hlast | intros regs4 HG4].
      assert (R4 : forall r, callee_saved r -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
      { intros r Hr. rewrite <- (R' r Hr).
        destruct (l03_cs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          rewrite HG4; reflexivity. }
      apply H13c3c. exists bc, bm, fx', L', A', regs4, mem', md'.
      split; [reflexivity|]. split; [exact Hfrm|].
      split; [apply (b8_FR_regs B APIf ra empty g _ L' A' regs' regs4 mem' md' HF'); rewrite HG4; reflexivity|].
      split; [exact HP'|].
      exact (l03_P_exit (g_in g) (g_p g) (g_S g) f bc bm t nt regs mem regs4 mem' HPc Hlast R4 HM HCk HMk).
    + (* f + 1 < nfiles: back to the loop head, K139e4 (S f). *)
      assert (Hlt : (S f < 4)%nat) by lia.
      eapply (b8_run_to B APIf ra empty FF);
        [exact HF' | unfold rmk; apply kL03t; rewrite U8, U26; exact Hnext | intros regs4 HG4].
      assert (R4 : forall r, callee_saved r -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
      { intros r Hr. rewrite <- (R' r Hr).
        destruct (l03_cs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          rewrite HG4; reflexivity. }
      apply H139e4. split; [exact Hlt|]. exists bc, bm, fx', L', A', regs4, mem', md'.
      split; [reflexivity|]. split; [exact Hfrm|].
      split; [apply (b8_FR_regs B APIf ra empty g _ L' A' regs' regs4 mem' md' HF'); rewrite HG4; reflexivity|].
      split; [exact HP'|].
      exact (l03_P_next (g_in g) (g_p g) (g_S g) f bc bm t nt regs mem regs4 mem' HPc Hnext R4 HM HCk HMk).
Qed.

End L03.

Theorem seg_L03_holds : seg_L03_stmt CPseg.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF.
  exact (@seg_L03 fx rc B APIf LS SH SK ra empty FF).
Qed.
