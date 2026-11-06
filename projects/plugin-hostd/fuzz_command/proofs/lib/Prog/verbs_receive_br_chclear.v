(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v, with its module paths and module names changed; 567 of its 616 lines of code are new or changed and 166 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun CTypeFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br verbs_receive_br2 sup_chain_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c number_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma chclear_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Definition chclear_w (sp tp : word) : list (Z * Z) :=
  [(bv_unsigned sp - number_c.NUMBER_K, bv_unsigned sp); (bv_unsigned sp + 524, bv_unsigned sp + 524 + 4);
   (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)].

Definition chclear_npre (m : word -> option byte) (sp tp p1 : word) (w ob : list byte) (lo : Z) (can ev : word) : Prop :=
  bv_unsigned sp + 528 <= 2 ^ 63 /\
  VerbsMem.cstr0_at m (bv_unsigned p1) w /\
  4096 <= bv_unsigned p1 /\ Z.of_nat (length w) <= 8192 /\
  bv_unsigned p1 + Z.of_nat (length w) + 1 <= 2 ^ 63 /\
  (bv_unsigned sp + 524) mod 4 = 0 /\
  bytes_at rsegs m (bv_unsigned sp + 524) ob /\ length ob = 4%nat /\ wr_at rsegs m (bv_unsigned sp + 524) 4 /\
  rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] /\
  VerbsMem.ssp_at m can /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\ lo + number_c.NUMBER_K <= bv_unsigned sp /\
  VerbsMem.off_lo lo sp (bv_unsigned p1) (Z.of_nat (length w) + 1) /\
  VerbsMem.off_lo lo sp (bv_unsigned tp + -164) 4 /\
  VerbsMem.off_lo lo sp VerbsMem.SSP_GOT 8 /\ VerbsMem.off_lo lo sp VerbsMem.SSP_GUARD 8 /\
  (bv_unsigned tp + -164 + 4 <= bv_unsigned p1 \/ bv_unsigned p1 + Z.of_nat (length w) + 1 <= bv_unsigned tp + -164) /\
  bv_unsigned p1 + Z.of_nat (length w) + 1 <= bv_unsigned sp /\
  bv_unsigned tp + -164 + 4 <= bv_unsigned sp /\
  (bv_unsigned tp + -164 + 4 <= VerbsMem.SSP_GUARD \/ VerbsMem.SSP_GUARD + 8 <= bv_unsigned tp + -164).

Lemma chclear_k1 : number_c.number_contract -> forall (tk : list (list byte))
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p1 : word) (w ob : list byte) (lo : Z) (can ev : word),
  s5 = verbs_receive_disp.ntokw tk -> (length tk <= 64)%nat ->
  (length tk = 2%nat -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1)) ->
  (length tk = 2%nat -> chclear_npre m sp tp p1 w ob lo can ev) ->
  evt rsegs (fun ms' =>
      (length tk = 2%nat /\ exists v, number_m w = Some v /\
       exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
       ms' = MS (mkR (Z_to_bv 64 0x1791c) sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x16cbc) fc None m' (seg_rom rsegs) /\
       munch (chclear_w sp tp) m m' /\ wmono rsegs m m' /\
       bytes_at rsegs m' (bv_unsigned sp + 524) (le4 (Z_to_bv 64 v))) \/
      (length tk = 2%nat /\ number_m w = None /\
       exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
       ms' = MS (mkR (Z_to_bv 64 0x17910) sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x17968) fc None m' (seg_rom rsegs) /\
       munch (chclear_w sp tp) m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' (bv_unsigned sp + 524) ob) \/
      (length tk <> 2%nat /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17968) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x178fc) fc None m (seg_rom rsegs)).
Proof.
  intros NB tk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p1 w ob lo can ev E5 HL HB HN. subst s5.
  do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
  destruct (Z.of_nat (length tk) =? 2) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. assert (L2 : length tk = 2%nat) by lia.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB L2)) as RD. rewrite length_le8 in RD.
    do 3 zstep.
    destruct (HN L2) as (S63 & HW & W4 & WL & WB & OM & OB & OL & OW & ER & HSSP & MI & ST & LO & OV & OE & OG & OGd & D2 & D1 & D3 & D4).
    assert (UA : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 524)) = bv_unsigned sp + 524) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); lia).
    eapply evt_cut.
    { eapply NB with (lo := lo) (can := can) (ev := ev) (wd := w) (ob := ob); rewrite ?UA;
        first [eassumption | unfold VerbsMem.off_lo; lia]. }
    intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & EM & MU & WM & MI' & ST' & OB').
    subst ms'. rewrite UA in MU, OB'.
    replace (ret_pc (Z_to_bv 64 96528)) with (Z_to_bv 64 0x17910) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    destruct (number_m w) as [v|] eqn:NM.
    + pose proof (verbs_receive_disp.read_all _ _ _ OB') as RD'. rewrite length_le4 in RD'.
      zstep. rewrite (rec_shape_of.eqb_lit_signed 1 0) by lia. cbn [Z.eqb].
      do 2 zstep. rewrite chclear_sx32 by (pose proof (number_m_range w v NM); lia).
      apply evt_done. left. split; [exact L2|]. exists v. split; [reflexivity|].
      exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact OB'].
    + zstep. rewrite (rec_shape_of.eqb_lit_signed 0 0) by lia. cbn [Z.eqb].
      apply evt_done. right. left. split; [exact L2|]. split; [reflexivity|].
      exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact OB'].
  - apply Z.eqb_neq in E. apply evt_done. right. right. split; [lia | reflexivity].
Qed.

Lemma k_j1791c : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x17970) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x1791c) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis EU : errno_unowned B API.

Local Notation rg0 := (s_regs S).
Local Notation spf := (s_spf S).
Local Notation VS f := (@vr_state f _ B API S).

Lemma chclear_eimg : forall a, errno_addr B <= a < errno_addr B + 4 -> in_img B a.
Proof using HF.
  intros a Ha. rewrite (vf_errno B API HF) in Ha.
  apply (RecKindB.in_img_found B (vf_segs B API HF)); [lia|].
  assert (C : a = 0x3413c \/ a = 0x3413d \/ a = 0x3413e \/ a = 0x3413f) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; intro E; vm_compute in E; discriminate E.
Qed.

Lemma chclear_ero : forall a, errno_addr B <= a < errno_addr B + 4 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof using HF.
  intros a Ha. rewrite (vf_errno B API HF) in Ha.
  assert (C : a = 0x3413c \/ a = 0x3413d \/ a = 0x3413e \/ a = 0x3413f) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
Qed.

Lemma chclear_eread : forall m (i : nat), (i < 4)%nat -> exists b, mrd rsegs m (wa (0x3413c + Z.of_nat i)) = Some b.
Proof.
  intros m i Hi. unfold mrd.
  destruct (m (wa (0x3413c + Z.of_nat i))) as [b|]; [exists b; reflexivity|].
  destruct i as [|[|[|[|i]]]]; [| | | | lia]; vm_compute; eexists; reflexivity.
Qed.

Lemma chclear_ecells : forall m, (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m a) ->
  exists ev, rw_cells rsegs m (errno_addr B) [C4 ev].
Proof using HF.
  intros m HW. pose proof (vf_errno B API HF) as ERR. rewrite ERR in HW |- *.
  destruct (chclear_eread m 0 ltac:(lia)) as (b0 & E0).
  destruct (chclear_eread m 1 ltac:(lia)) as (b1 & E1).
  destruct (chclear_eread m 2 ltac:(lia)) as (b2 & E2).
  destruct (chclear_eread m 3 ltac:(lia)) as (b3 & E3).
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  assert (LE : le4 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])) = [b0; b1; b2; b3]).
  { pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]) as N0. pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as N1.
    cbn [length Z.of_nat] in N1. rewrite <- le4_lit by lia. exact (Z_to_le_bytes_to_Z [b0; b1; b2; b3]). }
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, LE. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|[|[|[|i]]]]; [exact E0 | exact E1 | exact E2 | exact E3 | lia].
  - cbn [cells_size csize Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi.
    exact (HW (0x3413c + i) ltac:(lia)).
Qed.

Lemma chclear_tail_mem : forall L1 A1 mem1 md1 R1 O1 k1 X mem2,
  vtail B API S L1 A1 mem1 md1 R1 O1 k1 X ->
  MR L1 A1 mem2 md1 -> ro_agree (ms_segs B) mem2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg0 - VR_K <= a < spZ rg0) -> ~ (G_QUIT <= a < G_QUIT + 4) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
  (forall a, (spZ rg0 - VR_K <= a < spZ rg0) \/ (errno_addr B <= a < errno_addr B + 4) ->
     writable_at rsegs mem1 a -> writable_at rsegs mem2 a) ->
  vtail B API S L1 A1 mem2 md1 R1 O1 k1 X /\
  (forall a k s bs, In (a, k) (blocks L1 A1) -> a <= s -> s + Z.of_nat (length bs) <= a + k ->
     bytes_at rsegs mem1 s bs -> bytes_at rsegs mem2 s bs).
Proof using HF HS.
  intros L1 A1 mem1 md1 R1 O1 k1 X mem2 H HM2 RO2 OUT SW.
  pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (aa_laws API) as LAWS.
  pose proof (t_rel B API S _ _ _ _ _ _ _ _ H) as REL.
  pose proof REL as (HM1 & _).
  assert (GQI : forall i, 0 <= i < 4 -> in_img B (G_QUIT + i)) by (intros i Hi; exact (proj1 (vf_globs B API HF _ (gq_glob i Hi)))).
  assert (KH : forall a k i, In (a, k) (blocks L1 A1) -> 0 <= i < k ->
             mbyte rsegs mem2 (a + i) = mbyte rsegs mem1 (a + i)).
  { intros a k i Hin Hi. destruct (blk_low B API HF _ _ _ _ a k i HM1 Hin Hi) as (H4 & Hc & Hni & _).
    apply OUT; [lia | lia | |].
    - intros Hq. apply Hni. replace (a + i) with (G_QUIT + (a + i - G_QUIT)) by ring. apply GQI. lia.
    - intros He. apply Hni. exact (chclear_eimg _ He). }
  split.
  2:{ intros a k s bs Hin H1 H2 Hb. apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi.
      replace (s + i) with (a + (s - a + i)) by ring. apply (KH a k); [exact Hin | lia]. }
  constructor.
  - eapply (rel_mem B API); [exact REL | exact HM2 | | | ].
    + intros a Dm N1 Ns Nw. rewrite SEGS.
      assert (Ra : 0 <= a < 2 ^ 64).
      { destruct Dm as [Dm|Dm]; [lia|]. pose proof (in_img_low B SEGS a Dm). lia. }
      apply OUT; [exact Ra | | |].
      * intros Hw. apply Ns. left. exact Hw.
      * intros Hq. apply Nw. unfold vr_writes. right. right. exact Hq.
      * intros He. apply Ns. right. exact He.
    + intros a k i Hin Hx Hi.
      assert (Hno : ~ In (a, k) (s_O S)) by (intros Ho; apply Hx; apply in_map_iff; exists (a, k); split; [reflexivity | exact Ho]).
      destruct (t_old B API S _ _ _ _ _ _ _ _ H (a, k) Hin Hno) as [Hin1 _].
      rewrite SEGS. exact (KH a k i Hin1 Hi).
    + intros a Ha W. rewrite SEGS in *. exact (SW a Ha W).
  - apply (rec_rep_frame (ms_segs B) G_REC REC_SC L1 A1 mem1 R1 O1 L1 A1 mem2 (t_rec B API S _ _ _ _ _ _ _ _ H)).
    + intros a Ha. destruct (vf_globs B API HF a (rec_glob a Ha)) as (Hi & _ & _ & Hne).
      pose proof (in_img_low B SEGS a Hi) as Hlo. rewrite SEGS.
      destruct (OUT a) as [E W]; [lia | lia | unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT in *; lia | exact Hne |].
      split; [exact E | apply W].
    + intros p n i Hin Hi. destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ (t_rec B API S _ _ _ _ _ _ _ _ H) (p, n) Hin) as [Hb _].
      rewrite SEGS. exact (KH p n i Hb Hi).
    + intros pn Hin. exact (proj1 (reply.rec_rep_O _ _ _ _ _ _ _ _ (t_rec B API S _ _ _ _ _ _ _ _ H) pn Hin)).
  - exact RO2.
  - exact (t_init B API S _ _ _ _ _ _ _ _ H).
  - exact (t_res B API S _ _ _ _ _ _ _ _ H).
  - exact (t_old B API S _ _ _ _ _ _ _ _ H).
  - exact (t_sub B API S _ _ _ _ _ _ _ _ H).
  - exact (t_x B API S _ _ _ _ _ _ _ _ H).
  - exact (t_xap B API S _ _ _ _ _ _ _ _ H).
  - exact (t_xnd B API S _ _ _ _ _ _ _ _ H).
  - exact (t_xsz B API S _ _ _ _ _ _ _ _ H).
Qed.

Lemma chclear_heap_mem : forall L1 A1 mem1 md1 R1 O1 k1 xq mem2,
  vheap B API S L1 A1 mem1 md1 R1 O1 k1 xq ->
  MR L1 A1 mem2 md1 -> ro_agree (ms_segs B) mem2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg0 - VR_K <= a < spZ rg0) -> ~ (G_QUIT <= a < G_QUIT + 4) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
  (forall a, (spZ rg0 - VR_K <= a < spZ rg0) \/ (errno_addr B <= a < errno_addr B + 4) ->
     writable_at rsegs mem1 a -> writable_at rsegs mem2 a) ->
  vheap B API S L1 A1 mem2 md1 R1 O1 k1 xq.
Proof using HF HS.
  intros L1 A1 mem1 md1 R1 O1 k1 xq mem2 H HM2 RO2 OUT SW.
  destruct (chclear_tail_mem L1 A1 mem1 md1 R1 O1 k1 _ mem2 (h_t B API S _ _ _ _ _ _ _ _ H) HM2 RO2 OUT SW) as [T KB].
  pose proof (h_x B API S _ _ _ _ _ _ _ _ H) as HX.
  constructor.
  - exact T.
  - apply (KB (s_lb S) (s_nlb S)); [exact (proj1 (HX (s_lb S, s_nlb S) (or_introl eq_refl))) | lia | | exact (h_lb B API S _ _ _ _ _ _ _ _ H)].
    rewrite !length_app, repeat_length. cbn [length]. pose proof (line_le_upto S). unfold s_nlb. lia.
  - eapply Forall2_impl; [|exact (h_tok B API S _ _ _ _ _ _ _ _ H)]. intros p w ((Hb & Hnz) & H1 & H2).
    split; [split; [|exact Hnz]|split; assumption].
    apply (KB (s_cb S) (s_ncb S)); [exact (proj1 (HX (s_cb S, s_ncb S) (or_intror (or_introl eq_refl)))) | exact H1 | | exact Hb].
    rewrite length_app. cbn [length]. lia.
  - pose proof (h_q B API S _ _ _ _ _ _ _ _ H) as HQ. destruct xq as [[[q nq] t]|]; [|exact I].
    destruct HQ as [Hb Hl]. split; [|exact Hl].
    apply (KB q nq); [exact (proj1 (HX (q, nq) (or_intror (or_intror (or_introl eq_refl))))) | lia | | exact Hb].
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma chclear_bridge : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c (W : list (Z * Z)) (QQ : machine_state -> Prop) P,
  VS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ rg0 - VR_K <= x < spZ rg0) -> ~ (G_QUIT <= x < G_QUIT + 4) ->
     ~ (errno_addr B <= x < errno_addr B + 4) -> Frame.outside W x) ->
  evt rsegs (fun ms' => QQ ms' /\ exists R' pc' m', ms' = MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
                 munch W (normalize rsegs mem1) m' /\ wmono rsegs (normalize rsegs mem1) m')
    (MS (Regs6ss.mkR_of rg) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall R' pc' m' mem2 rg', QQ (MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs)) -> Regs6ss.xregs_eqv R' rg' ->
     mem_rel rsegs mem2 m' -> munch W mem1 mem2 -> wmono rsegs mem1 mem2 ->
     vheap B API S L1 A1 mem2 md1 R1 O1 k1 xq ->
     SR rsegs (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1) P) ->
  SR rsegs c P.
Proof using HF HS EU.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c W QQ P (-> & FPK & VR & H & FR & GQ & GW) WO EVT K.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as REL. pose proof REL as (HM1 & _).
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (aa_laws API) as LAWS.
  destruct (mr_model _ _ LAWS _ _ _ _ HM1) as (Hh & Hl & Hmat).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO1 | exact EVT]. }
  intros ms5 (can5 & (s5 & (Q5 & R' & pc' & m' & E5 & MU' & WM') & REL5 & ROS5) & EQ5).
  subst s5.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL5) as [CAN5 HR5].
  remember (ms_mem can5) as mem2 eqn:Em2. subst can5. clear Em2.
  assert (RN1 : mem_rel rsegs mem1 (normalize rsegs mem1)) by (apply mem_rel_normalize; exact RO1).
  pose proof (munch_rel rsegs _ _ _ _ _ RN1 HR5 ROS5 MU') as MU.
  pose proof (wmono_rel rsegs _ _ _ _ RN1 HR5 ROS5 WM') as WM.
  pose proof (ro_agree_same rsegs _ _ RO1 ROS5) as RO2.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (rg' & -> & X5).
  apply (K R' pc' m' mem2 rg' Q5 X5 HR5 MU WM).
  assert (NOQ : forall a, owned B L1 A1 a -> ~ (G_QUIT <= a < G_QUIT + 4)).
  { intros a Ho Hq. apply (vf_globo B API HF L1 A1 mem1 md1 a HM1); [|exact Ho].
    replace a with (G_QUIT + (a - G_QUIT)) by ring. apply gq_glob. lia. }
  assert (NOE : forall a, owned B L1 A1 a -> ~ (errno_addr B <= a < errno_addr B + 4)).
  { intros a Ho He. exact (EU L1 A1 mem1 md1 a HM1 He Ho). }
  apply (chclear_heap_mem L1 A1 mem1 md1 R1 O1 k1 xq mem2 H).
  - eapply (mr_frame B _ LAWS L1 A1 mem1 mem2 md1 md1 HM1).
    + intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HM1 Ho) as [Ha1 Ha2].
      rewrite SEGS. eapply munch_mbyte; [exact MU | lia | apply WO; [lia | lia | exact (NOQ a Ho) | exact (NOE a Ho)]].
    + intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HM1 Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU | lia | apply WO; [lia | lia | exact (NOQ a Ho) | exact (NOE a Ho)] | exact Hp].
    + intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L1 A1 mem1 md1 p k i HM1 Hin Hi) as (Hp & H4 & Hc & Hno).
      assert (Hni : ~ in_img B (ptr_addr L1 p + i)) by exact (ax_blocks_img (vf_ax B API HF) L1 A1 mem1 md1 p k i HM1 Hin Hi).
      eapply munch_present; [exact MU | lia | apply WO; [lia | lia | | ] | exact Hp].
      * intros Hq. apply Hni. replace (ptr_addr L1 p + i) with (G_QUIT + (ptr_addr L1 p + i - G_QUIT)) by ring.
        exact (proj1 (vf_globs B API HF _ (gq_glob (ptr_addr L1 p + i - G_QUIT) ltac:(lia)))).
      * intros He. apply Hni. exact (chclear_eimg _ He).
    + reflexivity.
    + exact Hh.
    + exact Hl.
    + exact Hmat.
  - rewrite SEGS. exact RO2.
  - intros a Ra Hs Hq He. split; [eapply munch_mbyte | eapply munch_writable]; (exact MU || exact Ra || (apply WO; assumption)).
  - intros a _ W1. apply WM. exact W1.
Qed.

Lemma chclear_vfr : forall mem1 mem' jk nb,
  (forall a, spf <= a < spf + 608 -> ~ (spf + 524 <= a < spf + 528) -> mbyte rsegs mem' a = mbyte rsegs mem1 a) ->
  (forall a, spf <= a < spf + 608 -> writable_at rsegs mem1 a -> writable_at rsegs mem' a) ->
  bytes_at rsegs mem' (spf + 524) nb -> length nb = 4%nat ->
  vfr S mem1 jk -> vfr S mem' (firstn 4 jk ++ nb).
Proof using HS.
  intros mem1 mem' jk nb KB KW HN LN (((WF1 & Hb1) & Hw1) & (junk & F2) & F3).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  cbn [cells_wf cell_wf] in WF1. destruct WF1 as (LJ & WFv).
  cbn [cells_bytes cbytes] in Hb1.
  apply bytes_at_app in Hb1 as [HJ HV].
  rewrite <- (firstn_skipn 4 jk) in HJ. apply bytes_at_app in HJ as [HJ1 _].
  rewrite LJ in HV.
  pose proof (cells_bytes_length _ WFv) as LV.
  destruct Hw1 as (W0 & W1 & W3). cbn [cells_size csize] in W1, W3.
  assert (LF : length (firstn 4 jk) = 4%nat) by (rewrite length_firstn, LJ; reflexivity).
  split; [|split; [exists junk|]].
  - split; [split|].
    + cbn [cells_wf cell_wf]. split; [rewrite length_app, LF, LN; reflexivity | exact WFv].
    + cbn [cells_bytes cbytes]. rewrite <- app_assoc. apply bytes_at_app. split.
      * apply (bytes_at_transfer rsegs mem1); [exact HJ1|]. intros i Hi. rewrite LF in Hi. apply KB; unfold s_spf in *; lia.
      * rewrite LF. apply bytes_at_app. split.
        { replace (spf + 520 + Z.of_nat 4) with (spf + 524) by lia. exact HN. }
        rewrite LN. replace (spf + 520 + Z.of_nat 4 + Z.of_nat 4) with (spf + 520 + Z.of_nat 8) by lia.
        apply (bytes_at_transfer rsegs mem1); [exact HV|]. intros i Hi. rewrite LV in Hi.
        change (cells_size (vsaved S)) with 80%nat in Hi.
        apply KB; unfold s_spf in *; lia.
    + cbn [cells_size csize]. split; [exact W0|]. split; [exact W1|]. intros i Hi.
      pose proof (W3 i Hi) as W3i. change (cells_size (vsaved S)) with 80%nat in Hi.
      apply (KW (spf + 520 + i)); [unfold s_spf in *; lia | exact W3i].
  - apply (rw_cells_transfer rsegs mem1); [exact F2|]. intros i Hi. cbn in Hi.
    split; [apply KB; unfold s_spf in *; lia | apply KW; unfold s_spf in *; lia].
  - apply (bytes_at_transfer rsegs mem1); [exact F3|]. intros i Hi.
    destruct F2 as [_ (Ha & Hn & _)]. cbn in Hn.
    assert (L : Z.of_nat (length (concat (map le8 (s_ps S)))) <= 512).
    { rewrite length_concat_le8. pose proof (ok_psl B API S HS). lia. }
    apply KB; unfold s_spf in *; lia.
Qed.

Lemma chclear_ka : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c (W : list (Z * Z)) (QQ : machine_state -> Prop) P,
  VS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ rg0 - VR_K <= x < spf) -> ~ (spf + 524 <= x < spf + 528) ->
     ~ (errno_addr B <= x < errno_addr B + 4) -> Frame.outside W x) ->
  evt rsegs (fun ms' => QQ ms' /\ exists R' pc' m', ms' = MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
                 munch W (normalize rsegs mem1) m' /\ wmono rsegs (normalize rsegs mem1) m')
    (MS (Regs6ss.mkR_of rg) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall R' pc' m' rg' mem2, QQ (MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs)) -> Regs6ss.xregs_eqv R' rg' ->
     (forall pz nb, pc' = Z_to_bv 64 pz -> vregs S rg' -> bytes_at rsegs m' (spf + 524) nb -> length nb = 4%nat ->
        VS fx rg' pz mem2 md1 L1 A1 R1 O1 k1 qv xq (firstn 4 jk ++ nb) (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1)) ->
     SR rsegs (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1) P) ->
  SR rsegs c P.
Proof using HF HS EU.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c W QQ P HST WO EVT K.
  pose proof HST as (_ & FPK & _ & _ & FR & GQ & GW).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (vf_errno B API HF) as ERR.
  apply (chclear_bridge rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c W QQ P HST).
  - intros x Hx H1 H2 H3. apply WO; [exact Hx | unfold s_spf in *; lia | unfold s_spf, VR_K in *; lia | exact H3].
  - exact EVT.
  - intros R' pc' m' mem2 rg' HQ X RL MU WM H2.
    apply (K R' pc' m' rg' mem2 HQ X). intros pz nb Epz VR' HN LN. subst pc'.
    assert (KP : forall a, s_spf S <= a < s_spf S + 608 \/ G_QUIT <= a < G_QUIT + 4 ->
              ~ (s_spf S + 524 <= a < s_spf S + 528) ->
              mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
    { intros a Ha Hj. assert (Ra : 0 <= a < 2 ^ 64) by (unfold s_spf, G_QUIT, VR_K in *; lia).
      assert (Oa : Frame.outside W a)
        by (apply WO; [exact Ra | unfold s_spf, G_QUIT, VR_K in *; lia | exact Hj | rewrite ERR; unfold s_spf, G_QUIT, VR_K in *; lia]).
      split; [exact (munch_mbyte rsegs W mem1 mem2 a MU Ra Oa) | exact (munch_writable rsegs W mem1 mem2 a MU Ra Oa)]. }
    split; [reflexivity|]. split; [exact FPK|]. split; [exact VR'|]. split; [exact H2|].
    split.
    + apply (chclear_vfr mem1 mem2 jk nb); [ | | | exact LN | exact FR].
      * intros a Ha Hj. exact (proj1 (KP a (or_introl Ha) Hj)).
      * intros a _ W1. apply WM. exact W1.
      * exact (proj2 (bytes_at_rel rsegs mem2 m' _ _ RL) HN).
    + apply (gq_transfer mem1 mem2 qv); [|exact GQ|exact GW]. intros i Hi.
      apply KP; [right; lia | unfold s_spf, G_QUIT, VR_K in *; lia].
Qed.

Lemma chclear_pre : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c,
  VS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  stk rsegs (normalize rsegs mem1) (spf - 14336) spf /\
  (exists can, VerbsMem.ssp_at (normalize rsegs mem1) can) /\
  (exists ev, rw_cells rsegs (normalize rsegs mem1) (errno_addr B) [C4 ev]) /\
  bytes_at rsegs (normalize rsegs mem1) (spf + 524) (skipn 4 jk) /\ length (skipn 4 jk) = 4%nat /\
  wr_at rsegs (normalize rsegs mem1) (spf + 524) 4.
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c HST.
  pose proof HST as (_ & _ & _ & H & FR & _).
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as REL. pose proof REL as (HM1 & _ & _ & _ & _ & _ & _ & _ & HS9).
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1, HS9.
  assert (RN1 : mem_rel rsegs mem1 (normalize rsegs mem1)) by (apply mem_rel_normalize; exact RO1).
  destruct FR as (((WF1 & Hb1) & Hw1) & _ & _).
  cbn [cells_wf cell_wf] in WF1. destruct WF1 as (LJ & _).
  cbn [cells_bytes cbytes] in Hb1.
  apply bytes_at_app in Hb1 as [HJ _].
  rewrite <- (firstn_skipn 4 jk) in HJ. apply bytes_at_app in HJ as [_ HJ2].
  assert (LF : length (firstn 4 jk) = 4%nat) by (rewrite length_firstn, LJ; reflexivity).
  rewrite LF in HJ2. replace (spf + 520 + Z.of_nat 4) with (spf + 524) in HJ2 by lia.
  split.
  { apply RecAns.stk_normalize; [unfold s_spf, VR_K in *; lia | unfold s_spf in *; lia |].
    intros a Ha. apply HS9. left. unfold s_spf, VR_K in *. lia. }
  split.
  { destruct (st_f18 B API HF _ _ _ _ HM1) as (_ & cn & SSP). exists cn. destruct SSP as [S1 S2].
    split; apply bytes_at_normalize; try exact RO1; rewrite <- SEGS; apply reply.le_at_bytes;
      first [exact S1 | exact S2 | unfold VerbsMem.SSP_GOT, VerbsMem.SSP_GUARD; rewrite ?length_le8; lia]. }
  split.
  { apply chclear_ecells. intros a Ha. unfold writable_at.
    rewrite (wview_rel_rw rsegs mem1 (normalize rsegs mem1) _ RN1 (chclear_ero a Ha)).
    exact (HS9 a (or_intror Ha)). }
  split; [apply bytes_at_normalize; [exact RO1 | exact HJ2]|].
  split; [rewrite length_skipn, LJ; reflexivity|].
  apply (wr_at_norm rsegs mem1); [exact RN1 | | ].
  - destruct Hw1 as (W0 & W1 & W3). cbn [cells_size csize] in W1, W3.
    change (cells_size (vsaved S)) with 80%nat in W1, W3.
    split; [lia|]. split; [lia|].
    intros i Hi. replace (spf + 524 + i) with (spf + 520 + (4 + i)) by ring. apply W3. lia.
  - intros i Hi. unfold wa. apply ro_addr_hi. unfold s_spf, VR_K in *. lia.
Qed.

End M.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis NB : number_c.number_contract.
Hypothesis DC : forall f : YK11.FPState, @sup_chain_clear_contract f rc B API.
Hypothesis TP : ms_tp B = 0x341e0.
Hypothesis EU : errno_unowned B API.

Local Notation D := (s_D S).

Lemma vr_br_chclear : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RChclear) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RChclear -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  join_k B API S 0x17970 10 rg R1 k1 qv P ->
  rej_k B API S f 0x17968 rg R1 k1 qv P ->
  SR rsegs c P.
Proof.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT N21 HK JOIN REJ.
  pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR.
  pose proof HST as (_ & _ & VR & H & FR & _).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (Forall2_length TOK) as LPT.
  pose proof (ok_psl B API S HS) as PSL.
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as (HM1 & _).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & SPM & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  assert (TP4 : bv_unsigned (reg_get rg 4) = 0x341e0).
  { destruct VR as (_ & _ & V4 & _). change (reg_get rg 4) with (getr rg 4). rewrite V4.
    pose proof (ok_pre B API S HS) as (_ & _ & _ & _ & _ & _ & _ & _ & HTP & _). rewrite HTP, TP.
    apply unsigned_lit. lia. }
  assert (EA : errno_addr B = bv_unsigned (reg_get rg 4) + -164) by (rewrite TP4, ERR; reflexivity).
  assert (R21 : reg_get rg 21 = verbs_receive_disp.ntokw (toks D)) by (rewrite <- N21; reflexivity).
  assert (NL : (length (toks D) <= 64)%nat) by lia.
  pose proof (h_x B API S _ _ _ _ _ _ _ _ H (s_cb S, s_ncb S) (or_intror (or_introl eq_refl))) as [INC _].
  assert (NC : 0 < s_ncb S) by (unfold s_ncb; lia).
  destruct (blk_low B API HF L1 A1 mem1 md1 (s_cb S) (s_ncb S) 0 HM1 INC ltac:(lia)) as (C4k & HC & _).
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  destruct (@chclear_pre f _ B API HF S HS rg _ mem1 md1 L1 A1 R1 O1 k1 qv None jk c HST)
    as (STK & (can & SSP) & (ev & ECL) & JB & JL & JW).
  rewrite EA in ECL.
  assert (EP1 : length (toks D) = 2%nat -> nth_error (s_ps S) 1 = Some p1)
    by (intros L2; unfold p1; apply nth_error_nth'; lia).
  assert (EW1 : length (toks D) = 2%nat -> nth_error (toks D) 1 = Some (nth 1 (toks D) []))
    by (intros L2; apply nth_error_nth'; lia).
  assert (HB1 : length (toks D) = 2%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 16) (le8 p1)).
  { intros L2. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    pose proof (frame_tok S mem1 jk 1 p1 FR (EP1 L2)) as FT.
    replace (s_spf S + 16) with (s_spf S + 8 + 8 * Z.of_nat 1) by lia. exact FT. }
  assert (HN : length (toks D) = 2%nat ->
    chclear_npre (normalize rsegs mem1) (reg_get rg 2) (reg_get rg 4) p1 (nth 1 (toks D) []) (skipn 4 jk)
      (s_spf S - 14336) can ev).
  { intros L2.
    destruct (Forall2_nth _ _ _ _ _ _ TOK (EP1 L2) (EW1 L2)) as ((Hb & Hnz) & H1 & H2).
    assert (LW : Z.of_nat (length (nth 1 (toks D) [])) <= 8192).
    { assert (IW : In (nth 1 (toks D) []) (toks D)) by (apply (nth_error_In _ 1); exact (EW1 L2)).
      pose proof (verbs_receive_route.toks_len D _ IW) as LWD.
      pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
    unfold chclear_npre. rewrite SP2.
    split; [unfold s_spf in *; lia|].
    split; [split; [apply bytes_at_normalize; [exact RO1 | exact Hb] | exact Hnz]|].
    split; [lia|].
    split; [exact LW|].
    split; [lia|].
    split; [unfold s_spf in *; Z.div_mod_to_equations; lia|].
    split; [exact JB|]. split; [exact JL|]. split; [exact JW|].
    split; [exact ECL|].
    split; [exact SSP|].
    split; [apply mem_inv_normalize|].
    split; [exact STK|].
    split; [unfold number_c.NUMBER_K; lia|].
    split; [unfold VerbsMem.off_lo; left; unfold s_spf, VR_K in *; lia|].
    split; [unfold VerbsMem.off_lo; left; unfold s_spf, VR_K in *; lia|].
    split; [unfold VerbsMem.off_lo, VerbsMem.SSP_GOT; left; unfold s_spf, VR_K in *; lia|].
    split; [unfold VerbsMem.off_lo, VerbsMem.SSP_GUARD; left; unfold s_spf, VR_K in *; lia|].
    split.
    { destruct (Z.le_gt_cases (bv_unsigned (reg_get rg 4) + -164 + 4) (bv_unsigned p1)) as [Hc|Hc]; [left; exact Hc|].
      destruct (Z.le_gt_cases (bv_unsigned p1 + Z.of_nat (length (nth 1 (toks D) [])) + 1) (bv_unsigned (reg_get rg 4) + -164))
        as [Hd|Hd]; [right; exact Hd|].
      exfalso.
      destruct (blk_low B API HF L1 A1 mem1 md1 (s_cb S) (s_ncb S) (Z.max (bv_unsigned p1) 0x3413c - s_cb S) HM1 INC
                  ltac:(lia)) as (_ & _ & NI & _).
      apply NI. replace (s_cb S + (Z.max (bv_unsigned p1) 0x3413c - s_cb S)) with (Z.max (bv_unsigned p1) 0x3413c) by ring.
      apply (chclear_eimg B API HF). rewrite ERR. lia. }
    split; [unfold s_spf, VR_K in *; lia|].
    split; [unfold s_spf, VR_K in *; lia|].
    unfold VerbsMem.SSP_GUARD. lia. }
  eapply (@chclear_ka f _ B API HF S HS EU rg (route_pc RChclear) mem1 md1 L1 A1 R1 O1 k1 qv None jk c
            (chclear_w (reg_get rg 2) (reg_get rg 4)) _ P HST).
  { intros x Hx H1 H2 H3. unfold chclear_w. rewrite SP2, TP4. cbn [Frame.outside]. unfold number_c.NUMBER_K.
    rewrite ERR in H3. split; [unfold s_spf, VR_K in *; lia|]. split; [lia|]. split; [lia | exact I]. }
  { eapply evt_mono.
    { unfold Regs6ss.mkR_of. cbn [route_pc].
      apply (chclear_k1 NB (toks D)) with (p1 := p1) (w := nth 1 (toks D) []) (ob := skipn 4 jk)
        (lo := s_spf S - 14336) (can := can) (ev := ev);
        [exact R21 | exact NL | exact HB1 | exact HN]. }
    intros ms' HQ. split; [exact HQ|].
    destruct HQ as [(_ & v & _ & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU & WM & _)
                   |[(_ & _ & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU & WM & _)
                    |(_ & E)]]; subst ms'.
    - do 3 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
    - do 3 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
    - do 3 eexists. split; [reflexivity|]. split; [apply munch_refl | apply wmono_refl]. }
  intros R' pc' m' rg' mem2 HQ X MK.
  destruct HQ as [(L2 & v & NM & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m'' & EQ & _ & _ & BV)
                 |[(L2 & NM & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m'' & EQ & _ & _ & BO)
                  |(L2 & EQ)]];
    injection EQ as ER EP EM; subst R' pc' m'.
  - destruct (len2 (toks D) L2) as (v0 & a & TK).
    assert (G2 : getr rg' 2 = getr rg 2) by (rewrite (getr_of_eqv _ _ 2 X eq_refl); reflexivity).
    assert (G3 : getr rg' 3 = getr rg 3) by (rewrite (getr_of_eqv _ _ 3 X eq_refl); reflexivity).
    assert (G4 : getr rg' 4 = getr rg 4) by (rewrite (getr_of_eqv _ _ 4 X eq_refl); reflexivity).
    assert (G8 : getr rg' 8 = getr rg 8) by (rewrite (getr_of_eqv _ _ 8 X eq_refl); reflexivity).
    assert (G9 : getr rg' 9 = getr rg 9) by (rewrite (getr_of_eqv _ _ 9 X eq_refl); reflexivity).
    assert (G18 : getr rg' 18 = getr rg 18) by (rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity).
    assert (G21 : getr rg' 21 = getr rg 21) by (rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity).
    assert (G25 : getr rg' 25 = getr rg 25) by (rewrite (getr_of_eqv _ _ 25 X eq_refl); reflexivity).
    assert (G26 : getr rg' 26 = getr rg 26) by (rewrite (getr_of_eqv _ _ 26 X eq_refl); reflexivity).
    assert (G27 : getr rg' 27 = getr rg 27) by (rewrite (getr_of_eqv _ _ 27 X eq_refl); reflexivity).
    assert (VR' : vregs S rg').
    { destruct VR as (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27).
      split; [rewrite G2; exact V2|]. split; [rewrite G3; exact V3|]. split; [rewrite G4; exact V4|].
      split; [rewrite G8; exact V8|]. split; [rewrite G9; exact V9|]. split; [rewrite G25; exact V25|].
      split; [rewrite G26; exact V26|]. rewrite G27; exact V27. }
    rewrite SP2 in BV.
    pose proof (MK 0x16cbc (le4 (Z_to_bv 64 v)) eq_refl VR' BV (length_le4 _)) as HST1.
    set (jk' := firstn 4 jk ++ le4 (Z_to_bv 64 v)) in HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x1791c) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (NMa : number_m a = Some v) by (rewrite TK in NM; exact NM).
    pose proof (number_m_range a v NMa) as VRg.
    assert (AR : -2^31 <= v < 2^31) by lia.
    assert (E10 : getr rg' 10 = Z_to_bv 64 v) by (rewrite (getr_of_eqv _ _ 10 X eq_refl); reflexivity).
    pose proof (dec_length _ AR) as DL.
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x1791c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_CHAIN_CLEAR_K <= 14336) by (unfold SUP_CHAIN_CLEAR_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x16cbc mem2 md1 L1 A1 R1 O1 k1 qv None jk' _ SUP_CHAIN_CLEAR_K 0x1791c
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    assert (LT : (length (snd (sup_chain_clear_m R1 v)) <= 28)%nat).
    { unfold sup_chain_clear_m, daemon_shape. apply stub_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_chain_clear_sizes v (snd (sup_chain_clear_m R1 v)))).
    { unfold sup_chain_clear_sizes. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length (sup_chain_clear_sizes v (snd (sup_chain_clear_m R1 v))) <= 32)%nat).
    { unfold sup_chain_clear_sizes. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    pose proof (st_room B API S HS k1 _ 17 HKS HSZ ltac:(lia)) as ROOM.
    assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_chain_clear_sizes v (snd (sup_chain_clear_m R1 v)))) <=
                  sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_chain_clear_sizes v (snd (sup_chain_clear_m R1 v))))).
    { destruct (sb_mallocs_fields (sup_chain_clear_sizes v (snd (sup_chain_clear_m R1 v))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_chain_clear_sizes. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x16cbc mem2 md1 L1 A1 R1 O1 k1 qv jk' _ SUP_CHAIN_CLEAR_K 0x1791c
             (sup_chain_clear_sizes v (snd (sup_chain_clear_m R1 v))) (sup_chain_clear_m R1 v) P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { pose proof (DC f L1 A1 rg' mem2 md1 v R1 O1 (sb_n (s_b S) k1) PRE E10 AR SH REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_CHAIN_CLEAR in C. exact C. }
      intros c'' HR.
      exact (ans_of B API HF SUP_CHAIN_CLEAR_K (sup_chain_clear_m R1 v) (sup_chain_clear_sizes v)
               L1 A1 rg' mem2 md1 O1 (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x1791c 0x17970 mem' md' L' A'
               (fst (sup_chain_clear_m R1 v)) O'
               (k1 + length (sup_chain_clear_sizes v (snd (sup_chain_clear_m R1 v))))
               q (snd (sup_chain_clear_m R1 v)) jk' c' P HST2 k_j1791c).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) G18).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) G21).
      * rewrite RT, TK. cbn [plan_at]. rewrite NMa. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_chain_clear_m R1 v); reflexivity.
      * unfold sup_chain_clear_sizes. cbn [length]. lia.
      * exact JOIN.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    rewrite SP2 in BO.
    eapply REJ. split; [exact (MK 0x17968 (skipn 4 jk) eq_refl (vregs_pres S rg rg' VR PR) BO JL)|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
    split; [|lia].
    destruct (len2 (toks D) L2) as (v0 & a & TK).
    assert (NMa : number_m a = None) by (rewrite TK in NM; exact NM).
    rewrite RT, TK. cbn [plan_at]. rewrite NMa. reflexivity.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    eapply REJ. split; [exact (MK 0x17968 (skipn 4 jk) eq_refl (vregs_pres S rg rg' VR PR) JB JL)|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
    split; [|lia].
    rewrite RT. destruct (toks D) as [|v0 [|a [|b r]]] eqn:TK'; cbn [plan_at]; try reflexivity.
    exfalso. apply L2. rewrite ?TK'. reflexivity.
Qed.

End R.
