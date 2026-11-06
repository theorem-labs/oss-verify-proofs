(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its addresses and numbers changed; 1390 of its 1552 lines of code are new or changed and 673 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/hand_back.v, with its module names changed; 447 of its 499 lines of code are new or changed and 1500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/SlotItCK.v; 349 of its 433 lines of code are new or changed and 415 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/SlotItB3q.v; 131 of its 171 lines of code are new or changed and 393 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SlotGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import SlotRuns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SlotCallees SlotIter SlotEnd SlotItBase SlotItSt verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandB VerbsB CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SlotItA SlotItC0 SlotItD0 SlotItE.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import check_refusal_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Slot SlotInv SlotRec RecTail RecAns CrtKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* check_refusal's call (pc 0x14390 .. 0x14398): a0 := s2, jal check_refusal; its stack window [FB - 64, FB)
   is the only memory it changes, so every fact of stC holds again at the return (stCR). *)

(* A byte outside the one window [lo, hi) of a munch keeps its value and writability. *)
Lemma d1_keep : forall mem mem' lo hi a, munch [(lo, hi)] mem mem' -> 0 <= a < 2 ^ 64 -> (a < lo \/ hi <= a) ->
  mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a).
Proof.
  intros mem mem' lo hi a MU Ha Hx.
  assert (Ho : Frame.outside [(lo, hi)] a) by (cbn; split; [lia | exact Logic.I]).
  split; [exact (KindB.munch_mbyte rsegs _ _ _ a MU Ha Ho) | exact (KindB.munch_writable rsegs _ _ _ a MU Ha Ho)].
Qed.

Section D1.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : CF.Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (CF.SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (CF.SlotInv.FB S).

Lemma seg_d1 : check_refusal_contract -> forall m p n R0 c,
  stC B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (stCR B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).
Proof.
  intros CRC m p n R0 c
    (fx & L & A & regs & mem & md & O & R1 & x & quit & text & copy & arr & kt & kc & ka & wp & jw & -> & HCF & HRC &
     EVR & DCL & HSR & HHR & HRX & D1 & D2 & D3 & K1 & K2 & K3 & AL8 & HLR & G18 & G19 & LC0 & LC1 & WV & WP & ILA & ILW &
     JN & MP).
  pose proof HCF as (M & Wf & Bd & HI0 & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  assert (SEGS : ms_segs B = rsegs) by exact (it_SEGS B API LS SH SK ra empty FG).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof alloc_ceiling_val as AC.
  destruct (it_model B API S rg mem0 md0 L0 A0 fx L A regs mem md HCF) as [Hh Hl].
  assert (SPV : bv_unsigned (reg_get regs 2) = FB).
  { change (reg_get regs 2) with (getr regs 2). rewrite R2. apply unsigned_lit.
    unfold CF.SlotInv.FB, SLOT_STACK in *. lia. }
  pose proof (it_cmd B API LS SH SK ra empty S rg mem0 md0 L0 A0 FG fx L A regs mem md HCF) as CMD.
  destruct (CF.CrtKeep.crt_got_bytes B SEGS mem CMD) as [GQB GRB].
  (* the harness facts of the message: the reply x and the refusal's state and quit *)
  assert (EVRp : OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_c.vr_run (rec_clear R0)
    (m_D p0 pl p n) = (R1, x, quit)) by exact EVR.
  pose proof MP as MP'. unfold msg_props in MP'. rewrite EVRp in MP'. cbv beta iota zeta in MP'.
  destruct MP' as (_ & RR & N0 & _ & _ & _ & _ & _ & RCX & _).
  (* the recorder's reply block and state word *)
  pose proof REP as (Q & (_ & _ & _ & RP & SC & _) & _).
  unfold reply_at in RP. rewrite RR in RP.
  destruct (l_reply Q) as [[pr pk]|]; [|cbn in RP; contradiction].
  destruct RP as (RW & _ & Hpr0 & _ & Hpb & Hpk & RXB & _). cbn [fst snd] in RW, Hpr0, Hpb, Hpk, RXB.
  rewrite length_app in Hpk. cbn [length] in Hpk.
  destruct (it_blk_out B API LS SH SK ra empty FG fx L A mem md pr pk 0 M Hpb ltac:(lia)) as (_ & Hp4 & Hpa).
  destruct SC as (_ & _ & _ & SST & _).
  unfold check_refusal_contract, CHECK_REFUSAL, CHECK_REFUSAL_K in CRC. cbv zeta in CRC.
  eapply (@sr_run fx regs (Z_to_bv 64 0x14390) mem md _ _ Hh Hl RO).
  { unfold Regs6ss.mkR_of.
    eapply evt_cut; [apply run_g_cr_ok|].
    intros ms' ->.
    eapply CRC with (lo := FB - 64) (reply := Z_to_bv 64 pr) (state := Z_to_bv 64 (r_state R1)) (quit := qv quit)
      (x := x).
    - apply mem_inv_normalize.
    - rewrite SPV. apply CF.RecAns.stk_normalize; [unfold CF.SlotInv.FB, SLOT_STACK in *; lia | unfold CF.SlotInv.FB in *; lia |].
      intros a Ha. apply SW. unfold lib_scratch. left. rewrite RG2. unfold CF.SlotInv.FB, SLOT_STACK in *. lia.
    - rewrite SPV. lia.
    - unfold IMG_END, CF.SlotInv.FB, SLOT_STACK in *. lia.
    - apply bytes_at_normalize; [exact RO | exact GRB].
    - apply bytes_at_normalize; [exact RO | exact RW].
    - apply bytes_at_normalize; [exact RO | exact SST].
    - apply bytes_at_normalize; [exact RO | exact GQB].
    - exact Hq.
    - apply bytes_at_normalize; [exact RO | exact QB].
    - intros _. rewrite unsigned_lit by lia. split.
      + unfold cstr_at. split; [apply bytes_at_normalize; [exact RO | exact RXB] | exact N0].
      + unfold outside_stack. cbn [disjoint_from]. rewrite SPV.
        split; [left; unfold CF.SlotInv.FB, SLOT_STACK in *; lia | exact Logic.I].
    - intros _ HX. destruct (RCX HX) as [E1 E2]. split.
      + rewrite E1. symmetry. exact G18.
      + rewrite E2. reflexivity. }
  { intros s0 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    do 5 eexists. reflexivity. }
  intros R' F' pc' fc' m0' regs2 mem2
    (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI & ST)
    REL ROS GR.
  injection E as ER EF Epc Efc Em. subst R' F' pc' fc' m0'.
  rewrite (ret_pc_even 0x14398) by first [lia | reflexivity].
  apply SR_ret.
  rewrite SPV in MU.
  pose proof (mem_rel_normalize rsegs mem RO) as REL0.
  assert (MU2 : munch [(FB - 64, FB)] mem mem2) by exact (munch_rel rsegs _ _ _ _ _ REL0 REL ROS MU).
  assert (WM2 : wmono rsegs mem mem2) by exact (wmono_rel rsegs _ _ _ _ REL0 REL ROS WM).
  assert (RO2 : ro_agree rsegs mem2) by exact (ro_agree_same rsegs _ _ RO ROS).
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> (a < FB - 64 \/ FB <= a) ->
     mbyte rsegs mem2 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem2 a))
    by (intros a Ha Hx; exact (d1_keep mem mem2 (FB - 64) FB a MU2 Ha Hx)).
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> (a < FB - 64 \/ FB <= a) -> mbyte rsegs mem2 a = mbyte rsegs mem a)
    by (intros a Ha Hx; exact (proj1 (KP a Ha Hx))).
  assert (KB : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs mem2 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hi. destruct (it_blk_out B API LS SH SK ra empty FG fx L A mem md a k i M Hin Hi) as (_ & H1 & H2).
    apply KM; unfold CF.SlotInv.FB, SLOT_STACK in *; lia. }
  assert (CF2 : CF (mkFP fp_regs fp_csr) L A regs2 mem2 md).
  { apply (it_cf_run B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx _ L A regs mem md
             [(FB - 64, FB)] mem2 regs2 HCF MU2 WM2 RO2).
    - intros a Ha Hx. left. apply it_not_out1 in Hx. unfold CF.SlotInv.FB, SLOT_STACK in *. lia.
    - intros p1 n1 i Hin Hi Hx. exfalso. apply it_not_out1 in Hx.
      pose proof (CF.RecTail.user_in_blocks L A p1 n1 Hin) as Hb.
      destruct (it_blk_out B API LS SH SK ra empty FG fx L A mem md _ _ i M Hb Hi) as (_ & H1 & H2).
      unfold CF.SlotInv.FB, SLOT_STACK in *. lia.
    - exact FZ.
    - rewrite GR. reflexivity.
    - rewrite GR. reflexivity.
    - rewrite GR. reflexivity. }
  assert (RX2 : RFX L0 A0 L A mem2 R1 O (qv quit) [(text, kt); (copy, kc); (arr, ka)]).
  { apply (it_rfx_move L0 A0 L A mem R1 O (qv quit) _ L A mem2 _ HRX).
    - intros a Ha. destruct (KP a) as [E1 W1]; [lia | unfold CF.SlotInv.FB, SLOT_STACK in *; lia |].
      split; [exact E1 | tauto].
    - intros p1 k1 i Hin Hi. destruct (it_rec_blk rsegs L A mem R1 O (p1, k1) REP Hin) as [Hb _].
      exact (KB p1 k1 i Hb Hi).
    - intros pn Hin. exact (proj1 (it_rec_blk rsegs L A mem R1 O pn REP Hin)).
    - exact BLK.
    - exact XC. }
  exists (mkFP fp_regs fp_csr), L, A, regs2, mem2, md, O, R1, x, quit, text, copy, arr, kt, kc, ka, wp, jw.
  split; [reflexivity|].
  split; [exact CF2|]. split; [exact HRC|]. split; [exact EVR|]. split; [exact DCL|].
  split; [exact HSR|]. split; [exact HHR|].
  split; [exact RX2|].
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|].
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact AL8|].
  split.
  { destruct HLR as (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & Hrest).
    unfold LR. split; [rewrite GR; exact L8|]. split; [rewrite GR; exact L9|]. split; [rewrite GR; exact L23|].
    split; [rewrite GR; exact L22|]. split; [rewrite GR; exact L26|]. split; [rewrite GR; exact L24|].
    split; [rewrite GR; exact L25|]. split; [rewrite GR; exact L27|].
    exact Hrest. }
  split; [rewrite GR; exact G18|]. split; [rewrite GR; exact G19|].
  split.
  { apply (KindB.rw_cells_transfer rsegs mem mem2 _ _ LC0). intros i Hi. unfold LOC1 in Hi. cbn in Hi.
    destruct (KP (FB + i)) as [E1 W1]; [unfold CF.SlotInv.FB, SLOT_STACK in *; lia | lia |].
    split; [exact E1 | tauto]. }
  split.
  { apply (KindB.rw_cells_transfer rsegs mem mem2 _ _ LC1). intros i Hi. cbn in Hi.
    destruct (KP (FB + 24 + i)) as [E1 W1]; [unfold CF.SlotInv.FB, SLOT_STACK in *; lia | lia |].
    split; [exact E1 | tauto]. }
  split.
  { apply (CF.CrtKeep.crt_words_view_keep B SEGS mem mem2 _ _ _ _ WV).
    - intros a Ha. apply KM; unfold CF.SlotInv.FB, SLOT_STACK in *; lia.
    - intros i Hi. destruct ILA as (pa & ka' & Hb & _ & H1 & H2).
      replace (arr + i) with (pa + (arr + i - pa)) by ring. apply (KB pa ka'); [exact Hb | lia].
    - intros k i Hk Hi. destruct (ILW k Hk) as (pw & kw & Hb & _ & H1 & H2).
      replace (nth k wp 0 + i) with (pw + (nth k wp 0 + i - pw)) by ring. apply (KB pw kw); [exact Hb | lia]. }
  split; [exact WP|]. split; [exact ILA|]. split; [exact ILW|]. split; [exact JN | exact MP].
Qed.

End D1.
