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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/SlotItB3q.v; 144 of its 183 lines of code are new or changed and 394 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import joined_c SlotItA SlotItBW SlotItC0 check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Slot SlotInv SlotRec RecTail RecAnsB send_message.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* check_words's call: from its entry (pc 0x14bac, stBW, a0 = &w at FB + 24) to its return (pc 0x14390, stC). *)

(* The harness facts (HarnessProps, stated with the plain build's check_words_c) give this build's words_prop:
   the two definitions agree item by item. *)
Definition it_witem (i : witem) : OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.witem :=
  match i with
  | IStar => OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.IStar | ILine => OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.ILine | IWord k => OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.IWord k
  | INum k => OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.INum k | IOpt k => OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.IOpt k
  end.

Lemma it_call_items : forall fn, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.call_items fn = map it_witem (call_items fn).
Proof.
  intros fn. destruct fn as [|q|q]; [reflexivity| |reflexivity].
  repeat (destruct q as [q|q|]; try reflexivity).
Qed.

Lemma it_words_prop : forall R ws, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.words_prop R ws -> words_prop R ws.
Proof.
  intros R ws H. unfold words_prop, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.words_prop in *.
  eapply Forall_impl; [|exact H]. intros c (C1 & C2 & C3 & C4).
  split; [|exact (conj C2 (conj C3 C4))].
  intros a i x Ha Hi y Hy.
  apply (C1 a (it_witem i) x Ha).
  - rewrite it_call_items. rewrite nth_error_map, Hi. reflexivity.
  - destruct i; exact Hy.
Qed.

Section CW.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : CF.Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (CF.SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (CF.SlotInv.FB S).

Ltac prs P H r := exact (eq_trans (P r ltac:(unfold callee_saved; lia)) H).

Lemma seg_cw : (forall fx : FPState, @check_words_contract fx rc B (API rc)) -> forall m p n R0 c,
  stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (stC B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).
Proof.
  intros CWC m p n R0 c
    (fx & L & A & regs & mem & md & O & R1 & x & quit & text & copy & arr & kt & kc & ka & wp & jw & -> & HCF & HRC &
     EVR & DCL & HSB & HHB & HRX & D1 & D2 & D3 & Hkt & Hkc & Hka & AL8 & HLR & G1 & G10 & G18 & G19 & LC0 & LC1 &
     WV & WP & IL & ILW & JN & MP).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & GR2 & GR3 & GR4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  pose proof HLR as (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  pose proof (it_SEGS B API LS SH SK ra empty FG) as SEGS.
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof (it_TS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as TS.
  pose proof (it_S16 B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as S16.
  pose proof (it_errno B API LS SH SK ra empty FG) as EV.
  pose proof alloc_ceiling_val as AC.
  assert (SP : spZ regs = FB) by (eapply it_spz; eassumption).
  pose proof (it_cmd B API LS SH SK ra empty S rg mem0 md0 L0 A0 FG fx L A regs mem md HCF) as CMD.
  assert (PREK : call_pre_k B (aa_MR (API rc)) CHECK_WORDS_K L A regs mem md).
  { apply (it_pre B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md CHECK_WORDS_K HCF).
    - rewrite G1. apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    - unfold CHECK_WORDS_K, ALLOC_STACK, SLOT_STACK. lia. }
  assert (QOUT : outside B L A CHECK_WORDS_K regs G_QUIT 4).
  { intros i Hi. split.
    - apply (it_GNOWN B API LS SH SK ra empty FG fx L A mem md _ M). apply se_g_of. unfold G_QUIT. lia.
    - unfold scratch_k. rewrite SP, EV.
      unfold CF.SlotInv.FB, SLOT_STACK, G_QUIT, CHECK_WORDS_K, ALLOC_STACK in *. lia. }
  assert (NOWN : forall i, 0 <= i < CHECK_WORDS_FRAME -> ~ owned B L A (spZ regs - i - 1)).
  { intros i Hi Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L A mem md _ M Ho) as Hlo.
    rewrite SP in Hlo. unfold CF.SlotInv.FB, SLOT_STACK, CHECK_WORDS_FRAME in *. lia. }
  assert (RSL : forall pn, In pn O -> 0 <= snd pn <= LMAX + 2).
  { intros pn Hin. pose proof (it_rec_blk rsegs L A mem R1 O pn REP Hin). lia. }
  assert (XS : forall pn, In pn [(text, kt); (copy, kc); (arr, ka)] -> 0 <= snd pn <= 2 ^ 16).
  { intros pn [<-|[<-|[<-|[]]]]; cbn [snd]; lia. }
  assert (ROOM : room_ag (CF.SlotInv.tb A) (join_need (hwords (m_D p0 pl p n)) + 1)).
  { pose proof (it_tb_range L A Wf) as [T1 T2].
    assert (JN0 : 0 <= join_need (hwords (m_D p0 pl p n))).
    { generalize (hwords (m_D p0 pl p n)) as ws0. clear. intros ws0. unfold join_need.
      induction ws0 as [|w ws IH]; cbn [fold_right]; lia. }
    apply (it_room B API LS SH SK ra empty rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A mem md O
             [(text, kt); (copy, kc); (arr, ka)] M Wf EB BLK HOL RSL ltac:(cbn; lia) XS).
    - reflexivity.
    - unfold CF.SlotInv.tb. cbn. lia.
    - unfold CF.SlotInv.tb. cbn. lia.
    - lia. }
  pose proof MP as MP'. unfold msg_props in MP'. cbv zeta in MP'.
  assert (EVRp : OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_c.vr_run (rec_clear R0)
    (m_D p0 pl p n) = (R1, x, quit)) by exact EVR.
  rewrite EVRp in MP'. cbv beta iota in MP'.
  destruct MP' as (_ & _ & _ & _ & _ & _ & _ & WPRp & _).
  pose proof (it_words_prop R1 _ WPRp) as WPR.
  pose proof (CWC fx) as K. unfold check_words_contract in K.
  specialize (K L A regs mem md (CF.SlotInv.tb A) (FB + 24) arr (qv quit) wp (hwords (m_D p0 pl p n)) R1 O).
  rewrite SEGS in K.
  specialize (K eq_refl PREK ltac:(rewrite SP; unfold CF.SlotInv.FB in *; lia) CMD FZ
    (CF.send_message.sm_le_of_bytes B mem _ _ SEGS QB) QOUT G10 WV WP ltac:(unfold CF.SlotInv.FB in *; lia) AL8
    ltac:(rewrite SP; lia) ltac:(unfold CF.SlotInv.FB in *; lia) ltac:(lia) REP NOWN (CF.SlotInv.res_tb L A Wf HRC) ROOM WPR).
  unfold CHECK_WORDS in K.
  eapply SR_bind; [exact K|]. clear K.
  intros c1 (fx1 & L1 & A1 & regs1 & mem1 & md1 & -> & FZ1 & POST & BEQ & BK & INIT1 & RGN1 & CMD1 & QL1 & REP1 &
    WV1 & RES1).
  destruct POST as (M1 & W1 & Bd1 & LLE1 & PA1 & PRES & (vm1 & Hmd1) & FRAME & BYTES & SCRW).
  pose proof CMD1 as (RO1 & GI1 & _). rewrite SEGS in RO1.
  pose proof FRAME as FRAMEr. rewrite SEGS in FRAMEr.
  apply SR_ret.
  assert (EB1 : CF.SlotInv.eblocks mem0 L0 A0 L1 A1 mem1).
  { intros a k Hin. destruct (EB a k Hin) as [Hb Hk]. split.
    - rewrite BEQ. exact Hb.
    - intros i Hi. rewrite <- (Hk i Hi). pose proof (BK a k i Hb (fun H => H) Hi) as KK. rewrite SEGS in KK. exact KK. }
  assert (CF1 : CF fx1 L1 A1 regs1 mem1 md1).
  { apply (it_cf_call B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx fx1 CHECK_WORDS_K
             L A regs mem md (fun _ => False) L1 A1 regs1 mem1 md1 regs1 HCF M1 W1 Bd1 (INIT1 I) PRES
             (ex_intro _ vm1 Hmd1)).
    - exact FRAME.
    - exact SCRW.
    - unfold CF.SlotInv.FB, CHECK_WORDS_K, ALLOC_STACK, SLOT_STACK. lia.
    - unfold CHECK_WORDS_K, ALLOC_STACK. lia.
    - intros a [].
    - exact RO1.
    - exact GI1.
    - exact EB1.
    - exact FZ1.
    - intros r. reflexivity. }
  assert (RX1 : RFX L0 A0 L1 A1 mem1 R1 O (qv quit) [(text, kt); (copy, kc); (arr, ka)]).
  { unfold RFX. split; [exact REP1|]. split; [exact SPILL|].
    split.
    { apply (CF.send_message.sm_bytes_of_le B mem1 _ _ SEGS); [unfold G_QUIT; lia | rewrite length_le4; unfold G_QUIT; lia |].
      exact QL1. }
    split; [exact Hq|]. split; [exact ENO|].
    split; [intros pn Hq0; rewrite BEQ in Hq0; exact (BLK pn Hq0)|].
    split; [|exact HOL].
    intros pn Hq0. destruct (XC pn Hq0) as (Hb & H0 & HO). rewrite BEQ. tauto. }
  exists fx1, L1, A1, regs1, mem1, md1, O, R1, x, quit, text, copy, arr, kt, kc, ka, wp, jw.
  split; [rewrite G1; reflexivity|].
  split; [exact CF1|].
  split; [exists (sb_free (sb_malloc (CF.SlotInv.tb A) (join_need (hwords (m_D p0 pl p n)) + 1))
                   (join_need (hwords (m_D p0 pl p n)) + 1)); split; [exact RES1 | reflexivity]|].
  split; [exact EVR|]. split; [exact DCL|]. split; [exact HSB|]. split; [exact HHB|].
  split; [exact RX1|].
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|].
  split; [exact Hkt|]. split; [exact Hkc|]. split; [exact Hka|]. split; [exact AL8|].
  split.
  { unfold LR. split; [prs PRES L8 8|]. split; [prs PRES L9 9|]. split; [prs PRES L23 23|].
    split; [prs PRES L22 22|]. split; [prs PRES L26 26|]. split; [prs PRES L24 24|].
    split; [prs PRES L25 25|]. split; [prs PRES L27 27|]. lia. }
  split; [prs PRES G18 18|]. split; [prs PRES G19 19|].
  split.
  { apply (it_frame_cells B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md
             CHECK_WORDS_K (fun _ => False) L1 A1 mem1 md1 FB _ HCF M1 FRAMEr).
    - intros a [].
    - lia.
    - unfold LOC1. cbn. lia.
    - exact LC0. }
  split.
  { apply (it_frame_cells B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md
             CHECK_WORDS_K (fun _ => False) L1 A1 mem1 md1 (FB + 24) _ HCF M1 FRAMEr).
    - intros a [].
    - lia.
    - cbn. lia.
    - exact LC1. }
  split; [exact WV1|].
  split; [unfold words_place, in_block in *; rewrite BEQ; exact WP|].
  split; [unfold in_live in *; rewrite BEQ; exact IL|].
  split; [intros k Hk; specialize (ILW k Hk); unfold in_live in *; rewrite BEQ; exact ILW|].
  split; [exact JN | exact MP].
Qed.

End CW.
