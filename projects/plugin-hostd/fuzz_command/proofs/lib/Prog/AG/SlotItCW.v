(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths changed; 599 of its 833 lines of code are new or changed and 2508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/RecStubU.v, with its module paths and module names changed; 444 of its 497 lines of code are new or changed and 780 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItCK.v; 330 of its 390 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItB3qh.v, with its module paths and numbers changed; 526 of its 771 lines of code are new or changed and 145 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/AG/SlotItB3h.v, with its module paths and module names changed; 137 of its 178 lines of code are new or changed and 730 lines of the source are left out. *)
(* lib/Prog/SlotItCW.v with the agreement room cap CAP_AG (lib/SlotAgree.v) for CAPMAX. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP SlotSpec SlotGlue SlotRuns HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotCallees SlotIter SlotEnd SlotItBase SlotItSt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c send_message_c CommandB VerbsB CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotItA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import joined_c check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotItBW SlotItC0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Slot SlotInv SlotRec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecTail RecAnsB.
Import ListNotations.
Local Open Scope Z_scope.

(* Segment (c) of one loop iteration: check_words' call from its entry (pc 0x14980, a0 = &w at FB + 40, stBW) to
   its return (pc 0x142dc, stC). *)

Lemma cw_join_need_nonneg : forall l, 0 <= join_need l.
Proof.
  induction l as [|w l IH]; [cbn; lia|].
  change (join_need (w :: l)) with (Z.of_nat (length w) + 1 + join_need l). lia.
Qed.

Section CW.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

Ltac cw_pres P H r := exact (eq_trans (P r ltac:(unfold callee_saved; lia)) H).

Lemma seg_c : (forall fx : FPState, @check_words_contract fx rc B (API rc)) -> forall m p n R0 c,
  stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (stC B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).
Proof.
  intros CWC m p n R0 c
    (fx & L & A & regs & mem & md & O & R1 & x & quit & text & copy & arr & kt & kc & ka & wp & -> & HCF & HRC & EVR &
     DCL & HSB & HHB & HRX & D1 & D2 & D3 & Hkt & Hkc & Hka & HLR & G1 & G10 & G18 & G19 & G20 & G21 & G26 & G23 &
     (jsv & jw & LC0 & LC1) & WV & WP & IL & ILW & JN & MP).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & GR2 & GR3 & GR4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  pose proof HLR as (L8 & L9 & L22 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  pose proof (it_SEGS B API LS SH SK ra empty FG) as SEGS.
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof (it_TS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as TS.
  pose proof (it_errno B API LS SH SK ra empty FG) as EV.
  pose proof alloc_ceiling_val as AC.
  assert (SP : spZ regs = FB) by exact (it_spz B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2 regs GR2).
  pose proof (it_cmd B API LS SH SK ra empty S rg mem0 md0 L0 A0 FG fx L A regs mem md HCF) as CMD.
  assert (PREK : call_pre_k B (aa_MR (API rc)) CHECK_WORDS_K L A regs mem md).
  { apply (it_pre B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md CHECK_WORDS_K HCF).
    - rewrite G1. apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    - unfold CHECK_WORDS_K, ALLOC_STACK, SLOT_STACK. lia. }
  assert (QOUT : outside B L A CHECK_WORDS_K regs VerbsB.G_QUIT 4).
  { intros i Hi. split.
    - apply (it_GNOWN B API LS SH SK ra empty FG fx L A mem md _ M). apply se_g_of. unfold VerbsB.G_QUIT. lia.
    - unfold scratch_k. rewrite SP, EV.
      unfold SlotInv.FB, SLOT_STACK, VerbsB.G_QUIT, CHECK_WORDS_K, ALLOC_STACK in *. lia. }
  assert (OWN : forall i, 0 <= i < CHECK_WORDS_FRAME -> ~ owned B L A (spZ regs - i - 1)).
  { intros i Hi Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L A mem md _ M Ho).
    rewrite SP in *. unfold SlotInv.FB, SLOT_STACK, CHECK_WORDS_FRAME in *. lia. }
  assert (RSL : forall pn, In pn O -> 0 <= snd pn <= LMAX + 2).
  { intros pn Hin. pose proof (it_rec_blk rsegs L A mem R1 O pn REP Hin). lia. }
  assert (XS : forall pn, In pn [(text, kt); (copy, kc); (arr, ka)] -> 0 <= snd pn <= 2 ^ 16).
  { intros pn [<-|[<-|[<-|[]]]]; cbn [snd]; lia. }
  pose proof (cw_join_need_nonneg (hwords (m_D p0 pl p n))) as JN0.
  assert (ROOM : room_slots (SlotInv.tb A) (join_need (hwords (m_D p0 pl p n)) + 1)).
  { pose proof (it_tb_range L A Wf) as [T1 T2].
    apply (it_room B API LS SH SK ra empty rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A mem md O
             [(text, kt); (copy, kc); (arr, ka)] M Wf EB BLK HOL RSL ltac:(cbn; lia) XS).
    - reflexivity.
    - unfold SlotInv.tb. cbn. lia.
    - unfold SlotInv.tb. cbn. lia.
    - lia. }
  pose proof MP as MP'. unfold msg_props in MP'. cbv zeta in MP'. rewrite EVR in MP'. cbv beta iota in MP'.
  destruct MP' as (_ & _ & _ & _ & _ & _ & _ & WPR & _ & _).
  pose proof (CWC fx) as K. unfold check_words_contract in K.
  specialize (K L A regs mem md (SlotInv.tb A) (FB + 40) arr (qv quit) wp (hwords (m_D p0 pl p n)) R1 O).
  rewrite SEGS in K.
  specialize (K eq_refl PREK ltac:(rewrite SP; unfold SlotInv.FB; lia) CMD FZ
    (send_message.sm_le_of_bytes B mem _ _ SEGS QB) QOUT G10 WV WP ltac:(rewrite SP; lia)
    ltac:(unfold SlotInv.FB; lia) ltac:(lia) REP OWN (SlotInv.res_tb L A Wf HRC) ROOM WPR).
  unfold CHECK_WORDS in K.
  eapply SR_bind; [exact K|]. clear K.
  intros c1 (fx1 & L1 & A1 & regs1 & mem1 & md1 & -> & FZ1 & POST & EQB & KEPT1 & INIT1 & RGN1 & CMD1 & QL1 & REP1 &
    WV1 & RES1).
  destruct POST as (M1 & W1 & Bd1 & LLE1 & PA1 & PRES & (vm1 & Hmd1) & FRAME & BYTES & SCRW).
  pose proof CMD1 as (RO1 & GI1 & _). rewrite SEGS in RO1.
  pose proof FRAME as FRAMEr. rewrite SEGS in FRAMEr.
  apply SR_ret.
  assert (EB1 : SlotInv.eblocks mem0 L0 A0 L1 A1 mem1).
  { intros a k Hin. destruct (EB a k Hin) as [Hb Hk]. split.
    - rewrite EQB. exact Hb.
    - intros i Hi. rewrite <- (Hk i Hi).
      pose proof (KEPT1 a k i Hb (fun H : False => H) Hi) as KK. rewrite SEGS in KK. exact KK. }
  assert (CF1 : CF fx1 L1 A1 regs1 mem1 md1).
  { apply (it_cf_call B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx fx1 CHECK_WORDS_K
             L A regs mem md (fun _ => False) L1 A1 regs1 mem1 md1 regs1 HCF M1 W1 Bd1 (INIT1 I) PRES
             (ex_intro _ vm1 Hmd1)).
    - exact FRAME.
    - exact SCRW.
    - unfold SlotInv.FB, CHECK_WORDS_K, ALLOC_STACK, SLOT_STACK. lia.
    - unfold CHECK_WORDS_K, ALLOC_STACK. lia.
    - intros a [].
    - exact RO1.
    - exact GI1.
    - exact EB1.
    - exact FZ1.
    - intros r. reflexivity. }
  assert (LC0' : rw_cells rsegs mem1 FB (LOC0 jsv)).
  { apply (it_frame_cells B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx
             L A regs mem md CHECK_WORDS_K (fun _ => False) L1 A1 mem1 md1 FB _ HCF M1 FRAMEr).
    - intros a [].
    - lia.
    - unfold LOC0. cbn. lia.
    - exact LC0. }
  assert (LC1' : rw_cells rsegs mem1 (FB + 40) [CB 32 jw]).
  { apply (it_frame_cells B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx
             L A regs mem md CHECK_WORDS_K (fun _ => False) L1 A1 mem1 md1 (FB + 40) _ HCF M1 FRAMEr).
    - intros a [].
    - lia.
    - cbn. lia.
    - exact LC1. }
  assert (RX1 : RFX L0 A0 L1 A1 mem1 R1 O (qv quit) [(text, kt); (copy, kc); (arr, ka)]).
  { unfold RFX. split; [exact REP1|]. split; [exact SPILL|].
    split.
    { apply (send_message.sm_bytes_of_le B mem1 _ _ SEGS); [unfold G_QUIT; lia | rewrite length_le4; unfold G_QUIT; lia |].
      exact QL1. }
    split; [exact Hq|]. split; [exact ENO|].
    split; [rewrite EQB; exact BLK|].
    split; [rewrite EQB; exact XC|].
    exact HOL. }
  assert (WP1 : words_place L1 A1 mem1 arr wp (hwords (m_D p0 pl p n)))
    by (unfold words_place, in_block in *; rewrite EQB; exact WP).
  assert (IL1 : in_live L1 A1 O arr (8 * Z.of_nat (length (hwords (m_D p0 pl p n)))))
    by (unfold in_live in *; rewrite EQB; exact IL).
  assert (ILW1 : forall k, (k < length (hwords (m_D p0 pl p n)))%nat ->
     in_live L1 A1 O (nth k wp 0) (Z.of_nat (length (nth k (hwords (m_D p0 pl p n)) [])) + 1)).
  { intros k Hk. pose proof (ILW k Hk) as H. unfold in_live in *. rewrite EQB. exact H. }
  exists fx1, L1, A1, regs1, mem1, md1, O, R1, x, quit, text, copy, arr, kt, kc, ka, wp.
  split; [rewrite G1; reflexivity|].
  split; [exact CF1|].
  split; [exists (sb_free (sb_malloc (SlotInv.tb A) (join_need (hwords (m_D p0 pl p n)) + 1))
                   (join_need (hwords (m_D p0 pl p n)) + 1)); split; [exact RES1 | reflexivity]|].
  split; [exact EVR|].
  split; [exact DCL|].
  split; [exact HSB|]. split; [exact HHB|].
  split; [exact RX1|].
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|].
  split; [exact Hkt|]. split; [exact Hkc|]. split; [exact Hka|].
  split.
  { unfold LR.
    split; [cw_pres PRES L8 8|]. split; [cw_pres PRES L9 9|]. split; [cw_pres PRES L22 22|].
    split; [cw_pres PRES L24 24|]. split; [cw_pres PRES L25 25|]. split; [cw_pres PRES L27 27|]. lia. }
  split; [cw_pres PRES G18 18|].
  split; [cw_pres PRES G19 19|].
  split; [cw_pres PRES G20 20|].
  split; [cw_pres PRES G21 21|].
  split; [cw_pres PRES G26 26|].
  split; [cw_pres PRES G23 23|].
  split; [exists jsv, jw; split; [exact LC0' | exact LC1']|].
  split; [exact WV1|].
  split; [exact WP1|].
  split; [exact IL1|].
  split; [exact ILW1|].
  split; [exact JN|].
  exact MP.
Qed.

End CW.
