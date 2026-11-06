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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/SlotItB3q.v; 167 of its 205 lines of code are new or changed and 395 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SlotItA joined_c check_round_trip_c SlotItC0 SlotItD0 SlotItE.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Slot SlotInv SlotRec RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* Segment (d2) of one loop iteration: from check_refusal's return (pc 0x14398, stCR) through check_round_trip's
   call (a0 = &w at FB + 24, a1 = s2, a2 = s3) to its return (pc 0x143a8, stD). *)

Section D2.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : CF.Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (CF.SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (CF.SlotInv.FB S).

Lemma seg_d2 : (forall fx : FPState, @check_round_trip_contract fx rc B (API rc)) -> forall m p n R0 c,
  stCR B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (fun c' => exists kt kc ka text copy arr,
    stD B API S rg mem0 md0 L0 A0 p0 n0 pl m p n kt kc ka text copy arr c').
Proof.
  intros CRT m p n R0 c
    (fx & L & A & regs & mem & md & O & R1 & x & quit & text & copy & arr & kt & kc & ka & wp & jw & -> & HCF & HRC &
     EVR & DCL & HSB & HHB & HRX & D1 & D2 & D3 & Hkt & Hkc & Hka & AL8 & HLR & G18 & G19 & LC0 & LC1 & WV & WP & IL &
     ILW & JN & MP).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & GR2 & GR3 & GR4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  pose proof HLR as (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  pose proof (it_SEGS B API LS SH SK ra empty FG) as SEGS.
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof (it_TS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as TS.
  pose proof (it_errno B API LS SH SK ra empty FG) as EV.
  pose proof alloc_ceiling_val as AC.
  assert (SPV : bv_unsigned (reg_get regs 2) = FB).
  { change (reg_get regs 2) with (getr regs 2). rewrite GR2. apply unsigned_lit.
    unfold CF.SlotInv.FB, SLOT_STACK in *. lia. }
  destruct (it_model B API S rg mem0 md0 L0 A0 fx L A regs mem md HCF) as [Hh Hl].
  assert (HTR : TR p0 pl m p n regs)
    by exact (conj L8 (conj L9 (conj L23 (conj L22 (conj L26 (conj L24 (conj L25 L27))))))).
  pose proof (it_S16 B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as S16.
  (* 0x14398 .. check_round_trip's entry *)
  eapply (@sr_raw fx regs (Z_to_bv 64 0x14398) mem md _ _ Hh Hl).
  { unfold Regs6ss.mkR_of. apply run_g_crt_ok. rewrite SPV. unfold CF.SlotInv.FB, SLOT_STACK in *. lia. }
  { intros s0 ->. do 5 eexists. reflexivity. }
  intros Rg1 F1 pc1 fc1 m1 regs1 E GR1. injection E as -> -> -> -> ->.
  assert (P1 : regs_preserved regs regs1) by (eapply pres_mkR; exact GR1).
  pose proof (TR_pres p0 pl m p n regs regs1 HTR P1) as HTR1.
  pose proof (ie_cf_regs B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx (mkFP fp_regs fp_csr)
    L A regs mem md regs1 HCF
    (P1 2 ltac:(unfold callee_saved; lia)) (P1 3 ltac:(unfold callee_saved; lia)) (P1 4 ltac:(unfold callee_saved; lia))
    FZ) as CF1.
  assert (G1' : getr regs1 1 = Z_to_bv 64 0x143a8) by (rewrite GR1; reflexivity).
  assert (G10' : getr regs1 10 = Z_to_bv 64 (FB + 24)).
  { transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + 24)); [rewrite GR1; reflexivity|]. rewrite SPV.
    reflexivity. }
  assert (G11' : getr regs1 11 = Z_to_bv 64 (r_state R0)).
  { transitivity (reg_get regs 18); [rewrite GR1; reflexivity | exact G18]. }
  assert (G12' : getr regs1 12 = Z_to_bv 64 (r_host R0)).
  { transitivity (reg_get regs 19); [rewrite GR1; reflexivity | exact G19]. }
  assert (SP1 : spZ regs1 = FB).
  { apply (it_spz B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2 regs1).
    exact (eq_trans (P1 2 ltac:(unfold callee_saved; lia)) GR2). }
  pose proof (it_cmd B API LS SH SK ra empty S rg mem0 md0 L0 A0 FG fx L A regs mem md HCF) as CMD.
  destruct (it_vrt B API LS SH SK ra empty FG fx L A mem md M GIm) as (can & VT).
  assert (PREK : call_pre_t B (API rc) CRT_K L A regs1 mem md).
  { split.
    - apply (it_pre B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 (mkFP fp_regs fp_csr)
               L A regs1 mem md CRT_K CF1).
      + rewrite G1'. apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
      + unfold CRT_K, CRT_FRAME, SM_K, SEND_MESSAGE_FRAME, VR_K, SLOT_STACK. lia.
    - rewrite SP1. unfold CF.SlotInv.FB. lia. }
  assert (QOUT : outside B L A CRT_K regs1 VerbsB.G_QUIT 4).
  { intros i Hi. split.
    - apply (it_GNOWN B API LS SH SK ra empty FG fx L A mem md _ M). apply se_g_of. unfold VerbsB.G_QUIT. lia.
    - unfold scratch_k. rewrite SP1, EV.
      unfold CF.SlotInv.FB, SLOT_STACK, VerbsB.G_QUIT, CRT_K, CRT_FRAME, SM_K, SEND_MESSAGE_FRAME, VR_K in *. lia. }
  assert (RSL : forall pn, In pn O -> 0 <= snd pn <= LMAX + 2).
  { intros pn Hin. pose proof (it_rec_blk rsegs L A mem R1 O pn REP Hin). lia. }
  assert (XS : forall pn, In pn [(text, kt); (copy, kc); (arr, ka)] -> 0 <= snd pn <= 2 ^ 16).
  { intros pn [<-|[<-|[<-|[]]]]; cbn [snd]; lia. }
  assert (ROOM : room_ag (sb_up (CF.SlotInv.tb A) CRT_PEAK CRT_PEAKB) VR_REQ).
  { pose proof (it_tb_range L A Wf) as [T1 T2].
    apply (it_room B API LS SH SK ra empty rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A mem md O
             [(text, kt); (copy, kc); (arr, ka)] M Wf EB BLK HOL RSL ltac:(cbn; lia) XS).
    - reflexivity.
    - unfold sb_up, CF.SlotInv.tb, CRT_PEAK, SM_PEAK. cbn. lia.
    - unfold sb_up, CF.SlotInv.tb, CRT_PEAKB. cbn. lia.
    - unfold VR_REQ. lia. }
  pose proof (CF.SlotRec.vr_keep R0 (m_D p0 pl p n)) as VK. rewrite EVR in VK. destruct VK as (VK1 & VK2 & VK3).
  assert (DCL1 : r_refuse R1 <> 0 -> declared (r_code R1) = true) by (rewrite VK1, VK2; exact DCL).
  assert (EVRp : OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_c.vr_run (rec_clear R0)
    (m_D p0 pl p n) = (R1, x, quit)) by exact EVR.
  pose proof MP as MP'. unfold msg_props in MP'. cbv zeta in MP'. rewrite EVRp in MP'. cbv beta iota in MP'.
  destruct MP' as (_ & RR & N0 & _ & _ & _ & _ & _ & _ & RT).
  pose proof (CRT (mkFP fp_regs fp_csr)) as K. unfold check_round_trip_contract in K.
  specialize (K L A regs1 mem md (CF.SlotInv.tb A) (FB + 24) arr (r_state R0) (r_host R0) (qv quit) wp
    (hwords (m_D p0 pl p n)) R1 O can).
  rewrite SEGS in K.
  specialize (K eq_refl PREK CMD FZ G10' G11' G12' HSB HHB WV WP ltac:(unfold CF.SlotInv.FB in *; lia) AL8
    ltac:(rewrite SP1; lia)
    ltac:(unfold CF.SlotInv.FB in *; lia) JN IL ILW REP DCL1 (fun _ => ex_intro _ x (conj RR N0)) Hq
    (CF.send_message.sm_le_of_bytes B mem _ _ SEGS QB)
    (fun i Hi => CF.SlotRec.g_writable mem (VerbsB.G_QUIT + i) ltac:(unfold VerbsB.G_QUIT; lia)) QOUT VT
    (CF.SlotInv.res_tb L A Wf HRC) ROOM RT).
  unfold CHECK_ROUND_TRIP in K.
  eapply SR_bind; [exact K|]. clear K.
  intros c1 (fx1 & L1 & A1 & regs2 & mem1 & md1 & Rr & O1 & b1 & -> & FZ1 & RGN1 & POST & CMD1 & REP1 & RF2 & RC2 &
    SP2 & ST2 & HO2 & QL1 & WV1 & WP1 & BLK1 & STAY1 & KEPT1 & INIT1 & NOTO1 & (can1 & VT1) & RES1 & CAP1).
  destruct POST as (M1 & W1 & Bd1 & LLE1 & PA1 & PRES & (vm1 & Hmd1) & FRAME & BYTES & SCRW).
  destruct (CF.SlotRec.rep_dedup rsegs L1 A1 mem1 Rr O1 REP1) as (O2 & O2E & O2L & REP2).
  pose proof CMD1 as (RO1 & GI1 & _). rewrite SEGS in RO1.
  pose proof FRAME as FRAMEr. rewrite SEGS in FRAMEr.
  apply SR_ret.
  assert (EB1 : CF.SlotInv.eblocks mem0 L0 A0 L1 A1 mem1).
  { intros a k Hin. destruct (EB a k Hin) as [Hb Hk]. split.
    - exact (STAY1 (a, k) Hb (ENO a k Hin)).
    - intros i Hi. rewrite <- (Hk i Hi).
      assert (NOB : ~ owned_by O a).
      { intros (k' & Hk'). apply (ENO a k Hin). apply in_map_iff. exists (a, k'). split; [reflexivity | exact Hk']. }
      pose proof (KEPT1 a k i Hb NOB Hi) as KK. rewrite SEGS in KK. exact KK. }
  assert (CF2 : CF fx1 L1 A1 regs2 mem1 md1).
  { apply (it_cf_call B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 (mkFP fp_regs fp_csr) fx1 CRT_K
             L A regs1 mem md vr_writes L1 A1 regs2 mem1 md1 regs2 CF1 M1 W1 Bd1 (INIT1 I) PRES (ex_intro _ vm1 Hmd1)).
    - exact FRAME.
    - exact SCRW.
    - unfold CF.SlotInv.FB, CRT_K, CRT_FRAME, SM_K, SEND_MESSAGE_FRAME, VR_K, SLOT_STACK. lia.
    - unfold CRT_K, CRT_FRAME, SM_K, SEND_MESSAGE_FRAME, VR_K. lia.
    - intros a Ha. left. apply se_g_of. exact (it_vrw_G a Ha).
    - exact RO1.
    - exact GI1.
    - exact EB1.
    - exact FZ1.
    - intros r. reflexivity. }
  pose proof (TR_pres p0 pl m p n regs1 regs2 HTR1 PRES) as HTR2.
  assert (LC0' : rw_cells rsegs mem1 FB (LOC1 (n - hdr_n n))).
  { apply (it_frame_cells B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 (mkFP fp_regs fp_csr)
             L A regs1 mem md CRT_K vr_writes L1 A1 mem1 md1 FB _ CF1 M1 FRAMEr).
    - intros a Ha. pose proof (it_vrw_G a Ha). lia.
    - lia.
    - unfold LOC1. cbn. lia.
    - exact LC0. }
  assert (LC1' : rw_cells rsegs mem1 (FB + 24)
    [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 8 jw]).
  { apply (it_frame_cells B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 (mkFP fp_regs fp_csr)
             L A regs1 mem md CRT_K vr_writes L1 A1 mem1 md1 (FB + 24) _ CF1 M1 FRAMEr).
    - intros a Ha. pose proof (it_vrw_G a Ha). lia.
    - lia.
    - cbn. lia.
    - exact LC1. }
  assert (RX2 : RFX L0 A0 L1 A1 mem1 Rr O2 (qv quit) [(text, kt); (copy, kc); (arr, ka)]).
  { unfold RFX. split; [exact REP2|]. split; [rewrite SP2; exact SPILL|].
    split.
    { apply (CF.send_message.sm_bytes_of_le B mem1 _ _ SEGS); [unfold G_QUIT; lia | rewrite length_le4; unfold G_QUIT; lia |].
      exact QL1. }
    split; [exact Hq|].
    split.
    { intros a k Hin Ha. apply in_map_iff in Ha as ([a' k'] & Ea & Hk'). cbn in Ea. subst a'.
      apply O2E in Hk'. destruct (it_rec_blk rsegs L1 A1 mem1 Rr O1 (a, k') REP1 Hk') as [Hb' _].
      destruct (EB1 a k Hin) as [Hb1 _].
      pose proof (it_fst_eq _ a k k' (it_fst_nodup B API LS SH SK ra empty FG fx1 L1 A1 mem1 md1 M1) Hb1 Hb') as Ek.
      subst k'.
      destruct (EB a k Hin) as [Hb _].
      exact (NOTO1 (a, k) Hb (ENO a k Hin) Hk'). }
    split.
    { intros pn Hpb. destruct (BLK1 pn Hpb) as [[Hp1 Hn1]|Hp1].
      - destruct (BLK pn Hp1) as [H|[H|H]]; [left; exact H | contradiction | right; right; exact H].
      - right. left. apply O2E. exact Hp1. }
    split.
    { intros [a k] HpX. destruct (XC (a, k) HpX) as (Hb & H0 & HO).
      split; [exact (STAY1 (a, k) Hb HO)|]. split; [exact H0|].
      intros Ha. apply in_map_iff in Ha as ([a' k'] & Ea & Hk'). cbn in Ea. subst a'.
      apply O2E in Hk'. destruct (it_rec_blk rsegs L1 A1 mem1 Rr O1 (a, k') REP1 Hk') as [Hb' _].
      pose proof (it_fst_eq _ a k k' (it_fst_nodup B API LS SH SK ra empty FG fx1 L1 A1 mem1 md1 M1)
        (STAY1 (a, k) Hb HO) Hb') as Ek.
      subst k'. exact (NOTO1 (a, k) Hb HO Hk'). }
    unfold CF.SlotInv.O_MAX. exact O2L. }
  exists kt, kc, ka, text, copy, arr.
  exists fx1, L1, A1, regs2, mem1, md1, Rr, O2, (qv quit), jw.
  split; [rewrite G1'; reflexivity|].
  split; [exact CF2|].
  split; [exists b1; split; [exact RES1 | rewrite CAP1; reflexivity]|].
  split; [exact RX2|].
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|].
  split; [exact HTR2|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact LC0' | exact LC1'].
Qed.

End D2.
