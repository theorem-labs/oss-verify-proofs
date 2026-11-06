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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/SlotItB3q.v; 359 of its 400 lines of code are new or changed and 392 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SlotItA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Slot SlotInv SlotRec RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* After the round-trip check (pc 0x143a8): the three frees of the message's blocks (text, copy, the pointer array),
   then the loop tail: the next loop head (message m + 1) or the entry of the last rec_clear. *)

Section Raw.
Context {fx : FPState}.

(* A Kind A run on the memory itself (no normalization): the memory after it is the run's. *)
Lemma sr_raw : forall regs pc mem md (P : config -> Prop) (Q : machine_state -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall s0, Q s0 -> exists R F' pc' fc' m0, s0 = MS R F' pc' fc' None m0 (seg_rom rsegs)) ->
  (forall R F' pc' fc' m0 regs', Q (MS R F' pc' fc' None m0 (seg_rom rsegs)) -> (forall r, getr regs' r = getr R r) ->
     SR rsegs (mkCfg (@mkst (mkFP F' fc') regs' pc' m0 (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md P Q Hh Hl EV SHAPE K.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. exact EV. }
  intros ms' (can & Q0 & EQ).
  destruct (SHAPE can Q0) as (R & F' & pc' & fc' & m0 & ->).
  destruct (CF.RecAnsB.eqv_mkst_fx R F' pc' fc' m0 (seg_rom rsegs) ms' EQ) as (R' & -> & X).
  apply (K R F' pc' fc' m0 R' Q0).
  intros r. exact (KindBGlue.kb_getr_eqv R R' X r).
Qed.

End Raw.

Section E.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : CF.Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (CF.SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (CF.SlotInv.FB S).

(* The recorder facts across a call that keeps G's bytes and the recorder's blocks. *)
Lemma it_rfx_move : forall L A mem R O q X L' A' mem' X',
  RFX L0 A0 L A mem R O q X ->
  (forall a, 0x33ff0 <= a < 0x343ec ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a -> writable_at rsegs mem' a)) ->
  (forall p k i, In (p, k) O -> 0 <= i < k -> mbyte rsegs mem' (p + i) = mbyte rsegs mem (p + i)) ->
  (forall pn, In pn O -> In pn (blocks L' A')) ->
  (forall pn, In pn (blocks L' A') -> In pn (blocks L0 A0) \/ In pn O \/ In pn X') ->
  (forall pn, In pn X' -> In pn (blocks L' A') /\ ~ In pn (blocks L0 A0) /\ ~ In (fst pn) (map fst O)) ->
  RFX L0 A0 L' A' mem' R O q X'.
Proof.
  intros L A mem R O q X L' A' mem' X' (REP & SP & QB & Hq & ENO & _ & _ & HOL) KG KB KL HB HX.
  refine (conj _ (conj SP (conj _ (conj Hq (conj ENO (conj HB (conj HX HOL))))))).
  - apply (rec_rep_frame rsegs RecInvU.G_REC RecInvU.REC_SC L A mem R O L' A' mem' REP); [|exact KB|exact KL].
    intros a Ha. apply KG. unfold RecInvU.G_REC, REC_SIZE, RecInvU.REC_SC, SC_SIZE in Ha. lia.
  - apply (KindB.bytes_at_transfer rsegs mem mem' _ _ QB). intros i Hi. rewrite length_le4 in Hi.
    apply KG. unfold CommandModel.G_QUIT. lia.
Qed.

(* free of the message's block pn (first of X) at the frame base, returning to ret. *)
Lemma ie_free : forall fx L A regs mem md R O q X pn ret (K : config -> Prop),
  CF fx L A regs mem md -> CF.SlotInv.rcap A -> RFX L0 A0 L A mem R O q (pn :: X) -> ~ In (fst pn) (map fst X) ->
  getr regs 10 = Z_to_bv 64 (fst pn) -> getr regs 1 = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
  (forall fx' L' A' regs' mem' md', CF fx' L' A' regs' mem' md' -> CF.SlotInv.rcap A' -> RFX L0 A0 L' A' mem' R O q X ->
     regs_preserved regs regs' ->
     (forall a cs, FB <= a -> a + Z.of_nat (cells_size cs) <= FB + 56 -> rw_cells rsegs mem a cs ->
        rw_cells rsegs mem' a cs) ->
     SR rsegs (mkCfg (@mkst fx' regs' (Z_to_bv 64 ret) mem' (seg_rom rsegs)) md') K) ->
  SR rsegs (mkCfg (@mkst fx regs (Z_to_bv 64 0x18ad0) mem (seg_rom rsegs)) md) K.
Proof.
  intros fx L A regs mem md R O q X pn ret K HCF HRC HRX NX G10 G1 Hr2 Hr KC.
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  assert (SEGS : ms_segs B = rsegs) by (eapply it_SEGS; eassumption).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof alloc_ceiling_val as AC.
  assert (SP : spZ regs = FB) by (eapply it_spz; eassumption).
  assert (EV : errno_addr B = 0x3441c) by (eapply it_errno; eassumption).
  destruct (it_FA B API LS SH SK ra empty FG fx)
    as (_ & FREE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & GNOWN & RNOWN).
  pose proof FG as FG'. fg_destruct FG'.
  destruct (XC pn (or_introl eq_refl)) as (PB & PN0 & PNO).
  destruct pn as [t k]. cbn [fst snd] in *.
  pose proof PB as PB'. unfold blocks in PB'. apply in_map_iff in PB' as ([pt k'] & Et & Hpt).
  cbn [fst snd] in Et. injection Et as Et Ek. subst k' t.
  assert (PREC : call_pre B (aa_MR (API rc)) L A regs mem md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR (API rc)) L A regs mem md)).
    apply (it_pre B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md ALLOC_STACK HCF).
    - rewrite G1. apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. exact Hr2.
    - unfold ALLOC_STACK, SLOT_STACK. lia. }
  pose proof (FREE L A regs mem md pt k (CF.SlotInv.tb A) PREC ltac:(rewrite SEGS; exact RO) Hpt G10
    (CF.SlotInv.res_tb L A Wf HRC)) as FR.
  rewrite SEGS, F3 in FR.
  eapply SR_bind; [exact FR|]. clear FR.
  intros c1 (L1 & A1 & regs1 & mem1 & md1 & -> & POST & (b1 & b2 & E1 & E2) & KEPT & RO1 & GK & UK & INIT & RGN & RES1).
  apply (proj1 (call_post_k_alloc B (aa_MR (API rc)) L A regs mem md _ L1 A1 regs1 mem1 md1)) in POST.
  destruct POST as (M1 & W1 & Bd1 & LLE1 & PA1 & PRES & (vm1 & Hmd1) & FRAME & BYTES & SCRW).
  pose proof FRAME as FRAMEr. rewrite SEGS in FRAMEr.
  assert (NDB : List.NoDup (blocks L A)) by exact (it_NODUP B API LS SH SK ra empty FG fx L A mem md M).
  assert (HEi : forall a, ptr_addr L pt <= a < ptr_addr L pt + k -> ~ in_img B a /\ a < alloc_ceiling).
  { intros a Ha. destruct (it_blk_out B API LS SH SK ra empty FG fx L A mem md
      (ptr_addr L pt) k (a - ptr_addr L pt) M PB ltac:(lia)) as (_ & _ & Hc).
    split; [|lia].
    replace a with (ptr_addr L pt + (a - ptr_addr L pt)) by lia.
    exact (ax_blocks_img AX L A mem md pt k (a - ptr_addr L pt) M Hpt ltac:(lia)). }
  assert (NEQ : forall a k0, In (a, k0) (blocks L A) -> a <> ptr_addr L pt -> In (a, k0) (blocks L1 A1)).
  { intros a k0 Hin Hne. rewrite E2. rewrite E1 in Hin. apply (CF.RecAnsB.in_mid_other b1 b2 (ptr_addr L pt, k)); [exact Hin|].
    intros E. injection E as E _. exact (Hne E). }
  assert (EB1 : CF.SlotInv.eblocks mem0 L0 A0 L1 A1 mem1).
  { intros a k0 Hin. destruct (EB a k0 Hin) as [Hb Hk].
    assert (Hne : a <> ptr_addr L pt).
    { intros ->. pose proof (it_fst_eq _ _ k0 k (it_fst_nodup B API LS SH SK ra empty FG fx L A mem md M) Hb PB) as <-.
      exact (PN0 Hin). }
    split; [exact (NEQ a k0 Hb Hne)|].
    intros i Hi. rewrite <- (Hk i Hi). pose proof (KEPT a k0 i Hb Hne Hi) as KK. rewrite SEGS in KK. exact KK. }
  assert (GI1 : G_img_c B frame_RELRO mem1).
  { intros a Ha. destruct (F26 a Ha) as (Hi & Hs & Hc & He).
    destruct (FRAME a (or_intror Hi)) as [E3 _].
    - exact (RNOWN L A mem md a M Ha).
    - exact (RNOWN L1 A1 mem1 md1 a M1 Ha).
    - unfold scratch_k. rewrite SP. pose proof (KindB.in_img_low B SEGS a Hi). unfold CF.SlotInv.FB, ALLOC_STACK, SLOT_STACK in *.
      intros [Hx|Hx]; [lia | exact (He Hx)].
    - intros Hx. exact (proj1 (HEi a Hx) Hi).
    - rewrite E3. exact (GIm a Ha). }
  assert (CF1 : CF fx L1 A1 regs1 mem1 md1).
  { apply (it_cf_call B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx fx ALLOC_STACK L A regs mem md
             (fun a => ptr_addr L pt <= a < ptr_addr L pt + k) L1 A1 regs1 mem1 md1 regs1 HCF M1 W1 Bd1 (INIT I) PRES
             (ex_intro _ vm1 Hmd1) FRAME SCRW).
    - unfold CF.SlotInv.FB, ALLOC_STACK, SLOT_STACK. lia.
    - unfold ALLOC_STACK. lia.
    - intros a Ha. right. destruct (HEi a Ha) as [H1 H2]. split; [exact H2 | exact H1].
    - exact RO1.
    - exact GI1.
    - exact EB1.
    - exact FZ.
    - intros r. reflexivity. }
  assert (RX1 : RFX L0 A0 L1 A1 mem1 R O q X).
  { apply (it_rfx_move L A mem R O q ((ptr_addr L pt, k) :: X) L1 A1 mem1 X HRX).
    - intros a Ha. destruct (F25 a (se_g_of a Ha)) as (Hi & Hs & Hc & He).
      destruct (FRAMEr a (or_intror Hi)) as [E3 W3].
      + exact (GNOWN L A mem md a M (se_g_of a Ha)).
      + exact (GNOWN L1 A1 mem1 md1 a M1 (se_g_of a Ha)).
      + unfold scratch_k. rewrite SP. unfold CF.SlotInv.FB, ALLOC_STACK, SLOT_STACK in *.
        intros [Hx|Hx]; [lia | exact (He Hx)].
      + intros Hx. exact (proj1 (HEi a Hx) Hi).
      + split; [exact E3 | tauto].
    - intros p1 k1 i Hin Hi. destruct (it_rec_blk rsegs L A mem R O (p1, k1) REP Hin) as [Hb _].
      assert (Hne : p1 <> ptr_addr L pt).
      { intros ->. apply PNO. apply in_map_iff. exists (ptr_addr L pt, k1). split; [reflexivity | exact Hin]. }
      pose proof (KEPT p1 k1 i Hb Hne Hi) as KK. rewrite SEGS in KK. exact KK.
    - intros [p1 k1] Hin. destruct (it_rec_blk rsegs L A mem R O (p1, k1) REP Hin) as [Hb _].
      apply (NEQ p1 k1 Hb). intros ->. apply PNO. apply in_map_iff. exists (ptr_addr L pt, k1).
      split; [reflexivity | exact Hin].
    - intros pn Hp. rewrite E2 in Hp.
      assert (Hp0 : In pn (blocks L A)) by (rewrite E1; exact (CF.RecAnsB.in_mid_inv b1 b2 _ pn Hp)).
      destruct (BLK pn Hp0) as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | | right; right; exact H].
      exfalso. subst pn. rewrite E1 in NDB. exact (NoDup_remove_2 _ _ _ NDB Hp).
    - intros [p1 k1] Hin. destruct (XC (p1, k1) (or_intror Hin)) as (Hb & H0 & HO).
      split; [|split; [exact H0 | exact HO]].
      apply (NEQ p1 k1 Hb). intros ->. apply NX. apply in_map_iff. exists (ptr_addr L pt, k1).
      split; [reflexivity | exact Hin]. }
  rewrite G1.
  apply (KC fx L1 A1 regs1 mem1 md1 CF1).
  - exists (sb_free (CF.SlotInv.tb A) k). split; [exact RES1 | reflexivity].
  - exact RX1.
  - exact PRES.
  - intros a cs Ha Hb HC.
    apply (it_frame_cells B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx L A regs mem md
             ALLOC_STACK _ L1 A1 mem1 md1 a cs HCF M1 FRAMEr); [|exact Ha|exact Hb|exact HC].
    intros a' Ha'. exact (proj2 (HEi a' Ha')).
Qed.

(* CF with the registers changed but sp, gp, tp. *)
Lemma ie_cf_regs : forall fx fx' L A regs mem md regs', CF fx L A regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  frm_zero (@fp_csr fx') -> CF fx' L A regs' mem md.
Proof.
  intros fx fx' L A regs mem md regs' HCF H2 H3 H4 FZ.
  pose proof HCF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RO & _).
  apply (it_cf_run B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx fx' L A regs mem md [] mem regs'
           HCF (munch_refl [] mem) (wmono_refl rsegs mem) RO); [| | exact FZ | exact H2 | exact H3 | exact H4].
  - intros a _ Hx. exfalso. apply Hx. exact Logic.I.
  - intros p1 n1 i _ _ Hx. exfalso. apply Hx. exact Logic.I.
Qed.

Lemma pres_mkR : forall regs regs' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  (forall r, getr regs' r = getr (mkR x1 (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) x5 x6 x7
     (reg_get regs 8) (reg_get regs 9) x10 x11 x12 x13 x14 x15 x16 x17 (reg_get regs 18) (reg_get regs 19)
     (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
     (reg_get regs 26) (reg_get regs 27) x28 x29 x30 x31) r) ->
  regs_preserved regs regs'.
Proof.
  intros regs regs' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 GR r Hr. rewrite GR.
  unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity.
Qed.

(* The loop registers from the frees on: s0 = src, s1 = len, s7 = m, s6 = 58, s10 = &g_rec, s8 = MASK, s9 = 32,
   s11 = -1. *)
Definition TR (m p n : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 8 = Z_to_bv 64 (m_src p n) /\ getr regs 9 = Z_to_bv 64 (m_len p0 pl p n) /\
  getr regs 23 = Z_to_bv 64 m /\ getr regs 22 = Z_to_bv 64 58 /\ getr regs 26 = Z_to_bv 64 CommandModel.G_REC /\
  getr regs 24 = Z_to_bv 64 MASK /\ getr regs 25 = Z_to_bv 64 32 /\ getr regs 27 = Z_to_bv 64 (2 ^ 64 - 1).

Lemma TR_pres : forall m p n regs regs', TR m p n regs -> regs_preserved regs regs' -> TR m p n regs'.
Proof.
  intros m p n regs regs' (H8 & H9 & H23 & H22 & H26 & H24 & H25 & H27) P.
  split; [exact (eq_trans (P 8 ltac:(unfold callee_saved; lia)) H8)|].
  split; [exact (eq_trans (P 9 ltac:(unfold callee_saved; lia)) H9)|].
  split; [exact (eq_trans (P 23 ltac:(unfold callee_saved; lia)) H23)|].
  split; [exact (eq_trans (P 22 ltac:(unfold callee_saved; lia)) H22)|].
  split; [exact (eq_trans (P 26 ltac:(unfold callee_saved; lia)) H26)|].
  split; [exact (eq_trans (P 24 ltac:(unfold callee_saved; lia)) H24)|].
  split; [exact (eq_trans (P 25 ltac:(unfold callee_saved; lia)) H25)|].
  exact (eq_trans (P 27 ltac:(unfold callee_saved; lia)) H27).
Qed.

(* After the round-trip check returned (pc 0x143a8): the message's blocks text, copy and the pointer array
   (kt, kc, ka bytes) still live, their addresses at FB + 24, FB + 32, FB + 40. *)
Definition stD (m p n kt kc ka text copy arr : Z) (c : config) : Prop :=
  exists (fx : FPState) L A regs mem md R O q jw,
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x143a8) mem (seg_rom rsegs)) md /\
    CF fx L A regs mem md /\ CF.SlotInv.rcap A /\
    RFX L0 A0 L A mem R O q [(text, kt); (copy, kc); (arr, ka)] /\
    text <> copy /\ text <> arr /\ copy <> arr /\
    TR m p n regs /\
    0 <= m <= 31 /\ 0 < n /\ p0 <= p /\ p + n = p0 + n0 /\
    rw_cells rsegs mem FB (LOC1 (n - hdr_n n)) /\
    rw_cells rsegs mem (FB + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 8 jw].

Lemma ie_tail : forall m p n kt kc ka text copy arr c, stD m p n kt kc ka text copy arr c ->
  SR rsegs c (fun c' => exit_at B (API rc) S rg mem0 md0 L0 A0 c' \/
                        head_at B (API rc) S rg mem0 md0 L0 A0 p0 n0 (m + 1) c').
Proof.
  intros m p n kt kc ka text copy arr c
    (fx & L & A & regs & mem & md & R & O & q & jw & -> & HCF & HRC & HRX & D1 & D2 & D3 & HTR & Hm & Hn & Hp &
     Hpn & LC0 & LC1).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  pose proof alloc_ceiling_val as AC.
  assert (Hn0 : 0 < n0) by lia.
  destruct (it_inblk B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0)
    as (_ & _ & Hp04 & Hpac & HL & _).
  pose proof (m_len_range p0 pl p n Hn) as [HL1 HL2].
  pose proof HCF as (_ & _ & _ & _ & _ & R2 & _ & _ & _ & _ & _ & _ & _ & _ & FZ).
  destruct (it_model B API S rg mem0 md0 L0 A0 fx L A regs mem md HCF) as [Hh Hl].
  assert (SPV : forall regs', getr regs' 2 = getr regs 2 -> bv_unsigned (reg_get regs' 2) = FB).
  { intros regs' E. change (reg_get regs' 2) with (getr regs' 2). rewrite E, R2. apply unsigned_lit.
    unfold CF.SlotInv.FB, SLOT_STACK in *. lia. }
  assert (W3 : forall mm, rw_cells rsegs mm (FB + 24)
      [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 8 jw] ->
      rw_cells rsegs mm (FB + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr)]).
  { intros mm H.
    change [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 8 jw] with
      ([C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr)] ++ [CB 8 jw]) in H.
    exact (proj1 (sr_app_split _ _ _ _ H)). }
  (* free text *)
  eapply (@sr_raw fx regs (Z_to_bv 64 0x143a8) mem md _ _ Hh Hl).
  { unfold Regs6ss.mkR_of. eapply run_g_f1_ok.
    - rewrite (SPV regs eq_refl). unfold CF.SlotInv.FB, SLOT_STACK, IMG_END in *. lia.
    - rewrite (SPV regs eq_refl). unfold CF.SlotInv.FB in *. lia.
    - rewrite (SPV regs eq_refl). exact (W3 mem LC1). }
  { intros s0 ->. do 5 eexists. reflexivity. }
  intros R1 F1 pc1 fc1 m1 regs1 E GR1. injection E as -> -> -> -> ->.
  assert (P1 : regs_preserved regs regs1) by (eapply pres_mkR; exact GR1).
  pose proof (TR_pres _ _ _ _ _ HTR P1) as HTR1.
  pose proof (ie_cf_regs fx (mkFP fp_regs fp_csr) L A regs mem md regs1 HCF
    (P1 2 ltac:(unfold callee_saved; lia)) (P1 3 ltac:(unfold callee_saved; lia)) (P1 4 ltac:(unfold callee_saved; lia))
    FZ) as CF1.
  apply (ie_free (mkFP fp_regs fp_csr) L A regs1 mem md R O q [(copy, kc); (arr, ka)]
           (text, kt) 0x143b0 _ CF1 HRC HRX).
  { cbn. intros [E|[E|[]]]; congruence. }
  { rewrite GR1. reflexivity. }
  { rewrite GR1. reflexivity. }
  { reflexivity. }
  { lia. }
  intros fx2 L2 A2 regs2 mem2 md2 CF2 RC2 RX2 PR2 CK2.
  pose proof (TR_pres _ _ _ _ _ HTR1 PR2) as HTR2.
  assert (P12 : getr regs2 2 = getr regs 2).
  { exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) (P1 2 ltac:(unfold callee_saved; lia))). }
  pose proof CF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FZ2).
  destruct (it_model B API S rg mem0 md0 L0 A0 fx2 L2 A2 regs2 mem2 md2 CF2) as [Hh2 Hl2].
  assert (LC0b : rw_cells rsegs mem2 FB (LOC1 (n - hdr_n n))) by (apply CK2; [lia | unfold LOC1; cbn; lia | exact LC0]).
  assert (LC1b : rw_cells rsegs mem2 (FB + 24)
      [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 8 jw])
    by (apply CK2; [lia | cbn; lia | exact LC1]).
  (* free copy *)
  eapply (@sr_raw fx2 regs2 (Z_to_bv 64 0x143b0) mem2 md2 _ _ Hh2 Hl2).
  { unfold Regs6ss.mkR_of. eapply run_g_f2_ok.
    - rewrite (SPV regs2 P12). unfold CF.SlotInv.FB, SLOT_STACK, IMG_END in *. lia.
    - rewrite (SPV regs2 P12). unfold CF.SlotInv.FB in *. lia.
    - rewrite (SPV regs2 P12). exact (W3 mem2 LC1b). }
  { intros s0 ->. do 5 eexists. reflexivity. }
  intros R3 F3 pc3 fc3 m3 regs3 E GR3. injection E as -> -> -> -> ->.
  assert (P3 : regs_preserved regs2 regs3) by (eapply pres_mkR; exact GR3).
  pose proof (TR_pres _ _ _ _ _ HTR2 P3) as HTR3.
  pose proof (ie_cf_regs fx2 (mkFP fp_regs fp_csr) L2 A2 regs2 mem2 md2 regs3 CF2
    (P3 2 ltac:(unfold callee_saved; lia)) (P3 3 ltac:(unfold callee_saved; lia)) (P3 4 ltac:(unfold callee_saved; lia))
    FZ2) as CF3.
  apply (ie_free (mkFP fp_regs fp_csr) L2 A2 regs3 mem2 md2 R O q [(arr, ka)]
           (copy, kc) 0x143b8 _ CF3 RC2 RX2).
  { cbn. intros [E|[]]; congruence. }
  { rewrite GR3. reflexivity. }
  { rewrite GR3. reflexivity. }
  { reflexivity. }
  { lia. }
  intros fx4 L4 A4 regs4 mem4 md4 CF4 RC4 RX4 PR4 CK4.
  pose proof (TR_pres _ _ _ _ _ HTR3 PR4) as HTR4.
  assert (P14 : getr regs4 2 = getr regs 2).
  { exact (eq_trans (PR4 2 ltac:(unfold callee_saved; lia)) (eq_trans (P3 2 ltac:(unfold callee_saved; lia)) P12)). }
  pose proof CF4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FZ4).
  destruct (it_model B API S rg mem0 md0 L0 A0 fx4 L4 A4 regs4 mem4 md4 CF4) as [Hh4 Hl4].
  assert (LC0c : rw_cells rsegs mem4 FB (LOC1 (n - hdr_n n))) by (apply CK4; [lia | unfold LOC1; cbn; lia | exact LC0b]).
  assert (LC1c : rw_cells rsegs mem4 (FB + 24)
      [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 8 jw])
    by (apply CK4; [lia | cbn; lia | exact LC1b]).
  (* free the pointer array *)
  eapply (@sr_raw fx4 regs4 (Z_to_bv 64 0x143b8) mem4 md4 _ _ Hh4 Hl4).
  { unfold Regs6ss.mkR_of. eapply run_g_f3_ok.
    - rewrite (SPV regs4 P14). unfold CF.SlotInv.FB, SLOT_STACK, IMG_END in *. lia.
    - rewrite (SPV regs4 P14). unfold CF.SlotInv.FB in *. lia.
    - rewrite (SPV regs4 P14). exact (W3 mem4 LC1c). }
  { intros s0 ->. do 5 eexists. reflexivity. }
  intros R5 F5 pc5 fc5 m5 regs5 E GR5. injection E as -> -> -> -> ->.
  assert (P5 : regs_preserved regs4 regs5) by (eapply pres_mkR; exact GR5).
  pose proof (TR_pres _ _ _ _ _ HTR4 P5) as HTR5.
  pose proof (ie_cf_regs fx4 (mkFP fp_regs fp_csr) L4 A4 regs4 mem4 md4 regs5 CF4
    (P5 2 ltac:(unfold callee_saved; lia)) (P5 3 ltac:(unfold callee_saved; lia)) (P5 4 ltac:(unfold callee_saved; lia))
    FZ4) as CF5.
  apply (ie_free (mkFP fp_regs fp_csr) L4 A4 regs5 mem4 md4 R O q [] (arr, ka) 0x143c0 _ CF5 RC4 RX4).
  { cbn. tauto. }
  { rewrite GR5. reflexivity. }
  { rewrite GR5. reflexivity. }
  { reflexivity. }
  { lia. }
  intros fx6 L6 A6 regs6 mem6 md6 CF6 RC6 RX6 PR6 CK6.
  pose proof (TR_pres _ _ _ _ _ HTR5 PR6) as (T8 & T9 & T23 & T22 & T26 & T24 & T25 & T27).
  assert (P16 : getr regs6 2 = getr regs 2).
  { exact (eq_trans (PR6 2 ltac:(unfold callee_saved; lia)) (eq_trans (P5 2 ltac:(unfold callee_saved; lia)) P14)). }
  pose proof CF6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FZ6).
  destruct (it_model B API S rg mem0 md0 L0 A0 fx6 L6 A6 regs6 mem6 md6 CF6) as [Hh6 Hl6].
  assert (LC0' : rw_cells rsegs mem6 FB (LOC1 (n - hdr_n n))) by (apply CK6; [lia | unfold LOC1; cbn; lia | exact LC0c]).
  assert (LC1' : rw_cells rsegs mem6 (FB + 24)
      [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); CB 8 jw])
    by (apply CK6; [lia | cbn; lia | exact LC1c]).
  assert (U23 : bv_unsigned (reg_get regs6 23) = m).
  { change (reg_get regs6 23) with (getr regs6 23). rewrite T23. apply unsigned_lit. lia. }
  assert (U8 : bv_unsigned (reg_get regs6 8) = m_src p n).
  { change (reg_get regs6 8) with (getr regs6 8). rewrite T8. apply unsigned_lit. unfold m_src, hdr_n in *. lia. }
  assert (U9 : bv_unsigned (reg_get regs6 9) = m_len p0 pl p n).
  { change (reg_get regs6 9) with (getr regs6 9). rewrite T9. apply unsigned_lit. lia. }
  (* the tail *)
  eapply (@sr_raw fx6 regs6 (Z_to_bv 64 0x143c0) mem6 md6 _ _ Hh6 Hl6).
  { unfold Regs6ss.mkR_of. eapply run_tail_ok.
    - rewrite (SPV regs6 P16). unfold CF.SlotInv.FB, SLOT_STACK, IMG_END in *. lia.
    - rewrite (SPV regs6 P16). unfold CF.SlotInv.FB in *. lia.
    - rewrite (SPV regs6 P16). exact LC0'.
    - rewrite U9. unfold hdr_n in *. lia.
    - rewrite U8, U9. unfold m_src, hdr_n in *. lia. }
  { intros s0 [(_ & _ & ->)|(_ & a0' & a2' & a3' & a4' & s1' & s2' & s7' & ->)]; do 5 eexists; reflexivity. }
  intros R7 F7 pc7 fc7 m7 regs7 HQ GR7.
  destruct (RX6) as (REP6 & SPILL6 & QB6 & Hq6 & ENO6 & BLK6 & _ & HOL6).
  assert (RF6 : CF.SlotInv.RF L0 A0 L6 A6 mem6 R O q).
  { refine (conj REP6 (conj SPILL6 (conj QB6 (conj Hq6 (conj ENO6 _))))).
    intros pn Hb6. destruct (BLK6 pn Hb6) as [H|[H|[]]]; [left | right]; exact H. }
  destruct HQ as [(Hs7 & Hs1 & E)|(Hx & a0' & a2' & a3' & a4' & s1' & s2' & s7' & E)];
    injection E as -> -> -> -> ->; apply SR_ret.
  - right. rewrite U23 in Hs7. rewrite U9 in Hs1.
    exists (mkFP fp_regs fp_csr), (m_src p n + m_len p0 pl p n), (n - hdr_n n - m_len p0 pl p n), L6, A6, regs7, mem6, md6,
      R, O, q.
    split; [reflexivity|].
    split.
    { apply (ie_cf_regs fx6 _ L6 A6 regs6 mem6 md6 regs7 CF6); [rewrite GR7; reflexivity | rewrite GR7; reflexivity |
        rewrite GR7; reflexivity | exact FZ6]. }
    split; [exact RF6|]. split; [exact RC6|]. split; [exact HOL6|].
    split.
    { transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs6 23) + 1)); [rewrite GR7; reflexivity|]. rewrite U23.
      reflexivity. }
    split.
    { transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs6 8) + bv_unsigned (reg_get regs6 9))); [rewrite GR7; reflexivity|].
      rewrite U8, U9. reflexivity. }
    split.
    { transitivity (Z_to_bv 64 (n - hdr_n n - bv_unsigned (reg_get regs6 9))); [rewrite GR7; reflexivity|].
      rewrite U9. reflexivity. }
    split; [rewrite GR7; exact T24|].
    split; [rewrite GR7; exact T25|].
    split; [rewrite GR7; exact T27|].
    split; [rewrite GR7; reflexivity|].
    split; [rewrite GR7; exact T22|].
    split; [rewrite GR7; exact T26|].
    split.
    { destruct (rw_cells_forget _ _ _ _ LC1') as [jw' LC1'']. cbn [cells_size csize Nat.add] in LC1''.
      exists (le8 (Z_to_bv 64 (n - hdr_n n))), jw'. split; [exact (loc1_loc0 _ _ _ LC0') | exact LC1'']. }
    unfold m_src, hdr_n in *. lia.
  - left. exists (mkFP fp_regs fp_csr), L6, A6, regs7, mem6, md6, R, O, q.
    split; [reflexivity|].
    split.
    { apply (ie_cf_regs fx6 _ L6 A6 regs6 mem6 md6 regs7 CF6); [rewrite GR7; reflexivity | rewrite GR7; reflexivity |
        rewrite GR7; reflexivity | exact FZ6]. }
    split; [exact RF6|]. split; [exact RC6|].
    rewrite GR7. reflexivity.
Qed.

End E.
