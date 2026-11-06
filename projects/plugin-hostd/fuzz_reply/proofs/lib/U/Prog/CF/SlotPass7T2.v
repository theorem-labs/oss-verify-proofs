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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v; 1022 of its 1119 lines of code are new or changed and 738 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/chain_words.v, with its module paths, module names and numbers changed; 961 of its 1017 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/source_reset.v, with its module paths and module names changed; 401 of its 467 lines of code are new or changed and 951 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass7S3.v; 219 of its 294 lines of code are new or changed and 392 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue relay_event_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_event_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass7D SlotPass7R.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op7_frame : forall B API LS SH SK ra empty rc fx j E CS,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  ms_segs B = rsegs /\ errno_addr B = 0x31acc /\
  (forall a, in_globals G_reply a -> img_plain B a) /\
  AllocExtra B (aa_MR (API rc)) /\ blocks_writable B (API rc) /\
  @YM05.alloc_ceiling rc + SLOT_STACK <= spZ (ss_regs E) /\ spZ (ss_regs E) < 2 ^ 63 /\
  (forall x, in_img B x -> 0 <= x < @YM05.alloc_ceiling rc).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS HF.
  pose proof HF as (FF & _ & PRE & _).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL fx). }
  assert (ETP : ms_tp B = 0x31b70) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  pose proof (proj1 (proj1 PRE)) as LP. destruct LP as (_ & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  split; [exact SEG|].
  split; [unfold errno_addr; rewrite ETP, EOFF; reflexivity|].
  split; [unfold frame_facts, G_reply, img_plain in *; tauto|].
  split; [unfold frame_allocator in FA; tauto|].
  split; [unfold frame_allocator in FA; tauto|].
  split; [exact SPLO|]. split; [exact SPHI|].
  exact (hg_img_low (rc := rc) B SEG).
Qed.

Lemma op7_E_hi : forall rc B live OUT CAP res EL a,
  fresh_block (rc := rc) B res (EL + 1) ->
  (live = true -> 0 < CAP -> OUT + CAP <= @YM05.alloc_ceiling rc) ->
  @YM05.alloc_ceiling rc <= a -> ~ op7_E live OUT CAP res EL a.
Proof.
  intros rc B live OUT CAP res EL a (_ & FH & _) HO Ha [X|X].
  - lia.
  - unfold event_writes, send_writes in X. pose proof (@YM05.alloc_ceiling_value rc) as AC.
    destruct X as [[X|[X|[X|(LV & X)]]]|X].
    + unfold G_BROKEN in X; lia.
    + unfold G_EINTR in X; lia.
    + unfold G_OUTV in X; lia.
    + assert (CP : 0 < CAP) by lia. specialize (HO LV CP). lia.
    + unfold G_LOCK in X; lia.
Qed.

Lemma op7_out_hi : forall rc B L A mem nout cap out,
  output_at (rc := rc) B L A mem nout cap out ->
  0 < bv_unsigned cap -> fresh_block (rc := rc) B (bv_unsigned out) (bv_unsigned cap).
Proof.
  intros rc B L A mem nout cap out ((O & junk & [(C0 & _)|(_ & _ & _ & FB & _)]) & _) HC; [lia|exact FB].
Qed.

Theorem op7_rb_stack_holds : op7_rb_stack_stmt.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd nout cap out EL res
    HF HM RM HEL FRB HOUT (S1 & S2 & S3).
  destruct (op7_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ERR & PL & AX & BW & SPLO & SPHI & IL).
  pose proof (@YM05.alloc_ceiling_value rc) as AC.
  assert (NE : forall a, @YM05.alloc_ceiling rc <= a ->
      ~ op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL a).
  { intros a Ha. apply (op7_E_hi rc B _ _ _ res EL a FRB); [|exact Ha].
    intros _ HC. destruct (op7_out_hi rc B L A mem nout cap out HOUT HC) as (_ & X & _). exact X. }
  assert (H1 : @YM05.alloc_ceiling rc <= slot_sp E) by (unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  assert (H2 : errno_addr B + 4 <= slot_sp E) by (rewrite ERR; lia).
  split; [|split].
  - eapply rmid_rw_hi; [exact H1|exact H2|exact HM|exact RM|exact S1|lia| |].
    + unfold saved_cells. cbn [cells_size csize]. unfold slot_sp, SLOT_FRAME in *. lia.
    + intros i Hi. apply NE. lia.
  - eapply rmid_rw_hi; [exact H1|exact H2|exact HM|exact RM|exact S2|lia| |].
    + cbn [cells_size csize]. unfold slot_sp, SLOT_FRAME in *. lia.
    + intros i Hi. apply NE. lia.
  - eapply rmid_rw_hi; [exact H1|exact H2|exact HM|exact RM|exact S3|lia| |].
    + cbn [cells_size csize]. unfold slot_sp, SLOT_FRAME in *. lia.
    + intros i Hi. apply NE. lia.
Qed.

Definition op7_W (x : Z) : Prop :=
  G_BROKEN <= x < G_BROKEN + 1 \/ G_EINTR <= x < G_EINTR + 1 \/ G_OUTV + 8 <= x < G_OUTV + 32 \/
  G_LOCK + 4 <= x < G_LOCK + 8.

Lemma op7_E_img : forall rc B live OUT CAP res EL a,
  fresh_block (rc := rc) B res (EL + 1) ->
  (live = true -> 0 < CAP -> fresh_block (rc := rc) B OUT CAP) ->
  in_img B a -> op7_E live OUT CAP res EL a -> op7_W a.
Proof.
  intros rc B live OUT CAP res EL a (_ & _ & FN) HO HI [X|X].
  - exfalso. apply (FN (a - res)); [lia|]. replace (res + (a - res)) with a by lia. exact HI.
  - unfold event_writes, send_writes in X. unfold op7_W.
    destruct X as [[X|[X|[X|(LV & X)]]]|X]; [left; exact X|right; left; exact X|right; right; left; exact X| |
      right; right; right; exact X].
    exfalso. destruct (HO LV ltac:(lia)) as (_ & _ & FO). apply (FO (a - OUT)); [lia|].
    replace (OUT + (a - OUT)) with a by lia. exact HI.
Qed.

Lemma op7_cells_writable : forall segs m A cs a, rw_cells segs m A cs ->
  A <= a < A + Z.of_nat (cells_size cs) -> writable_at segs m a.
Proof. intros segs m A cs a (_ & _ & _ & WR) Ha. replace a with (A + (a - A)) by lia. apply WR. lia. Qed.

Lemma op7_glob_cells : forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md'
    live OUT CAP res EL a cs,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> aa_MR (API rc) L A mem md ->
  rmid (rc := rc) B (API rc) OP7_K (slot_sp E) (op7_E live OUT CAP res EL) (op7_F live OUT res)
    L A mem md L' A' mem' md' ->
  fresh_block (rc := rc) B res (EL + 1) ->
  (live = true -> 0 < CAP -> fresh_block (rc := rc) B OUT CAP) ->
  rw_cells (ms_segs B) mem a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> in_globals G_reply (a + i) /\ ~ op7_W (a + i)) ->
  rw_cells (ms_segs B) mem' a cs.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' live OUT CAP res EL a cs
    HF HM RM FRB HO HC HG.
  destruct (op7_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ERR & PL & AX & BW & SPLO & SPHI & IL).
  pose proof (@YM05.alloc_ceiling_value rc) as AC.
  eapply (rmid_rw_img B (API rc) AX); [exact IL| |exact HM|exact RM|exact HC|].
  - unfold slot_sp, SLOT_FRAME, SLOT_STACK, OP7_K, RELAY_EVENT_K, RELAY_EVENT_FRAME, SEND_LINE_K, SEND_LINE_FRAME,
      REALLOC_STACK, ALLOC_STACK in *. lia.
  - intros i Hi. destruct (HG i Hi) as (HGi & NW). split; [exact (PL _ HGi)|].
    intros X. apply NW. apply (op7_E_img rc B live OUT CAP res EL (a + i) FRB HO); [|exact X].
    exact (proj1 (PL _ HGi)).
Qed.

Ltac gunf := cbv beta delta [op7_W CF.relay_finish_b_c.G_LISTEN CF.SlotInv.G_WAKE0 Statement.G_THREAD_UP
  CF.relay_finish_b_c.G_THREAD_UP send_line_c.G_BROKEN CheckRep.G_GONE check_shape_event_c.G_GONE send_line_c.G_DEAD
  send_line_c.G_EINTR Statement.G_NSRC check_bounded_c.G_NSRC CF.relay_add_b_c.G_NSRC CF.op_add_c.G_NFD
  CF.StatementKept.G_SRC check_bounded_c.G_SRC CF.relay_add_b_c.G_SRC send_line_c.G_OUTV Statement.G_LOCK
  relay_event_c.G_LOCK].

Ltac gside := intros i Hi; simpl in Hi; split;
  [first [ (apply in_G_bss; gunf; lia) | (exists 0x21620; exists 16; split; [left; reflexivity|gunf; lia]) ]
  |gunf; lia].

Theorem op7_rb_globals_holds : op7_rb_globals_stmt.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br gn dd ei N G nfd mx nout cap out
    EL res nout' cap' out' ev' HF HM RM HEL FRB HOUT HGL CBR CEI COUTV CERR CLOCK.
  assert (HO : op7_live cl br dd EL = true -> 0 < bv_unsigned cap ->
      fresh_block (rc := rc) B (bv_unsigned out) (bv_unsigned cap)).
  { intros _ HC. exact (op7_out_hi rc B L A mem nout cap out HOUT HC). }
  destruct HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & HCL & HBR & HGN &
    HDD & HEI & HGONE & HMX).
  assert (TR : forall a cs, rw_cells (ms_segs B) mem a cs ->
      (forall i, 0 <= i < Z.of_nat (cells_size cs) -> in_globals G_reply (a + i) /\ ~ op7_W (a + i)) ->
      rw_cells (ms_segs B) mem' a cs).
  { intros a cs H. exact (op7_glob_cells B API LS SH SK ra empty rc fx j E CS
      L A mem md L' A' mem' md' _ _ _ res EL a cs HF HM RM FRB HO H). }
  unfold globals_at.
  split; [apply TR; [exact G1|gside]|].
  split; [apply TR; [exact G2|gside]|].
  split; [apply TR; [exact G3|gside]|].
  split; [exact CBR|].
  split; [apply TR; [exact G5|gside]|].
  split; [apply TR; [exact G6|gside]|].
  split; [exact CEI|].
  split; [apply TR; [exact G8|gside]|].
  split; [apply TR; [exact G9|gside]|].
  split; [apply TR; [exact G10|gside]|].
  split; [exact COUTV|].
  split; [exact CLOCK|].
  split; [apply TR; [exact G13|gside]|].
  split; [exists ev'; exact CERR|].
  unfold op7_br, op7_ei, send_off.
  split; [exact HCL|].
  split; [destruct ((cl <? 0) || (br =? 1) || (EL + 1 =? 0)); lia|].
  split; [exact HGN|]. split; [exact HDD|].
  split; [destruct ((cl <? 0) || (br =? 1) || (EL + 1 =? 0)); lia|].
  split; [|exact HMX].
  destruct HGONE as (HG0 & HG1). split.
  - intros X. destruct (HG0 X) as (-> & -> & ->). cbn. replace (EL + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn. lia.
  - intros X. specialize (HG1 X).
    destruct (cl <? 0) eqn:C1; cbn [orb]; [left; apply Z.ltb_lt in C1; destruct HCL; lia|].
    destruct (br =? 1) eqn:C2; cbn [orb]; [right; left; apply Z.eqb_eq in C2; exact C2|].
    replace (EL + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply Z.ltb_ge in C1. apply Z.eqb_neq in C2. right. right.
    destruct HG1 as [X1|[X1|X1]]; [lia|lia|exact X1].
Qed.

Lemma op7_W_glob : forall a, op7_W a -> in_globals G_reply a.
Proof. intros a X. apply in_G_bss. revert X. gunf. lia. Qed.

Theorem op7_rb_output_holds : op7_rb_output_stmt.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res nout cap out nout' cap' out'
    HF HM RM HEL RSEP HOUT LF LT.
  destruct (op7_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ERR & PL & AX & BW & SPLO & SPHI & IL).
  destruct (op7_live cl br dd EL) eqn:LV.
  - destruct (LT eq_refl) as (N1 & (C1 & C2) & IN & FB & (ob & junk & BY & LO & LJ)).
    unfold output_at. cbv zeta. split; [|exact C2].
    exists ob, junk. right. split; [lia|]. split; [lia|]. split; [exact IN|]. split; [exact FB|].
    split; [exact BY|]. split; lia.
  - destruct (LF eq_refl) as (-> & -> & ->).
    destruct HOUT as ((O & junk & [C0|(CP & NC & IN & FB & BY & LO & LJ)]) & TB).
    + split; [exists O, junk; left; exact C0|exact TB].
    + split; [|exact TB]. exists O, junk. right.
      destruct (RSEP _ _ IN) as (NR & DJ).
      assert (NF : ~ op7_F false (bv_unsigned out) res (bv_unsigned out)).
      { intros [X|(X & _)]; [exact (NR X)|discriminate]. }
      assert (NE : forall i, 0 <= i < bv_unsigned cap ->
          ~ op7_E false (bv_unsigned out) (bv_unsigned cap) res EL (bv_unsigned out + i)).
      { intros i Hi [X|X]; [exact (DJ i Hi X)|].
        destruct FB as (_ & _ & FN). apply (FN i Hi). apply (fun W => proj1 (PL _ (op7_W_glob _ W))).
        unfold event_writes, send_writes in X. unfold op7_W.
        destruct X as [[X|[X|[X|(X & _)]]]|X]; [left; exact X|right; left; exact X|right; right; left; exact X|
          discriminate|right; right; right; exact X]. }
      split; [exact CP|]. split; [exact NC|].
      split; [exact (proj1 (rmid_block B (API rc) BW _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 RM IN CP NF ltac:(lia)
        (NE 0 ltac:(lia))))|].
      split; [exact FB|].
      split; [|split; assumption].
      eapply (rmid_bytes_block B (API rc) BW); [exact RM|exact IN|exact CP|exact NF|exact BY|lia|
        rewrite length_app, Nat2Z.inj_add; lia|].
      intros i Hi. apply NE. rewrite length_app, Nat2Z.inj_add in Hi. lia.
Qed.

Theorem op7_rb_image_holds : op7_rb_image_stmt.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br gn dd ei N G nfd mx nout cap out
    EL res nout' cap' out' HF HM RM HEL FRB HOUT (IK1 & IK2 & IK3 & IK4) HGL CBR CEI COUTV CLOCK.
  destruct (op7_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ERR & PL & AX & BW & SPLO & SPHI & IL).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof (aa_laws (API rc)) as LAWS.
  assert (HO : op7_live cl br dd EL = true -> 0 < bv_unsigned cap ->
      fresh_block (rc := rc) B (bv_unsigned out) (bv_unsigned cap)).
  { intros _ HC. exact (op7_out_hi rc B L A mem nout cap out HOUT HC). }
  assert (HK : @YM05.alloc_ceiling rc <= slot_sp E - OP7_K).
  { unfold slot_sp, SLOT_FRAME, SLOT_STACK, OP7_K, RELAY_EVENT_K, RELAY_EVENT_FRAME, SEND_LINE_K, SEND_LINE_FRAME,
      REALLOC_STACK, ALLOC_STACK in *. lia. }
  assert (NEI : forall a, in_img B a -> ~ op7_W a ->
      ~ op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL a).
  { intros a HI NW X. exact (NW (op7_E_img rc B _ _ _ res EL a FRB HO HI X)). }
  assert (NEH : forall a, @YM05.alloc_ceiling rc <= a ->
      ~ op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL a).
  { intros a Ha. apply (op7_E_hi rc B _ _ _ res EL a FRB); [|exact Ha].
    intros LV HC. destruct (HO LV HC) as (_ & X & _). exact X. }
  pose proof RM as (M' & W' & B' & _ & _ & _ & _ & _ & _ & _ & BY & _ & SC).
  assert (HIGH : forall a, @YM05.alloc_ceiling rc <= a < 2 ^ 64 -> ~ sk B OP7_K (slot_sp E) a ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha NS. apply BY; [left; exact Ha| | |exact NS|exact (NEH a (proj1 Ha))].
    - intros X. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM X). lia.
    - intros X. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M' X). lia. }
  unfold image_kept. split; [|split; [|split]].
  - intros a HI NS NC NER NG.
    assert (NW : ~ op7_W a) by (intros X; exact (NG (op7_W_glob a X))).
    destruct (rmid_img B (API rc) AX _ _ _ _ _ _ _ _ _ _ _ _ a IL HK HM RM (conj HI (conj NS (conj NC NER)))
      (NEI a HI NW)) as (Y1 & Y2).
    destruct (IK1 a HI NS NC NER NG) as (Z1 & Z2). split; [rewrite Y1; exact Z1|tauto].
  - intros a HG.
    assert (D : op7_W a \/ ~ op7_W a) by (unfold op7_W; lia).
    destruct D as [W|NW].
    + pose proof HGL as (_ & _ & _ & G4 & _ & _ & G7 & _ & _ & _ & G11 & G12 & _).
      assert (WR : writable_at (ms_segs B) mem a /\ writable_at (ms_segs B) mem' a).
      { revert W. gunf. intros W.
        destruct W as [W|[W|[W|W]]].
        - split; [eapply op7_cells_writable; [exact G4|]|eapply op7_cells_writable; [exact CBR|]];
            cbn [cells_size csize Nat.add]; gunf; lia.
        - split; [eapply op7_cells_writable; [exact G7|]|eapply op7_cells_writable; [exact CEI|]];
            cbn [cells_size csize Nat.add]; gunf; lia.
        - split; [eapply op7_cells_writable; [exact G11|]|eapply op7_cells_writable; [exact COUTV|]];
            cbn [cells_size csize Nat.add]; gunf; lia.
        - split; [eapply op7_cells_writable; [exact G12|]|eapply op7_cells_writable; [exact CLOCK|]];
            cbn [cells_size csize Nat.add]; gunf; lia. }
      pose proof (IK2 a HG). tauto.
    + destruct (rmid_img B (API rc) AX _ _ _ _ _ _ _ _ _ _ _ _ a IL HK HM RM (PL a HG)
        (NEI a (proj1 (PL a HG)) NW)) as (_ & Y2).
      pose proof (IK2 a HG). tauto.
  - intros a Ha NS.
    assert (NSK : ~ sk B OP7_K (slot_sp E) a).
    { intros X. apply NS. unfold sk, lib_scratch in *.
      unfold slot_sp, SLOT_FRAME, SLOT_STACK, OP7_K, RELAY_EVENT_K, RELAY_EVENT_FRAME, SEND_LINE_K, SEND_LINE_FRAME,
        REALLOC_STACK, ALLOC_STACK in *. lia. }
    destruct (HIGH a Ha NSK) as (Y1 & Y2). destruct (IK3 a Ha NS) as (Z1 & Z2).
    split; [rewrite Y1; exact Z1|tauto].
  - intros a HS.
    assert (D : sk B OP7_K (slot_sp E) a \/ ~ sk B OP7_K (slot_sp E) a) by (unfold sk; lia).
    destruct D as [D|D]; [exact (SC a D)|].
    assert (Ha : @YM05.alloc_ceiling rc <= a < 2 ^ 64).
    { unfold sk, lib_scratch in *. rewrite ERR in *.
      unfold slot_sp, SLOT_FRAME, SLOT_STACK, OP7_K, RELAY_EVENT_K, RELAY_EVENT_FRAME, SEND_LINE_K, SEND_LINE_FRAME,
        REALLOC_STACK, ALLOC_STACK in *. lia. }
    destruct (HIGH a Ha D) as (_ & Y2). apply Y2. exact (IK4 a HS).
Qed.
