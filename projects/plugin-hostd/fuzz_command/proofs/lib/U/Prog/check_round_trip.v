(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 1213 of its 1275 lines of code are new or changed and 486 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/send_message.v, with its module paths, module names and numbers changed; 1464 of its 1542 lines of code are new or changed and 1197 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB CommandB
  verbs_receive_c joined_c send_message_c rec_calls_copy_c rec_calls_free_c strdup_c rec_calls_equal_c strcmp_c
  xmalloc_c check_round_trip_c CrtSm CrtRun CrtRce CrtVr CrtFacts CrtCalls CrtRep CrtSlot CrtKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require joined.
Import ListNotations.
Local Open Scope Z_scope.

Ltac crt_keep X :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hx := fresh "Hx" in let C := fresh "C" in
  intros r Hr Hx; unfold callee_saved in Hr;
  assert (C : r = 3 \/ r = 4 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X) by reflexivity; reflexivity|]);
  subst r; rewrite (getr_of_eqv _ _ _ X) by reflexivity; reflexivity.

Section CRT.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis TP_AT : ms_tp B = 0x344c0.
Hypothesis EOFF_AT : ms_errno_off B = -164.
Hypothesis GUARD_AT : ms_guard B = SSP_GUARD_B.
Hypothesis GOT_AT : ms_got_guard B = SSP_GOT_B.
Hypothesis G_STAT : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RELRO_FREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a ->
  ~ (ms_got_guard B <= a < ms_got_guard B + 8) -> ~ owned B L A a /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis CTXO : ctx_owned B API.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis SLACK : block_slack_present B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis RCC : rec_calls_copy_contract B API.
Hypothesis SDUP : strdup_contract B API.
Hypothesis JOIN : joined_contract B API.
Hypothesis SEND : send_message_contract B API.
Hypothesis RCE : rec_calls_equal_contract.
Hypothesis STRCMP : strcmp_contract.
Hypothesis RCF : forall fx' : YK11.FPState, @rec_calls_free_contract fx' rc B API.

Lemma crt_nown : forall L A mem md a, aa_MR API L A mem md -> (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
  ~ owned B L A a -> forall L' A' mem' md', aa_MR API L' A' mem' md' -> ~ owned B L' A' a.
Proof using AX CTXO.
  intros L A mem md a HM Ha Ho L' A' mem' md' HM' Ho'.
  destruct Ha as [Ha|Ha].
  - pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM' Ho'). lia.
  - destruct Ho' as [Hal|Hst]; apply Ho; [|right; exact Hst].
    apply (CTXO L A mem md a HM). exact (ax_img AX L' A' mem' md' a HM' Ha Hal).
Qed.

Lemma crt_gnown : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof using AX G_STAT.
  intros L A mem md a HM Hg Ho. destruct (G_STAT a Hg) as (Hi & Hs & Hc & _).
  destruct Ho as [Hal|Hst]; [exact (Hc (ax_img AX L A mem md a HM Hi Hal)) | exact (Hs Hst)].
Qed.

Lemma crt_blk_img : forall L A mem md a k i, aa_MR API L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (a + i).
Proof using AX.
  intros L A mem md a k i HM Hin Hi. apply YI06.blocks_In in Hin as (p & <- & Hp).
  exact (ax_blocks_img AX L A mem md p k i HM Hp Hi).
Qed.

Theorem check_round_trip_holds : check_round_trip_contract B API.
Proof using SEGS FREE_PC TP_AT EOFF_AT GUARD_AT GOT_AT G_STAT RELRO_FREE CTXO AX SLACK FREE RCC SDUP JOIN SEND RCE
  STRCMP RCF.
  unfold check_round_trip_contract.
  intros L A regs mem md b W arr sb hb q wp ws R O can _ [PRE SPT] CMD FRM A10 A11 A12 RSB RHB WV WPL WAL ARL SPW WTOP JN
    ILA ILW REP DECL ACT RQ QAT QWR QOUT VT RES ROOM RT.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC. pose proof alloc_ceiling_lt as AC2.
  assert (ERRV : errno_addr B = 0x3441c) by (unfold errno_addr; rewrite TP_AT, EOFF_AT; reflexivity).
  assert (ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling) by lia.
  assert (CK : CRT_K = 16000) by reflexivity.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite CK in HCEIL, HWS.
  pose proof CMD as CMD0. destruct CMD as (RO & GIMG & _ & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (fun k => crt_al8 (bv_unsigned sp) k HAL) as SP8.
  rewrite SEGS in HWS, HERR, RO, QWR, REP.
  assert (GIM : forall a, in_globals frame_RELRO a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. rewrite <- SEGS. exact (GIMG a Ha). }
  clear GIMG.
  set (KP := fun a => (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) /\ ~ owned B L A a).
  assert (KPN : forall a L' A' m' md', KP a -> aa_MR API L' A' m' md' -> ~ owned B L' A' a).
  { intros a L' A' m' md' [Ha Ho] HM'. exact (crt_nown L A mem md a HMR Ha Ho L' A' m' md' HM'). }
  assert (KPR : forall a, KP a -> 0 <= a < 2 ^ 64).
  { intros a [[Ha|Ha] _]; [lia | pose proof (in_img_low B SEGS a Ha); lia]. }
  assert (KPH : forall a, alloc_ceiling <= a < 2 ^ 64 -> KP a).
  { intros a Ha. split; [left; exact Ha|]. intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ _ HMR Ho). lia. }
  assert (GX : forall a, in_globals frame_G a ->
             KP a /\ ~ scratch_k B CRT_K regs a /\ ~ (errno_addr B <= a < errno_addr B + 4)).
  { intros a Ha. pose proof (sm_g_iv a Ha) as Hr. destruct (G_STAT a Ha) as (Hi & _ & _ & He).
    split; [split; [right; exact Hi | exact (crt_gnown L A mem md a HMR Ha)]|]. split; [|exact He].
    unfold scratch_k. rewrite CK. change (spZ regs) with (bv_unsigned sp). intros [H|H]; [lia | exact (He H)]. }
  assert (RLX : forall a, in_globals frame_RELRO a -> ~ (SSP_GOT_B <= a < SSP_GOT_B + 8) ->
             KP a /\ ~ scratch_k B CRT_K regs a /\ ~ vr_writes a).
  { intros a Ha Hg. pose proof (sm_relro_iv a Ha) as Hr.
    destruct (RELRO_FREE L A mem md a HMR Ha ltac:(rewrite GOT_AT; exact Hg)) as [Ho He].
    split; [|split].
    - split; [right; apply (sm_img_iv B a SEGS); lia | exact Ho].
    - unfold scratch_k. rewrite CK. change (spZ regs) with (bv_unsigned sp). intros [H|H]; [lia | exact (He H)].
    - unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT. lia. }
  assert (ST : stk rsegs mem (bv_unsigned sp - 16000) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (Wa : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact Wa|].
    destruct (writable_hi_present mem a ltac:(lia) Wa) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  assert (INIT : st_init_done A = true).
  { pose proof ILA as (p & k & Hpk & _). apply YI06.blocks_In in Hpk as (p' & _ & Hp').
    exact (YI04.init_done_of_block A (p', k) HWF Hp'). }
  pose proof WV as (LWP & NLT & L24 & L16 & WK).
  assert (NWB : bytes_at rsegs mem (W + 24) (le4 (Z_to_bv 64 (Z.of_nat (length ws))))).
  { apply (sm_bytes_of_le B mem _ _ SEGS); [lia | rewrite Mem.length_le4; lia | exact L24]. }
  assert (QB : bytes_at rsegs mem 0x343e8 (le4 (Z_to_bv 64 q))).
  { apply (sm_bytes_of_le B mem _ _ SEGS); [lia | rewrite Mem.length_le4; lia | exact QAT]. }
  destruct (rep_ncalls rsegs L A mem R O REP) as (NCB & NC16 & NC6).
  destruct (crt_got_bytes B SEGS mem CMD0) as (GOTQ & GOTR).
  assert (BLR : forall a k, In (a, k) (blocks L A) -> 4096 <= a /\ a + k <= alloc_ceiling).
  { intros a k Hin. apply YI06.blocks_In in Hin as (p & <- & Hp). exact (mr_blocks_range B _ LAWS _ _ _ _ p k HMR Hp). }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of, CHECK_ROUND_TRIP. fold sp.
    eapply crt_s0 with (lo := bv_unsigned sp - 16000) (W := W) (nw := Z.of_nat (length ws)) (q := q)
      (nc := Z.of_nat (length (r_calls R)));
      [exact ST | lia | lia | exact A10 | exact WAL | lia | lia | exact NWB | lia | exact GOTQ | exact GOTR | exact QB | lia
      | exact NCB | lia]. }
  intros ms1 (can1 & Q1 & EQ1).
  destruct Q1 as [(EARLY & m1 & RET1 & MU1 & WM1) | (NW0 & ACTQ & m1 & junk & AT1 & MU1 & WM1 & FR1)].
  - (* early return *)
    unfold crt_ret in RET1.
    destruct RET1 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & ->).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 992 <= a < bv_unsigned sp) ->
               mbyte rsegs m1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m1 a)).
    { intros a Ha Hx. assert (Ho : Frame.outside [(bv_unsigned sp - 992, bv_unsigned sp)] a) by (cbn; split; [lia | exact I]).
      split; [exact (munch_mbyte _ _ _ _ _ MU1 Ha Ho) | exact (munch_writable _ _ _ _ _ MU1 Ha Ho)]. }
    assert (OUTB : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 992 <= a < bv_unsigned sp) ->
               mbyte rsegs m1 a = mbyte rsegs mem a) by (intros a Ha Hx; exact (proj1 (OUT a Ha Hx))).
    assert (MR1 : aa_MR API L A m1 md).
    { apply (KindBGlue.kb_MR_A B API L A mem m1 md _ HMR MU1). intros x Hx _. cbn. split; [lia | exact I]. }
    assert (BKE : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m1 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hi. destruct (BLR a k Hin). apply OUTB; lia. }
    assert (RO1 : ro_agree rsegs m1).
    { apply (sm_ro_munch _ mem m1 RO MU1). intros x Hx. cbn. split; [lia | exact I]. }
    assert (RK1 : relro_kept mem m1).
    { intros a Ha _. pose proof (sm_relro_iv a Ha). apply OUTB; lia. }
    destruct (ax_statics AX L A m1 md MR1) as (WG1 & (g1 & Hg1 & WGG1) & _).
    rewrite SEGS, GOT_AT, GUARD_AT in WG1. rewrite SEGS, GUARD_AT in WGG1.
    apply SR_ret.
    exists fx, L, A, R1, m1, md, R, O, b.
    split; [rewrite RP; reflexivity|].
    split; [exact FRM|].
    split; [lia|].
    split.
    { unfold call_post_ko. rewrite ?SEGS.
      split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|].
      split; [intros; reflexivity|].
      split.
      { intros r Hr. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X1) by reflexivity; reflexivity|]).
        subst r; rewrite (getr_of_eqv _ _ _ X1) by reflexivity; reflexivity. }
      split; [exists (m_vmmaps md); symmetry; apply KindBGlue.kb_vm_id|].
      split.
      { intros a Ha _ _ Hs _. unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
        assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (in_img_low B SEGS a Ha); lia]).
        apply OUT; [exact Hr | lia]. }
      split.
      { intros p k i Hp _ _ Hi. apply (BKE _ k); [|exact Hi]. unfold blocks. exact (in_map _ _ _ Hp). }
      intros a Hs. unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      unfold writable_at. apply WM1. change (writable_at rsegs mem a).
      destruct Hs as [Hs|Hs]; [apply HWS; lia | apply HERR; exact Hs]. }
    split; [exact (crt_cmd_mem_keep B SEGS mem m1 g1 CMD0 RO1 RK1 WG1 WGG1 Hg1)|].
    split.
    { apply (rec_rep_frame rsegs G_REC REC_SC L A mem R O L A m1 REP).
      - intros a Ha. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha.
        destruct (OUT a ltac:(lia) ltac:(lia)) as [E W1]. split; [exact E | apply W1].
      - intros p k i Hin Hi. exact (BKE p k i (proj1 (rep_O rsegs _ _ _ _ _ _ REP Hin)) Hi).
      - intros pn Hin. exact (proj1 (rep_O rsegs _ _ _ _ _ _ REP Hin)). }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { apply (sm_le_keep B mem); [exact QAT|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le4 in Hi.
      unfold G_QUIT. apply OUTB; lia. }
    split.
    { apply (crt_words_view_keep B SEGS mem m1); [exact WV | | |].
      - intros a Ha. apply OUTB; lia.
      - intros i Hi. destruct ILA as (p & k & Hpk & _ & Hp1 & Hp2). destruct (BLR p k Hpk).
        apply OUTB; lia.
      - intros k i Hk Hi. destruct (ILW k Hk) as (p & k' & Hpk & _ & Hp1 & Hp2). destruct (BLR p k' Hpk).
        apply OUTB; lia. }
    split; [exact WPL|].
    split.
    { intros pn Hin. destruct (in_dec zz_dec pn O) as [HO|HO]; [right; exact HO | left; split; assumption]. }
    split; [intros pn Hin _; exact Hin|].
    split.
    { unfold blocks_kept. rewrite ?SEGS. intros a k i Hin _ Hi. exact (BKE a k i Hin Hi). }
    split; [tauto|].
    split; [intros pn _ Hno HO; apply Hno; exact (in_map fst _ _ HO)|].
    split; [exists (Z_to_bv 64 g1); exact (crt_vr_tables_keep B SEGS mem m1 can g1 VT RK1 WG1 WGG1 Hg1)|].
    split; [exact RES | reflexivity].
  - (* main path *)
    unfold crt_at_copy in AT1. destruct AT1 as (a1x & ->).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (WSNE : ws <> []) by (intros E; rewrite E in NW0; cbn in NW0; lia).
    assert (ACTED : acted_m R q = true).
    { unfold acted_m. apply orb_true_iff. destruct ACTQ as [H|H].
      - left. apply negb_true_iff. apply Z.eqb_neq. exact H.
      - right. apply negb_true_iff. apply Nat.eqb_neq. intros E. apply H. rewrite E. reflexivity. }
    destruct (ACT ACTED) as (X & RX & NX).
    pose proof (RT WSNE ACTED) as RT1.
    assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 992 <= a < bv_unsigned sp) ->
               mbyte rsegs m1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m1 a)).
    { intros a Ha Hx. assert (Ho : Frame.outside [(bv_unsigned sp - 992, bv_unsigned sp)] a) by (cbn; split; [lia | exact I]).
      split; [exact (munch_mbyte _ _ _ _ _ MU1 Ha Ho) | exact (munch_writable _ _ _ _ _ MU1 Ha Ho)]. }
    assert (OUTB : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 992 <= a < bv_unsigned sp) ->
               mbyte rsegs m1 a = mbyte rsegs mem a) by (intros a Ha Hx; exact (proj1 (OUT a Ha Hx))).
    assert (MR1 : aa_MR API L A m1 md).
    { apply (KindBGlue.kb_MR_A B API L A mem m1 md _ HMR MU1). intros x Hx _. cbn. split; [lia | exact I]. }
    assert (RO1 : ro_agree rsegs m1).
    { apply (sm_ro_munch _ mem m1 RO MU1). intros x Hx. cbn. split; [lia | exact I]. }
    assert (USP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 992)) = bv_unsigned sp - 992) by (apply unsigned_lit; lia).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x14fd4) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 (bv_unsigned sp - 984))
      by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_18 : getr R1 18 = Z_to_bv 64 W) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; exact A10).
    assert (E1_19 : getr R1 19 = Z_to_bv 64 hb) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; exact A12).
    assert (E1_20 : getr R1 20 = Z_to_bv 64 sb) by (rewrite (getr_of_eqv _ _ 20 X1 eq_refl); simp_regs; exact A11).
    assert (E1_21 : getr R1 21 = Z_to_bv 64 0x34028) by (rewrite (getr_of_eqv _ _ 21 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_22 : getr R1 22 = Z_to_bv 64 0x343e8) by (rewrite (getr_of_eqv _ _ 22 X1 eq_refl); simp_regs; reflexivity).
    assert (K1 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by crt_keep X1.
    assert (SP1 : spZ R1 = bv_unsigned sp - 992) by (unfold spZ; rewrite E1_2; exact USP1).
    destruct (crt_cells_split m1 _ [CB 904 junk] _ FR1) as [FRC FRS1].
    replace (bv_unsigned sp - 992 + Z.of_nat (cells_size [CB 904 junk])) with (bv_unsigned sp - 88) in FRS1
      by (cbn; lia).
    assert (REP1 : g_rec_rep rsegs L A m1 R O).
    { apply (rec_rep_frame rsegs G_REC REC_SC L A mem R O L A m1 REP).
      - intros a Ha. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha.
        destruct (OUT a ltac:(lia) ltac:(lia)) as [E W1]. split; [exact E | apply W1].
      - intros p k i Hin Hi. destruct (BLR p k (proj1 (rep_O rsegs _ _ _ _ _ _ REP Hin))). apply OUTB; lia.
      - intros pn Hin. exact (proj1 (rep_O rsegs _ _ _ _ _ _ REP Hin)). }
    assert (PRE1 : call_pre_k B (aa_MR API) RCC_K L A R1 m1 md).
    { pose proof (KindBGlue.kb_pre_A B API CRT_K 992 RCC_K L A regs mem md R1 m1
        [(bv_unsigned sp - 992, bv_unsigned sp)] PRE0) as KPA.
      rewrite SEGS in KPA. unfold RCC_K, XMALLOC_K in *. change ALLOC_STACK with 8192 in *.
      apply KPA; clear KPA.
      - lia.
      - lia.
      - rewrite CK. lia.
      - rewrite SP1. reflexivity.
      - rewrite SP1. replace (bv_unsigned sp - 992) with (bv_unsigned sp + (-62) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      - exact E1_4.
      - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
      - exact MU1.
      - exact WM1.
      - intros x Hx Hs. change (spZ regs) with (bv_unsigned sp) in Hs. cbn. split; [lia | exact I].
      - intros x Hx _. cbn. split; [lia | exact I]. }
    assert (RWB : forall a, rcc_writes (bv_unsigned sp - 984) (r_calls R) a ->
               bv_unsigned sp - 984 <= a /\ a < bv_unsigned sp - 984 + 56 * Z.of_nat (length (r_calls R)) /\
               a < bv_unsigned sp - 88).
    { intros a (i & c & Ec & Ha).
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      pose proof (proj1 (NC6 c (nth_error_In _ _ Ec))). lia. }
    destruct (rcc_args_bound _ NC16 NC6) as [ARGS ARGB].
    destruct (rcc_b_fields (rcc_args (r_calls R)) b) as (RB1 & RB2 & RB3).
    assert (ROOM1 : forall n, 0 <= n <= VR_REQ -> room_slots (rcc_b b (rcc_args (r_calls R))) n).
    { intros n Hn. apply (RecKindB.room_slots_mono _ (sb_up b CRT_PEAK CRT_PEAKB) n VR_REQ); [|lia|exact ROOM].
      unfold RecKindB.sb_le, sb_up. rewrite RB1, RB2, RB3. cbn [sb_live sb_bytes sb_cap].
      unfold CRT_PEAK, SM_PEAK, CRT_PEAKB, LMAX in *. lia. }
    pose proof (RCC L A R1 m1 md R O (bv_unsigned sp - 984) b) as RC. unfold REC_CALLS_COPY in RC. rewrite SEGS in RC.
    eapply SR_bind.
    { apply RC; clear RC.
      - exact PRE1.
      - exact RO1.
      - exact E1_10.
      - exact REP1.
      - intros j Hj. rewrite SP1. split; [lia|].
        destruct FRC as [_ (_ & _ & WC)].
        replace (bv_unsigned sp - 984 + j) with (bv_unsigned sp - 992 + (8 + j)) by ring.
        exact (WC (8 + j) ltac:(cbn [cells_size csize]; lia)).
      - intros _. replace (bv_unsigned sp - 984) with (bv_unsigned sp + 8 * (-123)) by ring. apply SP8.
      - exact RES.
      - apply ROOM1. unfold LMAX, VR_REQ. lia. }
    intros c2 RET2.
    destruct RET2 as (L1 & A1 & R2 & m2 & md1 & qs & -> & POST2 & A0R2 & QSL & QCALL & PERM2 & ND2 & SEP2 & KEPT2
      & UB2 & REP2 & FG2 & DW2 & RO2 & GK2 & INIT2 & RLEN2 & RES2).
    destruct POST2 as (HMR1 & HWF1 & HBD1 & HLE1 & HSTAB1 & HPRES1 & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
    try rewrite SEGS in HFRAME1. try rewrite SEGS in HBLKS1. try rewrite SEGS in HSCR1. try rewrite SEGS in RO2.
    try rewrite SEGS in REP2. try rewrite SEGS in FG2. try rewrite SEGS in DW2. try rewrite SEGS in QCALL.
    unfold blocks_kept in KEPT2. try rewrite SEGS in KEPT2.
    destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & Hmat1).
    assert (CK2 : forall a, KP a -> ~ (bv_unsigned sp - 9328 <= a < bv_unsigned sp - 992) ->
               ~ (errno_addr B <= a < errno_addr B + 4) -> ~ rcc_writes (bv_unsigned sp - 984) (r_calls R) a ->
               mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
    { intros a Ha Hs He Hw.
      apply HFRAME1; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha MR1) | exact (KPN a _ _ _ _ Ha HMR1) | | exact Hw].
      unfold scratch_k. rewrite SP1. unfold RCC_K, XMALLOC_K. change ALLOC_STACK with 8192.
      intros [H|H]; [apply Hs; lia | exact (He H)]. }
    assert (F2 : forall a, KP a -> ~ scratch_k B CRT_K regs a -> ~ vr_writes a ->
               mbyte rsegs m2 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m2 a)).
    { intros a Ha Hs Hv. unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      assert (Hs1 : ~ (bv_unsigned sp - 16000 <= a < bv_unsigned sp)) by tauto.
      assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (OUT a (KPR a Ha) ltac:(lia)) as [E1 W1].
      destruct (CK2 a Ha ltac:(lia) Hs2 ltac:(intros Hw; pose proof (RWB a Hw); lia)) as [E2 W2].
      split; [congruence | tauto]. }
    assert (BM2 : forall pn, In pn (blocks L A) -> In pn (blocks L1 A1)).
    { intros pn Hin. apply (Permutation_in _ (Permutation_sym PERM2)). apply in_or_app. left. exact Hin. }
    assert (BK2 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m2 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hi. rewrite (KEPT2 a k i Hin (fun F => F) Hi). destruct (BLR a k Hin). apply OUTB; lia. }
    assert (SW2 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m2 a).
    { intros a Ha. destruct (Z_lt_ge_dec a (bv_unsigned sp - 9328)) as [Hlo|Hhi].
      - apply (proj2 (CK2 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(intros Hw; pose proof (RWB a Hw); lia))).
        apply (proj2 (OUT a ltac:(lia) ltac:(lia))). apply HWS. lia.
      - apply HSCR1. unfold scratch_k. rewrite SP1. unfold RCC_K, XMALLOC_K. change ALLOC_STACK with 8192. left. lia. }
    assert (ERR2 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m2 a)
      by (intros a Ha; apply HSCR1; right; exact Ha).
    assert (FRS2 := FRS1).
    apply (rw_cells_transfer rsegs m1 m2) in FRS2;
      [| intros i Hi; cbn in Hi;
         destruct (CK2 (bv_unsigned sp - 88 + i) (KPH (bv_unsigned sp - 88 + i) ltac:(lia)) ltac:(lia) ltac:(lia)
                   ltac:(intros Hw; pose proof (RWB _ Hw); lia)) as [E W2]; split; [exact E | apply W2]].
    assert (G2 : forall a, in_globals frame_G a ->
               mbyte rsegs m2 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m2 a)).
    { intros a Hg. pose proof (sm_g_iv a Hg). destruct (FG2 a Hg) as [E2 W2].
      destruct (OUT a ltac:(lia) ltac:(lia)) as [E1 W1]. split; [congruence | tauto]. }
    destruct (rep_reply rsegs L1 A1 m2 R O _ REP2 RX) as (pr & nr & BRP & PRZ & PRO & PRB & PRL & PRX & PRM).
    destruct (rep_scal rsegs L1 A1 m2 R O REP2) as (BST & BHO & RST & RHO).
    assert (QB2 : bytes_at rsegs m2 0x343e8 (le4 (Z_to_bv 64 q))).
    { apply (bytes_at_transfer rsegs mem); [exact QB|]. intros i Hi. rewrite Mem.length_le4 in Hi.
      exact (proj1 (G2 (0x343e8 + i) (sm_g_of (0x343e8 + i) ltac:(lia)))). }
    assert (E2_21 : getr R2 21 = Z_to_bv 64 0x34028)
      by exact (eq_trans (HPRES1 21 ltac:(unfold callee_saved; lia)) E1_21).
    assert (E2_22 : getr R2 22 = Z_to_bv 64 0x343e8)
      by exact (eq_trans (HPRES1 22 ltac:(unfold callee_saved; lia)) E1_22).
    rewrite E1_1.
    eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      eapply crt_s1 with (q := q) (rp := Z_to_bv 64 pr) (st := Z_to_bv 64 (r_state R)) (ho := Z_to_bv 64 (r_host R));
        [exact E2_21 | exact E2_22 | exact QB2 | exact BRP | exact BST | exact BHO]. }
    intros ms3 (can3 & -> & EQ3).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    assert (E3_1 : getr R3 1 = Z_to_bv 64 0x14ff0) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
    assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 992)).
    { rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs.
      exact (eq_trans (HPRES1 2 ltac:(unfold callee_saved; lia)) E1_2). }
    assert (E3_4 : getr R3 4 = getr regs 4).
    { rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs.
      exact (eq_trans (HPRES1 4 ltac:(unfold callee_saved; lia)) E1_4). }
    assert (E3_8 : getr R3 8 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
      by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; exact A0R2).
    assert (E3_10 : getr R3 10 = Z_to_bv 64 pr) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
    assert (E3_18 : getr R3 18 = Z_to_bv 64 W).
    { rewrite (getr_of_eqv _ _ 18 X3 eq_refl); simp_regs.
      exact (eq_trans (HPRES1 18 ltac:(unfold callee_saved; lia)) E1_18). }
    assert (E3_19 : getr R3 19 = Z_to_bv 64 hb).
    { rewrite (getr_of_eqv _ _ 19 X3 eq_refl); simp_regs.
      exact (eq_trans (HPRES1 19 ltac:(unfold callee_saved; lia)) E1_19). }
    assert (E3_20 : getr R3 20 = Z_to_bv 64 sb).
    { rewrite (getr_of_eqv _ _ 20 X3 eq_refl); simp_regs.
      exact (eq_trans (HPRES1 20 ltac:(unfold callee_saved; lia)) E1_20). }
    assert (E3_21 : getr R3 21 = Z_to_bv 64 0x34028) by (rewrite (getr_of_eqv _ _ 21 X3 eq_refl); simp_regs; exact E2_21).
    assert (E3_22 : getr R3 22 = Z_to_bv 64 0x343e8) by (rewrite (getr_of_eqv _ _ 22 X3 eq_refl); simp_regs; exact E2_22).
    assert (E3_23 : getr R3 23 = Z_to_bv 64 (r_host R))
      by (rewrite (getr_of_eqv _ _ 23 X3 eq_refl); simp_regs; reflexivity).
    assert (E3_24 : getr R3 24 = sx32 (Z_to_bv 64 q)) by (rewrite (getr_of_eqv _ _ 24 X3 eq_refl); simp_regs; reflexivity).
    assert (E3_25 : getr R3 25 = Z_to_bv 64 (r_state R))
      by (rewrite (getr_of_eqv _ _ 25 X3 eq_refl); simp_regs; reflexivity).
    assert (K3' : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R3 (Z_to_bv 5 r) = getr R2 (Z_to_bv 5 r)) by crt_keep X3.
    assert (K3 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr Hx. rewrite (K3' r Hr Hx), (HPRES1 r Hr). exact (K1 r Hr Hx). }
    clear K3'.
    assert (SP3 : spZ R3 = bv_unsigned sp - 992) by (unfold spZ; rewrite E3_2; exact USP1).
    (* strdup of the reply *)
    assert (PRB1 := PRB).
    destruct (YI06.blocks_In L1 A1 pr nr) as [BI _]. destruct (BI PRB1) as (ppr & PPR & UPR). clear BI.
    destruct (mr_blocks_range B _ LAWS _ _ _ _ ppr nr HMR1 UPR) as [PRlo PRhi]. rewrite PPR in PRlo, PRhi.
    rewrite length_app in PRL, PRM. cbn [length] in PRL, PRM.
    pose proof (joined.ceil8 (pr + Z.of_nat (length X) + 1)) as CE1.
    pose proof (joined.ceil8_mono (pr + Z.of_nat (length X) + 1) (pr + nr) ltac:(lia)) as CE2.
    pose proof (joined.ceil8_le (pr + nr) alloc_ceiling PRhi ltac:(Z.div_mod_to_equations; lia)) as CE3.
    pose proof (Z.mod_pos_bound (- (pr + Z.of_nat (length X) + 1)) 8 ltac:(lia)) as CE4.
    destruct (present_rw_cells rsegs m2 (pr + Z.of_nat (length X) + 1)
                (Z.to_nat ((- (pr + Z.of_nat (length X) + 1)) mod 8)) ltac:(lia) ltac:(lia)) as [slack [[SLW SLB] _]].
    { intros i Hi. rewrite Z2Nat.id in Hi by lia.
      destruct (Z_lt_ge_dec (pr + Z.of_nat (length X) + 1 + i) (pr + nr)) as [Hin|Hout].
      - replace (pr + Z.of_nat (length X) + 1 + i) with (pr + (Z.of_nat (length X) + 1 + i)) by ring.
        exact (proj1 (block_facts B _ LAWS _ _ _ _ _ _ (Z.of_nat (length X) + 1 + i) HMR1 PRB1 ltac:(lia))).
      - exact (SLACK L1 A1 m2 md1 pr nr (pr + Z.of_nat (length X) + 1 + i) HMR1 PRB1 ltac:(lia)). }
    cbn [cells_wf cell_wf] in SLW. destruct SLW as [SLL _].
    cbn [cells_bytes cbytes] in SLB. rewrite app_nil_r in SLB.
    assert (DUPB : bytes_at rsegs m2 pr (X ++ Z_to_bv 8 0 :: slack)).
    { replace (X ++ Z_to_bv 8 0 :: slack) with ((X ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact PRX|]. rewrite length_app. cbn [length].
      replace (pr + Z.of_nat (length X + 1)) with (pr + Z.of_nat (length X) + 1) by lia. exact SLB. }
    assert (PRE3 : call_pre_k B (aa_MR API) STRDUP_STACK L1 A1 R3 m2 md1).
    { unfold STRDUP_STACK. change ALLOC_STACK with 8192.
      split; [exact HMR1|]. split; [exact HWF1|]. split; [exact HBD1|].
      split; [rewrite E3_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP3; replace (bv_unsigned sp - 992) with (bv_unsigned sp + (-62) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP3; lia|]. split; [rewrite SP3; lia|].
      split; [intros a Ha; rewrite SP3 in Ha; rewrite SEGS; apply SW2; lia|].
      split; [rewrite E3_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; exact (ERR2 a Ha)|].
      intros HI. rewrite (INIT2 INIT) in HI. discriminate. }
    pose proof (SDUP L1 A1 R3 m2 md1 pr X slack (rcc_b b (rcc_args (r_calls R)))) as SD.
    unfold strdup_c.STRDUP in SD. rewrite SEGS in SD.
    eapply SR_bind.
    { apply SD; clear SD.
      - exact PRE3.
      - exact E3_10.
      - intros i Hi. exact (mbyte_of_bytes_at rsegs m2 pr _ i DUPB Hi).
      - exact NX.
      - rewrite SLL. rewrite Z2Nat.id by lia. lia.
      - lia.
      - left. rewrite SP3. rewrite length_app. cbn [length]. rewrite SLL.
        unfold STRDUP_STACK. change ALLOC_STACK with 8192. lia.
      - right. left. exists pr, nr. split; [exact PRB1 | lia].
      - unfold LMAX in PRM. lia.
      - exact RES2.
      - apply ROOM1. unfold LMAX, VR_REQ in *. lia.
      - exact RO2. }
    intros c4 RET4.
    destruct RET4 as (L2 & A2 & R4 & m3 & md2 & d & -> & POST4 & A0R4 & DNZ & DAL & DFR & DBLK & KEPT4 & DBY & RO3
      & GK4 & UB4 & INIT4 & RLEN4 & RES4).
    destruct POST4 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HPRES2 & HVM2 & HFRAME2 & HBLKS2 & HSCR2).
    try rewrite SEGS in HFRAME2. try rewrite SEGS in HBLKS2. try rewrite SEGS in HSCR2. try rewrite SEGS in RO3.
    try rewrite SEGS in DBY. unfold blocks_kept in KEPT4. try rewrite SEGS in KEPT4.
    destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
    destruct DBLK as (db1 & db2 & DB1 & DB2).
    destruct DFR as (DF1 & DF2 & DF3).
    assert (INBD : In (d, Z.of_nat (length X) + 1) (blocks L2 A2)) by (rewrite DB1; apply in_or_app; right; left; reflexivity).
    assert (BLD : forall a k, In (a, k) (blocks L1 A1) -> a + k <= d \/ d + (Z.of_nat (length X) + 1) <= a).
    { intros a k Hin. rewrite DB2 in Hin. exact (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 DB1 Hin). }
    assert (DNO : ~ In d (map fst O)).
    { intros H. apply in_map_iff in H as ([a k] & Ea & Hin). cbn in Ea. subst a.
      destruct (rep_O rsegs _ _ _ _ _ _ REP Hin) as [Hb Hk]. cbn in Hk. pose proof (BLD d k (BM2 _ Hb)). lia. }
    assert (M12 : forall pn, In pn (blocks L1 A1) -> In pn (blocks L2 A2)).
    { intros pn Hin. rewrite DB1. rewrite DB2 in Hin.
      apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
    assert (CK4 : forall a, KP a -> ~ (bv_unsigned sp - 9216 <= a < bv_unsigned sp - 992) ->
               ~ (errno_addr B <= a < errno_addr B + 4) ->
               mbyte rsegs m3 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a <-> writable_at rsegs m3 a)).
    { intros a Ha Hs He.
      apply HFRAME2; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha HMR1) | exact (KPN a _ _ _ _ Ha HMR2) | |].
      - unfold scratch_k. rewrite SP3. unfold STRDUP_STACK. change ALLOC_STACK with 8192.
        intros [H|H]; [apply Hs; lia | exact (He H)].
      - intros Hd. destruct (proj1 Ha) as [Hh'|Hi]; [lia|]. apply (DF3 (a - d)); [lia|].
        replace (d + (a - d)) with a by ring. exact Hi. }
    assert (F4 : forall a, KP a -> ~ scratch_k B CRT_K regs a -> ~ vr_writes a ->
               mbyte rsegs m3 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m3 a)).
    { intros a Ha Hs Hv. destruct (F2 a Ha Hs Hv) as [E2 W2].
      unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (CK4 a Ha ltac:(lia) Hs2) as [E4 W4]. split; [congruence | tauto]. }
    assert (G4 : forall a, in_globals frame_G a ->
               mbyte rsegs m3 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m3 a)).
    { intros a Hg. destruct (G2 a Hg) as [E2 W2]. destruct (GX a Hg) as (G1 & _ & G3). pose proof (sm_g_iv a Hg).
      destruct (CK4 a G1 ltac:(lia) G3) as [E4 W4]. split; [congruence | tauto]. }
    assert (BM4 : forall pn, In pn (blocks L A) -> In pn (blocks L2 A2)) by (intros pn Hin; exact (M12 _ (BM2 _ Hin))).
    assert (BK4 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m3 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hi. rewrite (KEPT4 a k i (BM2 _ Hin) (fun F => F) Hi). exact (BK2 a k i Hin Hi). }
    assert (SW4 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m3 a).
    { intros a Ha. destruct (Z_lt_ge_dec a (bv_unsigned sp - 9216)) as [Hlo|Hhi].
      - apply (proj2 (CK4 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia))). apply SW2. lia.
      - apply HSCR2. unfold scratch_k. rewrite SP3. unfold STRDUP_STACK. change ALLOC_STACK with 8192. left. lia. }
    assert (ERR4 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m3 a)
      by (intros a Ha; apply HSCR2; right; exact Ha).
    assert (FK4 : forall a, bv_unsigned sp - 992 <= a < bv_unsigned sp ->
               mbyte rsegs m3 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a <-> writable_at rsegs m3 a))
      by (intros a Ha; exact (CK4 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia))).
    assert (QF : forall pn, In pn (concat qs) -> 1 <= snd pn /\ fresh_block B (fst pn) (snd pn)).
    { intros pn Hpn. apply in_concat in Hpn as (P & HP & Hpn).
      apply In_nth_error in HP as (i & Ei). apply In_nth_error in Hpn as (k & Ek).
      assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- QSL; apply nth_error_Some; rewrite Ei; discriminate).
      destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
      destruct (QCALL i c P Ec Ei) as [(_ & _ & HL & _) QK].
      assert (Hk : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Ek; discriminate).
      destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
      destruct (QK k s pn Es Ek) as [Hs Hf]. split; [lia | exact Hf]. }
    assert (QIN1 : forall pn, In pn (concat qs) -> In pn (blocks L1 A1)).
    { intros pn Hpn. apply (Permutation_in _ (Permutation_sym PERM2)). apply in_or_app. right. exact Hpn. }
    assert (QSEP : forall pn a k, In pn (concat qs) -> In (a, k) (blocks L A) -> 1 <= k -> fst pn <> a).
    { intros pn a k Hpn Hq Hk E. pose proof (proj1 (QF pn Hpn)) as H1. pose proof (SEP2 pn (a, k) Hpn Hq) as Hs.
      cbn in Hs. lia. }
    assert (QNO : forall pn, In pn (concat qs) -> ~ In (fst pn) (map fst O)).
    { intros pn Hpn H. apply in_map_iff in H as ([a k] & Ea & Hin). cbn in Ea.
      destruct (rep_O rsegs _ _ _ _ _ _ REP Hin) as [Hb Hk]. exact (QSEP pn a k Hpn Hb Hk (eq_sym Ea)). }
    assert (QD : forall pn, In pn (concat qs) -> fst pn + snd pn <= d \/ d + (Z.of_nat (length X) + 1) <= fst pn).
    { intros [a k] Hpn. exact (BLD a k (QIN1 _ Hpn)). }
    assert (QK3 : forall a k i, In (a, k) (concat qs) -> 0 <= i < k -> mbyte rsegs m3 (a + i) = mbyte rsegs m2 (a + i)).
    { intros a k i Hpn Hi. exact (KEPT4 a k i (QIN1 _ Hpn) (fun F => F) Hi). }
    (* store of the new state and host *)
    assert (UD : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
    assert (A0R4' : reg_get R4 10 = Z_to_bv 64 d) by exact A0R4.
    assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by exact (eq_trans (HPRES2 2 ltac:(unfold callee_saved; lia)) E3_2).
    assert (E4_4 : getr R4 4 = getr regs 4) by exact (eq_trans (HPRES2 4 ltac:(unfold callee_saved; lia)) E3_4).
    assert (E4_8 : getr R4 8 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
      by exact (eq_trans (HPRES2 8 ltac:(unfold callee_saved; lia)) E3_8).
    assert (E4_18 : getr R4 18 = Z_to_bv 64 W) by exact (eq_trans (HPRES2 18 ltac:(unfold callee_saved; lia)) E3_18).
    assert (E4_19 : getr R4 19 = Z_to_bv 64 hb) by exact (eq_trans (HPRES2 19 ltac:(unfold callee_saved; lia)) E3_19).
    assert (E4_20 : getr R4 20 = Z_to_bv 64 sb) by exact (eq_trans (HPRES2 20 ltac:(unfold callee_saved; lia)) E3_20).
    assert (E4_21 : getr R4 21 = Z_to_bv 64 0x34028)
      by exact (eq_trans (HPRES2 21 ltac:(unfold callee_saved; lia)) E3_21).
    assert (E4_22 : getr R4 22 = Z_to_bv 64 0x343e8)
      by exact (eq_trans (HPRES2 22 ltac:(unfold callee_saved; lia)) E3_22).
    assert (E4_23 : getr R4 23 = Z_to_bv 64 (r_host R))
      by exact (eq_trans (HPRES2 23 ltac:(unfold callee_saved; lia)) E3_23).
    assert (E4_24 : getr R4 24 = sx32 (Z_to_bv 64 q))
      by exact (eq_trans (HPRES2 24 ltac:(unfold callee_saved; lia)) E3_24).
    assert (E4_25 : getr R4 25 = Z_to_bv 64 (r_state R))
      by exact (eq_trans (HPRES2 25 ltac:(unfold callee_saved; lia)) E3_25).
    assert (K4 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr Hx. rewrite (HPRES2 r Hr). exact (K3 r Hr Hx). }
    assert (REP3 : g_rec_rep rsegs L2 A2 m3 R O).
    { apply (rec_rep_frame rsegs G_REC REC_SC L1 A1 m2 R O L2 A2 m3 REP2).
      - intros a Ha. assert (Hg : in_globals frame_G a) by (apply sm_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
        destruct (GX a Hg) as (G1 & _ & G3). pose proof (sm_g_iv a Hg).
        destruct (CK4 a G1 ltac:(lia) G3) as [E W1]. split; [exact E | apply W1].
      - intros p k i Hin Hi. destruct (rep_O rsegs _ _ _ _ _ _ REP2 Hin) as [Hb _]. exact (KEPT4 p k i Hb (fun F => F) Hi).
      - intros pn Hin. destruct (rep_O rsegs _ _ _ _ _ _ REP2 Hin) as [Hb _]. exact (M12 _ Hb). }
    pose proof (rep_sh rsegs L2 A2 m3 R O REP3) as SH3.
    rewrite E3_1.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      eapply crt_s2; [ | exact E4_21 | exact SH3]. rewrite A0R4', UD. lia. }
    intros ms5 (can5 & (m4 & -> & MU4 & WM4 & SH4) & EQ5).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
    assert (E4_20' : reg_get R4 20 = Z_to_bv 64 sb) by exact E4_20.
    assert (E4_19' : reg_get R4 19 = Z_to_bv 64 hb) by exact E4_19.
    rewrite E4_20', E4_19' in SH4.
    assert (E5_1 : getr R5 1 = Z_to_bv 64 0x1500c) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
    assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; exact E4_2).
    assert (E5_4 : getr R5 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X5 eq_refl); simp_regs; exact E4_4).
    assert (E5_8 : getr R5 8 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
      by (rewrite (getr_of_eqv _ _ 8 X5 eq_refl); simp_regs; exact E4_8).
    assert (E5_9 : getr R5 9 = Z_to_bv 64 d) by (rewrite (getr_of_eqv _ _ 9 X5 eq_refl); simp_regs; exact A0R4).
    assert (E5_10 : getr R5 10 = Z_to_bv 64 W) by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact E4_18).
    assert (E5_11 : getr R5 11 = Z_to_bv 64 (bv_unsigned sp - 992))
      by (rewrite (getr_of_eqv _ _ 11 X5 eq_refl); simp_regs; exact E4_2).
    assert (E5_18 : getr R5 18 = Z_to_bv 64 W) by (rewrite (getr_of_eqv _ _ 18 X5 eq_refl); simp_regs; exact E4_18).
    assert (E5_19 : getr R5 19 = Z_to_bv 64 hb) by (rewrite (getr_of_eqv _ _ 19 X5 eq_refl); simp_regs; exact E4_19).
    assert (E5_20 : getr R5 20 = Z_to_bv 64 sb) by (rewrite (getr_of_eqv _ _ 20 X5 eq_refl); simp_regs; exact E4_20).
    assert (E5_21 : getr R5 21 = Z_to_bv 64 0x34028) by (rewrite (getr_of_eqv _ _ 21 X5 eq_refl); simp_regs; exact E4_21).
    assert (E5_22 : getr R5 22 = Z_to_bv 64 0x343e8) by (rewrite (getr_of_eqv _ _ 22 X5 eq_refl); simp_regs; exact E4_22).
    assert (E5_23 : getr R5 23 = Z_to_bv 64 (r_host R))
      by (rewrite (getr_of_eqv _ _ 23 X5 eq_refl); simp_regs; exact E4_23).
    assert (E5_24 : getr R5 24 = sx32 (Z_to_bv 64 q)) by (rewrite (getr_of_eqv _ _ 24 X5 eq_refl); simp_regs; exact E4_24).
    assert (E5_25 : getr R5 25 = Z_to_bv 64 (r_state R))
      by (rewrite (getr_of_eqv _ _ 25 X5 eq_refl); simp_regs; exact E4_25).
    assert (K5' : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R5 (Z_to_bv 5 r) = getr R4 (Z_to_bv 5 r)) by crt_keep X5.
    assert (K5 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr Hx. rewrite (K5' r Hr Hx). exact (K4 r Hr Hx). }
    clear K5'.
    assert (SP5 : spZ R5 = bv_unsigned sp - 992) by (unfold spZ; rewrite E5_2; exact USP1).
    assert (OUT4 : forall a, 0 <= a < 2 ^ 64 -> ~ (213976 <= a < 213992) ->
               mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
    { intros a Ha Hx. assert (Ho : Frame.outside [(213976, 213992)] a) by (cbn; split; [lia | exact I]).
      split; [exact (munch_mbyte _ _ _ _ _ MU4 Ha Ho) | exact (munch_writable _ _ _ _ _ MU4 Ha Ho)]. }
    assert (MR4 : aa_MR API L2 A2 m4 md2).
    { apply (KindBGlue.kb_MR_A B API L2 A2 m3 m4 md2 _ HMR2 MU4). intros x Hx Hob. cbn. split; [|exact I].
      intros Hr. assert (Hg : in_globals frame_G x) by (apply sm_g_of; lia).
      destruct Hob as [Ho|(p & k & Hpk & Hp)].
      - exact (crt_gnown L2 A2 m3 md2 x HMR2 Hg Ho).
      - apply (crt_blk_img L2 A2 m3 md2 p k (x - p) HMR2 Hpk ltac:(lia)). replace (p + (x - p)) with x by ring.
        exact (proj1 (G_STAT x Hg)). }
    assert (RO4 : ro_agree rsegs m4) by exact (crt_ro_munch _ m3 m4 RO3 MU4 crt_sh_ro).
    assert (NSH : forall a, ~ vr_writes a -> ~ (213976 <= a < 213992))
      by (intros a Hv Ha; apply Hv; left; unfold G_REC, REC_SIZE; lia).
    assert (F5 : forall a, KP a -> ~ scratch_k B CRT_K regs a -> ~ vr_writes a ->
               mbyte rsegs m4 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m4 a)).
    { intros a Ha Hs Hv. destruct (F4 a Ha Hs Hv) as [E1 W1]. destruct (OUT4 a (KPR a Ha) (NSH a Hv)) as [E2 W2].
      split; [congruence | tauto]. }
    assert (BRNG2 : forall a k i, In (a, k) (blocks L2 A2) -> 0 <= i < k -> 0 <= a + i < alloc_ceiling).
    { intros a k i Hin Hi. apply YI06.blocks_In in Hin as (p & <- & Hp).
      destruct (mr_blocks_range B _ LAWS _ _ _ _ p k HMR2 Hp). lia. }
    assert (BOUT : forall a k i, In (a, k) (blocks L2 A2) -> 0 <= i < k -> ~ (213976 <= a + i < 213992)).
    { intros a k i Hin Hi Hx. apply (crt_blk_img L2 A2 m3 md2 a k i HMR2 Hin Hi). apply (sm_img_iv B _ SEGS). lia. }
    assert (BK5 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m4 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hi. rewrite <- (BK4 a k i Hin Hi). pose proof (BRNG2 a k i (BM4 _ Hin) Hi).
      exact (proj1 (OUT4 (a + i) ltac:(lia) (BOUT a k i (BM4 _ Hin) Hi))). }
    assert (SW5 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m4 a).
    { intros a Ha. apply (proj2 (OUT4 a ltac:(lia) ltac:(lia))). apply SW4. lia. }
    assert (ERR5 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m4 a).
    { intros a Ha. apply (proj2 (OUT4 a ltac:(lia) ltac:(lia))). apply ERR4. exact Ha. }
    assert (FW2 : forall a, bv_unsigned sp - 992 <= a < bv_unsigned sp -> writable_at rsegs m2 a).
    { intros a Ha.
      destruct (Z_lt_ge_dec a (bv_unsigned sp - 984)) as [H1|H1];
        [|destruct (Z_lt_ge_dec a (bv_unsigned sp - 984 + 56 * Z.of_nat (length (r_calls R)))) as [H2|H2]].
      - apply (proj2 (CK2 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(intros Hw; pose proof (RWB a Hw); lia))).
        unfold writable_at. apply WM1. change (writable_at rsegs mem a). apply HWS. lia.
      - replace a with (bv_unsigned sp - 984 + (a - (bv_unsigned sp - 984))) by ring. apply DW2. lia.
      - apply (proj2 (CK2 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(intros Hw; pose proof (RWB a Hw); lia))).
        unfold writable_at. apply WM1. change (writable_at rsegs mem a). apply HWS. lia. }
    assert (FW5 : forall a, bv_unsigned sp - 992 <= a < bv_unsigned sp -> writable_at rsegs m4 a).
    { intros a Ha. apply (proj2 (OUT4 a ltac:(lia) ltac:(lia))). apply (proj2 (FK4 a Ha)). exact (FW2 a Ha). }
    set (R2' := set_host (set_state R sb) hb).
    assert (REP4 : g_rec_rep rsegs L2 A2 m4 R2' O).
    { apply (rep_set_sh rsegs L2 A2 m3 m4 R O sb hb REP3).
      - intros p k Hin. destruct (rep_O rsegs _ _ _ _ _ _ REP3 Hin) as [Hb Hk]. cbn [snd] in Hk.
        pose proof (BRNG2 p k 0 Hb ltac:(lia)). pose proof (BRNG2 p k (k - 1) Hb ltac:(lia)). lia.
      - intros x Hx Hn. exact (proj1 (OUT4 x Hx Hn)).
      - intros x Hw. unfold writable_at. apply WM4. exact Hw.
      - pose proof (sm_cell_get2 rsegs m4 213976 [] (C8 (Z_to_bv 64 sb)) [C8 (Z_to_bv 64 hb)] 0%nat SH4 eq_refl) as H.
        change (213976 + Z.of_nat 0) with 213976 in H. exact H.
      - pose proof (sm_cell_get2 rsegs m4 213976 [C8 (Z_to_bv 64 sb)] (C8 (Z_to_bv 64 hb)) [] 8%nat SH4 eq_refl) as H.
        change (213976 + Z.of_nat 8) with 213984 in H. exact H.
      - exact RSB.
      - exact RHB. }
    assert (GQ4 : le_at B m4 G_QUIT (Mem.le4 (Z_to_bv 64 q))).
    { apply (sm_le_keep B mem); [exact QAT|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le4 in Hi.
      unfold G_QUIT. rewrite (proj1 (OUT4 (0x343e8 + i) ltac:(lia) ltac:(lia))).
      exact (proj1 (G4 (0x343e8 + i) (sm_g_of (0x343e8 + i) ltac:(lia)))). }
    (* joined *)
    assert (WVK5 : words_view B m4 W arr wp ws).
    { apply (crt_words_view_keep B SEGS mem m4); [exact WV | | |].
      - intros a Ha. refine (proj1 (F5 a (KPH a ltac:(lia)) _ _)).
        + unfold scratch_k. rewrite CK. change (spZ regs) with (bv_unsigned sp). lia.
        + unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT. lia.
      - intros i Hi. destruct ILA as (p & k & Hpk & _ & Hp1 & Hp2).
        replace (arr + i) with (p + (arr + i - p)) by ring. apply (BK5 p k); [exact Hpk | lia].
      - intros k i Hk Hi. destruct (ILW k Hk) as (p & k' & Hpk & _ & Hp1 & Hp2).
        replace (nth k wp 0 + i) with (p + (nth k wp 0 + i - p)) by ring. apply (BK5 p k'); [exact Hpk | lia]. }
    assert (WPL5 : words_place L2 A2 m4 arr wp ws).
    { split.
      - destruct ILA as (p & k & Hpk & _ & Hp1 & Hp2). exists p, k. split; [exact (BM4 _ Hpk) | lia].
      - intros k Hk. destruct (ILW k Hk) as (p & k' & Hpk & _ & Hp1 & Hp2). exists p, k'. split; [exact (BM4 _ Hpk) | lia]. }
    assert (JN0 : 0 <= join_need ws) by exact (joined.jn_nonneg ws).
    assert (ROOM2 : forall n, 0 <= n <= VR_REQ ->
               room_slots (sb_malloc (rcc_b b (rcc_args (r_calls R))) (Z.of_nat (length X) + 1)) n).
    { intros n Hn. apply (RecKindB.room_slots_mono _ (sb_up b CRT_PEAK CRT_PEAKB) n VR_REQ); [|lia|exact ROOM].
      unfold RecKindB.sb_le, sb_up, sb_malloc. cbn [sb_live sb_bytes sb_cap]. rewrite RB1, RB2, RB3.
      unfold CRT_PEAK, SM_PEAK, CRT_PEAKB, LMAX in *. lia. }
    pose proof (JOIN L2 A2 R5 m4 md2 (sb_malloc (rcc_b b (rcc_args (r_calls R))) (Z.of_nat (length X) + 1)) W arr
                  (bv_unsigned sp - 992) wp ws) as JN5.
    unfold joined_c.JOINED, joined_c.JOINED_FRAME in JN5. rewrite SEGS in JN5.
    eapply SR_bind.
    { apply JN5; clear JN5.
      - change ALLOC_STACK with 8192.
        split; [exact MR4|]. split; [exact HWF2|]. split; [exact HBD2|].
        split; [rewrite E5_1; apply bv_eq; vm_compute; reflexivity|].
        split; [rewrite SP5; replace (bv_unsigned sp - 992) with (bv_unsigned sp + (-62) * 16) by ring;
                rewrite Z.mod_add by lia; exact HAL|].
        split; [rewrite SP5; lia|]. split; [rewrite SP5; lia|].
        split; [intros a Ha; rewrite SP5 in Ha; rewrite SEGS; apply SW5; lia|].
        split; [rewrite E5_4; exact HTP|].
        split; [intros a Ha; rewrite SEGS; exact (ERR5 a Ha)|].
        intros HI. rewrite INIT4 in HI. discriminate.
      - exact RO4.
      - exact E5_10.
      - exact E5_11.
      - exact WVK5.
      - exact WPL5.
      - exact WAL.
      - exact ARL.
      - rewrite SP5. lia.
      - lia.
      - lia.
      - rewrite SP5. lia.
      - lia.
      - left. lia.
      - intros i Hi. apply FW5. lia.
      - lia.
      - intros i Hi. split.
        + intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ _ MR4 Ho). lia.
        + unfold scratch_k. rewrite SP5. change ALLOC_STACK with 8192. intros [H|H]; lia.
      - exact RES4.
      - apply ROOM2. unfold VR_REQ. lia. }
    intros c6 RET6.
    destruct RET6 as (L3 & A3 & R6 & m5 & md3 & res & -> & POST6 & A0R6 & RNZ & RFR & RBLK & RJS & ROUT & KEPT6 & RO5 & UB6
      & INIT6 & RLEN6 & RES6).
    destruct POST6 as (HMR3 & HWF3 & HBD3 & HLE3 & HSTAB3 & HPRES3 & HVM3 & HFRAME3 & HBLKS3 & HSCR3).
    try rewrite SEGS in HFRAME3. try rewrite SEGS in HBLKS3. try rewrite SEGS in HSCR3. try rewrite SEGS in RO5.
    unfold blocks_kept in KEPT6. try rewrite SEGS in KEPT6.
    destruct (mr_model _ _ LAWS _ _ _ _ HMR3) as (Hh3 & Hl3 & Hmat3).
    destruct RBLK as (rb1 & rb2 & RBL1 & RBL2).
    destruct RFR as (RF1 & RF2 & RF3).
    assert (INBR : In (res, join_need ws + 1) (blocks L3 A3)) by (rewrite RBL1; apply in_or_app; right; left; reflexivity).
    assert (BLR3 : forall a k, In (a, k) (blocks L2 A2) -> a + k <= res \/ res + (join_need ws + 1) <= a).
    { intros a k Hin. rewrite RBL2 in Hin. exact (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR3 RBL1 Hin). }
    assert (RNO : ~ In res (map fst O)).
    { intros H. apply in_map_iff in H as ([a k] & Ea & Hin). cbn in Ea. subst a.
      destruct (rep_O rsegs _ _ _ _ _ _ REP Hin) as [Hb Hk]. cbn in Hk. pose proof (BLR3 res k (BM4 _ Hb)). lia. }
    assert (M23 : forall pn, In pn (blocks L2 A2) -> In pn (blocks L3 A3)).
    { intros pn Hin. rewrite RBL1. rewrite RBL2 in Hin.
      apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
    assert (CK6 : forall a, KP a -> ~ (bv_unsigned sp - 9264 <= a < bv_unsigned sp - 992) ->
               ~ (errno_addr B <= a < errno_addr B + 4) -> ~ (bv_unsigned sp - 992 <= a < bv_unsigned sp - 984) ->
               mbyte rsegs m5 a = mbyte rsegs m4 a /\ (writable_at rsegs m4 a <-> writable_at rsegs m5 a)).
    { intros a Ha Hs He Ho.
      apply HFRAME3; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha MR4) | exact (KPN a _ _ _ _ Ha HMR3) | |].
      - unfold scratch_k. rewrite SP5. change ALLOC_STACK with 8192. intros [H|H]; [apply Hs; lia | exact (He H)].
      - unfold joined_writes. intros [Hr|Hr]; [|apply Ho; lia].
        destruct (proj1 Ha) as [Hh'|Hi]; [lia|]. apply (RF3 (a - res)); [lia|].
        replace (res + (a - res)) with a by ring. exact Hi. }
    assert (F6 : forall a, KP a -> ~ scratch_k B CRT_K regs a -> ~ vr_writes a ->
               mbyte rsegs m5 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m5 a)).
    { intros a Ha Hs Hv. destruct (F5 a Ha Hs Hv) as [E1 W1].
      unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (CK6 a Ha ltac:(lia) Hs2 ltac:(lia)) as [E2 W2]. split; [congruence | tauto]. }
    assert (G6 : forall a, in_globals frame_G a -> ~ (213976 <= a < 213992) ->
               mbyte rsegs m5 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m5 a)).
    { intros a Hg Hn. pose proof (sm_g_iv a Hg). destruct (G4 a Hg) as [E1 W1]. destruct (OUT4 a ltac:(lia) Hn) as [E2 W2].
      destruct (GX a Hg) as (G1 & _ & G3). destruct (CK6 a G1 ltac:(lia) G3 ltac:(lia)) as [E3 W3].
      split; [congruence | tauto]. }
    assert (REP5 : g_rec_rep rsegs L3 A3 m5 R2' O).
    { apply (rec_rep_frame rsegs G_REC REC_SC L2 A2 m4 R2' O L3 A3 m5 REP4).
      - intros a Ha. assert (Hg : in_globals frame_G a) by (apply sm_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
        destruct (GX a Hg) as (G1 & _ & G3). pose proof (sm_g_iv a Hg).
        destruct (CK6 a G1 ltac:(lia) G3 ltac:(lia)) as [E W1]. split; [exact E | apply W1].
      - intros p k i Hin Hi. destruct (rep_O rsegs _ _ _ _ _ _ REP4 Hin) as [Hb _]. exact (KEPT6 p k i Hb (fun F => F) Hi).
      - intros pn Hin. destruct (rep_O rsegs _ _ _ _ _ _ REP4 Hin) as [Hb _]. exact (M23 _ Hb). }
    assert (BM6 : forall pn, In pn (blocks L A) -> In pn (blocks L3 A3)) by (intros pn Hin; exact (M23 _ (BM4 _ Hin))).
    assert (BK6 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m5 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hi. rewrite (KEPT6 a k i (BM4 _ Hin) (fun F => F) Hi). exact (BK5 a k i Hin Hi). }
    assert (SW6 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m5 a).
    { intros a Ha. destruct (Z_lt_ge_dec a (bv_unsigned sp - 9264)) as [Hlo|Hhi].
      - apply (proj2 (CK6 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))). apply SW5. lia.
      - apply HSCR3. unfold scratch_k. rewrite SP5. change ALLOC_STACK with 8192. left. lia. }
    assert (ERR6 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m5 a)
      by (intros a Ha; apply HSCR3; right; exact Ha).
    assert (FK6 : forall a, bv_unsigned sp - 984 <= a < bv_unsigned sp ->
               mbyte rsegs m5 a = mbyte rsegs m4 a /\ (writable_at rsegs m4 a <-> writable_at rsegs m5 a))
      by (intros a Ha; exact (CK6 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))).
    assert (GQ6 : le_at B m5 G_QUIT (Mem.le4 (Z_to_bv 64 q))).
    { apply (sm_le_keep B m4); [exact GQ4|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le4 in Hi.
      unfold G_QUIT. destruct (GX (0x343e8 + i) (sm_g_of (0x343e8 + i) ltac:(lia))) as (G1 & _ & G3).
      exact (proj1 (CK6 (0x343e8 + i) G1 ltac:(lia) G3 ltac:(lia))). }
    assert (RK6 : relro_kept mem m5).
    { intros a Ha Hg. destruct (RLX a Ha Hg) as (Q1 & Q2 & Q3). exact (proj1 (F6 a Q1 Q2 Q3)). }
    destruct (ax_statics AX L3 A3 m5 md3 HMR3) as (WG6 & (g6 & Hg6 & WGG6) & _).
    rewrite SEGS, GOT_AT, GUARD_AT in WG6. rewrite SEGS, GUARD_AT in WGG6.
    pose proof (crt_cmd_mem_keep B SEGS mem m5 g6 CMD0 RO5 RK6 WG6 WGG6 Hg6) as CMD6.
    pose proof (crt_vr_tables_keep B SEGS mem m5 can g6 VT RK6 WG6 WGG6 Hg6) as VT6.
    assert (E6_2 : getr R6 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by exact (eq_trans (HPRES3 2 ltac:(unfold callee_saved; lia)) E5_2).
    assert (E6_4 : getr R6 4 = getr regs 4) by exact (eq_trans (HPRES3 4 ltac:(unfold callee_saved; lia)) E5_4).
    assert (E6_8 : getr R6 8 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
      by exact (eq_trans (HPRES3 8 ltac:(unfold callee_saved; lia)) E5_8).
    assert (E6_9 : getr R6 9 = Z_to_bv 64 d) by exact (eq_trans (HPRES3 9 ltac:(unfold callee_saved; lia)) E5_9).
    assert (E6_19 : getr R6 19 = Z_to_bv 64 hb) by exact (eq_trans (HPRES3 19 ltac:(unfold callee_saved; lia)) E5_19).
    assert (E6_20 : getr R6 20 = Z_to_bv 64 sb) by exact (eq_trans (HPRES3 20 ltac:(unfold callee_saved; lia)) E5_20).
    assert (E6_21 : getr R6 21 = Z_to_bv 64 0x34028)
      by exact (eq_trans (HPRES3 21 ltac:(unfold callee_saved; lia)) E5_21).
    assert (E6_22 : getr R6 22 = Z_to_bv 64 0x343e8)
      by exact (eq_trans (HPRES3 22 ltac:(unfold callee_saved; lia)) E5_22).
    assert (E6_23 : getr R6 23 = Z_to_bv 64 (r_host R))
      by exact (eq_trans (HPRES3 23 ltac:(unfold callee_saved; lia)) E5_23).
    assert (E6_24 : getr R6 24 = sx32 (Z_to_bv 64 q))
      by exact (eq_trans (HPRES3 24 ltac:(unfold callee_saved; lia)) E5_24).
    assert (E6_25 : getr R6 25 = Z_to_bv 64 (r_state R))
      by exact (eq_trans (HPRES3 25 ltac:(unfold callee_saved; lia)) E5_25).
    assert (K6 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R6 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr Hx. rewrite (HPRES3 r Hr). exact (K5 r Hr Hx). }
    assert (LW : bytes_at rsegs m5 (bv_unsigned sp - 992) (le8 (Z_to_bv 64 (Z.of_nat (length (join_sp ws)))))).
    { apply (sm_bytes_of_le B m5 _ _ SEGS); [lia | rewrite Mem.length_le8; lia | exact ROUT]. }
    assert (E6_2' : reg_get R6 2 = Z_to_bv 64 (bv_unsigned sp - 992)) by exact E6_2.
    rewrite E5_1.
    eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E6_2'.
      eapply crt_s3 with (lw := Z_to_bv 64 (Z.of_nat (length (join_sp ws)))). rewrite USP1. exact LW. }
    intros ms7 (can7 & -> & EQ7).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ7 eq_refl eq_refl) as (R7 & -> & X7).
    assert (E7_1 : getr R7 1 = Z_to_bv 64 0x15018) by (rewrite (getr_of_eqv _ _ 1 X7 eq_refl); simp_regs; reflexivity).
    assert (E7_2 : getr R7 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by (rewrite (getr_of_eqv _ _ 2 X7 eq_refl); simp_regs; reflexivity).
    assert (E7_4 : getr R7 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X7 eq_refl); simp_regs; exact E6_4).
    assert (E7_8 : getr R7 8 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
      by (rewrite (getr_of_eqv _ _ 8 X7 eq_refl); simp_regs; exact E6_8).
    assert (E7_9 : getr R7 9 = Z_to_bv 64 d) by (rewrite (getr_of_eqv _ _ 9 X7 eq_refl); simp_regs; exact E6_9).
    assert (E7_10 : getr R7 10 = Z_to_bv 64 res) by (rewrite (getr_of_eqv _ _ 10 X7 eq_refl); simp_regs; exact A0R6).
    assert (E7_11 : getr R7 11 = Z_to_bv 64 (Z.of_nat (length (join_sp ws))))
      by (rewrite (getr_of_eqv _ _ 11 X7 eq_refl); simp_regs; reflexivity).
    assert (E7_18 : getr R7 18 = Z_to_bv 64 res) by (rewrite (getr_of_eqv _ _ 18 X7 eq_refl); simp_regs; exact A0R6).
    assert (E7_19 : getr R7 19 = Z_to_bv 64 hb) by (rewrite (getr_of_eqv _ _ 19 X7 eq_refl); simp_regs; exact E6_19).
    assert (E7_20 : getr R7 20 = Z_to_bv 64 sb) by (rewrite (getr_of_eqv _ _ 20 X7 eq_refl); simp_regs; exact E6_20).
    assert (E7_21 : getr R7 21 = Z_to_bv 64 0x34028) by (rewrite (getr_of_eqv _ _ 21 X7 eq_refl); simp_regs; exact E6_21).
    assert (E7_22 : getr R7 22 = Z_to_bv 64 0x343e8) by (rewrite (getr_of_eqv _ _ 22 X7 eq_refl); simp_regs; exact E6_22).
    assert (E7_23 : getr R7 23 = Z_to_bv 64 (r_host R))
      by (rewrite (getr_of_eqv _ _ 23 X7 eq_refl); simp_regs; exact E6_23).
    assert (E7_24 : getr R7 24 = sx32 (Z_to_bv 64 q)) by (rewrite (getr_of_eqv _ _ 24 X7 eq_refl); simp_regs; exact E6_24).
    assert (E7_25 : getr R7 25 = Z_to_bv 64 (r_state R))
      by (rewrite (getr_of_eqv _ _ 25 X7 eq_refl); simp_regs; exact E6_25).
    assert (K7' : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R7 (Z_to_bv 5 r) = getr R6 (Z_to_bv 5 r)) by crt_keep X7.
    assert (K7 : forall r, callee_saved r -> ~ (r = 2 \/ r = 8 \/ r = 9 \/ (18 <= r <= 25)) ->
               getr R7 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr Hx. rewrite (K7' r Hr Hx). exact (K6 r Hr Hx). }
    clear K7'.
    assert (SP7 : spZ R7 = bv_unsigned sp - 992) by (unfold spZ; rewrite E7_2; exact USP1).
    assert (JSL : Z.of_nat (length (join_sp ws)) + 1 = join_need ws) by exact (joined.jsp_len ws WSNE).
    assert (ROOM3 : room_slots (sb_up (sb_malloc (sb_malloc (rcc_b b (rcc_args (r_calls R))) (Z.of_nat (length X) + 1))
                                  (join_need ws + 1)) SM_PEAK SM_PEAKB) VR_REQ).
    { apply (RecKindB.room_slots_mono _ (sb_up b CRT_PEAK CRT_PEAKB) VR_REQ VR_REQ); [|unfold VR_REQ; lia|exact ROOM].
      unfold RecKindB.sb_le, sb_up, sb_malloc. cbn [sb_live sb_bytes sb_cap]. rewrite RB1, RB2, RB3.
      unfold CRT_PEAK, SM_PEAK, CRT_PEAKB, SM_PEAKB, LMAX in *. lia. }
    pose proof (SEND L3 A3 R7 m5 md3 (sb_malloc (sb_malloc (rcc_b b (rcc_args (r_calls R))) (Z.of_nat (length X) + 1))
                  (join_need ws + 1)) R2' O res (Z.of_nat (length (join_sp ws))) q (join_sp ws) (Z_to_bv 64 g6)) as SM.
    unfold SEND_MESSAGE in SM. rewrite SEGS in SM.
    eapply SR_bind.
    { apply SM; clear SM.
      - reflexivity.
      - unfold call_pre_t, SM_K, SEND_MESSAGE_FRAME, VR_K. split.
        + split; [exact HMR3|]. split; [exact HWF3|]. split; [exact HBD3|].
          split; [rewrite E7_1; apply bv_eq; vm_compute; reflexivity|].
          split; [rewrite SP7; replace (bv_unsigned sp - 992) with (bv_unsigned sp + (-62) * 16) by ring;
                  rewrite Z.mod_add by lia; exact HAL|].
          split; [rewrite SP7; lia|]. split; [rewrite SP7; lia|].
          split; [intros a Ha; rewrite SP7 in Ha; rewrite SEGS; apply SW6; lia|].
          split; [rewrite E7_4; exact HTP|].
          split; [intros a Ha; rewrite SEGS; exact (ERR6 a Ha)|].
          intros HI. rewrite INIT6 in HI. discriminate.
        + rewrite SP7. lia.
      - exact CMD6.
      - exact FRM.
      - exact E7_10.
      - exact E7_11.
      - exact (crt_le_prefix B m5 res (join_sp ws) [nul8] RJS).
      - reflexivity.
      - lia.
      - intros _. split; [lia|]. split; [lia|]. split.
        + exists res, (join_need ws + 1). split; [exact INBR|]. split; [exact RNO|]. lia.
        + intros i Hi. split.
          * intros Hv. apply (RF3 i ltac:(lia)). apply (sm_img_iv B _ SEGS).
            unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT in Hv. lia.
          * unfold scratch_k. rewrite SP7. unfold SM_K, SEND_MESSAGE_FRAME, VR_K. intros [H|H]; [lia|].
            apply (RF3 i ltac:(lia)). apply (sm_img_iv B _ SEGS). rewrite ERRV in H. lia.
      - exact REP5.
      - unfold R2'. cbn [r_refuse r_code set_host set_state]. exact DECL.
      - exact GQ6.
      - intros i Hi. unfold G_QUIT.
        destruct (G6 (0x343e8 + i) (sm_g_of (0x343e8 + i) ltac:(lia)) ltac:(lia)) as [_ W1].
        apply W1. exact (QWR i Hi).
      - intros i Hi. split.
        + exact (crt_gnown L3 A3 m5 md3 (G_QUIT + i) HMR3 (sm_g_of (G_QUIT + i) ltac:(unfold G_QUIT; lia))).
        + unfold scratch_k. rewrite SP7. unfold SM_K, SEND_MESSAGE_FRAME, VR_K, G_QUIT. rewrite ERRV. lia.
      - exact VT6.
      - exact RES6.
      - exact ROOM3. }
    intros c8 RET8.
    destruct RET8 as (fx' & L4 & A4 & R8 & m6 & md4 & O4 & b8 & -> & FZ & RLEN8 & POST8 & CMD8 & RUN8 & DAT8 & BL8
      & STAY8 & NO8 & KEPT8 & INIT8 & VT8 & RES8 & CAP8).
    destruct POST8 as (HMR4 & HWF4 & HBD4 & HLE4 & HSTAB4 & HPRES4 & HVM4 & HFRAME4 & HBLKS4 & HSCR4).
    try rewrite SEGS in HFRAME4. try rewrite SEGS in HBLKS4. try rewrite SEGS in HSCR4.
    unfold blocks_kept in KEPT8. try rewrite SEGS in KEPT8.
    destruct (mr_model _ _ LAWS _ _ _ _ HMR4) as (Hh4 & Hl4 & Hmat4).
    pose proof CMD8 as (RO6 & _ & _ & _). try rewrite SEGS in RO6.
    pose proof (vr_run_rc (rec_clear (set_host (set_state R sb) hb)) (join_sp ws)) as VRC.
    pose proof (vr_run_spill (rec_clear (set_host (set_state R sb) hb)) (join_sp ws) ltac:(cbn; lia)) as VRS.
    unfold R2' in RUN8.
    revert RUN8 RT1 VRC VRS.
    destruct (vr_run (rec_clear (set_host (set_state R sb) hb)) (join_sp ws)) as [[R9 x9] quit9].
    intros (REP8 & GQ8) (RC9 & RR9 & RQ9 & RS9 & RH9) VRC VRS.
    cbn [fst rec_clear set_host set_state r_refuse r_code r_spill] in VRC, VRS.
    try rewrite SEGS in REP8. rewrite RQ9 in GQ8.
    assert (CK8 : forall a, KP a -> ~ (bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992) ->
               ~ (errno_addr B <= a < errno_addr B + 4) -> ~ vr_writes a ->
               mbyte rsegs m6 a = mbyte rsegs m5 a /\ (writable_at rsegs m5 a <-> writable_at rsegs m6 a)).
    { intros a Ha Hs He Hv.
      apply HFRAME4; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha HMR3) | exact (KPN a _ _ _ _ Ha HMR4) | | exact Hv].
      unfold scratch_k. rewrite SP7. unfold SM_K, SEND_MESSAGE_FRAME, VR_K. intros [H|H]; [apply Hs; lia | exact (He H)]. }
    assert (F8 : forall a, KP a -> ~ scratch_k B CRT_K regs a -> ~ vr_writes a ->
               mbyte rsegs m6 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m6 a)).
    { intros a Ha Hs Hv. destruct (F6 a Ha Hs Hv) as [E1 W1].
      unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (CK8 a Ha ltac:(lia) Hs2 Hv) as [E2 W2]. split; [congruence | tauto]. }
    assert (BM8 : forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> In pn (blocks L4 A4))
      by (intros pn Hin Hno; exact (STAY8 pn (BM6 pn Hin) Hno)).
    assert (BK8 : forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
               mbyte rsegs m6 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hno Hi. rewrite <- (BK6 a k i Hin Hi).
      apply (KEPT8 a k i (BM6 _ Hin)); [|exact Hi]. intros (k' & H). apply Hno. exact (in_map fst _ _ H). }
    assert (SW8 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m6 a).
    { intros a Ha. apply HSCR4. unfold scratch_k. rewrite SP7. unfold SM_K, SEND_MESSAGE_FRAME, VR_K. left. lia. }
    assert (ERR8 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m6 a)
      by (intros a Ha; apply HSCR4; right; exact Ha).
    assert (FK8 : forall a, bv_unsigned sp - 984 <= a < bv_unsigned sp ->
               mbyte rsegs m6 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a <-> writable_at rsegs m6 a)).
    { intros a Ha. destruct (FK4 a ltac:(lia)) as [E3 W3].
      destruct (OUT4 a ltac:(lia) ltac:(lia)) as [E4 W4]. destruct (FK6 a Ha) as [E5 W5].
      destruct (CK8 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia)
                  ltac:(unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT; lia)) as [E6 W6].
      split; [congruence | tauto]. }
    assert (NOO : forall pn, In pn (blocks L3 A3) -> ~ In (fst pn) (map fst O) -> In pn (blocks L4 A4)) by exact STAY8.
    assert (DIN8 : In (d, Z.of_nat (length X) + 1) (blocks L4 A4)) by exact (NOO _ (M23 _ INBD) DNO).
    assert (RIN8 : In (res, join_need ws + 1) (blocks L4 A4)) by exact (NOO _ INBR RNO).
    assert (QIN8 : forall pn, In pn (concat qs) -> In pn (blocks L4 A4))
      by (intros pn Hpn; exact (NOO _ (M23 _ (M12 _ (QIN1 _ Hpn))) (QNO _ Hpn))).
    assert (KEPT_NO : forall a k i, In (a, k) (blocks L3 A3) -> ~ In a (map fst O) -> 0 <= i < k ->
               mbyte rsegs m6 (a + i) = mbyte rsegs m5 (a + i)).
    { intros a k i Hin Hno Hi. apply (KEPT8 a k i Hin); [|exact Hi]. intros (k' & H). apply Hno. exact (in_map fst _ _ H). }
    assert (DBY8 : forall i, (i < S (length X))%nat ->
               mbyte rsegs m6 (d + Z.of_nat i) = nth_error (X ++ [Z_to_bv 8 0]) i).
    { intros i Hi. rewrite (KEPT_NO d (Z.of_nat (length X) + 1) (Z.of_nat i) (M23 _ INBD) DNO ltac:(lia)).
      rewrite (KEPT6 d (Z.of_nat (length X) + 1) (Z.of_nat i) INBD (fun F => F) ltac:(lia)).
      rewrite (proj1 (OUT4 (d + Z.of_nat i) ltac:(lia) (BOUT d _ (Z.of_nat i) INBD ltac:(lia)))).
      exact (DBY i Hi). }
    assert (QK8 : forall a k i, In (a, k) (concat qs) -> 0 <= i < k -> mbyte rsegs m6 (a + i) = mbyte rsegs m2 (a + i)).
    { intros a k i Hpn Hi. rewrite (KEPT_NO a k i (M23 _ (M12 _ (QIN1 _ Hpn))) (QNO _ Hpn) Hi).
      rewrite (KEPT6 a k i (M12 _ (QIN1 _ Hpn)) (fun F => F) Hi).
      rewrite (proj1 (OUT4 (a + i) ltac:(pose proof (BRNG2 a k i (M12 _ (QIN1 _ Hpn)) Hi); lia)
                         (BOUT a k i (M12 _ (QIN1 _ Hpn)) Hi))).
      exact (QK3 a k i Hpn Hi). }
    assert (E8_2 : getr R8 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by exact (eq_trans (HPRES4 2 ltac:(unfold callee_saved; lia)) E7_2).
    assert (K8 : forall r, callee_saved r -> getr R8 (Z_to_bv 5 r) = getr R7 (Z_to_bv 5 r)) by exact HPRES4.
    rewrite E7_1.
    eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply crt_s4. }
    intros ms9 (can9 & -> & EQ9).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ9 eq_refl eq_refl) as (RG9 & -> & X9).
    assert (E9_1 : getr RG9 1 = Z_to_bv 64 0x15020) by (rewrite (getr_of_eqv _ _ 1 X9 eq_refl); simp_regs; reflexivity).
    assert (E9_2 : getr RG9 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by (rewrite (getr_of_eqv _ _ 2 X9 eq_refl); simp_regs; exact E8_2).
    assert (E9_4 : getr RG9 4 = getr regs 4).
    { rewrite (getr_of_eqv _ _ 4 X9 eq_refl); simp_regs.
      exact (eq_trans (K8 4 ltac:(unfold callee_saved; lia)) E7_4). }
    assert (E9_10 : getr RG9 10 = Z_to_bv 64 res).
    { rewrite (getr_of_eqv _ _ 10 X9 eq_refl); simp_regs.
      exact (eq_trans (K8 18 ltac:(unfold callee_saved; lia)) E7_18). }
    assert (KK9 : forall r, callee_saved r -> getr RG9 (Z_to_bv 5 r) = getr R8 (Z_to_bv 5 r)).
    { intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X9) by reflexivity; reflexivity|]).
      subst r; rewrite (getr_of_eqv _ _ _ X9) by reflexivity; reflexivity. }
    assert (SP9 : spZ RG9 = bv_unsigned sp - 992) by (unfold spZ; rewrite E9_2; exact USP1).
    destruct (proj1 (YI06.blocks_In L4 A4 res (join_need ws + 1)) RIN8) as (pres & PRES & UPRES).
    assert (PRE9 : call_pre B (aa_MR API) L4 A4 RG9 m6 md4).
    { split; [exact HMR4|]. split; [exact HWF4|]. split; [exact HBD4|].
      split; [rewrite E9_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP9; replace (bv_unsigned sp - 992) with (bv_unsigned sp + (-62) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP9; change ALLOC_STACK with 8192; lia|]. split; [rewrite SP9; lia|].
      split; [intros a Ha; rewrite SP9 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite SEGS; apply SW8; lia|].
      split; [rewrite E9_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; exact (ERR8 a Ha)|].
      intros HI. rewrite (INIT8 INIT6) in HI. discriminate. }
    pose proof (FREE fx' L4 A4 RG9 m6 md4 pres (join_need ws + 1) b8) as FRE.
    rewrite SEGS, FREE_PC in FRE.
    eapply SR_bind; [exact (FRE PRE9 RO6 UPRES ltac:(rewrite E9_10, PRES; reflexivity) RES8) |]. clear FRE.
    intros c10 RET10.
    destruct RET10 as (L5 & A5 & RG10 & m7 & md5 & -> & POST10 & BLK10 & KEPT10 & RO7 & GK10 & UB10 & INIT10 & RLEN10
      & RES10).
    destruct POST10 as (HMR5 & HWF5 & HBD5 & HLE5 & HSTAB5 & HPRES5 & HVM5 & HFRAME5 & HBLKS5 & HSCR5).
    try rewrite SEGS in HFRAME5. try rewrite SEGS in HBLKS5. try rewrite SEGS in HSCR5. try rewrite SEGS in RO7.
    unfold blocks_kept in KEPT10. try rewrite SEGS in KEPT10.
    rewrite PRES in BLK10, KEPT10, HFRAME5.
    destruct BLK10 as (e1 & e2 & BL10a & BL10b).
    destruct (mr_model _ _ LAWS _ _ _ _ HMR5) as (Hh5 & Hl5 & Hmat5).
    assert (PW4 : pairwise ranges_disjoint (blocks L4 A4)) by exact (mr_blocks_disjoint B _ LAWS _ _ _ _ HMR4).
    assert (NRES : forall a k, In (a, k) (blocks L4 A4) -> 1 <= k -> (a, k) <> (res, join_need ws + 1) -> a <> res).
    { intros a k Hin Hk Hne E. subst a. pose proof (pw_in_disjoint _ _ _ PW4 Hin RIN8 Hne) as Hd.
      unfold ranges_disjoint in Hd. cbn in Hd. lia. }
    assert (M45 : forall pn, In pn (blocks L4 A4) -> pn <> (res, join_need ws + 1) -> In pn (blocks L5 A5)).
    { intros pn Hin Hne. rewrite BL10b. rewrite BL10a in Hin.
      apply in_app_or in Hin as [H|[H|H]]; [apply in_or_app; left; exact H | congruence | apply in_or_app; right; exact H]. }
    assert (CK10 : forall a, KP a -> ~ (bv_unsigned sp - 9184 <= a < bv_unsigned sp - 992) ->
               ~ (errno_addr B <= a < errno_addr B + 4) ->
               mbyte rsegs m7 a = mbyte rsegs m6 a /\ (writable_at rsegs m6 a <-> writable_at rsegs m7 a)).
    { intros a Ha Hs He.
      apply HFRAME5; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha HMR4) | exact (KPN a _ _ _ _ Ha HMR5) | |].
      - unfold scratch. rewrite SP9. change ALLOC_STACK with 8192. intros [H|H]; [apply Hs; lia | exact (He H)].
      - intros Hr. destruct (proj1 Ha) as [Hh'|Hi]; [lia|]. apply (RF3 (a - res)); [lia|].
        replace (res + (a - res)) with a by ring. exact Hi. }
    assert (RNEW : forall a k, In (a, k) (blocks L2 A2) -> 1 <= k -> a <> res).
    { intros a k Hin Hk E. subst a. pose proof (BLR3 res k Hin). lia. }
    assert (F10 : forall a, KP a -> ~ scratch_k B CRT_K regs a -> ~ vr_writes a ->
               mbyte rsegs m7 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m7 a)).
    { intros a Ha Hs Hv. destruct (F8 a Ha Hs Hv) as [E1 W1].
      unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (CK10 a Ha ltac:(lia) Hs2) as [E2 W2]. split; [congruence | tauto]. }
    assert (BM10 : forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> In pn (blocks L5 A5)).
    { intros [a k] Hin Hno. apply M45; [exact (BM8 _ Hin Hno)|]. intros E. injection E as Ea Ek. subst a k.
      exact (RNEW res (join_need ws + 1) (BM4 _ Hin) ltac:(lia) eq_refl). }
    assert (BK10 : forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
               mbyte rsegs m7 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hno Hi. rewrite <- (BK8 a k i Hin Hno Hi).
      apply (KEPT10 a k i (BM8 _ Hin Hno)); [|exact Hi]. exact (RNEW a k (BM4 _ Hin) ltac:(lia)). }
    assert (SW10 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m7 a).
    { intros a Ha. destruct (Z_lt_ge_dec a (bv_unsigned sp - 9184)) as [Hlo|Hhi].
      - apply (proj2 (CK10 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia))). apply SW8. lia.
      - apply HSCR5. unfold scratch. rewrite SP9. change ALLOC_STACK with 8192. left. lia. }
    assert (ERR10 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m7 a)
      by (intros a Ha; apply HSCR5; right; exact Ha).
    assert (FK10 : forall a, bv_unsigned sp - 984 <= a < bv_unsigned sp ->
               mbyte rsegs m7 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a <-> writable_at rsegs m7 a)).
    { intros a Ha. destruct (FK8 a Ha) as [E1 W1]. destruct (CK10 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia)) as [E2 W2].
      split; [congruence | tauto]. }
    assert (DNR : d <> res) by exact (RNEW d _ INBD ltac:(lia)).
    assert (DIN10 : In (d, Z.of_nat (length X) + 1) (blocks L5 A5)).
    { apply M45; [exact DIN8|]. intros E. injection E as Ed _. exact (DNR Ed). }
    assert (QNR : forall pn, In pn (concat qs) -> fst pn <> res).
    { intros [a k] Hpn. exact (RNEW a k (M12 _ (QIN1 _ Hpn)) (proj1 (QF _ Hpn))). }
    assert (QIN10 : forall pn, In pn (concat qs) -> In pn (blocks L5 A5)).
    { intros pn Hpn. apply M45; [exact (QIN8 _ Hpn)|]. intros E. apply (QNR pn Hpn). rewrite E. reflexivity. }
    assert (DBY10 : forall i, (i < S (length X))%nat ->
               mbyte rsegs m7 (d + Z.of_nat i) = nth_error (X ++ [Z_to_bv 8 0]) i).
    { intros i Hi. rewrite (KEPT10 d (Z.of_nat (length X) + 1) (Z.of_nat i) DIN8 DNR ltac:(lia)). exact (DBY8 i Hi). }
    assert (QK10 : forall a k i, In (a, k) (concat qs) -> 0 <= i < k -> mbyte rsegs m7 (a + i) = mbyte rsegs m2 (a + i)).
    { intros a k i Hpn Hi. rewrite (KEPT10 a k i (QIN8 _ Hpn) (QNR _ Hpn) Hi). exact (QK8 a k i Hpn Hi). }
    assert (BRNG5 : forall a k, In (a, k) (blocks L5 A5) -> 0 <= a /\ a + k <= alloc_ceiling).
    { intros a k Hin. apply YI06.blocks_In in Hin as (p & <- & Hp).
      destruct (mr_blocks_range B _ LAWS _ _ _ _ p k HMR5 Hp). lia. }
    assert (R4NO : ~ In (res, join_need ws + 1) O4) by exact (NO8 _ INBR RNO).
    assert (REP10 : g_rec_rep rsegs L5 A5 m7 R9 O4).
    { apply (rec_rep_frame rsegs G_REC REC_SC L4 A4 m6 R9 O4 L5 A5 m7 REP8).
      - intros a Ha. assert (Hg : in_globals frame_G a) by (apply sm_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
        destruct (GX a Hg) as (G1 & _ & G3). pose proof (sm_g_iv a Hg).
        destruct (CK10 a G1 ltac:(lia) G3) as [E W1]. split; [exact E | apply W1].
      - intros p k i Hin Hi. destruct (rep_O rsegs _ _ _ _ _ _ REP8 Hin) as [Hb Hk]. cbn [snd] in Hk.
        apply (KEPT10 p k i Hb); [|exact Hi]. apply (NRES p k Hb Hk). intros E. rewrite E in Hin. exact (R4NO Hin).
      - intros pn Hin. destruct (rep_O rsegs _ _ _ _ _ _ REP8 Hin) as [Hb _]. apply (M45 _ Hb).
        intros E. rewrite E in Hin. exact (R4NO Hin). }
    assert (GQ10 : le_at B m7 G_QUIT (Mem.le4 (Z_to_bv 64 q))).
    { apply (sm_le_keep B m6); [exact GQ8|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le4 in Hi.
      unfold G_QUIT. destruct (GX (0x343e8 + i) (sm_g_of (0x343e8 + i) ltac:(lia))) as (G1 & _ & G3).
      exact (proj1 (CK10 (0x343e8 + i) G1 ltac:(lia) G3)). }
    assert (KR : forall r, callee_saved r -> getr RG10 (Z_to_bv 5 r) = getr R7 (Z_to_bv 5 r))
      by (intros r Hr; exact (eq_trans (HPRES5 r Hr) (eq_trans (KK9 r Hr) (K8 r Hr)))).
    assert (E10_2' : reg_get RG10 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by exact (eq_trans (KR 2 ltac:(unfold callee_saved; lia)) E7_2).
    assert (E10_4 : getr RG10 4 = getr regs 4) by exact (eq_trans (KR 4 ltac:(unfold callee_saved; lia)) E7_4).
    assert (E10_8 : getr RG10 8 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
      by exact (eq_trans (KR 8 ltac:(unfold callee_saved; lia)) E7_8).
    assert (E10_9' : reg_get RG10 9 = Z_to_bv 64 d) by exact (eq_trans (KR 9 ltac:(unfold callee_saved; lia)) E7_9).
    assert (E10_21 : getr RG10 21 = Z_to_bv 64 0x34028)
      by exact (eq_trans (KR 21 ltac:(unfold callee_saved; lia)) E7_21).
    assert (E10_22 : getr RG10 22 = Z_to_bv 64 0x343e8)
      by exact (eq_trans (KR 22 ltac:(unfold callee_saved; lia)) E7_22).
    assert (E10_23' : reg_get RG10 23 = Z_to_bv 64 (r_host R))
      by exact (eq_trans (KR 23 ltac:(unfold callee_saved; lia)) E7_23).
    assert (E10_24 : getr RG10 24 = sx32 (Z_to_bv 64 q))
      by exact (eq_trans (KR 24 ltac:(unfold callee_saved; lia)) E7_24).
    assert (E10_25' : reg_get RG10 25 = Z_to_bv 64 (r_state R))
      by exact (eq_trans (KR 25 ltac:(unfold callee_saved; lia)) E7_25).
    destruct (rep_calls rsegs L5 A5 m7 R9 O4 REP10) as (Ps9 & PSL & PSC).
    destruct (rep_ncalls rsegs L5 A5 m7 R9 O4 REP10) as (NCB9 & NC9 & _).
    assert (RX9 : r_reply R9 = Some (X ++ [Z_to_bv 8 0])) by (rewrite RR9; exact RX).
    destruct (rep_reply rsegs L5 A5 m7 R9 O4 _ REP10 RX9) as (p9 & n9 & BRP9 & P9Z & P9O & P9B & P9L & P9X & _).
    destruct (rep_scal rsegs L5 A5 m7 R9 O4 REP10) as (BST9 & BHO9 & _ & _).
    rewrite RS9 in BST9. rewrite RH9 in BHO9. rewrite RC9 in NCB9, NC9, PSL, PSC.
    destruct (BRNG5 p9 n9 P9B) as [P9lo P9hi].
    rewrite length_app in P9L. cbn [length] in P9L.
    assert (UP9 : bv_unsigned (Z_to_bv 64 p9) = p9) by (apply unsigned_lit; lia).
    assert (STK10 : stk rsegs m7 (bv_unsigned sp - 9184) (bv_unsigned sp - 992)).
    { apply stk_of_writable; [lia | lia |]. intros a Ha. apply SW10. lia. }
    assert (CA : calls_at m7 (bv_unsigned sp - 992 - 128) (bv_unsigned sp - 992) (bv_unsigned sp - 992 + 8)
                   (rcs (r_calls R) qs)).
    { apply (calls_at_rcs (concat qs) m7 _ _ _ (r_calls R) qs NC16 QSL).
      intros i c P Ec EP. destruct (QCALL i c P Ec EP) as [HC _].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      assert (HQ : forall pn, In pn P -> In pn (concat qs)).
      { intros pn Hpn. apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact Hpn]. }
      split; [|split].
      - replace (bv_unsigned sp - 992 + 8 + 56 * Z.of_nat i) with (bv_unsigned sp - 984 + 56 * Z.of_nat i) by ring.
        apply (call_at_keep rsegs (blocks L1 A1) (concat qs) m2 m7 _ c P HC).
        + intros x Hx. unfold CALL_SIZE in Hx. exact (proj1 (FK10 x ltac:(lia))).
        + intros [a k] Hpn. split; [exact (HQ _ Hpn)|]. intros j Hj. exact (QK10 a k j (HQ _ Hpn) Hj).
      - unfold apart. right. lia.
      - intros [a k] Hpn. unfold apart. left. destruct (BRNG5 a k (QIN10 _ (HQ _ Hpn))). cbn. lia. }
    assert (CB : calls_at m7 (bv_unsigned sp - 992 - 128) (bv_unsigned sp - 992) 213048 (rcs (r_calls R) Ps9)).
    { apply (calls_at_rcs (blocks L5 A5) m7 _ _ _ (r_calls R) Ps9 NC16 PSL).
      intros i c P Ec EP. destruct (PSC i c P Ec EP) as [HC HO].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      split; [exact HC|]. split; [unfold apart; left; lia|].
      intros [a k] Hpn. unfold apart. left. destruct (rep_O rsegs _ _ _ _ _ _ REP10 (HO _ Hpn)) as [Hb _].
      destruct (BRNG5 a k Hb). cbn. lia. }
    assert (EQB : calls_eqb (rcs (r_calls R) qs) (rcs (r_calls R) Ps9) = true).
    { apply calls_eqb_rcs; [exact QSL | exact PSL | |].
      - intros i c P Ec EP. destruct (QCALL i c P Ec EP) as [(_ & _ & HL & _) _]. exact HL.
      - intros i c P Ec EP. destruct (PSC i c P Ec EP) as [(_ & _ & HL & _) _]. exact HL. }
    assert (DUPB10 : bytes_at rsegs m7 d (X ++ [Z_to_bv 8 0])).
    { apply bytes_at_of_mbyte; [lia | rewrite length_app; cbn [length]; lia |].
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply DBY10. lia. }
    assert (QB10 : bytes_at rsegs m7 0x343e8 (le4 (Z_to_bv 64 q))).
    { apply (sm_bytes_of_le B m7 _ _ SEGS); [lia | rewrite Mem.length_le4; lia | exact GQ10]. }
    rewrite E9_1.
    eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E10_2', E10_9', E10_23', E10_25'.
      eapply (crt_s5 RCE STRCMP) with (lo := bv_unsigned sp - 9184) (q := q) (ca := rcs (r_calls R) qs)
        (cb := rcs (r_calls R) Ps9) (rpw := Z_to_bv 64 p9) (sx := X) (sy := X); rewrite ?USP1, ?UD, ?UP9.
      - exact E10_21.
      - exact E10_22.
      - rewrite rcs_length by exact QSL. exact E10_8.
      - exact E10_24.
      - exact RO7.
      - exact STK10.
      - lia.
      - lia.
      - lia.
      - rewrite rcs_length by exact PSL. exact NCB9.
      - rewrite rcs_length by exact PSL. exact NC9.
      - exact CA.
      - exact CB.
      - exact EQB.
      - exact BRP9.
      - exact P9Z.
      - exact P9X.
      - exact NX.
      - lia.
      - exact DUPB10.
      - exact NX.
      - lia.
      - reflexivity.
      - exact QB10.
      - exact BST9.
      - exact BHO9.
      - replace (bv_unsigned sp - 992) with (bv_unsigned sp + (-62) * 16) by ring. rewrite Z.mod_add by lia. exact HAL. }
    intros ms11 (can11 & (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & m8 & -> & MU8 & WM8 & RO8)
      & EQ11).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ11 eq_refl eq_refl) as (RG11 & -> & X11).
    assert (E11_1 : getr RG11 1 = Z_to_bv 64 0x15070) by (rewrite (getr_of_eqv _ _ 1 X11 eq_refl); simp_regs; reflexivity).
    assert (E11_2 : getr RG11 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by (rewrite (getr_of_eqv _ _ 2 X11 eq_refl); simp_regs; reflexivity).
    assert (E11_4 : getr RG11 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X11 eq_refl); simp_regs; exact E10_4).
    assert (E11_9 : getr RG11 9 = Z_to_bv 64 d) by (rewrite (getr_of_eqv _ _ 9 X11 eq_refl); simp_regs; reflexivity).
    assert (E11_10 : getr RG11 10 = Z_to_bv 64 (bv_unsigned sp - 984)).
    { rewrite (getr_of_eqv _ _ 10 X11 eq_refl); simp_regs. rewrite USP1. f_equal. lia. }
    assert (E11_11 : getr RG11 11 = Z_to_bv 64 (Z.of_nat (length qs))).
    { rewrite (getr_of_eqv _ _ 11 X11 eq_refl); simp_regs. rewrite QSL. exact E10_8. }
    assert (KK11 : forall r, (r = 3 \/ r = 4 \/ r = 26 \/ r = 27) -> getr RG11 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. assert (Hc : callee_saved r) by (unfold callee_saved; lia).
      rewrite <- (K7 r Hc ltac:(lia)), <- (KR r Hc).
      destruct Hr as [ -> | [ -> | [ -> | -> ]]]; rewrite (getr_of_eqv _ _ _ X11) by reflexivity; reflexivity. }
    assert (SP11 : spZ RG11 = bv_unsigned sp - 992) by (unfold spZ; rewrite E11_2; exact USP1).
    rewrite USP1 in MU8. unfold REC_CALLS_EQUAL_FRAME in MU8.
    assert (OUT8 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 992 - 128 <= a < bv_unsigned sp - 992) ->
               mbyte rsegs m8 a = mbyte rsegs m7 a /\ (writable_at rsegs m7 a <-> writable_at rsegs m8 a)).
    { intros a Ha Hx. assert (Ho : Frame.outside [(bv_unsigned sp - 992 - 128, bv_unsigned sp - 992)] a)
        by (cbn; split; [lia | exact I]).
      split; [exact (munch_mbyte _ _ _ _ _ MU8 Ha Ho) | exact (munch_writable _ _ _ _ _ MU8 Ha Ho)]. }
    assert (MR8 : aa_MR API L5 A5 m8 md5).
    { apply (KindBGlue.kb_MR_A B API L5 A5 m7 m8 md5 _ HMR5 MU8). intros x Hx _. cbn. split; [lia | exact I]. }
    assert (SW11 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m8 a)
      by (intros a Ha; unfold writable_at; apply WM8; exact (SW10 a Ha)).
    assert (ERR11 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m8 a)
      by (intros a Ha; unfold writable_at; apply WM8; exact (ERR10 a Ha)).
    assert (FK11 : forall a, bv_unsigned sp - 984 <= a < bv_unsigned sp ->
               mbyte rsegs m8 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a <-> writable_at rsegs m8 a)).
    { intros a Ha. destruct (FK10 a Ha) as [E1 W1]. destruct (OUT8 a ltac:(lia) ltac:(lia)) as [E2 W2].
      split; [congruence | tauto]. }
    assert (BK11 : forall a k i, In (a, k) (blocks L5 A5) -> 0 <= i < k -> mbyte rsegs m8 (a + i) = mbyte rsegs m7 (a + i)).
    { intros a k i Hin Hi. destruct (BRNG5 a k Hin). exact (proj1 (OUT8 (a + i) ltac:(lia) ltac:(lia))). }
    assert (PRE11 : call_pre_k B (aa_MR API) RCF_K L5 A5 RG11 m8 md5).
    { unfold RCF_K. change ALLOC_STACK with 8192.
      split; [exact MR8|]. split; [exact HWF5|]. split; [exact HBD5|].
      split; [rewrite E11_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP11; replace (bv_unsigned sp - 992) with (bv_unsigned sp + (-62) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP11; lia|]. split; [rewrite SP11; lia|].
      split; [intros a Ha; rewrite SP11 in Ha; rewrite SEGS; apply SW11; lia|].
      split; [rewrite E11_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; exact (ERR11 a Ha)|].
      intros HI. rewrite (INIT10 (INIT8 INIT6)) in HI. discriminate. }
    assert (FREEDQ : freed qs = concat qs).
    { unfold freed. apply crt_filter_nz. intros pn Hpn. destruct (QF pn Hpn) as (_ & F1 & _). lia. }
    pose proof (RCF fx' L5 A5 RG11 m8 md5 (bv_unsigned sp - 984) qs (sb_free b8 (join_need ws + 1))) as RF.
    unfold REC_CALLS_FREE in RF. rewrite SEGS in RF.
    eapply SR_bind.
    { apply RF; clear RF.
      - exact PRE11.
      - exact RO8.
      - exact E11_10.
      - exact E11_11.
      - unfold calls_slots. rewrite ?SEGS. split; [rewrite QSL; exact NC16|].
        intros i P EP.
        assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- QSL; apply nth_error_Some; rewrite EP; discriminate).
        destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
        destruct (QCALL i c P Ec EP) as [(_ & H6 & HL & _ & HN & _ & HK) _].
        unfold CALL_OFF_NARGS, CALL_OFF_ARGS in HN, HK.
        assert (KC : forall a bs, bv_unsigned sp - 984 <= a -> a + Z.of_nat (length bs) <= bv_unsigned sp ->
                       bytes_at rsegs m2 a bs -> bytes_at rsegs m8 a bs).
        { intros a bs H1 H2 Hb. apply (bytes_at_transfer rsegs m2); [exact Hb|]. intros j Hj.
          exact (proj1 (FK11 (a + j) ltac:(lia))). }
        split; [lia|]. split; [|split].
        + rewrite HL. apply KC; [lia | rewrite Mem.length_le4; lia | exact HN].
        + intros j Hj. apply (proj2 (FK11 (bv_unsigned sp - 984 + 56 * Z.of_nat i + 4 + j) ltac:(lia))).
          replace (bv_unsigned sp - 984 + 56 * Z.of_nat i + 4 + j)
            with (bv_unsigned sp - 984 + (56 * Z.of_nat i + 4 + j)) by ring.
          apply DW2. lia.
        + intros a pn Ea.
          assert (Ha : (a < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Ea; discriminate).
          destruct (nth_error (snd c) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
          destruct (HK a s pn Es Ea) as (B1 & _ & _ & _). split.
          * apply KC; [lia | rewrite Mem.length_le8; lia | exact B1].
          * right. apply QIN10. apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact (nth_error_In _ _ Ea)].
      - rewrite FREEDQ. exact ND2.
      - lia.
      - rewrite QSL. lia.
      - intros _. split; [lia|]. replace (bv_unsigned sp - 984) with (bv_unsigned sp + 8 * (-123)) by ring. apply SP8.
      - intros j Hj. left. rewrite SP11. lia.
      - exact RES10. }
    intros c12 RET12.
    destruct RET12 as (L6 & A6 & RG12 & m9 & md6 & -> & POST12 & PERM12 & KEPT12 & UBa12 & UBb12 & NZ12 & CPYK12 & G12
      & RO9 & GK12 & INIT12 & RLEN12 & AUXV12 & RES12).
    destruct POST12 as (HMR6 & HWF6 & HBD6 & HLE6 & HSTAB6 & HPRES6 & HVM6 & HFRAME6 & HBLKS6 & HSCR6).
    try rewrite SEGS in HFRAME6. try rewrite SEGS in HBLKS6. try rewrite SEGS in HSCR6. try rewrite SEGS in RO9.
    try rewrite SEGS in G12. try rewrite SEGS in NZ12. unfold blocks_kept in KEPT12. try rewrite SEGS in KEPT12.
    rewrite FREEDQ in PERM12, KEPT12, RES12.
    try rewrite SEGS.
    destruct (mr_model _ _ LAWS _ _ _ _ HMR6) as (Hh6 & Hl6 & Hmat6).
    assert (NARGS : forall a, nargs_field (bv_unsigned sp - 984) (length qs) a ->
               bv_unsigned sp - 984 <= a < bv_unsigned sp - 88).
    { intros a (i & Hi & Ha). rewrite QSL in Hi. lia. }
    assert (CK12 : forall a, KP a -> ~ (bv_unsigned sp - 9296 <= a < bv_unsigned sp - 992) ->
               ~ (errno_addr B <= a < errno_addr B + 4) -> ~ nargs_field (bv_unsigned sp - 984) (length qs) a ->
               mbyte rsegs m9 a = mbyte rsegs m8 a /\ (writable_at rsegs m8 a <-> writable_at rsegs m9 a)).
    { intros a Ha Hs He Hn.
      apply HFRAME6; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha MR8) | exact (KPN a _ _ _ _ Ha HMR6) | | exact Hn].
      unfold scratch_k. rewrite SP11. unfold RCF_K. change ALLOC_STACK with 8192.
      intros [H|H]; [apply Hs; lia | exact (He H)]. }
    assert (PW5 : pairwise ranges_disjoint (blocks L5 A5)) by exact (mr_blocks_disjoint B _ LAWS _ _ _ _ HMR5).
    assert (M56 : forall pn, In pn (blocks L5 A5) -> ~ In pn (concat qs) -> In pn (blocks L6 A6)).
    { intros pn Hin Hq. pose proof (Permutation_in _ PERM12 Hin) as H. apply in_app_or in H as [H|H]; [exact H|].
      contradiction. }
    assert (NQ6 : forall pn, In pn (blocks L6 A6) -> ~ In pn (concat qs)).
    { intros pn Hin Hq. apply (pw_perm_two _ _ _ pn PW5 PERM12 Hin Hq). pose proof (proj1 (QF pn Hq)). lia. }
    assert (QADDR : forall a k, In (a, k) (blocks L5 A5) -> 1 <= k -> ~ In (a, k) (concat qs) ->
               ~ In a (map fst (concat qs))).
    { intros a k Hin Hk Hq H. apply in_map_iff in H as ([a' k'] & Ea & Hq'). cbn in Ea. subst a'.
      assert (Hne : (a, k) <> (a, k')) by (intros E; rewrite E in Hq; exact (Hq Hq')).
      pose proof (pw_in_disjoint _ _ _ PW5 Hin (QIN10 _ Hq') Hne) as Hd. pose proof (proj1 (QF _ Hq')) as Hk'.
      unfold ranges_disjoint in Hd. cbn in Hd, Hk'. lia. }
    assert (DNQ : ~ In (d, Z.of_nat (length X) + 1) (concat qs)).
    { intros H. pose proof (QD _ H) as Hd. pose proof (proj1 (QF _ H)). cbn in Hd. lia. }
    assert (DIN12 : In (d, Z.of_nat (length X) + 1) (blocks L6 A6)) by exact (M56 _ DIN10 DNQ).
    assert (DBY12 : forall i, (i < S (length X))%nat ->
               mbyte rsegs m9 (d + Z.of_nat i) = nth_error (X ++ [Z_to_bv 8 0]) i).
    { intros i Hi. rewrite (KEPT12 d (Z.of_nat (length X) + 1) (Z.of_nat i) DIN10
        (QADDR d _ DIN10 ltac:(lia) DNQ) ltac:(lia)).
      rewrite (BK11 d (Z.of_nat (length X) + 1) (Z.of_nat i) DIN10 ltac:(lia)). exact (DBY10 i Hi). }
    assert (O4Q : forall pn, In pn O4 -> ~ In pn (concat qs)).
    { intros pn HO Hq. apply (NO8 pn (M23 _ (M12 _ (QIN1 _ Hq))) (QNO _ Hq)). exact HO. }
    assert (REP12 : g_rec_rep rsegs L6 A6 m9 R9 O4).
    { apply (rec_rep_frame rsegs G_REC REC_SC L5 A5 m7 R9 O4 L6 A6 m9 REP10).
      - intros a Ha. assert (Hg : in_globals frame_G a) by (apply sm_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
        pose proof (sm_g_iv a Hg).
        destruct (G12 a Hg ltac:(intros Hw; pose proof (NARGS a Hw); lia)) as [E1 W1].
        destruct (OUT8 a ltac:(lia) ltac:(lia)) as [E2 W2]. split; [congruence | tauto].
      - intros p k i Hin Hi. destruct (rep_O rsegs _ _ _ _ _ _ REP10 Hin) as [Hb Hk]. cbn [snd] in Hk.
        rewrite (KEPT12 p k i Hb (QADDR p k Hb Hk (O4Q _ Hin)) Hi). exact (BK11 p k i Hb Hi).
      - intros pn Hin. destruct (rep_O rsegs _ _ _ _ _ _ REP10 Hin) as [Hb _]. exact (M56 _ Hb (O4Q _ Hin)). }
    assert (LQ : forall a k, In (a, k) (blocks L A) -> ~ In (a, k) (concat qs)).
    { intros a k Hin Hq. pose proof (proj1 (QF _ Hq)) as Hk. cbn in Hk. exact (QSEP (a, k) a k Hq Hin Hk eq_refl). }
    assert (BM12 : forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> In pn (blocks L6 A6)).
    { intros [a k] Hin Hno. exact (M56 _ (BM10 _ Hin Hno) (LQ a k Hin)). }
    assert (BK12 : forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
               mbyte rsegs m9 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hno Hi.
      rewrite (KEPT12 a k i (BM10 _ Hin Hno) (QADDR a k (BM10 _ Hin Hno) ltac:(lia) (LQ a k Hin)) Hi).
      rewrite (BK11 a k i (BM10 _ Hin Hno) Hi). exact (BK10 a k i Hin Hno Hi). }
    assert (F12 : forall a, KP a -> ~ scratch_k B CRT_K regs a -> ~ vr_writes a ->
               mbyte rsegs m9 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m9 a)).
    { intros a Ha Hs Hv. destruct (F10 a Ha Hs Hv) as [E1 W1].
      unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (OUT8 a (KPR a Ha) ltac:(lia)) as [E2 W2].
      destruct (CK12 a Ha ltac:(lia) Hs2 ltac:(intros Hw; pose proof (NARGS a Hw); lia)) as [E3 W3].
      split; [congruence | tauto]. }
    assert (SW12 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m9 a).
    { intros a Ha. destruct (Z_lt_ge_dec a (bv_unsigned sp - 9296)) as [Hlo|Hhi].
      - apply (proj2 (CK12 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(intros Hw; pose proof (NARGS a Hw); lia))).
        apply SW11. lia.
      - apply HSCR6. unfold scratch_k. rewrite SP11. unfold RCF_K. change ALLOC_STACK with 8192. left. lia. }
    assert (ERR12 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m9 a)
      by (intros a Ha; apply HSCR6; right; exact Ha).
    assert (GQ12 : le_at B m9 G_QUIT (Mem.le4 (Z_to_bv 64 q))).
    { apply (sm_le_keep B m7); [exact GQ10|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le4 in Hi.
      unfold G_QUIT. assert (Hg : in_globals frame_G (0x343e8 + i)) by (apply sm_g_of; lia).
      destruct (G12 _ Hg ltac:(intros Hw; pose proof (NARGS _ Hw); lia)) as [E1 _].
      destruct (OUT8 (0x343e8 + i) ltac:(lia) ltac:(lia)) as [E2 _]. congruence. }
    assert (E12_2 : getr RG12 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by exact (eq_trans (HPRES6 2 ltac:(unfold callee_saved; lia)) E11_2).
    assert (E12_4 : getr RG12 4 = getr regs 4) by exact (eq_trans (HPRES6 4 ltac:(unfold callee_saved; lia)) E11_4).
    assert (E12_9 : getr RG12 9 = Z_to_bv 64 d) by exact (eq_trans (HPRES6 9 ltac:(unfold callee_saved; lia)) E11_9).
    rewrite E11_1.
    eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply crt_s8. }
    intros ms13 (can13 & -> & EQ13).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ13 eq_refl eq_refl) as (RG13 & -> & X13).
    assert (E13_1 : getr RG13 1 = Z_to_bv 64 0x15078) by (rewrite (getr_of_eqv _ _ 1 X13 eq_refl); simp_regs; reflexivity).
    assert (E13_2 : getr RG13 2 = Z_to_bv 64 (bv_unsigned sp - 992))
      by (rewrite (getr_of_eqv _ _ 2 X13 eq_refl); simp_regs; exact E12_2).
    assert (E13_4 : getr RG13 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X13 eq_refl); simp_regs; exact E12_4).
    assert (E13_10 : getr RG13 10 = Z_to_bv 64 d) by (rewrite (getr_of_eqv _ _ 10 X13 eq_refl); simp_regs; exact E12_9).
    assert (KK13 : forall r, callee_saved r -> getr RG13 (Z_to_bv 5 r) = getr RG12 (Z_to_bv 5 r)).
    { intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X13) by reflexivity; reflexivity|]).
      subst r; rewrite (getr_of_eqv _ _ _ X13) by reflexivity; reflexivity. }
    assert (SP13 : spZ RG13 = bv_unsigned sp - 992) by (unfold spZ; rewrite E13_2; exact USP1).
    destruct (proj1 (YI06.blocks_In L6 A6 d (Z.of_nat (length X) + 1)) DIN12) as (pdup & PDUP & UPDUP).
    assert (PRE13 : call_pre B (aa_MR API) L6 A6 RG13 m9 md6).
    { split; [exact HMR6|]. split; [exact HWF6|]. split; [exact HBD6|].
      split; [rewrite E13_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP13; replace (bv_unsigned sp - 992) with (bv_unsigned sp + (-62) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP13; change ALLOC_STACK with 8192; lia|]. split; [rewrite SP13; lia|].
      split; [intros a Ha; rewrite SP13 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite SEGS; apply SW12; lia|].
      split; [rewrite E13_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; exact (ERR12 a Ha)|].
      intros HI. rewrite (INIT12 (INIT10 (INIT8 INIT6))) in HI. discriminate. }
    pose proof (FREE fx' L6 A6 RG13 m9 md6 pdup (Z.of_nat (length X) + 1)
                  (RecKindB.rfree_b (sb_free b8 (join_need ws + 1)) (concat qs))) as FRE.
    rewrite SEGS, FREE_PC in FRE.
    eapply SR_bind; [exact (FRE PRE13 RO9 UPDUP ltac:(rewrite E13_10, PDUP; reflexivity) RES12) |]. clear FRE.
    intros c14 RET14.
    destruct RET14 as (L7 & A7 & RG14 & m10 & md7 & -> & POST14 & BLK14 & KEPT14 & RO10 & GK14 & UB14 & INIT14 & RLEN14
      & RES14).
    destruct POST14 as (HMR7 & HWF7 & HBD7 & HLE7 & HSTAB7 & HPRES7 & HVM7 & HFRAME7 & HBLKS7 & HSCR7).
    try rewrite SEGS in HFRAME7. try rewrite SEGS in HBLKS7. try rewrite SEGS in HSCR7. try rewrite SEGS in RO10.
    unfold blocks_kept in KEPT14. try rewrite SEGS in KEPT14.
    rewrite PDUP in BLK14, KEPT14, HFRAME7.
    destruct BLK14 as (f1 & f2 & BL14a & BL14b).
    destruct (mr_model _ _ LAWS _ _ _ _ HMR7) as (Hh7 & Hl7 & Hmat7).
    assert (PW6 : pairwise ranges_disjoint (blocks L6 A6)) by exact (mr_blocks_disjoint B _ LAWS _ _ _ _ HMR6).
    assert (NDUP : forall a k, In (a, k) (blocks L6 A6) -> 1 <= k -> (a, k) <> (d, Z.of_nat (length X) + 1) -> a <> d).
    { intros a k Hin Hk Hne E. subst a. pose proof (pw_in_disjoint _ _ _ PW6 Hin DIN12 Hne) as Hdj.
      unfold ranges_disjoint in Hdj. cbn in Hdj. lia. }
    assert (M67 : forall pn, In pn (blocks L6 A6) -> pn <> (d, Z.of_nat (length X) + 1) -> In pn (blocks L7 A7)).
    { intros pn Hin Hne. rewrite BL14b. rewrite BL14a in Hin.
      apply in_app_or in Hin as [H|[H|H]]; [apply in_or_app; left; exact H | congruence | apply in_or_app; right; exact H]. }
    assert (D7 : forall pn, In pn (blocks L7 A7) -> In pn (blocks L6 A6) /\ pn <> (d, Z.of_nat (length X) + 1)).
    { intros pn Hin. split.
      - rewrite BL14a. rewrite BL14b in Hin. apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H].
      - intros ->. rewrite BL14b in Hin. revert Hin. apply sm_pw_mid; [rewrite <- BL14a; exact PW6 | cbn; lia]. }
    assert (DNL : forall a k, In (a, k) (blocks L A) -> 1 <= k -> a <> d).
    { intros a k Hin Hk E. subst a. pose proof (BLD d k (BM2 _ Hin)). lia. }
    assert (CK14 : forall a, KP a -> ~ (bv_unsigned sp - 9184 <= a < bv_unsigned sp - 992) ->
               ~ (errno_addr B <= a < errno_addr B + 4) ->
               mbyte rsegs m10 a = mbyte rsegs m9 a /\ (writable_at rsegs m9 a <-> writable_at rsegs m10 a)).
    { intros a Ha Hs He.
      apply HFRAME7; [exact (proj1 Ha) | exact (KPN a _ _ _ _ Ha HMR6) | exact (KPN a _ _ _ _ Ha HMR7) | |].
      - unfold scratch. rewrite SP13. change ALLOC_STACK with 8192. intros [H|H]; [apply Hs; lia | exact (He H)].
      - intros Hr. destruct (proj1 Ha) as [Hh'|Hi]; [lia|]. apply (DF3 (a - d)); [lia|].
        replace (d + (a - d)) with a by ring. exact Hi. }
    assert (F14 : forall a, KP a -> ~ scratch_k B CRT_K regs a -> ~ vr_writes a ->
               mbyte rsegs m10 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m10 a)).
    { intros a Ha Hs Hv. destruct (F12 a Ha Hs Hv) as [E1 W1].
      unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      assert (Hs2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
      destruct (CK14 a Ha ltac:(lia) Hs2) as [E2 W2]. split; [congruence | tauto]. }
    assert (BM14 : forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> In pn (blocks L7 A7)).
    { intros [a k] Hin Hno. apply M67; [exact (BM12 _ Hin Hno)|]. intros E. injection E as Ea Ek. subst a k.
      exact (DNL d _ Hin ltac:(lia) eq_refl). }
    assert (BK14 : forall a k i, In (a, k) (blocks L A) -> ~ In a (map fst O) -> 0 <= i < k ->
               mbyte rsegs m10 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Hno Hi. rewrite (KEPT14 a k i (BM12 _ Hin Hno) (DNL a k Hin ltac:(lia)) Hi).
      exact (BK12 a k i Hin Hno Hi). }
    assert (DO4 : ~ In (d, Z.of_nat (length X) + 1) O4) by exact (NO8 _ (M23 _ INBD) DNO).
    assert (REP14 : g_rec_rep rsegs L7 A7 m10 R9 O4).
    { apply (rec_rep_frame rsegs G_REC REC_SC L6 A6 m9 R9 O4 L7 A7 m10 REP12).
      - intros a Ha. assert (Hg : in_globals frame_G a) by (apply sm_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
        destruct (GX a Hg) as (G1 & _ & G3). pose proof (sm_g_iv a Hg).
        destruct (CK14 a G1 ltac:(lia) G3) as [E W1]. split; [exact E | apply W1].
      - intros p k i Hin Hi. destruct (rep_O rsegs _ _ _ _ _ _ REP12 Hin) as [Hb Hk]. cbn [snd] in Hk.
        apply (KEPT14 p k i Hb); [|exact Hi]. apply (NDUP p k Hb Hk). intros E. rewrite E in Hin. exact (DO4 Hin).
      - intros pn Hin. destruct (rep_O rsegs _ _ _ _ _ _ REP12 Hin) as [Hb _]. apply (M67 _ Hb).
        intros E. rewrite E in Hin. exact (DO4 Hin). }
    assert (GQ14 : le_at B m10 G_QUIT (Mem.le4 (Z_to_bv 64 q))).
    { apply (sm_le_keep B m9); [exact GQ12|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le4 in Hi.
      unfold G_QUIT. destruct (GX (0x343e8 + i) (sm_g_of (0x343e8 + i) ltac:(lia))) as (G1 & _ & G3).
      exact (proj1 (CK14 (0x343e8 + i) G1 ltac:(lia) G3)). }
    assert (SW14 : forall a, bv_unsigned sp - 16000 <= a < bv_unsigned sp - 992 -> writable_at rsegs m10 a).
    { intros a Ha. destruct (Z_lt_ge_dec a (bv_unsigned sp - 9184)) as [Hlo|Hhi].
      - apply (proj2 (CK14 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia))). apply SW12. lia.
      - apply HSCR7. unfold scratch. rewrite SP13. change ALLOC_STACK with 8192. left. lia. }
    assert (ERR14 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m10 a)
      by (intros a Ha; apply HSCR7; right; exact Ha).
    assert (FW6 : forall a, bv_unsigned sp - 992 <= a < bv_unsigned sp -> writable_at rsegs m5 a).
    { intros a Ha. destruct (Z_lt_ge_dec a (bv_unsigned sp - 984)) as [H1|H1].
      - pose proof (ROUT (a - (bv_unsigned sp - 992)) ltac:(rewrite Mem.length_le8; lia)) as E.
        rewrite SEGS in E. replace (bv_unsigned sp - 992 + (a - (bv_unsigned sp - 992))) with a in E by ring.
        destruct (nth_error (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (join_sp ws))))) (Z.to_nat (a - (bv_unsigned sp - 992))))
          as [bb|] eqn:N.
        + exact (crt_writable_of_mbyte m5 a bb ltac:(lia) E).
        + apply nth_error_None in N. rewrite Mem.length_le8 in N. lia.
      - apply (proj2 (FK6 a ltac:(lia))). exact (FW5 a Ha). }
    assert (FW14 : forall a, bv_unsigned sp - 992 <= a < bv_unsigned sp -> writable_at rsegs m10 a).
    { intros a Ha.
      assert (W8 : writable_at rsegs m6 a).
      { apply (proj2 (CK8 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia)
                  ltac:(unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT; lia))). exact (FW6 a Ha). }
      assert (W10 : writable_at rsegs m7 a) by (apply (proj2 (CK10 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia))); exact W8).
      assert (W11 : writable_at rsegs m8 a) by (apply (proj2 (OUT8 a ltac:(lia) ltac:(lia))); exact W10).
      assert (W12 : writable_at rsegs m9 a).
      { destruct (crt_nargs_dec (bv_unsigned sp - 984) (length qs) a) as [Hn|Hn].
        - destruct Hn as (i & Hi & Hai). destruct (NZ12 i Hi) as [_ WN].
          replace a with (bv_unsigned sp - 984 + 56 * Z.of_nat i + 4 + (a - (bv_unsigned sp - 984 + 56 * Z.of_nat i + 4)))
            by ring.
          apply WN. lia.
        - apply (proj2 (CK12 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia) Hn)). exact W11. }
      apply (proj2 (CK14 a (KPH a ltac:(lia)) ltac:(lia) ltac:(lia))). exact W12. }
    assert (FRS14 := FRS2).
    apply (rw_cells_transfer rsegs m2 m10) in FRS14;
      [| intros i Hi; cbn in Hi;
         destruct (FK11 (bv_unsigned sp - 88 + i) ltac:(lia)) as [E1 W1];
         destruct (CK12 (bv_unsigned sp - 88 + i) (KPH (bv_unsigned sp - 88 + i) ltac:(lia)) ltac:(lia) ltac:(lia)
                     ltac:(intros Hw; pose proof (NARGS _ Hw); lia)) as [E2 W2];
         destruct (CK14 (bv_unsigned sp - 88 + i) (KPH (bv_unsigned sp - 88 + i) ltac:(lia)) ltac:(lia) ltac:(lia))
           as [E3 W3];
         split; [congruence | tauto]].
    assert (E14_2' : reg_get RG14 2 = Z_to_bv 64 (bv_unsigned sp - 992)).
    { exact (eq_trans (HPRES7 2 ltac:(unfold callee_saved; lia))
               (eq_trans (KK13 2 ltac:(unfold callee_saved; lia)) E12_2)). }
    assert (KF : forall r', (r' = 3 \/ r' = 4 \/ r' = 26 \/ r' = 27) ->
               getr RG14 (Z_to_bv 5 r') = getr regs (Z_to_bv 5 r')).
    { intros r' Hr'. assert (Hc : callee_saved r') by (unfold callee_saved; lia).
      rewrite (HPRES7 r' Hc), (KK13 r' Hc), (HPRES6 r' Hc). exact (KK11 r' Hr'). }
    rewrite E13_1.
    eapply evt_SR_canon; [ | exact Hh7 | exact Hl7 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E14_2'.
      eapply crt_s9 with (S := bv_unsigned sp); [rewrite USP1; reflexivity | lia | exact FRS14]. }
    intros ms15 (can15 & RET15 & EQ15).
    unfold crt_ret in RET15.
    destruct RET15 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & ->).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ15 eq_refl eq_refl) as (RG15 & -> & X15).
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    assert (RK14 : relro_kept mem m10).
    { intros a Ha Hg. destruct (RLX a Ha Hg) as (Q1 & Q2 & Q3). exact (proj1 (F14 a Q1 Q2 Q3)). }
    destruct (ax_statics AX L7 A7 m10 md7 HMR7) as (WG14 & (g14 & Hg14 & WGG14) & _).
    rewrite SEGS, GOT_AT, GUARD_AT in WG14. rewrite SEGS, GUARD_AT in WGG14.
    apply SR_ret.
    exists fx', L7, A7, RG15, m10, md7, R9, O4,
      (sb_free (RecKindB.rfree_b (sb_free b8 (join_need ws + 1)) (concat qs)) (Z.of_nat (length X) + 1)).
    split; [rewrite RP; reflexivity|].
    split; [exact FZ|].
    split; [lia|].
    split.
    { unfold call_post_ko. rewrite ?SEGS.
      split; [exact HMR7|]. split; [exact HWF7|]. split; [exact HBD7|].
      assert (LLE : layout_le A L L7).
      { apply (crt_lle_trans A A6 L L6 L7); [| exact HLE7 | lia].
        apply (crt_lle_trans A A5 L L5 L6); [| exact HLE6 | lia].
        apply (crt_lle_trans A A4 L L4 L5); [| exact HLE5 | lia].
        apply (crt_lle_trans A A3 L L3 L4); [| exact HLE4 | lia].
        apply (crt_lle_trans A A2 L L2 L3); [| exact HLE3 | lia].
        apply (crt_lle_trans A A1 L L1 L2); [exact HLE1 | exact HLE2 | lia]. }
      split; [exact LLE|].
      split; [intros p k Hp _; exact (crt_ptr_stable A L L7 p k HWF Hp LLE)|].
      split.
      { intros r Hr. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 26 \/ r = 27 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
                    r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25) by lia.
        destruct C as [C|[C|[C|[C|[C|C]]]]].
        - subst r. rewrite (getr_of_eqv _ _ _ X15) by reflexivity. simp_regs. apply Z_to_bv_bv_unsigned.
        - subst r. rewrite (getr_of_eqv _ _ _ X15) by reflexivity. simp_regs. exact (KF 3 ltac:(lia)).
        - subst r. rewrite (getr_of_eqv _ _ _ X15) by reflexivity. simp_regs. exact (KF 4 ltac:(lia)).
        - subst r. rewrite (getr_of_eqv _ _ _ X15) by reflexivity. simp_regs. exact (KF 26 ltac:(lia)).
        - subst r. rewrite (getr_of_eqv _ _ _ X15) by reflexivity. simp_regs. exact (KF 27 ltac:(lia)).
        - repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X15) by reflexivity; reflexivity|]).
          subst r; rewrite (getr_of_eqv _ _ _ X15) by reflexivity; reflexivity. }
      split.
      { destruct HVM1 as [vm1 ->]. destruct HVM2 as [vm2 ->]. destruct HVM3 as [vm3 ->]. destruct HVM4 as [vm4 ->].
        destruct HVM5 as [vm5 ->]. destruct HVM6 as [vm6 ->]. destruct HVM7 as [vm7 ->].
        exists vm7. reflexivity. }
      split.
      { intros a Ha Ho Ho' Hs Hv. exact (F14 a (conj Ha Ho) Hs Hv). }
      split.
      { intros p k i Hp _ Hno Hi. apply (BK14 (ptr_addr L p) k i); [| exact Hno | exact Hi].
        unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hp). }
      intros a Hs. unfold scratch_k in Hs. rewrite CK in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
      destruct Hs as [Hs|He]; [|exact (ERR14 a He)].
      destruct (Z_lt_ge_dec a (bv_unsigned sp - 992)) as [Hlo|Hhi]; [apply SW14; lia | apply FW14; lia]. }
    split; [exact (crt_cmd_mem_keep B SEGS mem m10 g14 CMD0 RO10 RK14 WG14 WGG14 Hg14)|].
    split; [exact REP14|].
    split; [exact (proj1 VRC)|]. split; [exact (proj2 VRC)|]. split; [exact VRS|].
    split; [exact RS9|]. split; [exact RH9|].
    split; [exact GQ14|].
    split.
    { apply (crt_words_view_keep B SEGS mem m10); [exact WV | | |].
      - intros a Ha. refine (proj1 (F14 a (KPH a ltac:(lia)) _ _)).
        + unfold scratch_k. rewrite CK. change (spZ regs) with (bv_unsigned sp). lia.
        + unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT. lia.
      - intros i Hi. destruct ILA as (p & k & Hpk & Hno & Hp1 & Hp2).
        replace (arr + i) with (p + (arr + i - p)) by ring. apply (BK14 p k); [exact Hpk | exact Hno | lia].
      - intros k i Hk Hi. destruct (ILW k Hk) as (p & k' & Hpk & Hno & Hp1 & Hp2).
        replace (nth k wp 0 + i) with (p + (nth k wp 0 + i - p)) by ring. apply (BK14 p k'); [exact Hpk | exact Hno | lia]. }
    split.
    { split.
      - destruct ILA as (p & k & Hpk & Hno & Hp1 & Hp2). exists p, k. split; [exact (BM14 _ Hpk Hno) | lia].
      - intros k Hk. destruct (ILW k Hk) as (p & k' & Hpk & Hno & Hp1 & Hp2). exists p, k'.
        split; [exact (BM14 _ Hpk Hno) | lia]. }
    split.
    { intros pn Hin. destruct (D7 pn Hin) as [H6 Hnd].
      assert (H5 : In pn (blocks L5 A5)) by (apply (Permutation_in _ (Permutation_sym PERM12)); apply in_or_app; left; exact H6).
      assert (Hnr : pn <> (res, join_need ws + 1)).
      { intros ->. rewrite BL10b in H5. revert H5. apply sm_pw_mid; [rewrite <- BL10a; exact PW4 | cbn; lia]. }
      assert (H4 : In pn (blocks L4 A4)).
      { rewrite BL10b in H5. rewrite BL10a. apply in_app_or in H5 as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
      destruct (BL8 pn H4) as [[H3 HnO]|HO4]; [left | right; exact HO4].
      split; [|exact HnO].
      assert (H2 : In pn (blocks L2 A2)).
      { rewrite RBL1 in H3. rewrite RBL2. apply in_app_or in H3 as [H|[H|H]];
          [apply in_or_app; left; exact H | exfalso; exact (Hnr (eq_sym H)) | apply in_or_app; right; exact H]. }
      assert (H1 : In pn (blocks L1 A1)).
      { rewrite DB1 in H2. rewrite DB2. apply in_app_or in H2 as [H|[H|H]];
          [apply in_or_app; left; exact H | exfalso; exact (Hnd (eq_sym H)) | apply in_or_app; right; exact H]. }
      apply (Permutation_in _ PERM2) in H1. apply in_app_or in H1 as [H|H]; [exact H|].
      exfalso. exact (NQ6 pn H6 H). }
    split; [exact BM14|].
    split.
    { unfold blocks_kept. rewrite ?SEGS. intros a k i Hin Hno Hi. apply (BK14 a k i Hin); [|exact Hi].
      intros H. apply Hno. apply in_map_iff in H as ([a' k'] & Ea & H). cbn in Ea. subst a'. exists k'. exact H. }
    split; [intros _; exact (INIT14 (INIT12 (INIT10 (INIT8 INIT6))))|].
    split; [intros pn Hin Hno; exact (NO8 pn (BM6 pn Hin) Hno)|].
    split; [exists (Z_to_bv 64 g14); exact (crt_vr_tables_keep B SEGS mem m10 can g14 VT RK14 WG14 WGG14 Hg14)|].
    split; [exact RES14|].
    cbn [sb_cap sb_free]. rewrite rfree_b_cap. cbn [sb_cap sb_free]. rewrite CAP8. cbn [sb_cap sb_malloc]. exact RB3.
Qed.

End CRT.
