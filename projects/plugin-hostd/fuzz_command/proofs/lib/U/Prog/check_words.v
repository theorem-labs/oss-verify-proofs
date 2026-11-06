(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 1213 of its 1275 lines of code are new or changed and 486 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/send_message.v, with its module paths, module names, addresses and numbers changed; 524 of its 628 lines of code are new or changed and 1171 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP ZBridge Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import CType StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandFP CommandTac
  printf_facts_c atoi_c snprintf_c strcmp_c strspn_c strcspn_c check_words_c check_words_chain syntax_reply_matches
  check_words_add_c check_words_chain_c check_words_pin_set_c CwItems CwBody.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecFacts.
Import ListNotations.
Open Scope Z_scope.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI06.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB joined_c CwAns.

Section CW.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis TP_AT : ms_tp B = 0x344c0.
Hypothesis ERRNO_OFF : ms_errno_off B = -164.
Hypothesis GUARD_AT : ms_guard B = 0x54730.
Hypothesis GOT_AT : ms_got_guard B = 0x22d40.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTXO : ctx_owned B API.
Hypothesis G_STAT : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RELRO_FREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a ->
  ~ (ms_got_guard B <= a < ms_got_guard B + 8) -> ~ owned B L A a /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis HJOIN : joined_contract B API.
Hypothesis SSP : strspn_contract.
Hypothesis SCS : strcspn_contract.
Hypothesis ATOI : atoi_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis SC : strcmp_contract.
Hypothesis ADD : check_words_add_contract.
Hypothesis CHAIN : check_words_chain_contract.
Hypothesis PIN : check_words_pin_set_contract.

Lemma cw_gnown : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof using AX G_STAT.
  intros L A mem md a HM Hg Ho. destruct (G_STAT a Hg) as (Hi & Hs & Hc & _).
  destruct Ho as [Hal|Hst]; [exact (Hc (ax_img AX L A mem md a HM Hi Hal)) | exact (Hs Hst)].
Qed.

Theorem check_words_holds : check_words_contract B API.
Proof using SEGS FREE_PC TP_AT ERRNO_OFF GUARD_AT GOT_AT AX CTXO G_STAT RELRO_FREE FREE HJOIN SSP SCS ATOI SNP SC
  ADD CHAIN PIN.
  unfold check_words_contract.
  intros L A regs mem md b W arr q wp ws R O _ PRE SPT CMD FRM QUIT0 QOUT A10 WV WP W8 A8 SPW WT JN REP NOWN RES ROOM
    WPR.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC. pose proof alloc_ceiling_lt as AC2.
  pose proof wx_apart_rsegs as WX.
  assert (EA : errno_addr B = 0x3441c) by (unfold errno_addr; rewrite TP_AT, ERRNO_OFF; reflexivity).
  assert (KV : CHECK_WORDS_K = 8480) by reflexivity.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite KV in HCEIL, HWS.
  pose proof CMD as (RO & GIMG & _ & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold TASK_SIZE in SPT, WT.
  rewrite SEGS in HWS, HERR, RO, REP.
  assert (GIM : forall a, in_globals frame_RELRO a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. rewrite <- SEGS. exact (GIMG a Ha). }
  pose proof WV as (WL & WN & W24 & W16 & WK).
  pose proof WP as ((pa & ka & Hpa & Hpa1 & Hpa2) & WPK).
  assert (NOH : forall a, alloc_ceiling <= a -> ~ owned B L A a).
  { intros a Ha Ho. destruct (mr_owned_low B _ LAWS _ _ _ _ _ HMR Ho). lia. }
  assert (NEH : forall a, alloc_ceiling <= a -> ~ (errno_addr B <= a < errno_addr B + 4)) by (intros a Ha; rewrite EA; lia).
  assert (BRNG : forall q0 k, In (q0, k) (blocks L A) -> 4096 <= q0 /\ q0 + k <= alloc_ceiling).
  { intros q0 k Hq. apply YI06.blocks_In in Hq as (p & <- & Hp). exact (mr_blocks_range B _ LAWS L A mem md p k HMR Hp). }
  pose proof (BRNG pa ka Hpa) as BPA.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8480) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (Wa : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact Wa|].
    destruct (writable_hi_present mem a ltac:(lia) Wa) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 W) by exact A10. rewrite R10. unfold CHECK_WORDS.
    eapply cw_run1 with (lo := bv_unsigned sp - 8480) (n := Z.of_nat (length ws));
      [exact ST | lia | lia | lia | lia | lia | exact W8 |].
    apply (cw_bytes_of_le B mem _ _ SEGS); [lia | rewrite Mem.length_le4; lia | exact W24]. }
  intros ms1 (can1 & Q1 & EQ1). unfold cw_mid1 in Q1.
  destruct Q1 as (u0 & u1 & u2 & a1v & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & j0 & j1 & j2 & j3 & j4
    & j5 & j6 & j7 & j9 & j10 & j11 & -> & EA1 & MU1 & WM1 & FR1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x14c10) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -208))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 (Z.min (Z.of_nat (length ws)) 64))
    by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 W) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 (bv_unsigned sp + -128))
    by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; exact EA1).
  assert (K1 : forall r, callee_saved r -> r <> 2 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr H2 H9. unfold callee_saved in Hr.
    assert (C : r = 3 \/ r = 4 \/ r = 8 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
                r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X1) by reflexivity; reflexivity|]).
    subst r; rewrite (getr_of_eqv _ _ _ X1) by reflexivity; reflexivity. }
  assert (SP1 : spZ R1 = bv_unsigned sp - 208) by (unfold spZ; rewrite E1_2; rewrite unsigned_lit by lia; lia).
  assert (RO1 : MemNorm.ro_agree rsegs m1).
  { apply (cw_ro_munch _ mem m1 RO MU1). intros x Hx. cbn. split; [lia | exact I]. }
  assert (WR1 : forall a, bv_unsigned sp - 8480 <= a < bv_unsigned sp -> writable_at rsegs m1 a).
  { intros a Ha. unfold writable_at. apply WM1. apply HWS. lia. }
  assert (PRE1 : call_pre_k B (aa_MR API) (ALLOC_STACK + JOINED_FRAME) L A R1 m1 md).
  { pose proof (KindBGlue.kb_pre_A B API CHECK_WORDS_K 208 (ALLOC_STACK + JOINED_FRAME) L A regs mem md R1 m1
      [(bv_unsigned sp + -208, bv_unsigned sp)] PRE0) as KPA.
    rewrite SEGS in KPA. change ALLOC_STACK with 8192 in *. unfold JOINED_FRAME in *. rewrite KV in KPA.
    apply KPA; clear KPA.
    - lia.
    - lia.
    - lia.
    - rewrite SP1. change (spZ regs) with (bv_unsigned sp). lia.
    - rewrite SP1. replace (bv_unsigned sp - 208) with (bv_unsigned sp + (-13) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - exact E1_4.
    - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    - exact MU1.
    - exact WM1.
    - intros x Hx Hs. change (spZ regs) with (bv_unsigned sp) in Hs. cbn. split; [lia | exact I].
    - intros x Hx _. cbn. split; [lia | exact I]. }
  pose proof HJOIN as JN0. unfold joined_contract, JOINED in JN0. rewrite SEGS in JN0.
  eapply SR_bind.
  { apply (JN0 L A R1 m1 md b W arr (bv_unsigned sp + -128) wp ws); clear JN0.
    - exact PRE1.
    - exact RO1.
    - exact E1_10.
    - exact E1_11.
    - apply (cw_wv_keep B L A mem m1 W arr wp ws WV WP).
      + intros i Hi. rewrite SEGS. apply (munch_mbyte _ _ _ _ _ MU1); [lia | cbn; split; [lia | exact I]].
      + intros p k i Hin Hi. rewrite SEGS. pose proof (BRNG p k Hin).
        apply (munch_mbyte _ _ _ _ _ MU1); [lia | cbn; split; [lia | exact I]].
    - exact WP.
    - exact W8.
    - exact A8.
    - rewrite SP1. lia.
    - lia.
    - exact JN.
    - rewrite SP1. lia.
    - lia.
    - left. lia.
    - intros i Hi. apply WR1. lia.
    - replace (bv_unsigned sp + -128) with (bv_unsigned sp mod 16 + 8 * (2 * (bv_unsigned sp / 16) - 16)) by
        (pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)); lia).
      rewrite HAL, Z.add_0_l, Z.mul_comm. apply Z.mod_mul. lia.
    - intros i Hi. split.
      + apply NOH. lia.
      + unfold scratch_k, JOINED_FRAME. change ALLOC_STACK with 8192. rewrite SP1.
        intros [H|H]; [lia | rewrite EA in H; lia].
    - exact RES.
    - exact ROOM. }
  intros c2 RET.
  destruct RET as (L1 & A1 & R2 & m2 & md1 & res & -> & POST & A0' & NZ & FRESH & BLK & LEJ & LEO & KEPT & RO2 & UBK
    & INIT1 & RLEN1 & RES1).
  destruct POST as (HMR1 & HWF1 & HBD1 & HLE1 & HSTAB1 & HPRES1 & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
  rewrite SEGS in HFRAME1, HSCR1.
  unfold blocks_kept in KEPT. rewrite ?SEGS in KEPT.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & Hmat1).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  destruct FRESH as (FR_lo & FR_hi & FR_img).
  pose proof (cw_join_len ws) as JLEN.
  assert (JNN : 0 <= join_need ws) by lia.
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 208))
    by exact (eq_trans (HPRES1 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_3 : reg_get R2 3 = reg_get regs 3)
    by exact (eq_trans (HPRES1 3 ltac:(unfold callee_saved; lia)) (K1 3 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia))).
  assert (E2_4 : reg_get R2 4 = reg_get regs 4) by exact (eq_trans (HPRES1 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 (Z.min (Z.of_nat (length ws)) 64))
    by exact (eq_trans (HPRES1 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 res) by exact A0'.
  assert (F01 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) ->
             mbyte rsegs m1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m1 a)).
  { intros a Ha Hx. assert (Ho : outside [(bv_unsigned sp + -208, bv_unsigned sp)] a) by (cbn; split; [lia | exact I]).
    split; [exact (munch_mbyte _ _ _ _ _ MU1 Ha Ho) | exact (munch_writable _ _ _ _ _ MU1 Ha Ho)]. }
  assert (F12 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
             ~ (bv_unsigned sp - 8480 <= a < bv_unsigned sp - 208) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             ~ (bv_unsigned sp - 128 <= a < bv_unsigned sp - 120) ->
             mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
  { intros a Hd N1 Hs He Ho.
    apply HFRAME1; [exact Hd | exact N1 | exact (not_owned_mid B _ LAWS AX CTXO L A mem md L1 A1 m2 md1 a HMR HMR1 Hd N1) | |].
    - unfold scratch_k, JOINED_FRAME. change ALLOC_STACK with 8192. rewrite SP1. intros [H|H]; [lia | exact (He H)].
    - unfold joined_writes. intros [H|H]; [|lia].
      destruct Hd as [Hd|Hd]; [lia|]. apply (FR_img (a - res)); [lia|]. replace (res + (a - res)) with a by ring. exact Hd. }
  assert (F02 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
             ~ (bv_unsigned sp - 8480 <= a < bv_unsigned sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             mbyte rsegs m2 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m2 a)).
  { intros a Hd N1 Hs He.
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hd as [Hd|Hd]; [lia | pose proof (in_img_low B SEGS a Hd); lia]).
    destruct (F01 a Ha ltac:(lia)) as [E1 W1]. destruct (F12 a Hd N1 ltac:(lia) He ltac:(lia)) as [E2 W2].
    split; [congruence | tauto]. }
  assert (B02 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m2 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hi. pose proof (BRNG a k Hin).
    rewrite (KEPT a k i Hin (fun F => F) Hi). exact (proj1 (F01 (a + i) ltac:(lia) ltac:(lia))). }
  assert (LEB : bytes_at rsegs m2 (bv_unsigned sp + -128) (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (RecFacts.join_sp ws)))))).
  { apply (cw_bytes_of_le B m2 _ _ SEGS); [lia | rewrite Mem.length_le8; lia | exact LEO]. }
  assert (WR2 : forall a, bv_unsigned sp - 8480 <= a < bv_unsigned sp -> writable_at rsegs m2 a).
  { intros a Ha.
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 208)) as [H1|H1].
    { apply HSCR1. unfold scratch_k, JOINED_FRAME. change ALLOC_STACK with 8192. rewrite SP1. left. lia. }
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 128)) as [H2|H2];
      [|destruct (Z_lt_ge_dec a (bv_unsigned sp - 120)) as [H3|H3]].
    - apply (proj2 (F12 a ltac:(left; lia) (NOH a ltac:(lia)) ltac:(lia) (NEH a ltac:(lia)) ltac:(lia))). apply WR1. lia.
    - pose proof LEB as (_ & _ & LB).
      assert (Hk : (Z.to_nat (a - (bv_unsigned sp + -128)) <
                    length (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (RecFacts.join_sp ws))))))%nat)
        by (rewrite Mem.length_le8; lia).
      pose proof (LB _ Hk) as E.
      replace (bv_unsigned sp + -128 + Z.of_nat (Z.to_nat (a - (bv_unsigned sp + -128)))) with a in E by lia.
      apply present_writable. apply cw_hi_present; [lia|].
      rewrite cw_mbyte_mrd. rewrite E. apply nth_error_Some. exact Hk.
    - apply (proj2 (F12 a ltac:(left; lia) (NOH a ltac:(lia)) ltac:(lia) (NEH a ltac:(lia)) ltac:(lia))). apply WR1. lia. }
  assert (WRJ : forall a, bv_unsigned sp - 8480 <= a < bv_unsigned sp ->
             writable_at rsegs (MemNorm.normalize_cj rsegs m2) a).
  { intros a Ha. apply (cw_wr_norm m2 a RO2); [unfold TASK_SIZE; lia | exact (WR2 a Ha)]. }
  assert (MJ : forall a, 0 <= a -> a < bv_unsigned sp \/ a < W + 32 ->
             mbyte rsegs (MemNorm.normalize_cj rsegs m2) a = mbyte rsegs m2 a).
  { intros a H0 H1. apply (cw_mbyte_norm m2 a RO2). unfold TASK_SIZE. lia. }
  assert (GKJ : forall a, in_globals frame_G a -> mbyte rsegs (MemNorm.normalize_cj rsegs m2) a = mbyte rsegs mem a).
  { intros a Hg. pose proof (cw_g_iv a Hg) as Hr. destruct (G_STAT a Hg) as (Hi & _ & _ & He).
    rewrite MJ by lia.
    exact (proj1 (F02 a (or_intror Hi) (cw_gnown L A mem md a HMR Hg) ltac:(lia) He)). }
  assert (RKJ : forall a, in_globals frame_RELRO a -> ~ (0x22d40 <= a < 0x22d48) ->
             mbyte rsegs (MemNorm.normalize_cj rsegs m2) a = mbyte rsegs mem a).
  { intros a Ha Hg. pose proof (cw_relro_iv a Ha) as Hr.
    destruct (RELRO_FREE L A mem md a HMR Ha ltac:(rewrite GOT_AT; lia)) as [Ho He].
    rewrite MJ by lia.
    exact (proj1 (F02 a (or_intror (cw_img_iv B a SEGS ltac:(lia))) Ho ltac:(lia) He)). }
  assert (BKJ : forall q0 k x, In (q0, k) (blocks L A) -> q0 <= x < q0 + k ->
             mbyte rsegs (MemNorm.normalize_cj rsegs m2) x = mbyte rsegs mem x).
  { intros q0 k x Hb Hx. pose proof (BRNG q0 k Hb). rewrite MJ by lia.
    replace x with (q0 + (x - q0)) by ring. apply (B02 q0 k); [exact Hb | lia]. }
  assert (HKJ : forall a, bv_unsigned sp <= a < W + 32 ->
             mbyte rsegs (MemNorm.normalize_cj rsegs m2) a = mbyte rsegs mem a).
  { intros a Ha. rewrite MJ by lia.
    exact (proj1 (F02 a ltac:(left; lia) (NOH a ltac:(lia)) ltac:(lia) (NEH a ltac:(lia)))). }
  assert (MV : forall X cs, rw_cells rsegs m1 X cs -> bv_unsigned sp - 208 <= X ->
             X + Z.of_nat (cells_size cs) <= bv_unsigned sp ->
             (X + Z.of_nat (cells_size cs) <= bv_unsigned sp - 128 \/ bv_unsigned sp - 120 <= X) ->
             rw_cells rsegs (MemNorm.normalize_cj rsegs m2) X cs).
  { intros X cs H H1 H2 H3. apply (cw_rw_move m1 _ X cs H). intros i Hi. split.
    - rewrite MJ by lia.
      exact (proj1 (F12 (X + i) ltac:(left; lia) (NOH (X + i) ltac:(lia)) ltac:(lia) (NEH (X + i) ltac:(lia)) ltac:(lia))).
    - apply WRJ. lia. }
  assert (FA : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 208) [CB 8 j0]).
  { apply MV; [| lia | cbn; lia | cbn; lia].
    eapply (cw_rw_sub m1 (bv_unsigned sp + -208) _ []); [exact FR1 | cbn; lia]. }
  assert (F8J : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 208 + 8)
                  [CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; C8 (Z_to_bv 64 W); CB 8 j9]).
  { apply MV; [| lia | cbn; lia | cbn; lia].
    eapply (cw_rw_sub m1 (bv_unsigned sp + -208) _ [CB 8 j0]); [exact FR1 | cbn; lia]. }
  assert (FJ11 : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 208 + 88) [CB 16 j11]).
  { apply MV; [| lia | cbn; lia | cbn; lia].
    eapply (cw_rw_sub m1 (bv_unsigned sp + -208) _
      [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; C8 (Z_to_bv 64 W); CB 8 j9; CB 8 j10]);
      [exact FR1 | cbn; lia]. }
  assert (FRS : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 208 + 104)
                  [C8 (reg_get regs 27); C8 (reg_get regs 26); C8 (reg_get regs 25); C8 (reg_get regs 24);
                   C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                   C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply MV; [| lia | cbn; lia | cbn; lia].
    eapply (cw_rw_sub m1 (bv_unsigned sp + -208) _
      [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; C8 (Z_to_bv 64 W); CB 8 j9; CB 8 j10;
       CB 16 j11] _ []);
      [exact FR1 | cbn; lia]. }
  assert (FB80 : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 208 + 80)
                   [CB 8 (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (RecFacts.join_sp ws)))))]).
  { apply cw_rw_bytes.
    - cbn [cells_wf cell_wf]. split; [apply Mem.length_le8 | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_at_transfer rsegs m2);
        [replace (bv_unsigned sp - 208 + 80) with (bv_unsigned sp + -128) by lia; exact LEB|].
      intros i Hi. rewrite Mem.length_le8 in Hi. apply MJ; lia.
    - intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply WRJ. lia. }
  destruct (ax_statics AX L1 A1 m2 md1 HMR1) as (WG2 & (g2 & Hg2 & WGG2) & _).
  rewrite SEGS, GOT_AT, GUARD_AT in WG2. rewrite SEGS, GUARD_AT in WGG2.
  assert (GGJ : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) 0x22d40 [C8 (Z_to_bv 64 0x54730)]).
  { apply cw_rw_bytes; [cbn [cells_wf cell_wf]; tauto | |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_at_transfer rsegs m2);
        [exact (KindBGlue.word_mem_le8 rsegs m2 0x22d40 0x54730 WG2 ltac:(lia) ltac:(lia) ltac:(lia))|].
      intros i Hi. rewrite Mem.length_le8 in Hi. apply MJ; lia.
    - intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      exact (proj1 (guard_wview (MemNorm.normalize_cj rsegs m2) i Hi)). }
  assert (GUJ : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) 0x54730 [C8 (Z_to_bv 64 g2)]).
  { apply cw_rw_bytes; [cbn [cells_wf cell_wf]; tauto | |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_at_transfer rsegs m2);
        [exact (KindBGlue.word_mem_le8 rsegs m2 0x54730 g2 WGG2 Hg2 ltac:(lia) ltac:(lia))|].
      intros i Hi. rewrite Mem.length_le8 in Hi. apply MJ; lia.
    - intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      exact (proj2 (guard_wview (MemNorm.normalize_cj rsegs m2) i Hi)). }
  assert (HGJ : bytes_at rsegs (MemNorm.normalize_cj rsegs m2) 0x22cf8 (Mem.le8 (Z_to_bv 64 CW_GREC))).
  { apply (cw_bytes_of_image rsegs _ 8 _ _ cw_grec_img); [| lia | lia].
    intros i Hi. rewrite (RKJ (0x22cf8 + i)); [| apply cw_relro_of; lia | lia]. apply GIM. apply cw_relro_of. lia. }
  assert (HTJ : forall fn, 0 <= fn < 26 ->
             bytes_at rsegs (MemNorm.normalize_cj rsegs m2) (CW_TBL + 8 * fn) (Mem.le8 (Z_to_bv 64 (cw_tp fn)))).
  { intros fn Hfn. apply (cw_bytes_of_image rsegs _ 8 _ _ (cw_tbl_img fn Hfn)); [| unfold CW_TBL; lia | unfold CW_TBL; lia].
    intros i Hi. rewrite (RKJ (CW_TBL + 8 * fn + i)); [| apply cw_relro_of; unfold CW_TBL; lia | unfold CW_TBL; lia].
    apply GIM. apply cw_relro_of. unfold CW_TBL. lia. }
  pose proof REP as (Q & (RS & RC & _) & HQO).
  destruct RC as (C1 & C2 & C3 & C4 & _).
  assert (HNC : bytes_at rsegs (MemNorm.normalize_cj rsegs m2) (CW_GREC + 8)
                  (Mem.le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R)))))).
  { apply (bytes_at_transfer rsegs mem); [exact C3|].
    intros i Hi. rewrite Mem.length_le4 in Hi. apply GKJ. apply cw_g_of. unfold CW_GREC. lia. }
  assert (HCA : forall i c, nth_error (r_calls R) i = Some c ->
             call_at_a (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 8480) (CW_GREC + 16 + 56 * Z.of_nat i) c).
  { intros i c Hc.
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    destruct (nth_error (l_calls Q) i) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
    destruct (C4 i c P Hc HP) as [CA _].
    apply (cw_call_a (blocks L A) mem _ _ _ c P).
    - exact CA.
    - intros [p k] Hb. cbn [fst snd]. pose proof (BRNG p k Hb). lia.
    - unfold CW_GREC. lia.
    - unfold CW_GREC. lia.
    - unfold CW_GREC. lia.
    - intros x Hx. apply GKJ. apply cw_g_of. unfold CW_GREC in Hx. lia.
    - intros [p k] x Hb Hx. cbn [fst snd] in Hx. apply (BKJ p k); [exact Hb | lia]. }
  assert (UW : bv_unsigned (Z_to_bv 64 W) = W) by (apply unsigned_lit; lia).
  assert (HWA : bytes_at rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned (Z_to_bv 64 W) + 16)
                  (Mem.le8 (Z_to_bv 64 arr))).
  { rewrite UW. apply (bytes_at_transfer rsegs mem);
      [apply (cw_bytes_of_le B mem _ _ SEGS); [lia | rewrite Mem.length_le8; lia | exact W16]|].
    intros i Hi. rewrite Mem.length_le8 in Hi. apply HKJ. lia. }
  assert (WVJ : words_view B (MemNorm.normalize_cj rsegs m2) W arr wp ws).
  { apply (cw_wv_keep B L A mem _ W arr wp ws WV WP); rewrite SEGS.
    - intros i Hi. apply HKJ. lia.
    - intros p k i Hin Hi. apply (BKJ p k); [exact Hin | lia]. }
  assert (HWSJ : forall k, 0 <= k < Z.min (Z.of_nat (length ws)) 64 ->
             lowp (bv_unsigned sp - 8480) (MemNorm.normalize_cj rsegs m2) (bv_unsigned (Z_to_bv 64 arr) + 8 * k)
               (nth (Z.to_nat k) (map (Z_to_bv 64) wp) (Z_to_bv 64 0)) (nth (Z.to_nat k) ws [])).
  { intros k Hk. apply (cw_word_low B _ _ W arr wp ws k SEGS WVJ); [lia | lia | lia | | lia].
    intros j Hj. destruct (WPK j Hj) as (p & kk & Hb & H1 & H2). pose proof (BRNG p kk Hb). lia. }
  assert (UR : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (HLJ : bytes_at rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned (Z_to_bv 64 res))
                  (RecFacts.join_sp ws ++ [NUL])).
  { rewrite UR. apply (bytes_at_transfer rsegs m2);
      [apply (cw_bytes_of_le B m2 _ _ SEGS); [lia | rewrite length_app; cbn [length]; lia | exact LEJ]|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply MJ; lia. }
  assert (HL0 : ~ In NUL (RecFacts.join_sp ws)).
  { apply cw_join_no0. intros w Hw. apply (In_nth ws w []) in Hw as (k & Hk & <-).
    destruct (WK k Hk) as (_ & Hn & _). exact Hn. }
  assert (STJ : stk rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 8480) (bv_unsigned sp - 208)).
  { apply stk_normalize_cj; [lia | unfold TASK_SIZE; lia | intros a Ha; apply WR2; lia]. }
  assert (UA : bv_unsigned (Z_to_bv 64 arr) = arr) by (apply unsigned_lit; lia).
  assert (HA1 : 0 < Z.min (Z.of_nat (length ws)) 64 ->
             bv_unsigned (Z_to_bv 64 arr) <> 0 /\ bv_unsigned (Z_to_bv 64 arr) mod 8 = 0).
  { intros _. rewrite UA. split; [lia | exact A8]. }
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_3, E2_4, E2_9, E2_10.
    eapply (MemNorm.evt_normalize_cj rsegs); [exact WX | exact RO2 |].
    eapply (cw_body SSP SCS ATOI SNP SC ADD CHAIN PIN (reg_get regs 3) (reg_get regs 4) (reg_get regs 1)
      (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
      (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
      fp_regs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 8480) (bv_unsigned sp - 208)
      (Z.min (Z.of_nat (length ws)) 64) ws (map (Z_to_bv 64) wp) (Z_to_bv 64 W) (Z_to_bv 64 arr) (Z_to_bv 64 res)
      (Z_to_bv 64 g2) (r_calls R) j0 j1 j2 j3 j4 j5 j6 j7 j9
      (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (RecFacts.join_sp ws))))) j11).
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold words_prop in WPR. exact WPR.
    - exact C1.
    - exact FA.
    - exact F8J.
    - exact FB80.
    - exact FJ11.
    - exact FRS.
    - exact GGJ.
    - exact GUJ.
    - exact HGJ.
    - exact HTJ.
    - exact HNC.
    - exact HCA.
    - exact HWA.
    - rewrite UW. lia.
    - exact HA1.
    - exact HWSJ.
    - exact HLJ.
    - exact HL0.
    - rewrite UR. lia.
    - rewrite UR. lia.
    - exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs m2)).
    - exact STJ.
    - exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs m2)).
    - exact FRM. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & CJ3) & EQ3).
  unfold cw_body_post in Q3.
  destruct Q3 as (y0 & y1 & y2 & z0 & z8 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10
    & x11 & y3 & y4 & y5 & y6 & Fc & fc & m3n & -> & MI3 & MU3n & WM3n & ST3n & FH3n & FRM3 & FPR3).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r CJ3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r CJ3 EQ3. subst can3.
  pose proof (MemNorm.munch_rel_cj rsegs _ _ _ _ _ (MemNorm.mem_rel_cj_normalize rsegs m2 RO2) MR3r CJ3 MU3n) as MU3.
  pose proof (MemNorm.ro_agree_same_cj rsegs _ _ RO2 CJ3) as RO3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3). clear EQ3.
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x14eb4) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 208))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_3 : getr R3 3 = reg_get regs 3) by (rewrite (getr_of_eqv _ _ 3 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_4 : getr R3 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 res) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (SP3 : spZ R3 = bv_unsigned sp - 208) by (unfold spZ; rewrite E3_2, unsigned_lit by lia; ring).
  assert (OUT3 : forall a, ~ (bv_unsigned sp - 8480 <= a < bv_unsigned sp - 104) ->
            outside [(bv_unsigned sp - 8480, bv_unsigned sp - 208 + 104)] a) by (intros a Ha; cbn; split; [lia | exact I]).
  assert (HMR3 : aa_MR API L1 A1 m3 md1).
  { apply (mr_frame B _ LAWS L1 A1 m2 m3 md1 md1 HMR1).
    - intros a Ho. destruct (mr_owned_low B _ LAWS _ _ _ _ a HMR1 Ho) as [Ha1 Ha2].
      apply (munch_mbyte _ _ _ _ _ MU3); [lia | apply OUT3; lia].
    - intros a Ho Hp. destruct (mr_owned_low B _ LAWS _ _ _ _ a HMR1 Ho) as [Ha1 Ha2].
      apply (munch_present _ _ _ a MU3); [lia | apply OUT3; lia | exact Hp].
    - intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L1 A1 m2 md1 p k i HMR1 Hin Hi) as (Hp & H4 & Hc & _).
      apply (munch_present _ _ _ _ MU3); [lia | apply OUT3; lia | exact Hp].
    - reflexivity.
    - exact Hh1.
    - exact Hl1.
    - exact Hmat1. }
  assert (WR3 : forall a, bv_unsigned sp - 8480 <= a < bv_unsigned sp -> writable_at rsegs m3 a).
  { intros a Ha. destruct ST3n as (_ & _ & HS). destruct (HS a ltac:(lia)) as [Hw _].
    exact (MemNorm.writable_at_rel_cj rsegs m3 m3n a MR3r Hw). }
  assert (ERR3 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m3 a).
  { intros a Ha. pose proof Ha as Ha'. rewrite EA in Ha'.
    apply (proj1 (munch_writable rsegs _ _ _ a MU3 ltac:(lia) (OUT3 a ltac:(lia)))).
    apply HSCR1. unfold scratch_k. right. exact Ha. }
  assert (INB : In (res, join_need ws + 1) (blocks L1 A1)) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  pose proof INB as INB'. apply YI06.blocks_In in INB' as (pf & EPF & UPF).
  pose proof (FREE (mkFP Fc fc)) as FR0. unfold free_contract in FR0. rewrite SEGS, FREE_PC in FR0.
  eapply SR_bind.
  { apply (FR0 L1 A1 R3 m3 md1 pf (join_need ws + 1) (sb_malloc b (join_need ws + 1))); clear FR0.
    - split; [exact HMR3|]. split; [exact HWF1|]. split; [exact HBD1|].
      split; [rewrite E3_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP3; replace (bv_unsigned sp - 208) with (bv_unsigned sp + (-13) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP3; change ALLOC_STACK with 8192; lia|].
      split; [rewrite SP3; lia|].
      split; [intros a Ha; rewrite SP3 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite SEGS; apply WR3; lia|].
      split; [rewrite E3_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; exact (ERR3 a Ha)|].
      intros HI. rewrite INIT1 in HI. discriminate.
    - exact RO3.
    - exact UPF.
    - rewrite E3_10, EPF. reflexivity.
    - exact RES1. }
  intros c4 RET4.
  destruct RET4 as (L2 & A2 & R4 & m4 & md2 & -> & CP4 & (d1 & d2 & BL2 & BL3) & KEPT4 & RO4 & GK4 & UB4 & INIT4
    & REG4 & RES4).
  destruct CP4 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HP4 & HVM2 & HFR2 & HBLKS2 & HSCR2).
  rewrite SEGS in HFR2, HSCR2.
  unfold blocks_kept in KEPT4. rewrite SEGS in KEPT4.
  assert (F34 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L1 A1 a ->
             ~ (bv_unsigned sp - 8400 <= a < bv_unsigned sp - 208) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             ~ (res <= a < res + (join_need ws + 1)) ->
             mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
  { intros a Hd N1 Hs He Hr.
    apply HFR2; [exact Hd | exact N1 | exact (not_owned_mid B _ LAWS AX CTXO L1 A1 m2 md1 L2 A2 m4 md2 a HMR1 HMR2 Hd N1) | |].
    - unfold scratch. rewrite SP3. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (He H)].
    - cbv beta. rewrite EPF. exact Hr. }
  assert (F24 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L1 A1 a ->
             ~ (bv_unsigned sp - 8480 <= a < bv_unsigned sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             ~ (res <= a < res + (join_need ws + 1)) ->
             mbyte rsegs m4 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a <-> writable_at rsegs m4 a)).
  { intros a Hd N1 Hs He Hr.
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hd as [Hd|Hd]; [lia | pose proof (in_img_low B SEGS a Hd); lia]).
    pose proof (munch_mbyte rsegs _ _ _ _ MU3 Ha (OUT3 a ltac:(lia))) as E23.
    pose proof (munch_writable rsegs _ _ _ _ MU3 Ha (OUT3 a ltac:(lia))) as W23.
    destruct (F34 a Hd N1 ltac:(lia) He Hr) as [E34 W34].
    split; [congruence | tauto]. }
  assert (FALL : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
             ~ (bv_unsigned sp - 8480 <= a < bv_unsigned sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             mbyte rsegs m4 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m4 a)).
  { intros a Hd N1 Hs He.
    assert (Hr : ~ (res <= a < res + (join_need ws + 1))).
    { intros Hr. destruct Hd as [Hd|Hd]; [lia|]. apply (FR_img (a - res)); [lia|].
      replace (res + (a - res)) with a by ring. exact Hd. }
    destruct (F02 a Hd N1 Hs He) as [E1 W1].
    destruct (F24 a Hd (not_owned_mid B _ LAWS AX CTXO L A mem md L1 A1 m2 md1 a HMR HMR1 Hd N1) Hs He Hr) as [E2 W2].
    split; [congruence | tauto]. }
  assert (B24 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m4 (a + i) = mbyte rsegs m2 (a + i)).
  { intros a k i Hin Hi. pose proof (BRNG a k Hin) as Rg.
    assert (Hin1 : In (a, k) (blocks L1 A1)) by (rewrite BLK1; rewrite BLK2 in Hin; apply in_mid_inv; exact Hin).
    assert (Hne : a <> ptr_addr L1 pf).
    { rewrite EPF. intros ->. rewrite BLK2 in Hin.
      destruct (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR1 BLK1 Hin); lia. }
    rewrite (KEPT4 a k i Hin1 Hne Hi).
    exact (munch_mbyte rsegs _ _ _ (a + i) MU3 ltac:(lia) (OUT3 (a + i) ltac:(lia))). }
  assert (BALL : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m4 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hi. rewrite (B24 a k i Hin Hi). exact (B02 a k i Hin Hi). }
  assert (BL2' : blocks L1 A1 = d1 ++ (res, join_need ws + 1) :: d2) by (rewrite <- EPF; exact BL2).
  assert (BLEQ : blocks L2 A2 = blocks L A).
  { rewrite BL3, BLK2. symmetry. apply (cw_mid_eq b1 b2 d1 d2 (res, join_need ws + 1)).
    - rewrite <- BLK1. exact BL2'.
    - intros H. destruct (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR1 BLK1 (in_or_app _ _ _ (or_introl H)));
        lia.
    - intros H. destruct (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR1 BL2' (in_or_app _ _ _ (or_introl H)));
        lia. }
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  assert (E4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 208))
    by exact (eq_trans (HP4 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (E4_3 : reg_get R4 3 = reg_get regs 3) by exact (eq_trans (HP4 3 ltac:(unfold callee_saved; lia)) E3_3).
  assert (E4_4 : reg_get R4 4 = reg_get regs 4) by exact (eq_trans (HP4 4 ltac:(unfold callee_saved; lia)) E3_4).
  assert (FH4 : rw_cells rsegs m4 (bv_unsigned sp - 208 + 104)
                  [C8 (reg_get regs 27); C8 (reg_get regs 26); C8 (reg_get regs 25); C8 (reg_get regs 24);
                   C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                   C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (cw_rw_move m3 m4 _ _ (rw_cells_rel_cj rsegs m3 m3n _ _ MR3r FH3n)).
    intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    assert (N1 : ~ owned B L1 A1 (bv_unsigned sp - 208 + 104 + i))
      by (intros Ho; destruct (mr_owned_low B _ LAWS _ _ _ _ _ HMR1 Ho); lia).
    destruct (F34 (bv_unsigned sp - 208 + 104 + i) ltac:(left; lia) N1 ltac:(lia) ltac:(rewrite EA; lia) ltac:(lia))
      as [E Wq].
    split; [exact E|]. apply Wq. apply WR3. lia. }
  rewrite E3_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E4_2.
    eapply cw_epi with (rao := reg_get regs 1) (s0o := reg_get regs 8) (s1o := reg_get regs 9)
      (s2o := reg_get regs 18) (s3o := reg_get regs 19) (s4o := reg_get regs 20) (s5o := reg_get regs 21)
      (s6o := reg_get regs 22) (s7o := reg_get regs 23) (s8o := reg_get regs 24) (s9o := reg_get regs 25)
      (s10o := reg_get regs 26) (s11o := reg_get regs 27).
    - rewrite unsigned_lit by lia. exact FH4.
    - rewrite unsigned_lit by lia. lia. }
  intros ms5 (can5 & E5 & EQ5). subst can5.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ5) as (R5 & -> & X5). clear EQ5.
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  apply SR_ret. cbv beta.
  exists (mkFP Fc fc), L2, A2, R5, m4, md2.
  split; [rewrite RP; reflexivity|].
  split; [exact FRM3|].
  split.
  { unfold call_post_k.
    split; [exact HMR2|]. split; [exact HWF2|]. split; [exact HBD2|].
    split; [exact (cw_lle_trans A A1 L L1 L2 HLE1 HLE2 RLEN1)|].
    split; [intros p k H1 H3; pose proof (UBK p k H1) as H2; rewrite (HSTAB2 p k H2 H3); exact (HSTAB1 p k H1 H2)|].
    split.
    { intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [C|C].
      { subst r. rewrite (getr_of_eqv _ _ _ X5) by reflexivity. simp_regs. rewrite unsigned_lit by lia.
        replace (bv_unsigned sp - 208 + 208) with (bv_unsigned sp) by ring. rewrite Z_to_bv_bv_unsigned. reflexivity. }
      repeat (destruct C as [C|C];
        [subst r; rewrite (getr_of_eqv _ _ _ X5) by reflexivity; simp_regs; first [reflexivity | exact E4_3 | exact E4_4]|]).
      subst r; rewrite (getr_of_eqv _ _ _ X5) by reflexivity; simp_regs; reflexivity. }
    split; [destruct HVM1 as [vm1 ->]; destruct HVM2 as [vm2 ->]; exists vm2; apply with_vmmaps_twice'|].
    split.
    { intros a Hd N1 _ Hs _. rewrite SEGS. unfold scratch_k in Hs. rewrite KV in Hs.
      change (spZ regs) with (bv_unsigned sp) in Hs.
      exact (FALL a Hd N1 (fun H => Hs (or_introl H)) (fun H => Hs (or_intror H))). }
    split.
    { intros p k i H1 _ Hi. rewrite SEGS. apply (BALL (ptr_addr L p) k i); [|exact Hi].
      unfold blocks. exact (in_map (fun e => (ptr_addr L (fst e), snd e)) _ _ H1). }
    intros a Hs. rewrite SEGS. unfold scratch_k in Hs. rewrite KV in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
    destruct Hs as [Hs|He]; [|apply HSCR2; unfold scratch; right; exact He].
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 8400)) as [Hl8|Hh8];
      [|destruct (Z_lt_ge_dec a (bv_unsigned sp - 208)) as [Hlo2|Hhi2]].
    - assert (N1 : ~ owned B L1 A1 a) by (intros Ho; destruct (mr_owned_low B _ LAWS _ _ _ _ _ HMR1 Ho); lia).
      apply (proj2 (F34 a ltac:(left; lia) N1 ltac:(lia) ltac:(rewrite EA; lia) ltac:(lia))).
      apply WR3. lia.
    - apply HSCR2. unfold scratch. rewrite SP3. change ALLOC_STACK with 8192. left. lia.
    - assert (N1 : ~ owned B L1 A1 a) by (intros Ho; destruct (mr_owned_low B _ LAWS _ _ _ _ _ HMR1 Ho); lia).
      apply (proj2 (F34 a ltac:(left; lia) N1 ltac:(lia) ltac:(rewrite EA; lia) ltac:(lia))).
      apply WR3. lia. }
  split; [exact BLEQ|].
  split; [unfold blocks_kept; rewrite SEGS; intros a k i Hin _ Hi; exact (BALL a k i Hin Hi)|].
  split; [intros _; exact (INIT4 INIT1)|].
  split; [lia|].
  split.
  { unfold CommandB.cmd_mem. rewrite SEGS.
    destruct (ax_statics AX L2 A2 m4 md2 HMR2) as (WG4 & (g4 & Hg4 & WGG4) & _).
    rewrite SEGS, GOT_AT, GUARD_AT in WG4. rewrite SEGS, GUARD_AT in WGG4.
    split; [exact RO4|].
    split.
    { unfold G_img_c. intros a Ha. rewrite SEGS. pose proof (cw_relro_iv a Ha) as Hr.
      destruct (Z_lt_ge_dec a 0x22d40) as [H1|H1]; [|destruct (Z_lt_ge_dec a 0x22d48) as [H2|H2]].
      - destruct (RELRO_FREE L A mem md a HMR Ha ltac:(rewrite GOT_AT; lia)) as [Ho He].
        rewrite <- (GIM a Ha). exact (proj1 (FALL a (or_intror (cw_img_iv B a SEGS ltac:(lia))) Ho ltac:(lia) He)).
      - exact (cw_got_rom m4 a WG4 ltac:(lia)).
      - destruct (RELRO_FREE L A mem md a HMR Ha ltac:(rewrite GOT_AT; lia)) as [Ho He].
        rewrite <- (GIM a Ha). exact (proj1 (FALL a (or_intror (cw_img_iv B a SEGS ltac:(lia))) Ho ltac:(lia) He)). }
    split.
    { exists (Z_to_bv 64 g4). apply (cw_le_of_bytes B m4 _ _ SEGS).
      exact (KindBGlue.word_mem_le8 rsegs m4 0x54730 g4 WGG4 Hg4 ltac:(lia) ltac:(lia)). }
    intros i Hi. exact (cw_guard_wr m4 i Hi). }
  split.
  { apply (cw_le_keep B mem); [exact QUIT0|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le4 in Hi.
    destruct (QOUT i Hi) as [No Ns].
    unfold scratch_k in Ns. rewrite KV in Ns. change (spZ regs) with (bv_unsigned sp) in Ns.
    assert (Hg : in_globals frame_G (VerbsB.G_QUIT + i)) by (apply cw_g_of; unfold VerbsB.G_QUIT; lia).
    destruct (G_STAT _ Hg) as (Hi' & _ & _ & _).
    exact (proj1 (FALL _ (or_intror Hi') No (fun H => Ns (or_introl H)) (fun H => Ns (or_intror H)))). }
  split.
  { unfold g_rec_rep in REP |- *. apply (rec_rep_frame rsegs G_REC REC_SC L A mem R O L2 A2 m4 REP).
    - intros a Ha. assert (Hg : in_globals frame_G a) by (apply cw_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
      destruct (G_STAT a Hg) as (Hi & _ & _ & He). pose proof (cw_g_iv a Hg) as Hr.
      destruct (FALL a (or_intror Hi) (cw_gnown L A mem md a HMR Hg) ltac:(lia) He) as [E Wq].
      split; [exact E | apply Wq].
    - intros p k i Hin Hi. exact (BALL p k i (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) Hi).
    - intros pn Hin. rewrite BLEQ. exact (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin). }
  split.
  { apply (cw_wv_keep B L A mem m4 W arr wp ws WV WP); rewrite SEGS.
    - intros i Hi.
      exact (proj1 (FALL (W + 16 + i) ltac:(left; lia) (NOH (W + 16 + i) ltac:(lia)) ltac:(lia) (NEH (W + 16 + i) ltac:(lia)))).
    - intros p k i Hin Hi. exact (BALL p k i Hin Hi). }
  exact RES4.
Qed.

End CW.
