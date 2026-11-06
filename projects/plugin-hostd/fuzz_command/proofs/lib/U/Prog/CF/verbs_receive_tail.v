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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/chain_words.v, with its module paths and module names changed; 183 of its 219 lines of code are new or changed and 1083 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 217 of its 258 lines of code are new or changed and 178 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_call.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail0 verbs_receive_tail_k reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail_m verbs_receive_tail_r.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail_e verbs_receive_tail_f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br3 verbs_receive_tail_a.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import sup_after_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strcspn_c strncmp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section T.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).
Local Notation TS f := (@tl_state f _ B API S).

Let TLM_text := tl_text.
Let TLM_nrep := tl_nrep.
Let TLM_run := tl_run.
Let TLM_short := tl_after_short.
Hypothesis RP : forall f : YK11.FPState, @reply_contract f rc B API.
Hypothesis SAR : forall f : YK11.FPState, @sup_after_reply_contract f rc B API.
Hypothesis FREE : forall f : YK11.FPState, @free_contract f rc B API.
Hypothesis CSPN : strcspn_contract.
Hypothesis NCMP : strncmp_contract.
Hypothesis ATOI : atoi_c.atoi_contract.
Let TLR := fun f : YK11.FPState => @tl_call_reply f rc B API HF S HS RP.
Let TLA := fun f : YK11.FPState => @tl_after f rc B API HF S HS SAR CSPN NCMP ATOI.
Let TLF := fun f : YK11.FPState => @tl_frees f rc B API HF S HS FREE.
Let TLE := fun f : YK11.FPState => @tl_epi f rc B API HF S HS.

Lemma tl_tail : forall (f : YK11.FPState) rg mem md L A R O k q nq x jk c ret (qt : bool),
  VS f rg REPLY mem md L A R O k (if qt then 1 else s_q0 S) (Some (q, nq, x)) jk c ->
  getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) -> getr rg 11 = Z_to_bv 64 q ->
  VerbsRun.run_step sup_reply_code_c.reply_code (s_R S)
    (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) = (R, x, qt) ->
  (k + 3 <= 32)%nat ->
  (forall rg' mem' md' L' A' O' c',
     VS f rg' ret mem' md' L' A' (fst (socket_send_m R (x ++ [Z_to_bv 8 0]))) O' (k + 1)
       (if qt then 1 else s_q0 S) None jk c' ->
     regs_preserved rg rg' ->
     (forall rg2 mem2 md2 L2 A2 O2 c2,
        VS f rg2 0x17aa8 mem2 md2 L2 A2 (fst (socket_send_m R (x ++ [Z_to_bv 8 0]))) O2 (k + 1)
          (if qt then 1 else s_q0 S) None jk c2 ->
        (2 <= length (toks D))%nat -> SR rsegs c2 (vr_post B API S)) ->
     (forall rg2 mem2 md2 L2 A2 O2 c2,
        VS f rg2 0x17b10 mem2 md2 L2 A2 (fst (socket_send_m R (x ++ [Z_to_bv 8 0]))) O2 (k + 1)
          (if qt then 1 else s_q0 S) None jk c2 ->
        (length (toks D) <= 1)%nat -> SR rsegs c2 (vr_post B API S)) ->
     SR rsegs c' (vr_post B API S)) ->
  SR rsegs c (vr_post B API S).
Proof.
  intros f rg mem md L A R O k q nq x jk c ret qt HST E1 RET E11 RUN HK KONT.
  destruct (TLM_text _ _ _ _ _ RUN) as [NZ LX].
  pose proof (TLM_nrep _ _ _ _ _ RUN) as NR. pose proof (ok_nrep B API S HS) as NR0.
  apply (TLR f rg mem md L A R O k _ q nq x jk c ret _ HST E1 RET E11 NZ LX ltac:(lia) ltac:(lia)).
  intros rg' mem' md' L' A' O' c' HST' PR'.
  apply (KONT rg' mem' md' L' A' O' c' HST' PR').
  - intros rg2 mem2 md2 L2 A2 O2 c2 HST2 HL2.
    apply (TLA f rg2 mem2 md2 L2 A2 _ O2 (k + 1) _ jk c2 _ HST2 HL2 ltac:(lia)).
    intros f' rg3 mem3 md3 L3 A3 O3 k3 c3 HST3 _.
    apply (TLF f' rg3 mem3 md3 L3 A3 _ O3 k3 _ jk c3 _ HST3).
    intros rg4 mem4 md4 L4 A4 c4 HT4.
    exact (TLE f' rg4 mem4 md4 L4 A4 _ O3 k3 _ jk c4 x qt HT4 (TLM_run _ _ _ _ _ RUN) eq_refl).
  - intros rg2 mem2 md2 L2 A2 O2 c2 HST2 HL2.
    apply (TLF f rg2 mem2 md2 L2 A2 _ O2 (k + 1) _ jk c2 _ HST2).
    intros rg4 mem4 md4 L4 A4 c4 HT4.
    pose proof (TLM_run _ _ _ _ _ RUN) as VR. rewrite (TLM_short _ _ HL2) in VR.
    exact (TLE f rg4 mem4 md4 L4 A4 _ O2 (k + 1) _ jk c4 x qt HT4 VR eq_refl).
Qed.

Lemma tl_ntok : (length (toks D) <= 64)%nat.
Proof. unfold toks. rewrite length_firstn. unfold line_words_max. lia. Qed.

Lemma tl_vregs : forall rg rg', vregs S rg ->
  getr rg' 2 = getr rg 2 -> getr rg' 3 = getr rg 3 -> getr rg' 4 = getr rg 4 -> getr rg' 8 = getr rg 8 ->
  getr rg' 9 = getr rg 9 -> getr rg' 25 = getr rg 25 -> getr rg' 26 = getr rg 26 -> getr rg' 27 = getr rg 27 ->
  vregs S rg'.
Proof.
  intros rg rg' (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27) E2 E3 E4 E8 E9 E25 E26 E27.
  unfold vregs. rewrite E2, E3, E4, E8, E9, E25, E26, E27. tauto.
Qed.

Lemma vr_tail_17834_ge : forall rg0 k0,
  (2 <= length (toks D))%nat -> (k0 + 11 <= 32)%nat ->
  join_k_ge B API S 0x178b0 19 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof.
  intros rg0 k0 HL HK0 f rg mem md L A R O k q nq x jk c (qt & HST & _ & E19 & _ & _ & RUN & HK1).
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw f _ B API HF S HS rg 0x178b0 mem md L A R O k _ _ jk c _ _ HST).
  { unfold Regs6ss.mkR_of. apply tk_17834. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK REPLY eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  apply (tl_tail f rg' mem2 md L A R O k q _ x jk _ 0x178bc qt HST1).
  - rewrite (getr_of_eqv _ _ 1 X eq_refl). reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - rewrite (getr_of_eqv _ _ 11 X eq_refl). exact E19.
  - exact RUN.
  - lia.
  - intros rg2 mem3 md3 L3 A3 O3 c3 HST3 _ CHK _.
    pose proof HST3 as (_ & _ & VR3 & _).
    eapply (@ka_nw f _ B API HF S HS rg2 0x178bc mem3 md3 L3 A3 _ O3 (k + 1) _ _ jk c3 _ _ HST3 (tk_17840 _ _ _ _)).
    { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
    intros R' pc' rg4 mem4 EQ X4 MK4. cbv beta in EQ. injection EQ as E3 E4. subst R' pc'.
    pose proof (getr_eqv_of rg2 rg4 X4) as GE.
    apply (CHK rg4 mem4 md3 L3 A3 O3 _); [|exact HL].
    apply MK4; [reflexivity | apply (vregs_pres S rg2 rg4 VR3); intros r _; apply GE].
Qed.

Lemma vr_tail_17830_ge : forall rg0 k0,
  (2 <= length (toks D))%nat -> (k0 + 11 <= 32)%nat ->
  join_k_ge B API S 0x178ac 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof.
  intros rg0 k0 HL HK0 f rg mem md L A R O k q nq x jk c (qt & HST & HNQ & E10 & E18 & _ & RUN & HK1).
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw f _ B API HF S HS rg 0x178ac mem md L A R O k _ _ jk c _ _ HST).
  { unfold Regs6ss.mkR_of. apply tk_17830. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (VR' : vregs S rg') by (apply (tl_vregs rg rg' VR);
    match goal with |- getr _ ?r = _ => rewrite (getr_of_eqv _ _ r X eq_refl); reflexivity end).
  apply (vr_tail_17834_ge rg0 k0 HL HK0 f rg' mem2 md L A R O k q nq x jk _).
  exists qt. split; [exact (MK 0x178b0 eq_refl VR')|]. split; [exact HNQ|].
  split; [rewrite (getr_of_eqv _ _ 19 X eq_refl); exact E10|].
  split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); exact E18|].
  split; [intros [H|H]; lia|].
  split; [exact RUN | exact HK1].
Qed.

Lemma vr_tail_17974_ge : forall rg0 k0,
  getr rg0 21 = verbs_receive_disp.ntokw (toks D) -> toks D <> [] -> (k0 + 11 <= 32)%nat ->
  join_k_ge B API S 0x17a94 20 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof.
  intros rg0 k0 N21 NE HK0 f rg mem md L A R O k q nq x jk c (qt & HST & _ & E20 & E18 & E21 & RUN & HK1).
  specialize (E21 (or_intror eq_refl)).
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw f _ B API HF S HS rg 0x17a94 mem md L A R O k _ _ jk c _ _ HST).
  { unfold Regs6ss.mkR_of. apply tk_17974. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK REPLY eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  apply (tl_tail f rg' mem2 md L A R O k q _ x jk _ 0x17aa0 qt HST1).
  - rewrite (getr_of_eqv _ _ 1 X eq_refl). reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - rewrite (getr_of_eqv _ _ 11 X eq_refl). exact E20.
  - exact RUN.
  - lia.
  - intros rg2 mem3 md3 L3 A3 O3 c3 HST3 PR3 CHK DIR.
    pose proof HST3 as (_ & _ & VR3 & _).
    assert (R21 : reg_get rg2 21 = verbs_receive_disp.ntokw (toks D)).
    { transitivity (getr rg0 21); [|exact N21].
      transitivity (getr rg 21); [|exact E21].
      transitivity (getr rg' 21); [|exact (PR 21 ltac:(unfold callee_saved; lia))].
      exact (PR3 21 ltac:(unfold callee_saved; lia)). }
    eapply (@ka_nw f _ B API HF S HS rg2 0x17aa0 mem3 md3 L3 A3 _ O3 (k + 1) _ _ jk c3 _ _ HST3).
    { unfold Regs6ss.mkR_of. apply (tk_17980 (toks D)); [exact R21 | exact tl_ntok]. }
    { intros ms' [(_ & E)|(_ & E)]; subst ms'; do 2 eexists; reflexivity. }
    intros R' pc' rg4 mem4 HQ X4 MK4.
    destruct HQ as [(LN & EQ)|(LN & EQ)]; injection EQ as E3 E4; subst R' pc';
      (assert (PR4 : regs_preserved rg2 rg4) by (apply (pres_of rg2 _ rg4 X4); intros r Hr; cs_cases r Hr; reflexivity)).
    + apply (DIR rg4 mem4 md3 L3 A3 O3 _); [exact (MK4 0x17b10 eq_refl (vregs_pres S rg2 rg4 VR3 PR4)) | lia].
    + assert (L0 : length (toks D) <> 0%nat) by (intros H; apply NE; apply length_zero_iff_nil; exact H).
      apply (CHK rg4 mem4 md3 L3 A3 O3 _); [exact (MK4 0x17aa8 eq_refl (vregs_pres S rg2 rg4 VR3 PR4)) | lia].
Qed.

Lemma vr_tail_17970_ge : forall rg0 k0,
  getr rg0 21 = verbs_receive_disp.ntokw (toks D) -> toks D <> [] -> (k0 + 11 <= 32)%nat ->
  join_k_ge B API S 0x17a90 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof.
  intros rg0 k0 N21 NE HK0 f rg mem md L A R O k q nq x jk c (qt & HST & HNQ & E10 & E18 & E21 & RUN & HK1).
  specialize (E21 (or_introl eq_refl)).
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw f _ B API HF S HS rg 0x17a90 mem md L A R O k _ _ jk c _ _ HST).
  { unfold Regs6ss.mkR_of. apply tk_17970. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (VR' : vregs S rg') by (apply (tl_vregs rg rg' VR);
    match goal with |- getr _ ?r = _ => rewrite (getr_of_eqv _ _ r X eq_refl); reflexivity end).
  apply (vr_tail_17974_ge rg0 k0 N21 NE HK0 f rg' mem2 md L A R O k q nq x jk _).
  exists qt. split; [exact (MK 0x17a94 eq_refl VR')|]. split; [exact HNQ|].
  split; [rewrite (getr_of_eqv _ _ 20 X eq_refl); exact E10|].
  split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); exact E18|].
  split; [intros _; rewrite (getr_of_eqv _ _ 21 X eq_refl); exact E21|].
  split; [exact RUN | exact HK1].
Qed.

Lemma vr_tail_176c8_ge : forall rg0 k0,
  (length (toks D) <= 1)%nat -> (k0 + 11 <= 32)%nat ->
  join_k_ge B API S 0x176c4 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof.
  intros rg0 k0 HL HK0 f rg mem md L A R O k q nq x jk c (qt & HST & _ & E10 & _ & _ & RUN & HK1).
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw f _ B API HF S HS rg 0x176c4 mem md L A R O k _ _ jk c _ _ HST).
  { unfold Regs6ss.mkR_of. apply tk_176c8. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK REPLY eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  apply (tl_tail f rg' mem2 md L A R O k q _ x jk _ 0x176d0 qt HST1).
  - rewrite (getr_of_eqv _ _ 1 X eq_refl). reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - rewrite (getr_of_eqv _ _ 11 X eq_refl). exact E10.
  - exact RUN.
  - lia.
  - intros rg2 mem3 md3 L3 A3 O3 c3 HST3 _ _ DIR.
    pose proof HST3 as (_ & _ & VR3 & _).
    eapply (@ka_nw f _ B API HF S HS rg2 0x176d0 mem3 md3 L3 A3 _ O3 (k + 1) _ _ jk c3 _ _ HST3 (tk_176d4 _ _ _ _)).
    { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
    intros R' pc' rg4 mem4 EQ X4 MK4. cbv beta in EQ. injection EQ as E3 E4. subst R' pc'.
    pose proof (getr_eqv_of rg2 rg4 X4) as GE.
    apply (DIR rg4 mem4 md3 L3 A3 O3 _); [|exact HL].
    apply MK4; [reflexivity | apply (vregs_pres S rg2 rg4 VR3); intros r _; apply GE].
Qed.

Lemma vr_tail_17830 : forall rg0 k0,
  (2 <= length (toks D))%nat -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x178ac 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof. intros rg0 k0 HL HK. apply join_k_of_ge. exact (vr_tail_17830_ge rg0 k0 HL HK). Qed.

Lemma vr_tail_17834 : forall rg0 k0,
  (2 <= length (toks D))%nat -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x178b0 19 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof. intros rg0 k0 HL HK. apply join_k_of_ge. exact (vr_tail_17834_ge rg0 k0 HL HK). Qed.

Lemma vr_tail_17970 : forall rg0 k0,
  getr rg0 21 = verbs_receive_disp.ntokw (toks D) -> toks D <> [] -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x17a90 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof. intros rg0 k0 N21 NE HK. apply join_k_of_ge. exact (vr_tail_17970_ge rg0 k0 N21 NE HK). Qed.

Lemma vr_tail_17974 : forall rg0 k0,
  getr rg0 21 = verbs_receive_disp.ntokw (toks D) -> toks D <> [] -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x17a94 20 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof. intros rg0 k0 N21 NE HK. apply join_k_of_ge. exact (vr_tail_17974_ge rg0 k0 N21 NE HK). Qed.

Lemma vr_tail_176c8 : forall rg0 k0,
  (length (toks D) <= 1)%nat -> (k0 + 11 <= 32)%nat ->
  join_k B API S 0x176c4 10 rg0 (s_R S) k0 (s_q0 S) (vr_post B API S).
Proof. intros rg0 k0 HL HK. apply join_k_of_ge. exact (vr_tail_176c8_ge rg0 k0 HL HK). Qed.

End T.
