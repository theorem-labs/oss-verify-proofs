(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module names changed; 605 of its 653 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_chain.v, with its module paths and module names changed; 239 of its 280 lines of code are new or changed and 612 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0 AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel printf_facts_c arg_i RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM06 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import arg_i_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import xstrdup_c rec_calls_free_c answer_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecInv RecInvP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecAnsB RecTail RecStub.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecCore.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import SupChainA.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis MALLOC_PC : ms_malloc B = 0x18a0c.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis ARGI : forall fx0 : YK11.FPState, arg_i_contract (fx := fx0) B API.

Lemma sch_mid : forall K S L A mem md O Lc Ac mc mdc Rp fn Oc bc regs_c (n id : Z) (P : config -> Prop),
  sinv B API K S L A mem md O Lc Ac mc mdc (rec_record Rp fn []) Oc bc ->
  (length (r_calls Rp) <= 16)%nat ->
  getr regs_c 1 = Z_to_bv 64 0x16bd4 -> spZ regs_c mod 16 = 0 -> getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs_c 8 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp) -> getr regs_c 9 = Z_to_bv 64 n ->
  getr regs_c 10 = Z_to_bv 64 (12 * n + 1) -> getr regs_c 20 = Z_to_bv 64 id ->
  0 <= n < 2 ^ 31 -> -2 ^ 31 <= id < 2 ^ 31 ->
  S - K <= spZ regs_c - ARG_I_K -> spZ regs_c <= S -> spZ regs_c <= TASK_SIZE ->
  frm_zero fp_csr ->
  room_slots (sb_shift bc A Ac) (12 * n + 1) ->
  room_slots (sb_malloc (sb_malloc (sb_shift bc A Ac) (12 * n + 1)) (Z.of_nat (length (dec id)) + 1))
    (Z.of_nat (length (dec id)) + 1) ->
  room_slots (sb_malloc (sb_malloc (sb_malloc (sb_shift bc A Ac) (12 * n + 1)) (Z.of_nat (length (dec id)) + 1))
      (Z.of_nat (length (dec n)) + 1)) (Z.of_nat (length (dec n)) + 1) ->
  (forall (fx' : YK11.FPState) L' A' R' m' md' lp p1 p2, fp_kept fx fx' ->
     sinvx B API K S L A mem md O L' A' m' md' (rec_record Rp fn [dec id; dec n])
       ((Oc ++ [(p1, Z.of_nat (length (dec id)) + 1)]) ++ [(p2, Z.of_nat (length (dec n)) + 1)]) bc
       (lp, 12 * n + 1) ->
     m_halted md' = None -> m_vm_lazy md' = [] ->
     sb_shift bc A A' = sb_malloc (sb_malloc (sb_malloc (sb_shift bc A Ac) (12 * n + 1))
                          (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length (dec n)) + 1) ->
     (forall a, spZ regs_c <= a < S -> mbyte rsegs m' a = mbyte rsegs mc a /\
        (writable_at rsegs mc a -> writable_at rsegs m' a)) ->
     getr R' 2 = getr regs_c 2 -> getr R' 3 = getr regs_c 3 -> getr R' 4 = getr regs_c 4 ->
     getr R' 8 = getr regs_c 8 -> getr R' 9 = getr regs_c 9 -> getr R' 18 = getr regs_c 18 ->
     getr R' 19 = Z_to_bv 64 lp ->
     getr R' 24 = getr regs_c 24 -> getr R' 25 = getr regs_c 25 -> getr R' 26 = getr regs_c 26 ->
     getr R' 27 = getr regs_c 27 ->
     SR rsegs (mkCfg (@mkst fx' R' (Z_to_bv 64 0x16bf4) m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 0x18a0c) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS ERRNO_LOW GFACT GOWN AX MALLOC_PC GOTG GRD MALLOC ARGI.
  intros K S L A mem md O Lc Ac mc mdc Rp fn Oc bc regs_c n id P SI HRp E1 HAL HTP E8 E9 E10 E20 HN HID HLO HHI HTS
    FZ ROOM1 ROOM2 ROOM3 KC.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_value as (ACr & _).
  pose proof SI as (RJ & _).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & HK1 & HK2 & HK3 & _).
  assert (ER : rec_entry G_REC REC_SC Rp mod 8 = 0 /\ REC_SC <= rec_entry G_REC REC_SC Rp /\
               rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC, REC_SIZE.
      split; [|lia]. apply Z.mod_divide; [lia|]. exists (26539 + 7 * Z.of_nat (length (r_calls Rp))). lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. split; [reflexivity | lia]. }
  assert (EB : 0x33d10 <= rec_entry G_REC REC_SC Rp /\ rec_entry G_REC REC_SC Rp + 56 <= 0x34108).
  { set (e := rec_entry G_REC REC_SC Rp) in *. unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE in ER. lia. }
  assert (KA : ALLOC_STACK <= ARG_I_K) by (unfold ARG_I_K, XSTRDUP_K; lia).
  assert (CP0 : call_pre B (aa_MR API) Lc Ac regs_c mc mdc).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) Lc Ac regs_c mc mdc)).
    apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md Lc Ac mc mdc ALLOC_STACK regs_c RJ).
    - rewrite E1. apply bv_eq. vm_compute. reflexivity.
    - exact HAL.
    - unfold ALLOC_STACK. lia.
    - lia.
    - exact HHI.
    - exact HTP. }
  apply (sch_malloc B API SEGS ERRNO_LOW GFACT GOWN AX MALLOC_PC GOTG GRD MALLOC K S L A mem md O Lc Ac mc mdc
           (rec_record Rp fn []) Oc bc regs_c (12 * n + 1) P SI CP0 ltac:(lia) HHI E10 ltac:(lia) ROOM1).
  intros L1 A1 R1 m1 md1 p SI1 POST1 A01 NZ FB SH1.
  rewrite E1.
  pose proof POST1 as (PM1 & _ & _ & _ & _ & RP1 & _).
  destruct (mr_model B _ LAWS L1 A1 m1 md1 PM1) as (Hh1 & Hl1 & _).
  pose proof FB as (FB1 & FB2 & _).
  assert (R1_10 : reg_get R1 10 = Z_to_bv 64 p) by exact A01.
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R1_10.
    eapply sch_m1. lia. }
  intros ms1 (can1 & Ec1 & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  assert (F2_1 : getr R2 1 = Z_to_bv 64 0x16be8) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (F2_2 : getr R2 2 = getr regs_c 2)
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact (RP1 2 ltac:(unfold callee_saved; lia))).
  assert (F2_3 : getr R2 3 = getr regs_c 3)
    by (rewrite (getr_of_eqv _ _ 3 X2 eq_refl); simp_regs; exact (RP1 3 ltac:(unfold callee_saved; lia))).
  assert (F2_4 : getr R2 4 = getr regs_c 4)
    by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact (RP1 4 ltac:(unfold callee_saved; lia))).
  assert (F2_8 : getr R2 8 = getr regs_c 8)
    by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; exact (RP1 8 ltac:(unfold callee_saved; lia))).
  assert (F2_9 : getr R2 9 = getr regs_c 9)
    by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; exact (RP1 9 ltac:(unfold callee_saved; lia))).
  assert (F2_10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp))
    by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs;
        exact (eq_trans (RP1 8 ltac:(unfold callee_saved; lia)) E8)).
  assert (F2_11 : getr R2 11 = Z_to_bv 64 id)
    by (rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs;
        exact (eq_trans (RP1 20 ltac:(unfold callee_saved; lia)) E20)).
  assert (F2_18 : getr R2 18 = getr regs_c 18)
    by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; exact (RP1 18 ltac:(unfold callee_saved; lia))).
  assert (F2_19 : getr R2 19 = Z_to_bv 64 p) by (rewrite (getr_of_eqv _ _ 19 X2 eq_refl); simp_regs; reflexivity).
  assert (F2_24 : getr R2 24 = getr regs_c 24)
    by (rewrite (getr_of_eqv _ _ 24 X2 eq_refl); simp_regs; exact (RP1 24 ltac:(unfold callee_saved; lia))).
  assert (F2_25 : getr R2 25 = getr regs_c 25)
    by (rewrite (getr_of_eqv _ _ 25 X2 eq_refl); simp_regs; exact (RP1 25 ltac:(unfold callee_saved; lia))).
  assert (F2_26 : getr R2 26 = getr regs_c 26)
    by (rewrite (getr_of_eqv _ _ 26 X2 eq_refl); simp_regs; exact (RP1 26 ltac:(unfold callee_saved; lia))).
  assert (F2_27 : getr R2 27 = getr regs_c 27)
    by (rewrite (getr_of_eqv _ _ 27 X2 eq_refl); simp_regs; exact (RP1 27 ltac:(unfold callee_saved; lia))).
  assert (SP2 : spZ R2 = spZ regs_c) by (unfold spZ; rewrite F2_2; reflexivity).
  pose proof SI1 as (RJ1 & GR1 & _).
  destruct (RecCore.rec_rep_entry rsegs G_REC REC_SC L1 A1 m1 Rp _ fn [] GR1 HRp) as (Q1 & CA1).
  pose proof CA1 as (_ & _ & _ & _ & NA1 & _).
  apply (sch_argi B API SEGS ERRNO_LOW GFACT GOWN AX (ARGI fx) K S L A mem md O L1 A1 m1 md1 Rp fn [] Oc bc
           (p, 12 * n + 1) R2 id P SI1 ltac:(cbn; lia)).
  - split; [|rewrite SP2; exact HTS].
    apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md L1 A1 m1 md1 ARG_I_K R2 RJ1).
    + rewrite F2_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP2. exact HAL.
    + unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
    + rewrite SP2. exact HLO.
    + rewrite SP2. exact HHI.
    + rewrite F2_4. exact HTP.
  - rewrite SP2. exact HLO.
  - rewrite SP2. exact HHI.
  - exact F2_10.
  - exact F2_11.
  - exact HID.
  - exact (proj1 ER).
  - exact (proj1 (proj2 ER)).
  - exact (proj2 (proj2 ER)).
  - apply glob_wr_at; unfold GLOB_LO, GLOB_N, CALL_SIZE; lia.
  - exact NA1.
  - exact FZ.
  - rewrite SH1. exact ROOM2.
  - intros fx2 L3 A3 R3 m3 md3 p1 FK2 SI3 POST3 SH3.
    rewrite F2_1.
    pose proof POST3 as (PM3 & _ & _ & _ & _ & RP3 & _).
    destruct (mr_model B _ LAWS L3 A3 m3 md3 PM3) as (Hh3 & Hl3 & _).
    eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply sch_m2. }
    intros ms4 (can4 & Ec4 & EQ4). subst can4.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
    assert (F4_1 : getr R4 1 = Z_to_bv 64 0x16bf4)
      by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
    assert (F4_2 : getr R4 2 = getr regs_c 2)
      by (rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) F2_2)).
    assert (F4_3 : getr R4 3 = getr regs_c 3)
      by (rewrite (getr_of_eqv _ _ 3 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 3 ltac:(unfold callee_saved; lia)) F2_3)).
    assert (F4_4 : getr R4 4 = getr regs_c 4)
      by (rewrite (getr_of_eqv _ _ 4 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 4 ltac:(unfold callee_saved; lia)) F2_4)).
    assert (F4_8 : getr R4 8 = getr regs_c 8)
      by (rewrite (getr_of_eqv _ _ 8 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) F2_8)).
    assert (F4_9 : getr R4 9 = getr regs_c 9)
      by (rewrite (getr_of_eqv _ _ 9 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) F2_9)).
    assert (F4_10 : getr R4 10 = Z_to_bv 64 (rec_entry G_REC REC_SC Rp))
      by (rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs;
          exact (eq_trans (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) F2_8) E8)).
    assert (F4_11 : getr R4 11 = Z_to_bv 64 n)
      by (rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs;
          exact (eq_trans (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) F2_9) E9)).
    assert (F4_18 : getr R4 18 = getr regs_c 18)
      by (rewrite (getr_of_eqv _ _ 18 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 18 ltac:(unfold callee_saved; lia)) F2_18)).
    assert (F4_19 : getr R4 19 = Z_to_bv 64 p)
      by (rewrite (getr_of_eqv _ _ 19 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 19 ltac:(unfold callee_saved; lia)) F2_19)).
    assert (F4_24 : getr R4 24 = getr regs_c 24)
      by (rewrite (getr_of_eqv _ _ 24 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 24 ltac:(unfold callee_saved; lia)) F2_24)).
    assert (F4_25 : getr R4 25 = getr regs_c 25)
      by (rewrite (getr_of_eqv _ _ 25 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 25 ltac:(unfold callee_saved; lia)) F2_25)).
    assert (F4_26 : getr R4 26 = getr regs_c 26)
      by (rewrite (getr_of_eqv _ _ 26 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 26 ltac:(unfold callee_saved; lia)) F2_26)).
    assert (F4_27 : getr R4 27 = getr regs_c 27)
      by (rewrite (getr_of_eqv _ _ 27 X4 eq_refl); simp_regs;
          exact (eq_trans (RP3 27 ltac:(unfold callee_saved; lia)) F2_27)).
    assert (SP4 : spZ R4 = spZ regs_c) by (unfold spZ; rewrite F4_2; reflexivity).
    pose proof SI3 as (RJ3 & GR3 & _).
    destruct (RecCore.rec_rep_entry rsegs G_REC REC_SC L3 A3 m3 Rp _ fn [dec id] GR3 HRp) as (Q3 & CA3).
    pose proof CA3 as (_ & _ & _ & _ & NA3 & _).
    assert (IN3 : In (p1, Z.of_nat (length (dec id)) + 1) (blocks L3 A3)).
    { apply (rec_rep_O_blocks rsegs G_REC REC_SC L3 A3 m3 _ _ _ GR3).
      apply in_or_app. right. left. reflexivity. }
    destruct (block_facts B _ LAWS L3 A3 m3 md3 p1 _ 0 PM3 IN3 ltac:(lia)) as (_ & _ & BP1 & _).
    apply (sch_argi (fx := fx2) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGI fx2) K S L A mem md O L3 A3 m3 md3 Rp fn
             [dec id] (Oc ++ [(p1, Z.of_nat (length (dec id)) + 1)]) bc (p, 12 * n + 1) R4 n P SI3 ltac:(cbn; lia)).
    + split; [|rewrite SP4; exact HTS].
      apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md L3 A3 m3 md3 ARG_I_K R4 RJ3).
      * rewrite F4_1. apply bv_eq. vm_compute. reflexivity.
      * rewrite SP4. exact HAL.
      * unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      * rewrite SP4. exact HLO.
      * rewrite SP4. exact HHI.
      * rewrite F4_4. exact HTP.
    + rewrite SP4. exact HLO.
    + rewrite SP4. exact HHI.
    + exact F4_10.
    + exact F4_11.
    + lia.
    + exact (proj1 ER).
    + exact (proj1 (proj2 ER)).
    + exact (proj2 (proj2 ER)).
    + apply glob_wr_at; unfold GLOB_LO, GLOB_N, CALL_SIZE; lia.
    + exact NA3.
    + exact (proj1 FK2).
    + rewrite SH3, SH1. exact ROOM3.
    + intros fx3 L5 A5 R5 m5 md5 p2 FK3 SI5 POST5 SH5.
      rewrite F4_1.
      pose proof POST5 as (PM5 & _ & _ & _ & _ & RP5 & _).
      destruct (mr_model B _ LAWS L5 A5 m5 md5 PM5) as (Hh5 & Hl5 & _).
      pose proof SI5 as (_ & GR5 & _).
      assert (IN5 : In (p2, Z.of_nat (length (dec n)) + 1) (blocks L5 A5)).
      { apply (rec_rep_O_blocks rsegs G_REC REC_SC L5 A5 m5 _ _ _ GR5).
        apply in_or_app. right. left. reflexivity. }
      destruct (block_facts B _ LAWS L5 A5 m5 md5 p2 _ 0 PM5 IN5 ltac:(lia)) as (_ & _ & BP2 & _).
      apply (KC fx3 L5 A5 R5 m5 md5 p p1 p2 (RecCore.fp_kept_trans fx fx2 fx3 FK2 FK3) SI5 Hh5 Hl5).
      * rewrite SH5, SH3, SH1. reflexivity.
      * intros a Ha.
        destruct (post_k_keep_hi B API SEGS ERRNO_LOW ALLOC_STACK Lc Ac regs_c mc mdc _ L1 A1 R1 m1 md1 a HM POST1
                    ltac:(unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK in *; lia) ltac:(lia)) as [K1 W1].
        { intros H. exact H. }
        destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_I_K L1 A1 R2 m1 md1 _ L3 A3 R3 m3 md3 a PM1 POST3
                    ltac:(unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK in *; lia) ltac:(rewrite SP2; lia)) as [K2 W2].
        { cbv beta. unfold CALL_OFF_NARGS, CALL_OFF_ARGS. cbn [length Z.of_nat].
          unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK in *. lia. }
        destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_I_K L3 A3 R4 m3 md3 _ L5 A5 R5 m5 md5 a PM3 POST5
                    ltac:(unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK in *; lia) ltac:(rewrite SP4; lia)) as [K3 W3].
        { cbv beta. unfold CALL_OFF_NARGS, CALL_OFF_ARGS. cbn [length Z.of_nat].
          unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK in *. lia. }
        split; [rewrite K3, K2, K1; reflexivity | intros Hw; apply W3, W2, W1, Hw].
      * exact (eq_trans (RP5 2 ltac:(unfold callee_saved; lia)) F4_2).
      * exact (eq_trans (RP5 3 ltac:(unfold callee_saved; lia)) F4_3).
      * exact (eq_trans (RP5 4 ltac:(unfold callee_saved; lia)) F4_4).
      * exact (eq_trans (RP5 8 ltac:(unfold callee_saved; lia)) F4_8).
      * exact (eq_trans (RP5 9 ltac:(unfold callee_saved; lia)) F4_9).
      * exact (eq_trans (RP5 18 ltac:(unfold callee_saved; lia)) F4_18).
      * exact (eq_trans (RP5 19 ltac:(unfold callee_saved; lia)) F4_19).
      * exact (eq_trans (RP5 24 ltac:(unfold callee_saved; lia)) F4_24).
      * exact (eq_trans (RP5 25 ltac:(unfold callee_saved; lia)) F4_25).
      * exact (eq_trans (RP5 26 ltac:(unfold callee_saved; lia)) F4_26).
      * exact (eq_trans (RP5 27 ltac:(unfold callee_saved; lia)) F4_27).
Qed.

End M.
