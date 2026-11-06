(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at 25d4b718638 and the definitions
   w7_kept, w7_hull, w7_strok, w7_strz of proofs/reac-pw/fuzz_role/lib/A/RPgW7bKit.v at 25d4b718638, for
   reac-pw/fuzz_headamp's image B: w7_ -> hw7b_, role's image A code and record -> fuzz_headamp.asan-ubsan's (its own
   code table, pcs, registers and real-frame cells, measured on image B), module paths; the statements of the walk's
   blocks and call steps are new (hw7b_*_stmt), one per block of image B's own code; its hw7b_post,
   hw7b_post_of_run, hw7b_kept, hw7b_hull, hw7b_ra_kept, hw7b_hull_kept, hw7b_strok, hw7b_strz, hw7b_strok_kept and
   hw7b_strok_first_byte are lib/AU/HPgCaseB.v's cb_* since the dedup. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW7bBase.v, with its numbers changed; 102 of its 142 lines of code are new or changed and 274 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bIter.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths and the rm_ prefix renamed, every pc moved by the code's uniform shift +0xd20, the strlen trampoline 0x41b98 and __asan_memcpy 0x51d0c (W7_STRLEN / W7_MEMCPY of lib/A/HPgW7bBase.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW7bIter.v; 467 of its 535 lines of code are new or changed and 74 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC1.v at f3898085bda (the vocab strings,
   the model of a case-1 turn, e62's bytes at the join, the bounds of the shadow hulls, c1_calls and the block
   lemma w6b_c1) for reac-pw/fuzz_headamp's image B: image B's vocab table and pcs, e62 at F+0x210 with its body
   at F+0x218, the strlen wrapper at STRLEN_ENTRY_B and __asan_memcpy at 0x51d8c through HPgCaseB.cb_memcpy_at,
   the string facts taken from HPgBase.hd_cstr (which carries the tail of the NUL's word, so role's
   c1_vtail / c1_vtail_chk are dropped), and the post HPgSteps.hdu_blk_postE / HPgCaseBJ.cj_J_R. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW6bC1.v, with its module paths and module names changed; 321 of its 365 lines of code are new or changed and 491 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC1a.v at f3898085bda (c1_head, c1_vcell,
   c1_set: one engine run per block from an entry state to a call or to the next block) for reac-pw/fuzz_headamp's
   image B: image B's code, registers and real-frame cells (below); the head runs from the kit's entry state
   HPgW6bBase.ss_hb (a6 pinned to 1, s4 to 0 when no byte is left) and splits `beqz s4` itself; the UBSan
   pointer tests of image B are decided by the engine from the cursor's and the index's ranges; the post is
   HPgCaseB.cb_post. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the first three blocks of
   case 1 of ent_build's `switch (kind % 10)` (pod.h:285-296, ent_text pod.h:209-219) inside LLVMFuzzerTestOneInput
   (0x80c40), each an engine run (lib/Reusable/YCbn.v) from an entry state to a call or to the next block, with its
   post in the shape of HPgCaseB.cb_post. Proves no function (kind: segment lemma).

   THE CODE (registers as at a case entry, HPgW6bBase.hw6b_in: s1 = x9 = R, s11 = x27 = SHADOW_OFF, s2 = x18 = c the
   cursor after the kind byte, a7 = x17 = c - 1, t1 = x6 = |r| + 1, s4 = x20 = |r|, a6 = x16 = 1, a3 = x13 the kind
   byte sign-extended; real-frame cells read: [R+0x118] = F + 0x218 (&e62.body); written: [R+0x58], [R+0x110]):
     hb1_head  0x81e04 .. 0x82114
       0x81e04  beqz s4 -> 0x820f8               no byte left: t1 := 0; a0 := 0x9c4e0 (&vocab[0]); a7 := s2
       0x81e08  a0 := s2 + 1; bltu a6,a0          the UBSan pointer test (its `unimp` arm 0x83a14 needs c = 0)
       0x81e14 .. 0x81e20  the shadow check of s2 (slow block 0x8281c)
       0x81e24  lbu a1,0(s2) (= m); a0 := 0x9c4e0; a1 := 8 * (m % 9) (mul by 0x39, srli 9, two subw, zext.b, slli 3)
       0x81e50  not a2,a0; bgeu a2,a1             the UBSan pointer test of &vocab[i] (never taken: a1 <= 2040)
       0x81e5c  t1 := t1 - 2; a7 := a7 + 2; a0 := a0 + a1; j 0x82108
       0x82108  s7 := [R+0x118]; sd a3,0x58(s1) (the kind byte's spill); sd a7,0x110(s1) (the cursor's spill)
     hb1_vcell 0x82114 .. the strlen trampoline 0x41c18 (`jal` at 0x82134, ra = 0x82138)
       0x82114 .. 0x82120  the instrumented check of the 8-byte cell at a0: its shadow byte must be 0 (`beqz` to
                0x82128; else `j` to the error path 0x83c44, which the proof shows is not reached)
       0x82128  mv s5,t1; ld s10,0(a0) (= vocab[i]); mv a0,s10; jal strlen
     hb1_set   0x82138 .. __asan_memcpy 0x51d8c (`jal` at 0x82158, ra = 0x8215c)
       s4 := len; s2 := len; bltu len,0x5f (taken: the vocab lengths are 12 .. 18); a0 := s7 (&e62.body);
       a1 := s10; a2 := s2; jal __asan_memcpy
   THE STATES. hb1_head: HPgW6bBase.ss_hb (the extra atoms 32 = F, 33 = pp, 34 = [R+0xe8], 35 = m); the shadow
   entry over e62 (HPgW6bBase.hb_SH) makes the kit's e62 window safe for the token engine. hb1_vcell: a0 is its own
   atom (x10) with the fact [0x9c4e0, 0x9c520] (8-aligned), so the engine sees the check's `(x >> 3) + s11` form;
   the check's obligation `range_addressable` over the cell's 8 bytes is paid by the registered table's addressable
   range (HPgW6bBase.hw6b_vocab_ok). hb1_set: no memory, len (x10) with the fact [12, 18]. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgW6bBase HPgW6bC1k HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition HB1_V : Z := 0x82114.      (* a0 = &vocab[i]: the check of the cell, its `ld`, the strlen call *)
Definition HB1_SLR : Z := 0x82138.    (* strlen returns here *)
Definition HB1_MCR : Z := 0x8215c.    (* __asan_memcpy returns here *)

(* ======================================== the head's post ======================================== *)
(* the registers the head may change: t1, a0, a1, a2, a6 (pinned), a7, s4 (pinned), s7 *)
Definition hb1_hclob : list (bv 5) := [6; 10; 11; 12; 16; 17; 20; 23]%bv.
(* the bytes the head may change: the two spills, and e62 (a write window of the kit state; the head keeps it 0) *)
Definition hb1_head_wr (R F : Z) : Z -> Prop := fun a =>
  (R + 0x58 <= a < R + 0x60) \/ (R + 0x110 <= a < R + 0x118) \/ (F + 0x210 <= a < F + 0x278).
(* what the head computes: a0 = &vocab[i], t1 = |r'|, s7 = &e62.body, the two spills, e62 still 0 *)
Definition hb1_head_R (W : world rsegs) (R F c kd : Z) (r : list byte) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) : Prop :=
  getr regs2 10 = w64 (HB_VOCAB + 8 * (fst (fuzz_u8 r) mod 9)) /\
  getr regs2 6 = w64 (Z.of_nat (length (snd (fuzz_u8 r)))) /\
  getr regs2 23 = w64 (F + 0x218) /\
  val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x58) 8 ((kd - 256 * (kd / 128)) mod 2 ^ 64) /\
  val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x110) 8
    (c + Z.of_nat (length r) - Z.of_nat (length (snd (fuzz_u8 r)))) /\
  (forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) mem2) (F + 0x210 + i) = Some (Z_to_bv 8 0)).

(* ======================================== helpers ======================================== *)
(* `beqz s4` with s4 = n >= 1 is not taken *)
Lemma hb1_beqz : forall E n, ew E 20 = Z_to_bv 64 n -> 1 <= n < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff 20 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E n H Hn. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. rewrite Z.add_0_r.
cbn [branch_taken]. destruct (bv_eqb (Z_to_bv 64 n) (Z_to_bv 64 0)) eqn:E0; [|reflexivity].
apply bv_eqb_true_iff in E0. apply (f_equal bv_unsigned) in E0. rewrite !unsigned_lit_small in E0 by lia. lia.
Qed.
Lemma hb1_vptr_range : forall i, 0 <= hb_vptr i <= 0x21020.
Proof.
intros i. unfold hb_vptr.
destruct (Z.to_nat i) as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; cbn [nth]; try lia. destruct n; lia.
Qed.
Lemma hb1_af : forall E n v lo hi al, bv_unsigned (ew E n) = v -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H. auto. Qed.
Lemma hb1_mod16 : forall R, R mod 32 = 0 -> R mod 16 = 0.
Proof.
intros R H. pose proof (Z.div_mod R 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (32 * (R / 32)) with ((R / 32 * 2) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* the write windows of a start state lie in Zn *)
Ltac hb1_kwr B9 B32 :=
  let a := fresh "a" in let r0 := fresh "r0" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
  intros a (r0 & Hin & Hb);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r0 rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B9, ?B32 in Hb; cbv beta;
     try unfold hb1_head_wr; lia|]);
  destruct Hin.
(* the windows of the kit state: A, C, E and I read only, B and D in the stack window, F in the frame (4, pos) *)
Ltac hb1_awr_kit B9 B32 R sp0 pos Hown HFa :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat _); [reflexivity | exact B32 |
      cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 4, pos; split; [exact Hown|]; left;
      unfold in_zr; cbn [fst snd]; rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia |] ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

(* ======================================== hb1_head: 0x81e04 .. 0x82114 ======================================== *)
Lemma hb1_head : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos c pp kd r,
  hw6b_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  kd mod 10 = 1 ->
  hw6b_in B W memc regs R F c pp kd r ->
  SRr rsegs W (cfg_at rsegs HB_D1 regs memc mdc)
  (cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HB1_V regs memc mdc hb1_hclob (hb1_head_wr R F)
     (hb1_head_R W R F c kd r)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp kd r Hctx Hk1 Hin.
pose proof hb_wx as Hwx. pose proof hb_segs_low as Hsegs.
destruct Hctx as (HJ & HR32 & HRsp & HspR & Hown & HFa & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & H13 & V40 & Ve8 & V118 & V130 & V138 & V148 &
  Hkd & Hpp1 & Hpp2 & HF1 & HF2 & HF32 & HRc & HFp & Ez & Hrae & Hhe & Hc1 & Hinp & Hhin & HdisF).
destruct Hinp as (Hg & Hrain & Hc0 & Hcr & Ham & Hdis).
specialize (H13 ltac:(rewrite Hk1; discriminate)).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@asan_consts rc) as (Hac & _).
assert (HT : T_SEG_STK = 16384) by reflexivity. rewrite HT in HspR, HRc, Hdis.
pose proof (hb1_mod16 R HR32) as HR16.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & Happ).
rewrite <- HFa in Happ. change (fs_frame_bytes 4) with 1024 in Happ.
assert (Hap : forall a, F + 0x210 <= a < F + 0x278 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
{ intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia. }
assert (Pw : forall o, (0x58 <= o < 0x60 \/ 0x110 <= o < 0x118) -> apresent (w_H W) memc (R + o))
  by (intros o Ho; apply Hpres; lia).
assert (Pe : forall o, 0 <= o < 104 -> apresent (w_H W) memc (F + 0x210 + o))
  by (intros o Ho; rewrite <- Z.add_assoc; apply HFp; lia).
pose proof (hb_e8_range F HF1 HF2) as He8.
unfold Layout.PP_SIZE in Hpp2.
assert (Vkd : 0 <= (kd - 256 * (kd / 128)) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
clear Hsp0al HSTK0 Hceil Hslo.
assert (HRa : alloc_ceiling <= R) by lia.
assert (HRb : R + 0x220 <= 2 ^ 47) by lia.
assert (Hpa : 0 <= pp) by lia.
assert (Hpb : pp + 0x4000 < 2 ^ 64) by lia.
assert (Hpc0 : 0 <= HB_D1) by (unfold HB_D1; lia).
destruct r as [|mb r1].
- (* no byte left: t1 = 0, a0 = &vocab[0], the cursor c spilled *)
  cbn [length Z.of_nat] in H20, H6, Ham, Hcr.
  assert (Hcb : 1 <= c <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
  assert (H0b : 0 <= 0 < 256) by lia.
  pose proof (hb_entry HB_D1 false W regs memc R F c pp 0 Hpc0 H9 H27 H18 HRa HRb HR16 HF1 HF2 Hcb H0b Hpa Hpb
    V40 Ve8 V118 V130 V138 V148 Pw Ez Pe (fun X => False_ind _ (Bool.diff_false_true X))) as HS0.
  set (e8 := (- (F + 0x219)) mod 2 ^ 64) in *.
  set (E := Ereg regs (hb_extra F pp e8 0)) in HS0.
  pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 0 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H20; reflexivity)) as HS.
  clear HS0.
  assert (B9 : bv_unsigned (ew E 9) = R) by exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
  assert (B32 : bv_unsigned (ew E 32) = F).
  { subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth hb_extra]. apply unsigned_lit_small. lia. }
  assert (E13 : ew E 13 = Z_to_bv 64 (kd - 256 * (kd / 128))) by exact (eq_trans (ew_Ereg_nat regs _ 13 13%bv eq_refl) H13).
  assert (E18 : ew E 18 = Z_to_bv 64 c) by exact (eq_trans (ew_Ereg_nat regs _ 18 18%bv eq_refl) H18).
  assert (SHOK : sh_ok rsegs HBx hb_SH E (mrestrict (w_H W) memc))
    by exact (hb_shok regs (w_H W) memc F pp e8 0 H27 HF1 HF2 Hrae Hap).
  assert (HAE : env_agree 32 E E) by apply env_agree_refl.
  unfold cfg_at. change (w64 HB_D1) with (Z_to_bv 64 HB_D1).
  aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB1_V.
  + hb1_awr_kit B9 B32 R sp0 pos Hown HFa.
  + eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | cb_kio | | | exact HG | ].
    * eapply (regs_kept_of_st_ok rsegs _ _ ms regs (hb_extra F pp e8 0) (w_H W) _ HS);
        [env_agree_chain HAE | vm_compute; reflexivity].
    * intros a Ha Hz.
      exact (cb_kept_run (hb1_head_wr R F) _ _ (w_H W) memc memc (ms_mem ms)
        (fun a _ _ => eq_refl) HFr ltac:(hb1_kwr B9 B32) a Ha Hz).
    * unfold hb1_head_R. cbn [fuzz_u8 fst snd length Z.of_nat].
      split; [hb1_reg HS (10%bv : bv 5); reflexivity|].
      split; [hb1_reg HS (6%bv : bv 5); reflexivity|].
      split; [hb1_reg HS (23%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite B32; reflexivity|].
      split.
      { eapply (cb_val_at _ _ (w_H W) ms 1%nat _ 0x58 8%N _ _ R _);
          [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
          | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E13, Z.add_0_r; apply bv_eq;
            rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_mod by lia;
            reflexivity
          | cbn; lia | lia]. }
      split.
      { eapply (cb_val_at _ _ (w_H W) ms 3%nat _ 0x110 8%N _ _ R _);
          [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
          | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E18, unsigned_lit_small by lia; f_equal; lia
          | cbn; lia | lia]. }
      intros i Hi.
      pose proof (hb_chunk_zero _ _ _ 0x210 104 (hb_region _ _ _ hb_rF HS ltac:(apply (nth_error_In _ 5);
        vm_compute; reflexivity)) ltac:(left; reflexivity) i Hi) as Hz.
      cbn [YP09.r_base base_val hb_rF] in Hz. rewrite ?ew_ewset_other in Hz by lia. rewrite B32 in Hz. exact Hz.
- (* a byte m left *)
  pose proof (byte_range mb) as Hmb.
  set (m := bv_unsigned mb) in *.
  set (n := Z.of_nat (length (mb :: r1))) in *.
  assert (Hn : n = Z.of_nat (length r1) + 1) by (subst n; cbn [length]; lia).
  assert (Hnb : 1 <= n /\ c + n <= 2 ^ 47 - 1).
  { split; [lia|]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) c 1 m).
  { destruct (Hg 0%nat ltac:(cbn [length map hd_zbytes]; lia)) as [Hv _]. rewrite Z.add_0_r in Hv. exact Hv. }
  assert (Hcd : c + 1 <= R + 0x40 \/ R + 0x150 <= c) by (pose proof (Hdis c ltac:(lia)) as Hd; lia).
  assert (HcF : c + 1 <= F + 0x210 \/ F + 0x278 <= c) by (pose proof (HdisF c ltac:(lia)) as Hd; lia).
  assert (Hcb : 1 <= c <= 2 ^ 47 - 1) by lia.
  pose proof (hb_entry HB_D1 true W regs memc R F c pp m Hpc0 H9 H27 H18 HRa HRb HR16 HF1 HF2 Hcb Hmb Hpa Hpb
    V40 Ve8 V118 V130 V138 V148 Pw Ez Pe (fun _ => conj Hm0 (conj Hcd HcF))) as HS0.
  set (e8 := (- (F + 0x219)) mod 2 ^ 64) in *.
  set (E := Ereg regs (hb_extra F pp e8 m)) in HS0.
  pose proof (st_ok_pin_lit rsegs _ _ _ (16%bv : bv 5) 1 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H16; reflexivity)) as HS.
  clear HS0.
  assert (B9 : bv_unsigned (ew E 9) = R) by exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
  assert (B32 : bv_unsigned (ew E 32) = F).
  { subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth hb_extra]. apply unsigned_lit_small. lia. }
  assert (E35 : ew E 35 = Z_to_bv 64 m) by (subst E; exact (ew_Ereg_extra regs (hb_extra F pp e8 m) 3)).
  assert (E13 : ew E 13 = Z_to_bv 64 (kd - 256 * (kd / 128))) by exact (eq_trans (ew_Ereg_nat regs _ 13 13%bv eq_refl) H13).
  assert (E17 : ew E 17 = Z_to_bv 64 (c - 1)) by exact (eq_trans (ew_Ereg_nat regs _ 17 17%bv eq_refl) H17).
  assert (E20 : ew E 20 = Z_to_bv 64 n) by exact (eq_trans (ew_Ereg_nat regs _ 20 20%bv eq_refl) H20).
  assert (E6 : ew E 6 = Z_to_bv 64 (n + 1)) by exact (eq_trans (ew_Ereg_nat regs _ 6 6%bv eq_refl) H6).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by exact (eq_trans (ew_Ereg_nat regs _ 27 27%bv eq_refl) H27).
  assert (E18 : ew E 18 = Z_to_bv 64 c) by exact (eq_trans (ew_Ereg_nat regs _ 18 18%bv eq_refl) H18).
  assert (SHOK : sh_ok rsegs HBx hb_SH E (mrestrict (w_H W) memc))
    by exact (hb_shok regs (w_H W) memc F pp e8 m H27 HF1 HF2 Hrae Hap).
  assert (HAE : env_agree 32 E E) by apply env_agree_refl.
  unfold cfg_at. change (w64 HB_D1) with (Z_to_bv 64 HB_D1).
  (* `beqz s4`: s4 = n >= 1, not taken *)
  srr_branch_tok hb_tbl_ok HS SHOK HBspan.
  { exfalso. rewrite (hb1_beqz E n E20 ltac:(lia)) in Hc. discriminate Hc. }
  aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB1_V.
  + (* the check of s2: the input byte is addressable *)
    apply (obl_of_range rsegs (w_H W) memc _ HBx _ _ c n Hrain).
    * apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
    * rewrite (U_atom _ 18 c E18) by lia. lia.
    * rewrite (U_atom _ 18 c E18) by lia. lia.
  + hb1_awr_kit B9 B32 R sp0 pos Hown HFa.
  + eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | cb_kio | | | exact HG | ].
    * eapply (regs_kept_of_st_ok rsegs _ _ ms regs (hb_extra F pp e8 m) (w_H W) _ HS);
        [env_agree_chain HAE | vm_compute; reflexivity].
    * intros a Ha Hz.
      exact (cb_kept_run (hb1_head_wr R F) _ _ (w_H W) memc memc (ms_mem ms)
        (fun a _ _ => eq_refl) HFr ltac:(hb1_kwr B9 B32) a Ha Hz).
    * unfold hb1_head_R. cbn [fuzz_u8 fst snd]. fold m.
      split.
      { hb1_reg HS (10%bv : bv 5). unfold w64.
        lazymatch goal with |- sv_denot ?Ex ?e = _ =>
          assert (X : forall E0 : env, ew E0 35 = Z_to_bv 64 m -> sv_denot E0 e = sv_denot (cb_envz m) e)
            by (intros E0 H0; cbn [sv_denot ew cb_envz]; rewrite H0; reflexivity);
          rewrite (X Ex ltac:(rewrite ?ew_ewset_other by lia; exact E35));
          exact (hb1_chk256 e (fun z => HB_VOCAB + 8 * (z mod 9)) m ltac:(vm_compute; reflexivity) Hmb) end. }
      split.
      { hb1_reg HS (6%bv : bv 5). cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E6, unsigned_lit_small by lia. unfold w64. f_equal. lia. }
      split; [hb1_reg HS (23%bv : bv 5); cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite B32; reflexivity|].
      split.
      { eapply (cb_val_at _ _ (w_H W) ms 1%nat _ 0x58 8%N _ _ R _);
          [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
          | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E13, Z.add_0_r; apply bv_eq;
            rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_mod by lia;
            reflexivity
          | cbn; lia | lia]. }
      split.
      { eapply (cb_val_at _ _ (w_H W) ms 3%nat _ 0x110 8%N _ _ R _);
          [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
          | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E17, unsigned_lit_small by lia; f_equal;
            cbn [length]; lia
          | cbn; lia | lia]. }
      intros i Hi.
      pose proof (hb_chunk_zero _ _ _ 0x210 104 (hb_region _ _ _ hb_rF HS ltac:(apply (nth_error_In _ 5);
        vm_compute; reflexivity)) ltac:(left; reflexivity) i Hi) as Hz.
      cbn [YP09.r_base base_val hb_rF] in Hz. rewrite ?ew_ewset_other in Hz by lia. rewrite B32 in Hz. exact Hz.
Qed.

(* ======================================== hb1_vcell: 0x82114 .. 0x41c18 ======================================== *)
Definition hb1_rV : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition hb1_vss : sstate := mkSS HB1_V sr_atoms [hb1_rV] None
  (mkFacts [(10%nat, mkAF 0x9c4e0 0x9c520 3); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).

Lemma hb1_vcell : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) i,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 (HB_VOCAB + 8 * i) -> 0 <= i < 9 -> getr regs 27 = w64 SHADOW_OFF ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF HB_VOCAB 72 ->
  val_mem rsegs (mrestrict (w_H W) memc) (HB_VOCAB + 8 * i) 8 (hb_vptr i) ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HB1_V) memc (seg_rom rsegs)) mdc)
  (cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k STRLEN_ENTRY_B regs memc mdc [1; 10; 11; 21; 26]%bv
   (fun _ => False)
   (fun regs2 _ => getr regs2 1 = w64 HB1_SLR /\ getr regs2 10 = w64 (hb_vptr i) /\
      getr regs2 26 = w64 (hb_vptr i) /\ getr regs2 21 = getr regs 6)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i HJ H10 Hi H27 Hra Hval.
pose proof hb_wx as Hwx. pose proof hb_segs_low as Hsegs.
pose proof (hb1_vptr_range i) as Hvp.
set (E := Ereg regs [Z_to_bv 64 (hb_vptr i)]).
assert (B10 : bv_unsigned (ew E 10) = HB_VOCAB + 8 * i)
  by exact (hb_U_reg regs _ 10 10%bv _ eq_refl H10 ltac:(unfold HB_VOCAB; lia)).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by exact (eq_trans (ew_Ereg_nat regs _ 27 27%bv eq_refl) H27).
assert (B27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E10 : ew E 10 = Z_to_bv 64 (HB_VOCAB + 8 * i)) by exact (eq_trans (ew_Ereg_nat regs _ 10 10%bv eq_refl) H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hb_vptr i)) by exact (ew_Ereg_extra regs [Z_to_bv 64 (hb_vptr i)] 0).
assert (B32 : bv_unsigned (ew E 32) = hb_vptr i) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E6 : ew E 6 = getr regs 6) by exact (ew_Ereg_nat regs _ 6 6%bv eq_refl).
assert (HS : st_ok rsegs E hb1_vss (restrict (w_H W) (mkst regs (Z_to_bv 64 HB1_V) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, hb1_rV. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (Ereg regs [Z_to_bv 64 (hb_vptr i)]) with E. rewrite B10.
    split; [unfold HB_VOCAB; lia|]. split; [unfold HB_VOCAB; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ _ 0 8 (SOff 32 0) (hb_vptr i));
      [cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia |].
    rewrite Z.add_0_r. exact Hval.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [hb1_vss ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    change (Ereg regs [Z_to_bv 64 (hb_vptr i)]) with E.
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (hb1_af _ _ _ _ _ _ B10); [unfold HB_VOCAB; lia | | lia].
      change (2 ^ 3) with 8. replace (HB_VOCAB + 8 * i) with ((80028 + i) * 8) by (unfold HB_VOCAB; lia).
      apply Z.mod_mul. lia.
    + apply (hb1_af _ _ SHADOW_OFF _ _ _ B27); [lia | reflexivity | lia]. }
assert (SHOK : sh_ok rsegs HBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 E E) by apply env_agree_refl.
aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan STRLEN_ENTRY_B.
- (* the check of the cell: the table's 72 bytes are addressable *)
  apply (obl_of_range rsegs (w_H W) memc _ HBx _ _ HB_VOCAB 72 Hra).
  + apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
  + rewrite (U_atom _ 10 (HB_VOCAB + 8 * i) E10) by (unfold HB_VOCAB; lia). lia.
  + rewrite (U_atom _ 10 (HB_VOCAB + 8 * i) E10) by (unfold HB_VOCAB; lia). lia.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | cb_kio | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [Z_to_bv 64 (hb_vptr i)] (w_H W) _ HS);
      [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr ltac:(hb1_kwr B10 B32) a Ha Hz).
  + cbv beta. split; [|split; [|split]].
    * hb1_reg HS (1%bv : bv 5). reflexivity.
    * hb1_reg HS (10%bv : bv 5). cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite B32, Z.add_0_r. reflexivity.
    * hb1_reg HS (26%bv : bv 5). cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite B32, Z.add_0_r. reflexivity.
    * hb1_reg HS (21%bv : bv 5). cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
      rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ======================================== hb1_set: 0x82138 .. 0x51d8c ======================================== *)
Definition hb1_mss : sstate := mkSS HB1_SLR sr_atoms [] None (mkFacts [(10%nat, mkAF 12 18 0)] [] []).

Lemma hb1_set : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) n,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 n -> 12 <= n <= 18 ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HB1_SLR) memc (seg_rom rsegs)) mdc)
  (cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HB_MEMCPY regs memc mdc [1; 10; 11; 12; 18; 20]%bv
   (fun _ => False)
   (fun regs2 _ => getr regs2 1 = w64 HB1_MCR /\ getr regs2 10 = getr regs 23 /\ getr regs2 11 = getr regs 26 /\
     getr regs2 12 = w64 n /\ getr regs2 18 = w64 n /\ getr regs2 20 = w64 n)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n HJ H10 Hn.
pose proof hb_wx as Hwx. pose proof hb_segs_low as Hsegs.
set (E := Ereg regs []).
assert (B10 : bv_unsigned (ew E 10) = n) by exact (hb_U_reg regs _ 10 10%bv n eq_refl H10 ltac:(lia)).
assert (HS : st_ok rsegs E hb1_mss (restrict (w_H W) (mkst regs (Z_to_bv 64 HB1_SLR) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - unfold facts_ok. cbn [hb1_mss ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    change (Ereg regs []) with E.
    split; [|split; exact I]. split; [|exact I].
    apply (hb1_af _ _ n _ _ _ B10); [lia | apply Z.mod_1_r | lia]. }
assert (SHOK : sh_ok rsegs HBx [] E (mrestrict (w_H W) memc)) by constructor.
aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_MEMCPY.
- apply awr_ok_nil.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | cb_kio | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr ltac:(hb1_kwr B10 B10) a Ha Hz).
  + cbv beta.
    split; [hb1_reg HS (1%bv : bv 5); reflexivity|].
    split; [hb1_reg HS (10%bv : bv 5); exact (hb1_atom regs _ 23 23%bv eq_refl)|].
    split; [hb1_reg HS (11%bv : bv 5); exact (hb1_atom regs _ 26 26%bv eq_refl)|].
    split; [hb1_reg HS (12%bv : bv 5); exact (eq_trans (hb1_atom regs _ 10 10%bv eq_refl) H10)|].
    split; [hb1_reg HS (18%bv : bv 5); exact (eq_trans (hb1_atom regs _ 10 10%bv eq_refl) H10)|].
    hb1_reg HS (20%bv : bv 5). exact (eq_trans (hb1_atom regs _ 10 10%bv eq_refl) H10).
Qed.
End d.
End b.

Print Assumptions hb1_head.
Print Assumptions hb1_vcell.
Print Assumptions hb1_set.
