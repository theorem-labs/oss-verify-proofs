(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   memchr call 0x86ef8 to the return of sup_reply_code 0x86f18, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's call steps: cl_callS, the state
   after the return) at c8557374ad2e.

   The pieces: 0x86ef8 jal memchr (the reply holds no NUL, so the wrapper returns 0: the not-found contract
   through PaArt.v's aj_art_at); 0x86efc bnez a0 (not taken); 0x86f00 mv a0,s3; 0x86f04 jal check_reply_answer
   (cl_callS); 0x86f08 the inline check of &g_rec.reply (a shadow entry of g_rec makes it a literal 0); 0x86f10
   ld a0,928(s9); 0x86f14 jal sup_reply_code (cl_callS), whose return point 0x86f18 is CR_CODE_stmt's.
   After each call the mid-walk invariant cr_mid and the registers cr_regs_at are rebuilt from the callee's journal
   (the frame (1, pos) is among the caller's frames, the saved registers lie above the callee's stack pointer, g_rec
   is a program static), and the walk is seeded again with check_reply_sd.v's cr_seed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s2.v, with its module paths and module names changed; 330 of its 373 lines of code are new or changed and 542 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KIGNP: the call of ieq(k, kl, "ignore") from the KIGN cut
   0x8693c to its return 0x86950 (KI_R1, lib/A/Prog/m_file_s_kign_m.v). The KIGNP segment lane of the G2 walk owner's G2.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's first piece).

   The code (listing m_file.fuzz_segconf.asan.s): 0x8693c auipc a0; 0x86940 addi a2,a0 (listing object 20, the
   literal "ignore" 0x21240); 0x86944 mv a0,s11 (k); 0x86948 mv a1,s6 (kl); 0x8694c jal ieq. No memory access, no
   inline check: the seed's regions are dropped for the run (st_ok_pi_submem), so the memory at the jal is the cut's.
   The call is m_file_iq.v's mf_ieq_call; at the return every cut fact is kept and a0 = b2z (ieq k S_ignore). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k ieq_c m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_kign_t m_file_s_kign_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom *)
Lemma ki_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros segs E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the shared Section hypotheses (the m_file cut-statement lane's list (a)) this piece uses *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the text left's sub-range [o, o + n) inside the line: its bytes as list byte, addressable, in the text block *)
Lemma ki_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc cur line p rest ->
  (o + n <= length rest)%nat ->
  sa_bytes (rdW Wc memc) (p + Z.of_nat o) (seg_spec.zb (firstn n (skipn o rest))) /\
  seg_spec.zs (seg_spec.zb (firstn n (skipn o rest))) = firstn n (skipn o rest) /\
  Z.of_nat (length (seg_spec.zb (firstn n (skipn o rest)))) = Z.of_nat n /\
  sa_addr (rdW Wc memc) (p + Z.of_nat o) (Z.of_nat n) /\ sa_heap B lyc Sc (p + Z.of_nat o) (Z.of_nat n) /\
  p + Z.of_nat o <> 0.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n CX CORE LOOP Hon.
pose proof LOOP as (L1 & L2 & L3 & ((LZ & LN) & LT) & LADDR & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
assert (HZ : sa_zs (rdW Wc memc) (p + Z.of_nat o) (firstn n (skipn o rest))).
{ intros i Hi. rewrite length_firstn, length_skipn in Hi.
  replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia.
  rewrite (LZ (o + i)%nat) by (rewrite length_app; cbn [length]; lia).
  f_equal. rewrite nth_firstn. destruct (Nat.ltb_spec i n) as [Hlt|Hge]; [|lia].
  rewrite nth_skipn. apply app_nth1. lia. }
destruct (ki_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HZB & _).
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bt & mt & Hin & Hb & He).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hin) as (_ & Hbt4096 & Hbtceil & _ & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
assert (Hlen : length (seg_spec.zb (firstn n (skipn o rest))) = n).
{ unfold seg_spec.zb. rewrite length_map, length_firstn, length_skipn. lia. }
pose proof LADDR as (A0 & A1 & AM & ARA & AHV).
assert (Hpe : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hpt : mv_t v <= p) by (rewrite L3; lia).
split; [exact HB|]. split; [exact HZB|]. split; [rewrite Hlen; reflexivity|]. split.
- split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR Hin
      ltac:(lia) ltac:(lia)).
  + intros Hn. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR
      Hin ltac:(lia) ltac:(lia) Hn).
- split; [exists bt, mt; split; [exact Hin | lia] | lia].
Qed.

(* the registers mf_regs_at names are callee-saved (fuzz_command check_reply_s2.v cr2_regs_keep) *)
Lemma ki_regs_keep : forall v lyc pos regs1 regs2,
  mf_regs_at B v lyc pos regs1 -> aregs_preserved regs1 regs2 -> mf_regs_at B v lyc pos regs2.
Proof.
intros v lyc pos regs1 regs2 (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26) HP.
assert (G : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HP.
split; [rewrite <- R2; exact (G 2 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R3; exact (G 3 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R4; exact (G 4 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R8; exact (G 8 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R9; exact (G 9 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R18; exact (G 18 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R19; exact (G 19 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R25; exact (G 25 ltac:(unfold acallee_saved; lia))|].
rewrite <- R26; exact (G 26 ltac:(unfold acallee_saved; lia)).
Qed.

(* the callee-saved registers of a state whose symbolic registers are the seed's on CALLEE_SAVED *)
Lemma ki_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
  E = mfE regs1 v lyc pos cur np xs -> mf_regs_base v regs1 ->
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get R r) (sr_get sr_mf r)) CALLEE_SAVED = true ->
  aregs_preserved regs1 rr.
Proof.
intros E R regs1 v lyc pos cur np xs rr HE RB HR HC r Hr.
pose proof (mf_regs_ok v regs1 lyc pos cur np xs RB) as HO. rewrite <- HE in HO.
rewrite HR, HO. f_equal. apply sv_eqb_eq.
assert (Hin : In (Z_to_bv 5 r) CALLEE_SAVED).
{ unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    unfold CALLEE_SAVED; cbn [In]; first [ tauto | intuition (apply bv_eq; reflexivity) ]. }
exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

(* KIGN 0x8693c: ieq(k, kl, "ignore"), then KI_R1 *)
Lemma ki_s_kign : forall n, KI_R1_stmt B n -> MF_KIGN_stmt B n.
Proof.
intros n R1. unfold MF_KIGN_stmt, MF_KAT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX LS FRM CORE CELLS RA Hn Hr LOOP KV MISS FIN R27 R22 R21 R20 R23 R24 NP.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof LOOP as (L1 & L2 & L3 & _).
pose proof (ki_line_le rest) as Hml.
(* the seed, its regions dropped: the run reads and writes no memory *)
set (np := mf_next p rest).
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & (bs & _ & (_ & HL32 & _)) & (CA0 & CA1 & _) & _).
unfold mf_cur_ok in LCUR.
assert (Hcur : 0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64)
  by (unfold mf_cur_ptr, seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *; lia).
assert (Hnp : 0 <= np < 2 ^ 64) by (unfold np, mf_next; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] MF_KIGN true true [] false
  false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) np []) in *.
assert (HS : st_ok_pi SEGS VAL E (mkSS MF_KIGN sr_mf [] None mf_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + MF_KIGN)) memc (seg_rom SEGS))))
  by (exact (st_ok_pi_submem E (ss_mf MF_KIGN true true [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _)
      eq_refl)).
clear HS0.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
pose proof CORE as (HJ & _).
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
(* the registers at the jal: the callee-saved ones are the cut's, a0 = k, a1 = kl, a2 = "ignore", ra = KI_R1 *)
assert (QS : forall (r : bv 5) (k0 : nat), Z.of_nat k0 = bv_unsigned r ->
  getr (ms_regs ms) r = ew E k0 -> getr (ms_regs ms) r = getr regs1 r)
  by (intros r k0 Hk Hrr; rewrite Hrr; unfold E; apply mfE_reg; exact Hk).
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ intros r Hcs. unfold acallee_saved in Hcs.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct RB as (B2 & B8 & B9 & B18).
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    try first
      [ lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = _ =>
          apply (QS (Z_to_bv 5 r) (Z.to_nat r)); [vm_compute; reflexivity |];
          apply (ki_st_reg SEGS _ _ _ _ _ (Z.to_nat r) HS); vm_compute; reflexivity end
      | lazymatch goal with |- getr _ (Z_to_bv 5 9) = _ =>
          transitivity (ew E 2%nat); [apply (ki_st_reg SEGS _ _ _ _ _ 2%nat HS); vm_compute; reflexivity|];
          unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 (Z_to_bv 5 2) eq_refl);
          exact (eq_trans B2 (eq_sym B9)) end
      | lazymatch goal with |- getr _ (Z_to_bv 5 18) = _ =>
          transitivity (ew E 32%nat); [apply (ki_st_reg SEGS _ _ _ _ _ 32%nat HS); vm_compute; reflexivity|];
          pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32;
          cbn [Nat.add nth mf_extra map app] in E32; unfold E; rewrite E32; exact (eq_sym B18) end ]. }
pose proof RA as (R2 & R3 & R4 & R8 & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ok)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 27%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl). exact R27. }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat kl)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 22%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 22 (Z_to_bv 5 22) eq_refl). exact R22. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstA.seg_litA_fz S_ignore)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 20) HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) np [] (A_OBJ 20) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (mf_lit_obj VOBJS S_ignore 20 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
  reflexivity. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R1)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E KI_R1 HEI). }
(* the jal's target *)
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
(* the cut's facts at the jal's memory (the run changed no byte) *)
pose proof CX as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & _).
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo.
destruct (iq_s1 (mv_sp v) Hal16) as (Hs1 & _).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (Hlo : alloc_ceiling + 16 <= mf_s1 (mv_sp v)) by (destruct Hs1 as [Es | Es]; rewrite Es; lia).
destruct (iq_keep B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) line p rest np Sc Wc (ms_mem ms) mdq
  (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) CX LS CORE CELLS LOOP NP HJ (Permutation_refl _) (fun a _ _ => EQV a) Hlo
  (Z.le_refl _)) as (CORE' & CELLS' & LOOP' & NP').
destruct (ki_slice_facts v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ok kl CX CORE' LOOP'
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite KV3 in SB, SZ, SL.
refine (mf_ieq_call B RELRO IEQ v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi)
  line p rest np KI_R1 (p + Z.of_nat ok) (Z.of_nat kl) (seg_spec.zb k) S_ignore CX LS CORE' CELLS' LOOP' NP'
  Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
- unfold KI_R1, AF_m_file; lia.
- unfold KI_R1, AF_m_file; reflexivity.
- unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
- intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
  assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
  rewrite SZ in A02.
  apply (R1 v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv).
  + unfold ki_kbase.
    refine (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj (ki_regs_keep v lyc pos regs1 regs2 RA HP12)
      (conj Hn (conj Hr (conj LOOP2 (conj KV _)))))))))).
    split; [transitivity (getr regs1 27); [exact (HP12 27 ltac:(unfold acallee_saved; lia)) | exact R27]|].
    split; [transitivity (getr regs1 22); [exact (HP12 22 ltac:(unfold acallee_saved; lia)) | exact R22]|].
    split; [transitivity (getr regs1 21); [exact (HP12 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
    split; [transitivity (getr regs1 20); [exact (HP12 20 ltac:(unfold acallee_saved; lia)) | exact R20]|].
    split; [transitivity (getr regs1 23); [exact (HP12 23 ltac:(unfold acallee_saved; lia)) | exact R23]|].
    split; [transitivity (getr regs1 24); [exact (HP12 24 ltac:(unfold acallee_saved; lia)) | exact R24]|].
    exact NP2.
  + exact MISS.
  + exact FIN.
  + exact A02.
Qed.


(* the seed at a K cut's pc with its regions dropped (a run that touches no memory) *)
Lemma ki_seed0 : forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  mf_regs_at B v lyc pos regs1 -> mf_loop v Wc memc mcc (Some gi) line p rest -> mf_np v memc Wc (mf_next p rest) ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) (mkSS pc sr_mf [] None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest pc CX CORE CELLS RA LOOP NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & (bs & _ & (_ & HL32 & _)) & (CA0 & CA1 & _) & _).
unfold mf_cur_ok in LCUR.
assert (Hcur : 0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64)
  by (unfold mf_cur_ptr, seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *; lia).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] pc true true []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
exact (st_ok_pi_submem _ (ss_mf pc true true [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _) eq_refl).
Qed.

(* KI_R1 0x86950: `beqz a0` on ieq's answer; 0 goes to KKNOCK, else ieq(v, vl, "yes") and KI_R2 *)
Lemma ki_s_r1 : forall n, MF_KKNOCK_stmt B n -> KI_R2_stmt B n -> KI_R1_stmt B n.
Proof.
intros n KK R2s v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KB MISS FIN A0.
pose proof KB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & KV & R27 & R22 & R21 & R20 & R23 & R24 & NP).
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (ki_line_le rest) as Hml.
pose proof (ki_seed0 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest KI_R1 CX CORE CELLS RA LOOP NP) as HS1.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
pose proof MISS as MISS0. apply Forall_cons_iff in MISS0 as [MR MISS1]. apply Forall_cons_iff in MISS1 as [MM _].
destruct (ieq k S_ignore) eqn:EIG; cbn [seg_spec.b2z] in A0.
- (* "ignore": a0 = 1, the beqz falls through to ieq(v, vl, "yes") *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (HPc : aregs_preserved regs1 (ms_regs ms)).
  { eapply (ki_pres E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) eq_refl RB).
    - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  pose proof RA as (R2 & R3 & R4 & R8 & _).
  assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
  assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
  assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
  assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
  assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 21%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 21 (Z_to_bv 5 21) eq_refl). exact R21. }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 20%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 20 (Z_to_bv 5 20) eq_refl). exact R20. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstA.seg_litA_fz S_yes)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 21) HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) np [] (A_OBJ 21) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    rewrite (mf_lit_obj VOBJS S_yes 21 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
    reflexivity. }
  assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R2)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
    lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
      transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
    exact (codeptr_val E KI_R2 HEI). }
  rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  pose proof (NPk np NP) as NP'. pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
  destruct (ki_slice_facts v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ov vl CX CORE' LOOP'
    ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
  rewrite KV4 in SB, SZ, SL.
  refine (mf_ieq_call B RELRO IEQ v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi)
    line p rest np KI_R2 (p + Z.of_nat ov) (Z.of_nat vl) (seg_spec.zb vv) S_yes CX LS CORE' CELLS' LOOP' NP'
    Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
  + unfold KI_R2, AF_m_file; lia.
  + unfold KI_R2, AF_m_file; reflexivity.
  + unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
  + intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
    assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
    rewrite SZ in A02.
    apply (R2s v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv).
    * unfold ki_vbase.
      refine (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj (mf_regs_keep B v lyc pos regs1 regs2 RA HP12)
        (conj Hn (conj Hr (conj LOOP2 (conj KV2 (conj KV4 (conj NP2 _)))))))))))).
      split; [transitivity (getr regs1 21); [exact (HP12 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
      split; [transitivity (getr regs1 20); [exact (HP12 20 ltac:(unfold acallee_saved; lia)) | exact R20]|].
      transitivity (getr regs1 24); [exact (HP12 24 ltac:(unfold acallee_saved; lia)) | exact R24].
    * rewrite <- (ki_val_disp mcc gi k vv (line + 1) MR MM EIG). exact FIN.
    * exact A02.
- (* "ignore" missed: a0 = 0, the beqz goes to KKNOCK with the cut's state *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KKNOCK.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (HPc : aregs_preserved regs1 (ms_regs ms)).
  { eapply (ki_pres E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) eq_refl RB).
    - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with MF_KKNOCK by (unfold MF_KKNOCK, AF_m_file; reflexivity) end.
  apply (KK v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ok kl ov vl k vv CX LS FRM CORE' CELLS'
    (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc) Hn Hr (LPk mcc (Some gi) line p rest LOOP) KV).
  + constructor; [exact MR|]. constructor; [exact MM|]. constructor; [exact EIG | constructor].
  + exact FIN.
  + transitivity (getr regs1 27); [exact (HPc 27 ltac:(unfold acallee_saved; lia)) | exact R27].
  + transitivity (getr regs1 22); [exact (HPc 22 ltac:(unfold acallee_saved; lia)) | exact R22].
  + transitivity (getr regs1 21); [exact (HPc 21 ltac:(unfold acallee_saved; lia)) | exact R21].
  + transitivity (getr regs1 20); [exact (HPc 20 ltac:(unfold acallee_saved; lia)) | exact R20].
  + transitivity (getr regs1 23); [exact (HPc 23 ltac:(unfold acallee_saved; lia)) | exact R23].
  + transitivity (getr regs1 24); [exact (HPc 24 ltac:(unfold acallee_saved; lia)) | exact R24].
  + exact (NPk _ NP).
Qed.

End e.
End f.
End d.
