(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_stem.v, with its module paths and module names changed; 203 of its 230 lines of code are new or changed and 245 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), the segment S_MF_HDRB (HFIND 0x865c0 ->
   TAIL 0x86820): its first piece, the m_find call from the cut HFIND to the cut MFB_RFIND 0x865cc (mf_hdrb_2.v).
   A walk lane of the image-B m_file-family owner's G2B (a piece agent). proves no function (kind: segment lemma of m_file's
   image-B walk, S_MF_HDRB's m_find call).

   THE CODE (the neutral listing of m_file in image B lines 290-292):
     0x865c0 `mv a0,s9`  (a0 = c; mf_regs_at's s9)
     0x865c4 `mv a2,s10` (a2 = |nm|; a1 = p + o, the name, since 0x865a8)
     0x865c8 `jal m_find` (0x874f4 = BASE + AF_m_find; listing offset AF_m_file + 0x488, slot PCall SS_m_find)
   No store, no instrumented check, no UBSan trap branch in these three instructions.

   THE PROOF (B's m_file_iq.v mf_ieq_call and mf_kknockp_2.v kk_s_kknock at this site): m_file_sd.v's mf_seed at
   HFIND, the frame-cell region made read-only (nothing here stores), one token run through the `jal` (the run ends at
   m_find's entry with ra = BASE + MFB_RFIND); every window of the run's state is empty, so no byte changed and the
   cut facts hold at the run's memory (m_file_iq.v's iq_keep). The callee is M_FIND (m_find_c.v's contract at
   BASE + AF_m_find, STK_m_find = 64 + 2 ESTACK = 8,256) taken through PaCall.cl_callS: afn_pre from the walk's journal
   with m_file_k.v's frame chain mf_chain at sp = s1, s0 = sp0; arodata_okP by mf_rod_now (RELRO); m_find_pre with
   l = zb nm by mf_hdrb_3.v's hb3_find_pre (zs (zb nm) = nm). The window [s1 - 8,256, s1) is inside m_file's own
   (s1 >= sp0 - 336 and STK_m_file = 8,592 = 336 + 8,256: an exact fit). m_find's post is apost_base, so the walk goes
   on at the SAME FP state; m_file_k.v's mf_keep_call0 (sa_kept with E empty, STK_m_find <= STK_fuzz_catalogue_row)
   carries mf_core, mf_cells, mf_regs_at, mf_np and mf_loop; 192(s1) (the name) is above s1, outside the window
   (sa_kept); a0 = m_find_ptr c mcc nm; s4, s10, s11 are callee-saved (aregs_preserved). Then MFB_RFIND_stmt at
   ra = BASE + MFB_RFIND.

   Section hypotheses (the HDRB piece plan's texts): VOBJS (the seed), SIGP (the call target), RELRO (mf_rod_now), M_FIND. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegGlob SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_file_m m_file_sd m_file_k m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_hdrb_2 mf_hdrb_3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom (mf_kknockp_1.v's kk_st_reg) *)
Lemma hb10_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_FIND : forall fx0 : YK11.FPState, m_find_contract (fx := fx0) SEGS B (BASE + AF_m_find)
  SegInstB.STK_m_find SegInstB.RLO_A SegInstB.RHI_A.
Let RUN := paj_run B LAWS.

(* the callee-saved registers of a state whose symbolic registers are the seed's on CALLEE_SAVED (mf_kknockp_1.v's
   kk_pres) *)
Lemma hb10_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
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

(* HFIND 0x865c0 -> MFB_RFIND 0x865cc: a0 = c, a2 = |nm|, m_find(c, p + o, |nm|), at the same FP state *)
Lemma hb10_hfind_at : forall n, MFB_RFIND_stmt B n -> MF_HFIND_stmt B n.
Proof.
intros n RF. unfold MF_HFIND_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest o nm CX LS FRM CORE CELLS RA Hn Hne LOOP Hnm Hon Hfs
  HFIN R11 S192 R26 R20 R27 NP.
unfold mf_at.
assert (HNM : hb_nm rest o nm) by (split; [exact Hnm | split; [exact Hon | exact Hfs]]).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos cur np []).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur np [] MF_HFIND
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
(* the frame-cell region read-only: this piece stores nothing *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS1 end.
clear HS0 HR1.
lazymatch type of HS1 with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS1 end.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
pose proof CORE as (HJ & _).
(* the run 0x865c0 .. 0x865c8: a0 = s9, a2 = s10, `jal m_find` *)
paj_run_tok RUN HS1 HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* every window of the run's state is empty: no byte changed *)
assert (HMEQ : forall x, ms_mem ms x = memc x).
{ intros x. apply HF. intros (rr & Hin & Hw). cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia |]). destruct Hin. }
assert (EQV : forall a, rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
(* the registers at m_find's entry: the callee-saved ones are the cut's, a0 = c, a1 = p + o, a2 = |nm|,
   ra = BASE + MFB_RFIND *)
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ eapply (hb10_pres E _ regs1 v lyc pos cur np [] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS1).
  - vm_compute. reflexivity. }
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10 : getr (ms_regs ms) 10 = w64 (mv_c v)).
{ rewrite (hb10_st_reg SEGS _ _ _ _ 10%bv 25%nat HS1) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos cur np [] 25 (Z_to_bv 5 25) eq_refl). exact R25. }
assert (Q11 : getr (ms_regs ms) 11 = w64 (p + Z.of_nat o)).
{ rewrite (hb10_st_reg SEGS _ _ _ _ 11%bv 11%nat HS1) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos cur np [] 11 (Z_to_bv 5 11) eq_refl). exact R11. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (Z.of_nat (length nm))).
{ rewrite (hb10_st_reg SEGS _ _ _ _ 12%bv 26%nat HS1) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos cur np [] 26 (Z_to_bv 5 26) eq_refl). exact R26. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + MFB_RFIND)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS1).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E MFB_RFIND HEI). }
(* the jal's target *)
rewrite (SIGP SS_m_find ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_m_find) with AF_m_find by (vm_compute; reflexivity).
(* the cut's facts at the jal's memory (the run changed no byte) *)
destruct (mf_s1_facts B v CX) as (Hs1 & _ & Hceil1).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (HSTK1 : SegInstB.STK_m_find = 8256) by (vm_compute; reflexivity).
assert (HSTKR : SegInstB.STK_fuzz_catalogue_row = 8256) by (vm_compute; reflexivity).
assert (Hlo : alloc_ceiling + 16 <= mf_s1 (mv_sp v)) by (destruct Hs1 as [Es | Es]; rewrite Es; lia).
destruct (iq_keep B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur line p rest np Sc Wc (ms_mem ms) mdq
  (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) CX LS CORE CELLS LOOP NP HJ (Permutation_refl _) (fun a _ _ => EQV a) Hlo
  (Z.le_refl _)) as (CORE' & CELLS' & LOOP' & NP').
assert (S192' : mf_slot v (ms_mem ms) Wc 192 (p + Z.of_nat o)).
{ unfold mf_slot in *. apply (iq_val_keep Wc Wc memc (ms_mem ms)); [intros x _; exact (EQV x) | exact S192]. }
pose proof (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc) as RA'.
(* m_find's premises at the jal's state *)
destruct (hb3_find_pre B v lyc Sc Wc (ms_mem ms) mdq pos mcc cur line p rest o nm CX CORE' LOOP' HNM)
  as (PRE & HZ & Hname & Hlen64).
pose proof (mf_rod_now B RELRO v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_OFF mcc CX CORE') as HROD.
pose proof (mf_nev B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_OFF mcc CX CORE') as HEV.
destruct (mf_chain B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_OFF mcc CX CORE') as (ch1 & HCH).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo, Hshi.
destruct (iq_s1 (mv_sp v) Hal16) as (_ & Ho16).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
assert (HRF : MFB_RFIND = 0x180c) by (vm_compute; reflexivity).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
set (sp0 := mv_sp v) in *.
assert (Hsp : spZ (ms_regs ms) = sp0 + (mf_s1 sp0 - sp0)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the call: m_find_contract through cl_callS, at the same FP state (apost_base) *)
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_m_find)) SegInstB.STK_m_file sp0
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
    lyc Sc mdq 0 SegInstB.STK_m_find [] EV_m_find (mf_s1 sp0 - sp0) (Z_to_bv 64 (BASE + MFB_RFIND)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (m_find_ptr (mv_c v) mcc (seg_spec.zs (seg_spec.zb nm))) /\
       sa_kept SEGS Wc (ms_mem ms) W2 mem2 (ms_regs ms) SegInstB.STK_m_find (fun _ => False) /\
       sa_noalloc B lyc Sc ly2 S2)
    HJ Hsp Ho16).
  - destruct Hs1 as [E1 | E1]; rewrite E1; lia.
  - rewrite HSTK1; lia.
  - rewrite HSTK, HSTK1. destruct Hs1 as [E1 | E1]; rewrite E1; lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - rewrite HRF. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (sp0 + (mf_s1 sp0 - sp0)) with (mf_s1 sp0) by lia.
    unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    + apply (M_FIND fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq ch1 (mv_c v) (p + Z.of_nat o) (Z.of_nat (length nm))
        mcc (seg_spec.zb nm) HPRE1 HROD Q10 Hc64 Q11 Hname Q12 Hlen64 PRE).
      unfold EV_m_find. exact HEV.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, Q1; reflexivity|]. split; [exact HJc|].
      split; [exact HPr | exact HK].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (A0 & HKP & HNA)).
(* every cut fact at m_find's return *)
destruct (mf_keep_call0 B v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_OFF mcc cur ly3 S3 W3 regs3 mem3 md3
  (0 + EV_m_find) SegInstB.STK_m_find CX CORE' CELLS' RA' HJo ltac:(unfold EV_m_find; lia) HP3 HNA
  ltac:(rewrite HSTK1, HSTKR; lia) HKP)
  as (Ely & LSK & CORE3 & CELLS3 & RA3 & NPK & LOOPK).
subst ly3.
pose proof (aregs_preserved_trans _ _ _ HPc HP3) as HP13.
rewrite HZ in A0.
(* the name in 192(s1): above s1, outside m_find's window *)
assert (S192'' : mf_slot v mem3 W3 192 (p + Z.of_nat o)).
{ unfold mf_slot in *. apply (iq_val_keep Wc W3 (ms_mem ms) mem3); [|exact S192'].
  intros x Hx. change (mv_sp v) with sp0 in Hx.
  apply (HKP x); [lia | rewrite Hsp; lia | intros []]. }
refine (RF v lyc S3 W3 regs3 mem3 md3 pos mcc cur line p rest o nm CX (LSK LS) FRM CORE3 CELLS3 RA3 Hn Hne
  (LOOPK _ _ _ _ _ LOOP') HNM HFIN A0 S192'' _ _ _ (NPK _ NP')).
- transitivity (getr regs1 26); [exact (HP13 26 ltac:(unfold acallee_saved; lia)) | exact R26].
- transitivity (getr regs1 20); [exact (HP13 20 ltac:(unfold acallee_saved; lia)) | exact R20].
- transitivity (getr regs1 27); [exact (HP13 27 ltac:(unfold acallee_saved; lia)) | exact R27].
Qed.
End e.
End f.
End d.

(* at every FP state (mf_hdrb_2.v's MFB_RFIND_F, m_file_m.v's MF_HFIND_F): m_find keeps the FP state *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_FIND : forall fx0 : YK11.FPState, m_find_contract (fx := fx0) SEGS B (BASE + AF_m_find)
  SegInstB.STK_m_find SegInstB.RLO_A SegInstB.RHI_A.
Lemma hb10_hfind : forall n, MFB_RFIND_F B n -> MF_HFIND_F B n.
Proof. intros n RF fx0. exact (hb10_hfind_at (fx := fx0) B VOBJS SIGP RELRO M_FIND n (RF fx0)). Qed.
(* inside the Sections: the piece's hypotheses as its assumptions *)
About hb10_hfind. Print Assumptions hb10_hfind.
End i.
End h.
End g.
About hb10_hfind. Print Assumptions hb10_hfind.
