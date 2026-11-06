(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 126 of its 167 lines of code are new or changed and 412 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): segment S_MF_KKNOCKP, part 2: the call of
   ieq(k, kl, "knock") from the KKNOCK cut 0x86a7c to its return KK_R1 0x86a90 (lib/B/Prog/mf_kknockp_1.v). A walk lane of the image-B m_file-family owner's G2B. proves no function (kind: segment lemma of m_file's walk).

   THE CODE: 0x86a7c `ld a0,208(s1)` (k, the cut's 208(s1) = p + ok); 0x86a80 auipc a1; 0x86a84 addi a2,a1 (listing
   object 25, the literal "knock" 0x212e0); 0x86a88 `mv a1,s5` (kl); 0x86a8c `jal ieq`. No store, no instrumented
   check, no UBSan trap. THE PROOF (image A's m_file_s_kign_1.v ki_s_kign, a working branch, at image
   B's code): m_file_sd.v's mf_seed at KKNOCK with 208(s1) as the caller's chunk atom 52 = p + ok, the frame-cell
   region made read-only (nothing here stores), one token run to the jal; the run changed no byte (every window
   empty), so the cut facts hold at the jal's memory (m_file_iq.v's iq_keep); the call is m_file_iq.v's mf_ieq_call
   at ret = KK_R1, and its continuation is KK_R1_stmt with b = ieq k "knock" (mk_disp's knock branch, kk_disp_miss).
   Section hypotheses: VOBJS, SIGP (the listing), RELRO (m_file_k.v's mf_rod_now), IEQ (ieq_contract). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c ieq_c m_file_m m_file_mdl m_file_sd m_file_k m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kknockp_1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
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
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Let RUN := paj_run B LAWS.

(* KKNOCK 0x86a7c: ieq(k, kl, "knock"), then KK_R1 *)
Lemma kk_s_kknock : forall n, KK_R1_stmt B n -> MF_KKNOCK_stmt B n.
Proof.
intros n R1. unfold MF_KKNOCK_stmt, MF_KAT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX LS FRM CORE CELLS RA Hn Hne LOOP KV MISS FIN S208 KA0 R21 S192 R26 R27 NP.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof LOOP as (L1 & L2 & L3 & _ & (LA0 & LA1 & _) & LCUR & _).
pose proof (kk_line_le rest) as Hml.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
assert (Hk64 : 0 <= p + Z.of_nat ok < 2 ^ 64) by lia.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ok]).
assert (E52 : ew E 52 = Z_to_bv 64 (p + Z.of_nat ok))
  by exact (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ok] 0 ltac:(unfold A_TEXT; lia)).
assert (SLX : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v)))
  [YP09.mkChunk 208 (CVal 8 (SOff 52 0))]).
{ constructor; [|constructor].
  apply (mf_chunk_atom E _ (mf_s1 (mv_sp v)) 208 52 0 (p + Z.of_nat ok) E52); [lia | lia |].
  rewrite Z.add_0_r. exact S208. }
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [p + Z.of_nat ok] MF_KKNOCK
  true true [YP09.mkChunk 208 (CVal 8 (SOff 52 0))] false false [] false CX CORE RB (fun _ => CELLS) Hcur
  (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) SLX (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
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
(* the registers at the jal: the callee-saved ones are the cut's, a0 = k, a1 = kl, a2 = "knock", ra = KK_R1 *)
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ eapply (kk_pres E _ regs1 v lyc pos (Some gi) np [p + Z.of_nat ok] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS1).
  - vm_compute. reflexivity. }
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ok)).
{ rewrite (kk_st_reg SEGS _ _ _ _ 10%bv 52%nat HS1) by (vm_compute; reflexivity). exact E52. }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat kl)).
{ rewrite (kk_st_reg SEGS _ _ _ _ 11%bv 21%nat HS1) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [p + Z.of_nat ok] 21 (Z_to_bv 5 21) eq_refl). exact R21. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_knock)).
{ rewrite (kk_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 25) HS1) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) np [p + Z.of_nat ok] (A_OBJ 25) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (mf_lit_obj VOBJS S_knock 25 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
  reflexivity. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KK_R1)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS1).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E KK_R1 HEI). }
(* the jal's target *)
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
(* the cut's facts at the jal's memory (the run changed no byte) *)
destruct (mf_s1_facts B v CX) as (Hs1 & _ & Hceil1).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (Hlo : alloc_ceiling + 16 <= mf_s1 (mv_sp v)) by (destruct Hs1 as [Es | Es]; rewrite Es; lia).
destruct (iq_keep B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) line p rest np Sc Wc (ms_mem ms) mdq
  (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) CX LS CORE CELLS LOOP NP HJ (Permutation_refl _) (fun a _ _ => EQV a) Hlo
  (Z.le_refl _)) as (CORE' & CELLS' & LOOP' & NP').
destruct (kk_slice_facts B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ok kl CX CORE' LOOP'
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite KV3 in SB, SZ, SL.
refine (mf_ieq_call B IEQ (mf_chain B) (mf_rod_now B RELRO) (mf_lit_now B) v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq
  pos MF_LOW_ON mcc (Some gi) line p rest np KK_R1 (p + Z.of_nat ok) (Z.of_nat kl) (seg_spec.zb k) S_knock
  CX LS CORE' CELLS' LOOP' NP' Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
- unfold KK_R1, AF_m_file; lia.
- unfold KK_R1, AF_m_file; reflexivity.
- unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
- intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
  assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
  rewrite SZ in A02.
  rewrite (kk_disp_miss mcc gi k vv (line + 1) MISS) in FIN.
  apply (R1 v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest (ieq k S_knock) CX LS2 FRM CORE2 CELLS2
    (mf_regs_keep B v lyc pos regs1 regs2 RA HP12) Hn Hne LOOP2 FIN).
  + transitivity (getr regs1 27); [exact (HP12 27 ltac:(unfold acallee_saved; lia)) | exact R27].
  + exact NP2.
  + exact A02.
Qed.

End e.
End f.
End d.

(* at every FP state: ieq keeps the FP state, so KK_R1 at each one gives KKNOCK at it *)
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
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Lemma kk_s_kknock_F : forall n, (forall fx0 : YK11.FPState, KK_R1_stmt (fx := fx0) B n) -> MF_KKNOCK_F B n.
Proof. intros n R1 fx0. exact (kk_s_kknock (fx := fx0) B VOBJS SIGP RELRO IEQ n (R1 fx0)). Qed.
End i.
End h.
End g.
