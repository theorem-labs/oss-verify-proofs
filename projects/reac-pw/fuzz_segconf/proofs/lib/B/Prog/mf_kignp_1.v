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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 182 of its 235 lines of code are new or changed and 400 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KIGNP, its
   first two pieces: KIGN 0x86968 -> KI_R1 0x8697c (ieq(k, kl, "ignore")) and KI_R1 -> KKNOCK 0x86a7c or KI_R2
   0x86998 (ieq(v, vl, "yes")). A walk lane of the image-B m_file-family owner's G2B. ADAPTED from the image-A m_file-family lane's image-A
   lib/A/Prog/m_file_s_kign_1.v (commit a11e040adbd4: ki_s_kign, ki_s_r1) at image B.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's pieces KIGN and KI_R1).

   The code (the neutral listing of m_file in image B):
     0x86968 ld a0,208(s1) (k); 0x8696c auipc a1 / 0x86970 addi a2,a1 (listing object 20, "ignore" 0x21240);
     0x86974 mv a1,s5 (kl); 0x86978 jal ieq.
     0x8697c ld s9,112(s1) (c, the value s9 already holds); 0x86980 beqz a0 -> KKNOCK 0x86a7c; 0x86984 ld a0,192(s1)
     (v); 0x86988 auipc a1 / 0x8698c addi a2,a1 (object 21, "yes" 0x21260); 0x86990 mv a1,s10 (vl); 0x86994 jal ieq.
   No store, no instrumented check, no UBSan trap branch. Each run starts from mf_kignp_c.v's ki_seed_ro (the frame
   cells read-only, so the run changes no byte: ki_ro_frame) with the scratch cells 208(s1) = k (atom 52) and
   192(s1) = v (atom 53) and s9 pinned to atom 33, so the reload at 0x8697c leaves every register the K state names
   as it was; the ieq calls are mf_kignp_q.v's ki_ieq_k / ki_ieq_v (m_file_iq.v's mf_ieq_call).
   Section hypotheses: VOBJS (the literal bridge), SIGP (ieq's call target), RELRO and IEQ (mf_kignp_q.v's). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_iq ieq_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kignp_t mf_kignp_m mf_kignp_c mf_kignp_q.
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
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

(* the value's state from the K state with the key *)
Lemma ki_vbase_of_kbase : forall n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv,
  ki_kbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv ->
  ki_vbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & (KV1 & KV2 & KV3 & KV4) & S208 & R21 & S192 & R26 & R27 & NP).
exact (conj CX (conj LS (conj FRM (conj CORE (conj CELLS (conj RA (conj Hn (conj Hr (conj LOOP (conj KV2 (conj KV4
  (conj S192 (conj R26 (conj R27 NP)))))))))))))).
Qed.

(* the two literals' registers: "ignore" is listing object 20, "yes" object 21 *)
Lemma ki_lit_reg : forall E x i, In (x, i) MF_LIT_OBJS -> (A_TEXT <= A_OBJ i < A_LIM)%nat -> img_env VAL A_LIM E ->
  sv_denot E (SOff (A_OBJ i) 0) = w64 (SegInstB.seg_litA_fz x).
Proof.
intros E x i Hx Hi HEI. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (mf_lit_obj VOBJS x i Hx). unfold w64. f_equal. apply (HEI (A_OBJ i) Hi).
Qed.

(* KIGN 0x86968: ieq(k, kl, "ignore"), then KI_R1 *)
Lemma ki_s_kign : forall n, KI_R1_stmt B n -> MF_KIGN_stmt B n.
Proof.
intros n R1s. unfold MF_KIGN_stmt, MF_KAT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX LS FRM CORE CELLS RA Hn Hr LOOP KV MISS FIN S208 _ R21 S192 R26 R27 NP.
unfold mf_at.
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (ki_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
assert (Hk64 : 0 <= p + Z.of_nat ok < 2 ^ 64) by lia.
assert (Hv64 : 0 <= p + Z.of_nat ov < 2 ^ 64) by lia.
assert (KB : ki_kbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv)
  by exact (conj CX (conj LS (conj FRM (conj CORE (conj CELLS (conj RA (conj Hn (conj Hr (conj LOOP (conj KV
    (conj S208 (conj R21 (conj S192 (conj R26 (conj R27 NP))))))))))))))).
destruct ki_kslx_wf as (WF1 & WF2).
pose proof (ki_seed_ro B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc (Some gi) np [p + Z.of_nat ok; p + Z.of_nat ov]
  ki_kslx MF_KIGN CX CORE CELLS RA LCUR NP Hnp
  (ki_kslx_ok v regs1 lyc pos (Some gi) np Wc memc _ _ Hk64 Hv64 S208 S192) WF1 WF2) as HS.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ok; p + Z.of_nat ov]) in *.
pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS) as HR0. cbn [ms_regs mkst ss_regs] in HR0.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
pose proof CORE as (HJ & _).
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
pose proof (ki_ro_frame E ki_kslx _ _ HF) as HMEQ.
assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r).
{ intros r Hin.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    apply (ki_reg_same E sr_mf9 (ss_regs ss) regs1 (ms_regs ms) r HR0
      (fun r => st_ok_restrict_reg SEGS (w_H Wc) E ss ms r HS)) end.
  unfold ki_kregs in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]). destruct Hin. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R1)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E KI_R1 HEI). }
assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ok)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 52%nat HS) by (vm_compute; reflexivity).
  exact (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ok; p + Z.of_nat ov] 0 ltac:(unfold A_TEXT; lia)). }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat kl)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 21%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np _ 21 (Z_to_bv 5 21) eq_refl). exact R21. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_ignore)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 12%bv HS).
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
  apply (ki_lit_reg E S_ignore 20); [unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]) | unfold A_OBJ, A_TEXT, A_LIM; lia | exact HEI]. }
(* the jal's target *)
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
pose proof (ki_kbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ok kl ov
  vl k vv KB HJ HMEQ KR) as KB1.
apply (ki_ieq_k B RELRO IEQ n v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ok kl ov vl k vv KI_R1
  S_ignore KB1 Q1 ltac:(unfold KI_R1, AF_m_file; lia) ltac:(unfold KI_R1, AF_m_file; reflexivity)
  ltac:(unfold M_FILE_LITS; repeat (first [left; reflexivity | right])) Q10 Q11 Q12).
intros S2 W2 regs2 mem2 md2 KB2 HP2 A02.
exact (R1s v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv KB2 MISS FIN A02).
Qed.

(* KI_R1 0x8697c: s9 = 112(s1), `beqz a0` on ieq's answer; 0 goes to KKNOCK, else ieq(v, vl, "yes") and KI_R2 *)
Lemma ki_s_r1 : forall n, MF_KKNOCK_stmt B n -> KI_R2_stmt B n -> KI_R1_stmt B n.
Proof.
intros n KK R2s v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KB MISS FIN A0.
pose proof KB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & KV & S208 & R21 & S192 & R26 & R27 & NP).
unfold mf_at.
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (ki_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
assert (Hk64 : 0 <= p + Z.of_nat ok < 2 ^ 64) by lia.
assert (Hv64 : 0 <= p + Z.of_nat ov < 2 ^ 64) by lia.
destruct ki_kslx_wf as (WF1 & WF2).
pose proof (ki_seed_ro B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc (Some gi) np [p + Z.of_nat ok; p + Z.of_nat ov]
  ki_kslx KI_R1 CX CORE CELLS RA LCUR NP Hnp
  (ki_kslx_ok v regs1 lyc pos (Some gi) np Wc memc _ _ Hk64 Hv64 S208 S192) WF1 WF2) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ok; p + Z.of_nat ov]) in *.
pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS0) as HR0. cbn [ms_regs mkst ss_regs] in HR0.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
pose proof CORE as (HJ & _).
pose proof MISS as MISS0. apply Forall_cons_iff in MISS0 as [MR MISS1]. apply Forall_cons_iff in MISS1 as [MM _].
destruct (ieq k S_ignore) eqn:EIG; cbn [seg_spec.b2z] in A0.
- (* "ignore": a0 = 1, the beqz falls through to ieq(v, vl, "yes") *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS0.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  pose proof (ki_ro_frame E ki_kslx _ _ HF) as HMEQ.
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r).
  { intros r Hin.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      apply (ki_reg_same E sr_mf9 (ss_regs ss) regs1 (ms_regs ms) r HR0
        (fun r => st_ok_restrict_reg SEGS (w_H Wc) E ss ms r HS)) end.
    unfold ki_kregs in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]). destruct Hin. }
  assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R2)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
    lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
      transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
    exact (codeptr_val E KI_R2 HEI). }
  assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 53%nat HS) by (vm_compute; reflexivity).
    exact (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ok; p + Z.of_nat ov] 1 ltac:(unfold A_TEXT; lia)). }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 26%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np _ 26 (Z_to_bv 5 26) eq_refl). exact R26. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_yes)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 12%bv HS).
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    apply (ki_lit_reg E S_yes 21); [unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]) | unfold A_OBJ, A_TEXT, A_LIM; lia | exact HEI]. }
  rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
  pose proof (ki_vbase_of_kbase n v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ok kl ov vl k vv
    (ki_kbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ok kl ov vl k vv
       KB HJ HMEQ KR)) as VB1.
  apply (ki_ieq_v B RELRO IEQ n v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv KI_R2 S_yes
    VB1 Q1 ltac:(unfold KI_R2, AF_m_file; lia) ltac:(unfold KI_R2, AF_m_file; reflexivity)
    ltac:(unfold M_FILE_LITS; repeat (first [left; reflexivity | right])) Q10 Q11 Q12).
  intros S2 W2 regs2 mem2 md2 VB2 HP2 A02.
  apply (R2s v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv VB2); [|exact A02].
  rewrite <- (ki_val_disp mcc gi k vv (line + 1) MR MM EIG). exact FIN.
- (* "ignore" missed: a0 = 0, the beqz goes to KKNOCK with the K state *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS0 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KKNOCK.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  pose proof (ki_ro_frame E ki_kslx _ _ HF) as HMEQ.
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r).
  { intros r Hin.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
      apply (ki_reg_same E sr_mf9 (ss_regs ss) regs1 (ms_regs ms) r HR0
        (fun r => st_ok_pi_restrict_reg (w_H Wc) E ss ms r HS)) end.
    unfold ki_kregs in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]). destruct Hin. }
  pose proof (ki_kbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ok kl ov
    vl k vv KB HJ HMEQ KR) as KB1.
  destruct KB1 as (_ & _ & _ & CORE1 & CELLS1 & RA1 & _ & _ & LOOP1 & _ & S2081 & R211 & S1921 & R261 & R271 & NP1).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with MF_KKNOCK by (unfold MF_KKNOCK, AF_m_file; reflexivity) end.
  apply (KK v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ok kl ov vl k vv CX LS FRM CORE1 CELLS1
    RA1 Hn Hr LOOP1 KV).
  + constructor; [exact MR|]. constructor; [exact MM|]. constructor; [exact EIG | constructor].
  + exact FIN.
  + exact S2081.
  + intros H; discriminate H.
  + exact R211.
  + exact S1921.
  + exact R261.
  + exact R271.
  + exact NP1.
Qed.
End e.
End f.
End d.
