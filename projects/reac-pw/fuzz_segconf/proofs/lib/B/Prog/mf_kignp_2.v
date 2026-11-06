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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 185 of its 235 lines of code are new or changed and 403 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KIGNP, two
   of its pieces: KI_R2 0x86998 -> KI_HIT 0x86a18 or KI_R3 0x869b4 (ieq(v, vl, "true")) and KI_R4 0x869f8 -> KI_HIT or
   KI_R5 0x86a10 (ieq(v, vl, "false")). A walk lane of the image-B m_file-family owner's G2B. The image-B pieces of the image-A m_file-family lane's
   image-A KI_R2 / KI_R4 (m_file_s_kign_m.v's statements), in the form of mf_kignp_1.v.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's pieces KI_R2 and KI_R4).

   The code (the neutral listing of m_file in image B):
     0x86998 li s4,1; 0x8699c bnez a0 -> 0x86a18 (KI_HIT, s4 = 1: "yes"); 0x869a0 ld a0,192(s1) (v); 0x869a4 auipc a1 /
     0x869a8 addi a2,a1 (listing object 22, "true" 0x21280); 0x869ac mv a1,s10 (vl); 0x869b0 jal ieq (return KI_R3).
     0x869f8 bnez a0 -> 0x86a14 (li s4,0; KI_HIT with s4 = 0: "no"); 0x869fc ld a0,192(s1); 0x86a00 auipc a1 /
     0x86a04 addi a2,a1 (object 24, "false" 0x212c0); 0x86a08 mv a1,s10; 0x86a0c jal ieq (return KI_R5).
   No store, no instrumented check, no UBSan trap branch. The runs start from mf_kignp_c.v's ki_seed_ro with the
   scratch cell 192(s1) = v (atom 52), a0 pinned to ieq's answer; the ieq calls are mf_kignp_q.v's ki_ieq_v.
   Section hypotheses: VOBJS, SIGP, RELRO, IEQ. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kignp_t mf_kignp_m mf_kignp_c mf_kignp_q mf_kignp_1.
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

(* the awr_ok goal of a run from ki_seed_ro: every region read-only *)
Ltac ki_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* KI_R2 0x86998: s4 = 1, `bnez a0` on ieq "yes"; a hit goes to KI_HIT, else ieq(v, vl, "true") and KI_R3 *)
Lemma ki_s_r2 : forall n, KI_HIT_stmt B n -> KI_R3_stmt B n -> KI_R2_stmt B n.
Proof.
intros n HIT R3s v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN A0.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
unfold mf_at.
pose proof (ki_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
assert (Hv64 : 0 <= p + Z.of_nat ov < 2 ^ 64) by lia.
destruct ki_vslx_wf as (WF1 & WF2).
pose proof (ki_seed_ro B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc (Some gi) np [p + Z.of_nat ov] ki_vslx KI_R2
  CX CORE CELLS RA LCUR NP Hnp (ki_vslx_ok v regs1 lyc pos (Some gi) np Wc memc _ Hv64 S192) WF1 WF2) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ov]) in *.
pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS0) as HR0. cbn [ms_regs mkst ss_regs] in HR0.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
pose proof CORE as (HJ & _).
destruct (ieq vv S_yes) eqn:EY; cbn [seg_spec.b2z] in A0.
- (* "yes": a0 = 1, s4 = 1, the bnez goes to KI_HIT *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
  { ki_awr_ro. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  pose proof (ki_ro_frame E ki_vslx _ _ HF) as HMEQ.
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r).
  { intros r Hin.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
      apply (ki_reg_same E sr_mf9 (ss_regs ss) regs1 (ms_regs ms) r HR0
        (fun r => st_ok_pi_restrict_reg (w_H Wc) E ss ms r HS)) end.
    unfold ki_kregs in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]). destruct Hin. }
  assert (R20 : getr (ms_regs ms) 20 = w64 (seg_spec.b2z true)).
  { rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 20%bv HS).
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    reflexivity. }
  pose proof (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
    VB HJ HMEQ KR) as VB1.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv true VB1); [|exact R20].
  unfold ki_val in FIN. rewrite (ki_dec_yes vv EY) in FIN. exact FIN.
- (* "yes" missed: a0 = 0, ieq(v, vl, "true") *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS0 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS0.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { ki_awr_ro. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  pose proof (ki_ro_frame E ki_vslx _ _ HF) as HMEQ.
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r).
  { intros r Hin.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      apply (ki_reg_same E sr_mf9 (ss_regs ss) regs1 (ms_regs ms) r HR0
        (fun r => st_ok_restrict_reg SEGS (w_H Wc) E ss ms r HS)) end.
    unfold ki_kregs in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]). destruct Hin. }
  assert (Q20 : getr (ms_regs ms) 20 = w64 1).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 20%bv HS).
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    reflexivity. }
  assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R3)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
    lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
      transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
    exact (codeptr_val E KI_R3 HEI). }
  assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 52%nat HS) by (vm_compute; reflexivity).
    exact (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov] 0 ltac:(unfold A_TEXT; lia)). }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 26%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np _ 26 (Z_to_bv 5 26) eq_refl). exact R26. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_true)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 12%bv HS).
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    apply (ki_lit_reg VOBJS E S_true 22); [unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]) | unfold A_OBJ, A_TEXT, A_LIM; lia | exact HEI]. }
  rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
  pose proof (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
    VB HJ HMEQ KR) as VB1.
  apply (ki_ieq_v B RELRO IEQ n v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv KI_R3 S_true
    VB1 Q1 ltac:(unfold KI_R3, AF_m_file; lia) ltac:(unfold KI_R3, AF_m_file; reflexivity)
    ltac:(unfold M_FILE_LITS; repeat (first [left; reflexivity | right])) Q10 Q11 Q12).
  intros S2 W2 regs2 mem2 md2 VB2 HP2 A02.
  apply (R3s v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv VB2 FIN EY A02).
  transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact Q20].
Qed.

(* KI_R4 0x869f8: `bnez a0` on ieq "no"; a hit sets s4 = 0 (0x86a14) and goes to KI_HIT, else ieq(v, vl, "false")
   and KI_R5 *)
Lemma ki_s_r4 : forall n, KI_HIT_stmt B n -> KI_R5_stmt B n -> KI_R4_stmt B n.
Proof.
intros n HIT R5s v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN NY NT N1 A0.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
unfold mf_at.
pose proof (ki_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
assert (Hv64 : 0 <= p + Z.of_nat ov < 2 ^ 64) by lia.
destruct ki_vslx_wf as (WF1 & WF2).
pose proof (ki_seed_ro B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc (Some gi) np [p + Z.of_nat ov] ki_vslx KI_R4
  CX CORE CELLS RA LCUR NP Hnp (ki_vslx_ok v regs1 lyc pos (Some gi) np Wc memc _ Hv64 S192) WF1 WF2) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ov]) in *.
pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS0) as HR0. cbn [ms_regs mkst ss_regs] in HR0.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
pose proof CORE as (HJ & _).
destruct (ieq vv S_no) eqn:EN; cbn [seg_spec.b2z] in A0.
- (* "no": a0 = 1, s4 = 0 at 0x86a14, then KI_HIT *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
  { ki_awr_ro. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  pose proof (ki_ro_frame E ki_vslx _ _ HF) as HMEQ.
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r).
  { intros r Hin.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
      apply (ki_reg_same E sr_mf9 (ss_regs ss) regs1 (ms_regs ms) r HR0
        (fun r => st_ok_pi_restrict_reg (w_H Wc) E ss ms r HS)) end.
    unfold ki_kregs in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]). destruct Hin. }
  assert (R20 : getr (ms_regs ms) 20 = w64 (seg_spec.b2z false)).
  { rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 20%bv HS).
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    reflexivity. }
  pose proof (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
    VB HJ HMEQ KR) as VB1.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv false VB1); [|exact R20].
  unfold ki_val in FIN. rewrite (ki_dec_no vv NY NT N1 EN) in FIN. exact FIN.
- (* "no" missed: a0 = 0, ieq(v, vl, "false") *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS0 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS0.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { ki_awr_ro. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  pose proof (ki_ro_frame E ki_vslx _ _ HF) as HMEQ.
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r).
  { intros r Hin.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      apply (ki_reg_same E sr_mf9 (ss_regs ss) regs1 (ms_regs ms) r HR0
        (fun r => st_ok_restrict_reg SEGS (w_H Wc) E ss ms r HS)) end.
    unfold ki_kregs in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]). destruct Hin. }
  assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R5)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
    lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
      transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
    exact (codeptr_val E KI_R5 HEI). }
  assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 52%nat HS) by (vm_compute; reflexivity).
    exact (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov] 0 ltac:(unfold A_TEXT; lia)). }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)).
  { rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 26%nat HS) by (vm_compute; reflexivity).
    unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np _ 26 (Z_to_bv 5 26) eq_refl). exact R26. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_false)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 12%bv HS).
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    apply (ki_lit_reg VOBJS E S_false 24); [unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]) | unfold A_OBJ, A_TEXT, A_LIM; lia | exact HEI]. }
  rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
  pose proof (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
    VB HJ HMEQ KR) as VB1.
  apply (ki_ieq_v B RELRO IEQ n v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv KI_R5 S_false
    VB1 Q1 ltac:(unfold KI_R5, AF_m_file; lia) ltac:(unfold KI_R5, AF_m_file; reflexivity)
    ltac:(unfold M_FILE_LITS; repeat (first [left; reflexivity | right])) Q10 Q11 Q12).
  intros S2 W2 regs2 mem2 md2 VB2 HP2 A02.
  exact (R5s v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv VB2 FIN NY NT N1 EN A02).
Qed.
End e.
End f.
End d.
