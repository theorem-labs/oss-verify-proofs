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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/mf_kignp_1.v; 64 of its 134 lines of code are new or changed and 165 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KIGNP: the
   refusal of a bad ignore value, KI_REF 0x86c08 -> KI_S4 0x86c18 (S_MF_KMOD's block 0x86c08-0x86c14, which
   S_MF_KIGNP also runs). A walk lane of the image-B m_file-family owner's G2B.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's refusal piece).

   The code: 0x86c08 ld s9,112(s1) (c); 0x86c0c mv a0,s9; 0x86c10 mv a1,s11 (line + 1); 0x86c14 jal m_refuse.
   The run from mf_kignp_c.v's ki_seed_ro stops at the `jal` (no store, no check, no trap); the call is the owner's
   shared step m_file_rf.v mf_refuse_step (knock = false, mcl = mcc), which returns at 0x86c18 at the FP state fx1
   with the block holding m_refuse mcc (line + 1) false; KI_S4's statement (mf_kignp_m.v KI_DONE_stmt) goes on.
   Section hypotheses: VOBJS, SIGP, SSP, RELRO, M_REFUSE (m_file_rf.v's, the image-B m_file segment table's m_refuse row). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaFx SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_mdl m_file_k m_file_rf m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kignp_t mf_kignp_m mf_kignp_c mf_kignp_q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offset of the `jal m_refuse` (0x86c14) and its return (0x86c18 = KI_S4) *)
Definition KI_JREF : Z := AF_m_file + 0xad4.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the rounding mode 0 survives a callee (fxrel) *)
Lemma ki_frm0_fxrel : forall fx1 : YK11.FPState, fxrel fx fx1 -> sa_frm0 (fx := fx) -> sa_frm0 (fx := fx1).
Proof. intros fx1 (_ & [E | E]) H; unfold sa_frm0 in *; [rewrite E; exact H | exact E]. Qed.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
Let RUNTO := paj_run_to B LAWS.

(* KI_REF 0x86c08: m_refuse(c, line + 1), then KI_S4 at the FP state m_refuse returns *)
Lemma ki_s_ref : forall n, (forall fx0 : YK11.FPState, KI_DONE_stmt (fx := fx0) B KI_S4 n) -> KI_REF_stmt B n.
Proof.
intros n KD v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
unfold mf_at.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & Hk0 & _).
pose proof (ki_line_le rest) as Hml.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
assert (Hv64 : 0 <= p + Z.of_nat ov < 2 ^ 64) by lia.
destruct ki_vslx_wf as (WF1 & WF2).
pose proof (ki_seed_ro B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc (Some gi) np [p + Z.of_nat ov] ki_vslx KI_REF
  CX CORE CELLS RA LCUR NP Hnp (ki_vslx_ok v regs1 lyc pos (Some gi) np Wc memc _ Hv64 S192) WF1 WF2) as HS.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ov]) in *.
pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS) as HR0. cbn [ms_regs mkst ss_regs] in HR0.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
pose proof CORE as (HJ & _).
paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_JREF.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
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
assert (Q10 : getr (ms_regs ms) 10 = w64 (mv_c v)).
{ rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 10%bv HS).
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
  pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _).
  pose proof (mfE_extra regs1 v lyc pos (Some gi) np [p + Z.of_nat ov] 1 ltac:(unfold A_TEXT; lia)) as E33.
  cbn [Nat.add nth mf_extra map app] in E33. fold E in E33.
  cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q11 : getr (ms_regs ms) 11 = w64 (line + 1)).
{ rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 11%bv HS).
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
  cbn [sv_denot]. unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np _ 27 (Z_to_bv 5 27) eq_refl).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact R27. }
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE1 & CELLS1 & NPk & LPk).
pose proof (ki_regs_at_move B v lyc pos regs1 (ms_regs ms) RA KR) as RA1.
pose proof RA1 as ((R2 & R3 & R4 & R8 & _) & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KI_JREF by (unfold KI_JREF, AF_m_file; reflexivity) end.
change (mf_at B v Wc (ms_regs ms) (ms_mem ms) mdq KI_JREF).
assert (HKEPT : (length (mc_kept (m_refuse mcc (line + 1) false)) <= length (mc_kept (mf_final v)))%nat)
  by exact (mf_kept_le_refuse mcc (line + 1) false (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) false LCUR) FIN).
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc mcc false
  (Some gi) line p rest np KI_JREF CX LS FRM (mf_corek_of_core B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc CORE1)
  CELLS1 (NPk _ NP) R2 R3 R4 R8 (LPk _ _ _ _ _ LOOP) Hr eq_refl Hk0 ltac:(vm_compute; reflexivity)
  ltac:(unfold KI_JREF, AF_m_file; lia) Q10 Q11 HKEPT).
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfx LS2 CORE2 CELLS2 NP2 LOOP2 HPr.
pose proof LS as (Ely & _). pose proof LS2 as (Ely2 & _). assert (Ey : ly2 = lyc) by congruence.
rewrite Ey in LS2, CORE2, CELLS2. clear Ely Ely2.
replace (KI_JREF + 4) with KI_S4 by (unfold KI_JREF, KI_S4; lia).
destruct (ki_refuse_cnt mcc (line + 1) false) as (RC1 & RC2 & RC3 & _ & _ & RC6).
apply (KD fx1 v lyc S2 W2 regs2 mem2 md2 pos (m_refuse mcc (line + 1) false) mcc gi line p rest CX LS2
  (ki_frm0_fxrel fx1 Hfx FRM) CORE2 CELLS2 (mf_regs_at_kept B v lyc pos (ms_regs ms) regs2 RA1 HPr) Hn Hr LOOP2).
- lia.
- lia.
- exact RC6.
- rewrite RC1. exact LCUR.
- exact FIN.
- transitivity (getr (ms_regs ms) 27); [exact (HPr 27 ltac:(unfold acallee_saved; lia))|].
  rewrite (KR 27%bv ltac:(unfold ki_kregs; cbn [In]; tauto)). exact R27.
- exact NP2.
Qed.
End e.
End f.
End d.
