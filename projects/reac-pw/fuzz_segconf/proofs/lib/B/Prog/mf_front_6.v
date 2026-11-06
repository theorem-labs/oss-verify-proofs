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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 155 of its 197 lines of code are new or changed and 411 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_FRONT of
   lib/B/Prog/m_file_m.v, piece 6 (fr_st): the strip call. A walk lane of the image-B m_file-family owner's G2B (a piece agent,
   on a working branch).
   proves no function (kind: segment lemma of m_file's image-B walk, S_MF_FRONT piece 6).

   fr_st : FR_SR_stmt B n -> FR_ST_stmt B n (the point statements of lib/B/Prog/mf_front_m.v).
   THE CODE (the neutral listing of m_file in image B lines 223-226, FR_ST = BASE + AF_m_file + 0x374):
     0x864b4 `li s5,32`; 0x864b8 `addi a0,s1,176`; 0x864bc `addi a1,s1,168`; 0x864c0 `jal 879cc <strip>`;
   strip returns to 0x864c4 = FR_SR. No store, no instrumented check and no UBSan trap branch lies between FR_ST and
   the call, and the call is the last instruction of the piece.
   THE WALK: the three register instructions by the symbolic executor from a state of registers only (every
   register its own atom, no region: the run writes no byte, so every cut fact holds at the new memory, m_file_k.v's
   mf_keep_run0); the `jal` by m_file_rf.v's mf_jal_step (the listing slot `PCall SS_strip 1` at AF_m_file + 0x380);
   its target pa_sigma SS_strip is BASE + AF_strip by SIGP (lib/B/Prog/SegObj.v seg_sig_prog: the PAImg class links
   no call target to the text base, PaTable.v pi_slot_check states only the jal's own target); the call itself by
   lib/B/Prog/m_file_strip.v's mf_strip_call (strip_contract through cl_callS_wide, the cut facts kept by
   mf_keep_callx) at the cells osc = 176, oec = 168 over the bytes [0, C) of the text left, C = fr_C rest: the
   comment cut is a prefix of the line, which is a prefix of the text left (p6_cut_firstn), so slice 0 C rest =
   fr_cut rest. At the return the cells hold p + strip_lead (fr_cut rest) and p + C - strip_trail (fr_cut rest),
   which is FR_SR with i0 = strip_lead (fr_cut rest), j0 = C - strip_trail (fr_cut rest) (mf_front_mdl.v
   fr_strip_idx: i0 <= j0 <= L and the slice equation); s5 = 0x20 (set at 0x864b4), s11 = line + 1 and s4 = 511
   (fr_short) are callee-saved across strip, 152(s1) by mf_strip_call's mf_np.
   POSITIONAL NAMES (checked against the listing by what each is): the cells 176(s1) / 168(s1) are strip's
   arguments a0 / a1 (0x864b8 / 0x864bc), the line start (`sd s10,176(s1)` 0x86384) and the line end / comment cut
   (168(s1), the image-B m_file cut map's cell list); s5 = x21, s4 = x20, s11 = x27, s1 = x9; the jal's listing offset
   FR_JAL = AF_m_file + 0x380 (BASE + AF_m_file = 0x86140, so pc 0x864c0, slot PCall SS_strip 1 by vm_compute) and
   the return offset FR_JAL + 4 = AF_m_file + 0x384 = FR_SR (0x864c4); strip's entry BASE + AF_strip = 0x879cc.
   Section hypotheses: SIGP (the jal's target, the owner's 2026-10-30 decision) and STRIP (strip_contract at
   BASE + AF_strip and SegInstB.STK_strip, at every FP state). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegObj SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k strip_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_c m_file_rf m_file_strip.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_front_mdl mf_front_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* 0x864c0, the `jal strip` (listing slot PCall SS_strip 1) *)
Definition FR_JAL : Z := AF_m_file + 0x380.

(* the comment cut is the first C bytes of the text left (the cut is a prefix of the line, the line of the text
   left) *)
Lemma p6_cut_firstn : forall rest, fr_cut rest = firstn (fr_C rest) rest.
Proof.
intros rest. unfold fr_C, fr_cut. destruct (fr_cut_len (mf_line rest)) as [_ [q Hq]].
destruct (fr_line_split rest) as [R ER]. rewrite Hq.
set (L := mf_line rest) in *. clearbody L. subst rest.
rewrite firstn_app, length_firstn.
replace (Nat.min q (length L) - length L)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
destruct (Nat.min_spec q (length L)) as [[H1 ->] | [H1 ->]]; [reflexivity|].
rewrite (firstn_all2 L H1), firstn_all. reflexivity.
Qed.
Lemma p6_slice_cut : forall rest, slice 0 (fr_C rest) rest = fr_cut rest.
Proof. intros rest. rewrite p6_cut_firstn. unfold slice. rewrite Nat.sub_0_r. reflexivity. Qed.

(* the state of registers only (every register its own atom, no region, no fact) *)
Definition ss_p6 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* a register after a run from ss_p6: the run's register atom k is the start's register k *)
Ltac p6_lkq Q k :=
  unfold A_TEXT in Q; cbn [Nat.leb andb] in Q; rewrite (ew_Ereg_nat _ [] k (Z_to_bv 5 (Z.of_nat k)) eq_refl) in Q.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma p6_reg_seed : forall (W : world SEGS) regs mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (ss_p6 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold ss_p6. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. exact I.
- split; [exact I | split; exact I].
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* the jal's target (SegObj.v; the owner's decision for this piece) *)
Hypothesis SIGP : seg_sig_prog.
(* the callee, at every FP state (the image-B m_file segment table's strip row) *)
Hypothesis STRIP : forall fx0 : YK11.FPState, @strip_contract fx0 rc SK SEGS B (BASE + AF_strip) SegInstB.STK_strip.

Lemma fr_st : forall n, FR_SR_stmt B n -> FR_ST_stmt B n.
Proof.
intros n SR. unfold FR_ST_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX SHORT S176 S168.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & MOD).
pose proof SHORT as (R27 & R20 & NP & HL512).
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof CORE as (HJ & _).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as (HB0 & HB1 & HB4).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CRlo & CRhi) & CRal); unfold YG0f.ASAN_CEIL in CRlo, CRhi, CRal.
assert (Hs1b : mv_sp v - 336 <= mf_s1 (mv_sp v) <= mv_sp v - 320) by (destruct Hs1 as [E1|E1]; lia).
pose proof (fr_C_le rest) as HCL. pose proof (fr_line_len rest) as HLL.
(* 0x864b4 .. 0x864bc: li s5,32; addi a0,s1,176; addi a1,s1,168 (registers only) *)
pose proof (p6_reg_seed Wc regs1 memc FR_ST) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
unfold mf_at.
paj_run_to_sh RUNTOP HS HJ FR_JAL.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. refine (kept_of_frame _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr _ a Ha (fun x => x)).
  intros bb wlo whi x Hinw Hr. vm_compute in Hinw. destruct Hinw. }
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
(* the run wrote no byte: every cut fact at the call's memory *)
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE1 & CELLS1 & NPf & LPf).
pose proof (NPf _ NP) as NP1. pose proof (LPf _ _ _ _ _ LOOP) as LOOP1. clear NPf LPf.
assert (K0' : forall a, 0 <= a < 2 ^ 64 -> ~ (fun _ : Z => False) a -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a Ha _; exact (K0 a Ha)).
assert (S176a : mf_slot v (ms_mem ms) Wc 176 (p + Z.of_nat 0)).
{ change (Z.of_nat 0) with 0. rewrite Z.add_0_r. unfold mf_slot in *.
  apply (mf_val_keep Wc Wc memc (ms_mem ms) (fun _ => False) _ 8 _ K0');
    [lia | change (Z.of_nat 8) with 8; lia | intros k _ [] | exact S176]. }
assert (S168a : mf_slot v (ms_mem ms) Wc 168 (p + Z.of_nat (fr_C rest))).
{ unfold mf_slot in *.
  apply (mf_val_keep Wc Wc memc (ms_mem ms) (fun _ => False) _ 8 _ K0');
    [lia | change (Z.of_nat 8) with 8; lia | intros k _ [] | exact S168]. }
(* the registers at the jal *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (20%bv : bv 5) Q20. prreg HS (27%bv : bv 5) Q27. prreg HS (21%bv : bv 5) Q21.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
p6_lkq Q2 2%nat. p6_lkq Q3 3%nat. p6_lkq Q4 4%nat. p6_lkq Q8 8%nat. p6_lkq Q9 9%nat. p6_lkq Q18 18%nat.
p6_lkq Q23 23%nat. p6_lkq Q24 24%nat. p6_lkq Q19 19%nat. p6_lkq Q22 22%nat. p6_lkq Q25 25%nat.
p6_lkq Q20 20%nat. p6_lkq Q27 27%nat.
p6_lkq Q10 9%nat. p6_lkq Q11 9%nat.
assert (RA1 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); assumption. }
assert (U9 : bv_unsigned (getr regs1 9) = mf_s1 (mv_sp v)) by (rewrite R9; apply mf_w64_u; lia).
assert (G10 : getr (ms_regs ms) 10 = w64 (mf_s1 (mv_sp v) + 176)).
{ rewrite Q10. unfold w64.
  lazymatch goal with |- Z_to_bv 64 (bv_unsigned ?g + 176) = _ =>
    change (bv_unsigned g) with (bv_unsigned (getr regs1 9)) end.
  rewrite U9. reflexivity. }
assert (G11 : getr (ms_regs ms) 11 = w64 (mf_s1 (mv_sp v) + 168)).
{ rewrite Q11. unfold w64.
  lazymatch goal with |- Z_to_bv 64 (bv_unsigned ?g + 168) = _ =>
    change (bv_unsigned g) with (bv_unsigned (getr regs1 9)) end.
  rewrite U9. reflexivity. }
assert (G21 : getr (ms_regs ms) 21 = w64 0x20) by (rewrite Q21; reflexivity).
pmkst HS.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  change (Z_to_bv 64 (BASE + k)) with (Z_to_bv 64 (BASE + FR_JAL)) end.
(* 0x864c0: jal strip *)
apply (mf_jal_step Wc (ms_regs ms) (ms_mem ms) mdw _ FR_JAL SS_strip);
  [vm_compute; reflexivity | unfold FR_JAL, AF_m_file; lia |].
intros mat'.
assert (SIGR : pa_sigma SS_strip = BASE + AF_strip).
{ rewrite (SIGP SS_strip) by (unfold seg_prog_syms; cbn [In]; tauto). f_equal; try (vm_compute; reflexivity). }
rewrite SIGR.
set (mdc' := with_vm_backing (m_vm_lazy mdw) mat' mdw).
set (regsc := regupd (ms_regs ms) 1%bv (Z_to_bv 64 (BASE + (FR_JAL + 4)))).
pose proof CORE1 as (HJ1 & CR1).
pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ1) as HJ1'. fold mdc' in HJ1'.
assert (CORE1' : mf_core B v lyc Sc Wc (ms_mem ms) mdc' pos MF_LOW_OFF mcc) by exact (conj HJ1' CR1).
assert (GR : forall r : bv 5, r <> 1%bv -> getr regsc r = getr (ms_regs ms) r)
  by (intros r Hr; apply mf_getr_upd1; exact Hr).
assert (RAc : mf_regs_at B v lyc pos regsc).
{ apply (mf_regs_at_of B v lyc pos (ms_regs ms) regsc RA1); apply GR; discriminate. }
(* strip(s1 + 176, s1 + 168) over the bytes [0, C) of the text left *)
apply (mf_strip_call B STRIP v lyc Sc Wc regsc (ms_mem ms) mdc' pos MF_LOW_OFF mcc cur line p rest (mf_next p rest)
  (FR_JAL + 4) 176 168 0 (fr_C rest) CX LS CORE1' CELLS1 LOOP1 NP1 RAc).
- apply mf_getr_upd1_same.
- unfold FR_JAL, AF_m_file; lia.
- vm_compute. reflexivity.
- lia.
- lia.
- vm_compute. reflexivity.
- lia.
- lia.
- vm_compute. reflexivity.
- lia.
- rewrite GR by discriminate. exact G10.
- rewrite GR by discriminate. exact G11.
- lia.
- exact S176a.
- exact S168a.
- intros S2 W2 regs2 mem2 md2 HWle LS2 CORE2 CELLS2 LOOP2 NP2 RA2 HPR V176 V168 _.
  rewrite p6_slice_cut in V176, V168.
  replace (FR_JAL + 4) with FR_SR by (unfold FR_JAL, FR_SR; lia).
  pose proof (fr_strip_idx rest) as (I1 & I2 & I3).
  pose proof (strip_le (fr_cut rest)) as ILE.
  apply (SR v lyc S2 W2 regs2 mem2 md2 pos mcc cur line p rest (strip_lead (fr_cut rest))
    (fr_C rest - strip_trail (fr_cut rest))%nat).
  + exact (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj Hn (conj Hne (conj LOOP2 MOD))))))))).
  + split; [|split; [|split; [exact NP2 | exact HL512]]].
    * transitivity (getr regsc 27); [exact (HPR 27 ltac:(unfold acallee_saved; lia))|].
      rewrite GR by discriminate. rewrite Q27. exact R27.
    * transitivity (getr regsc 20); [exact (HPR 20 ltac:(unfold acallee_saved; lia))|].
      rewrite GR by discriminate. rewrite Q20. exact R20.
  + transitivity (getr regsc 21); [exact (HPR 21 ltac:(unfold acallee_saved; lia))|].
    rewrite GR by discriminate. exact G21.
  + replace (p + Z.of_nat (strip_lead (fr_cut rest))) with
      (p + Z.of_nat 0 + Z.of_nat (strip_lead (fr_cut rest))) by lia.
    exact V176.
  + replace (p + Z.of_nat (fr_C rest - strip_trail (fr_cut rest))%nat) with
      (p + Z.of_nat (fr_C rest) - Z.of_nat (strip_trail (fr_cut rest))) by (unfold fr_C in *; lia).
    exact V168.
  + lia.
  + exact I3.
Qed.
Print Assumptions fr_st.
End e.
End f.
End d.
