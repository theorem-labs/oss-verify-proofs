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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 164 of its 207 lines of code are new or changed and 410 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, m_file at 0x86140): segment S_MF_LONGP of its walk
   (LONG 0x863d4 -> TAIL 0x86820), part 3: the call half, LP_CALLPX (lib/B/Prog/mf_longp_1.v) from TAIL. A walk lane of the image-B m_file-family owner's G2B. Adapted from the image-A m_file-family lane's image-A walk
   (commit 93220999e732, lib/A/Prog/m_file_s_long.v lk_after / lk_callp) at image B's numbers.
   - lp_after: 0x8681c `mv s10,s5` (s5 = the next line's address), then TAIL 0x86820 with s10 = s5, s11 = the lines
     consumed, s4 = 511.
   - lp_callp: at 0x86810 the cut facts at the memory memc' (the cur cell rewritten: m_file_k.v's mf_keep_run_s),
     then 0x86810 `mv a0,s9`, 0x86814 `mv a1,s11`, the call 0x86818 `jal m_refuse` (m_file_rf.v's mf_refuse_step0:
     152(s1) holds no next-line fact on the long-line path), and lp_after at the returned FP state for the next
     line: line + 1, mf_next p rest, mf_rest rest, the model m_refuse mcc (line + 1) false with the cursor cur'
     (m_file_k.v's mf_loop_next).
   The runs between the calls use a state of registers only (mf_longp_1.v's lp_seed0): they write no byte, so the
   cut facts hold at the new memory (m_file_k.v's mf_keep_run0). No UBSan trap branch and no instrumented check lie
   in this part.
   Section hypotheses, the shared list of m_file_rf.v verbatim: SIGP, SSP, RELRO, M_REFUSE (mf_refuse_step0). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
m_refuse_c m_file_c m_file_m m_file_sd m_file_k m_file_mdl m_file_rf mf_longp_1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* a register after a run from the light state: the run's register atom k is the start's register k *)
Ltac lpq Q k := rewrite (lp_ew_reg _ _ _ k (Z_to_bv 5 (Z.of_nat k)) eq_refl) in Q.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* 0x8681c: TAIL with s10 = s5 *)
Lemma lp_after : forall n, MF_TAIL_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
getr regs1 21 = w64 p -> getr regs1 27 = w64 line -> getr regs1 20 = w64 511 ->
mf_at B v Wc regs1 memc mdc LP_AFT.
Proof.
intros n TAIL v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA Hn LOOP MOD R21 R27 R20.
pose proof CORE as (HJ & _).
pose proof (lp_seed0 Wc regs1 memc LP_AFT 0 0) as HS.
assert (HEI : img_env VAL A_LIM (lp_E regs1 0 0)) by (unfold lp_E; apply Eimg_env).
unfold mf_at.
paj_run_to_sh RUNTOP HS HJ MF_TAIL.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. refine (kept_of_frame _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr _ a Ha (fun x => x)).
  intros bb wlo whi x Hinw Hr. vm_compute in Hinw. destruct Hinw. }
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE' & CELLS' & _ & LOOPK).
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27. prreg HS (20%bv : bv 5) Q20.
lpq Q2 2%nat. lpq Q3 3%nat. lpq Q4 4%nat. lpq Q8 8%nat. lpq Q9 9%nat. lpq Q18 18%nat. lpq Q23 23%nat.
lpq Q24 24%nat. lpq Q19 19%nat. lpq Q22 22%nat. lpq Q25 25%nat. lpq Q26 21%nat. lpq Q27 27%nat. lpq Q20 20%nat.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); assumption. }
pmkst HS.
apply (TAIL v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc cur line p rest CX LS FRM CORE' CELLS' RA' Hn
  (LOOPK mcc cur line p rest LOOP) MOD).
- rewrite Q26. exact R21.
- rewrite Q27. exact R27.
- rewrite Q20. exact R20.
Qed.
End e.
End f.
End d.

(* LP_CALLPX from TAIL at every FP state: the cut facts at memc', the moves, m_refuse, lp_after *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* the shared hypotheses of m_file_rf.v, verbatim *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.

Lemma lp_callp : forall n, (forall fx0 : YK11.FPState, MF_TAIL_stmt (fx := fx0) B n) -> LP_CALLPX_stmt B n.
Proof.
intros n TAIL. unfold LP_CALLPX_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur cur' line p rest memc' mdc' CX LS FRM CORE CELLS RA Hn Hne LOOP
  Hlong Hcur' MOD R21 R27 R20 (HJ' & KEEP & VCUR).
pose proof CORE as (HJ & HPm & VFL & VSH & VSV & V120 & MC & ADDR & TAIL0).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof LOOP as (_ & _ & _ & _ & _ & Hcok & Hk0 & Hl0 & Hl1 & _).
set (RW := fun a => mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144).
assert (KEEP' : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc memc' a = rdW Wc memc a) by exact KEEP.
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) memc') (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ intros i Hi. pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
  apply (mf_val_keep Wc Wc memc memc' RW _ 1 MF_LOW_OFF KEEP');
    [unfold SHADOW_OFF; lia | unfold SHADOW_OFF; cbn; lia | | exact (VSH i Hi)].
  intros k Hk. unfold RW. cbn in Hk. unfold SHADOW_OFF. destruct Hs1 as [Hs1|Hs1]; rewrite Hs1; lia. }
assert (MC' : sa_mconf (rdW Wc memc') (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc memc' RW (mv_c v) mcc KEEP'); [lia | lia | | exact MC].
  intros a Ha. unfold RW. destruct Hs1 as [Hs1|Hs1]; rewrite Hs1; lia. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur memc' mdc' RW MF_LOW_OFF cur' mcc CX CORE
  CELLS HJ' KEEP') as (CORE1 & CELLS1 & LOOPK).
{ intros a Ha. unfold mf_rw. unfold RW in Ha. right; right; right; right; right. lia. }
{ intros a Ha _. unfold RW in Ha. left. exact Ha. }
{ exact VSH'. }
{ exact VCUR. }
{ exact MC'. }
assert (LOOP1 : mf_loop v Wc memc' mcc cur' line p rest).
{ pose proof (LOOPK mcc cur line p rest LOOP) as L1. destruct Hcur' as [-> | ->]; [exact L1|].
  destruct L1 as (L1 & L2 & L3 & L4 & L5 & _ & L7 & L8 & L9 & L10 & L11).
  exact (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj I (conj L7 (conj L8 (conj L9 (conj L10 L11)))))))))). }
assert (Hcok' : mf_cur_ok mcc cur') by (destruct LOOP1 as (_ & _ & _ & _ & _ & H & _); exact H).
assert (Hcok2 : mf_cur_ok (m_refuse mcc (line + 1) false) cur') by (apply mf_cur_ok_refuse; exact Hcok').
change (mf_fin (m_refuse mcc (line + 1) false, cur') line rest) with
  (fst (m_lines (m_refuse mcc (line + 1) false, cur') (line + 1) (lines (mf_rest rest)))) in MOD.
(* 0x86810 .. 0x86814: a0 = s9, a1 = s11 *)
pose proof (lp_seed0 Wc regs1 memc' LP_CALLP 0 0) as HS.
assert (HEI : img_env VAL A_LIM (lp_E regs1 0 0)) by (unfold lp_E; apply Eimg_env).
pose proof CORE1 as (HJ1 & _).
unfold mf_at.
paj_run_to_sh RUNTOP HS HJ1 LP_JAL.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc' a).
{ intros a Ha. refine (kept_of_frame _ _ (w_H Wc) memc' (ms_mem ms) (fun _ => False) HFr _ a Ha (fun x => x)).
  intros bb wlo whi x Hinw Hr. vm_compute in Hinw. destruct Hinw. }
set (mdw := with_vm_backing (m_vm_lazy mdc') mat mdc') in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc' mdc' pos MF_LOW_OFF mcc cur' (ms_mem ms) mdw CX CORE1 CELLS1 HJ1 K0)
  as (CORE2 & CELLS2 & _ & LOOPK2).
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (27%bv : bv 5) Q27.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
lpq Q2 2%nat. lpq Q3 3%nat. lpq Q4 4%nat. lpq Q8 8%nat. lpq Q9 9%nat. lpq Q18 18%nat. lpq Q23 23%nat.
lpq Q24 24%nat. lpq Q19 19%nat. lpq Q22 22%nat. lpq Q25 25%nat. lpq Q20 20%nat. lpq Q21 21%nat. lpq Q27 27%nat.
lpq Q10 25%nat. lpq Q11 27%nat.
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); assumption. }
pose proof RA as (_ & _ & _ & R25).
pmkst HS.
pose proof (mf_regs_at_call B v lyc pos _ RA2) as (S2r & S3r & S4r & S8r).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?j)) _ _) _) _ =>
  change (Z_to_bv 64 (BASE + j)) with (Z_to_bv 64 (BASE + LP_JAL)) end.
apply (mf_refuse_step0 B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos MF_LOW_OFF mcc mcc
  false cur' line p rest LP_JAL CX LS FRM (mf_corek_of_core B v lyc Sc Wc _ _ pos MF_LOW_OFF mcc CORE2) CELLS2
  S2r S3r S4r S8r (LOOPK2 mcc cur' line p rest LOOP1) Hne eq_refl Hk0).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- rewrite Q10. exact R25.
- rewrite Q11. exact R27.
- exact (mf_kept_le_refuse mcc (line + 1) false cur' (line + 1) (lines (mf_rest rest)) (mf_final v) Hcok2 MOD).
- intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfx LS2 CORE3 CELLS3 _ LOOP3 CS.
  assert (Ely2 : ly2 = lyc) by (destruct LS as (E1 & _); destruct LS2 as (E2 & _); congruence).
  subst ly2.
  replace (LP_JAL + 4) with LP_AFT by (unfold LP_JAL, LP_AFT; lia).
  pose proof (mf_regs_at_kept B v lyc pos (ms_regs ms) regs2 RA2 CS) as RA3.
  assert (C20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (CS 20 ltac:(unfold acallee_saved; lia)).
  assert (C21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (CS 21 ltac:(unfold acallee_saved; lia)).
  assert (C27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (CS 27 ltac:(unfold acallee_saved; lia)).
  apply (lp_after (fx := fx1) B n (TAIL fx1) v lyc S2 W2 regs2 mem2 md2 pos (m_refuse mcc (line + 1) false) cur'
    (line + 1) (mf_next p rest) (mf_rest rest) CX LS2 (fxrel_frm0 fx fx1 FRM Hfx) CORE3 CELLS3 RA3).
  + destruct (mf_break_snd rest) as (_ & Hlt & _). specialize (Hlt Hne). unfold mf_rest. lia.
  + apply (mf_loop_next v W2 mem2 mcc cur' line p rest (m_refuse mcc (line + 1) false) cur' LOOP3 Hne).
    * unfold m_refuse. cbn [mc_refused]. lia.
    * unfold m_refuse. cbn [mc_overflow]. lia.
    * exact (proj1 (proj2 (m_refuse_sizes mcc (line + 1) false))).
    * exact Hcok2.
  + exact MOD.
  + rewrite C21, Q21. exact R21.
  + rewrite C27, Q27. exact R27.
  + rewrite C20, Q20. exact R20.
Qed.
End e2.
End f2.
End d2.
