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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 206 of its 244 lines of code are new or changed and 415 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): segment S_MF_LONGP of its walk (LONG 0x86110 -> TAIL 0x86cf8;
   the G2 walk owner's guide/MF-CUTS-A.md sections 2 and 4). The LONGP / KKNOCKP segment lane of the G2 walk owner's G2.
   S_MF_LONGP is cut at LK_CALLP 0x861e4 (lib/A/Prog/m_file_s_long_d.v): lib/A/Prog/m_file_s_long_l.v proves LONG
   from LK_CALLPX (the blank skip 0x86110-0x86144 and its two exits, cur' = NULL when the first non-blank byte is
   '['); this file proves LK_CALLPX from TAIL and closes the segment:
   - lk_after: 0x861f0 `mv a7,s4`, 0x861f4 `j 0x86cf8`: TAIL with a7 = s4 (the next line's address).
   - lk_callp: at 0x861e4 the cut facts at the memory memc' (the cur slot rewritten, m_file_k.v's mf_keep_run_s), then
     0x861e4 `mv a0,s5`, 0x861e8 `mv a1,s6`, the call 0x861ec `jal m_refuse` (lib/A/Prog/m_file_rf.v's
     mf_refuse_step0: the slot 144(s1) holds no next-line fact on this path), and lk_after at the returned FP
     state for the next line: line + 1, mf_next p rest, mf_rest rest, the model m_refuse mcc (line + 1) false with
     the cursor cur' (m_file_k.v's mf_loop_next).
   The runs between the calls use a state of registers only (every register its own atom, no region): they write
   no byte, so the cut facts hold at the new memory (m_file_k.v's mf_keep_run0).
   - s_mf_longp : S_MF_LONGP B, from m_file_s_long_l.v's lk_long (the LONGP blank-skip sub-lane) and lk_callp at every FP
     state.
   Section hypotheses, from the shared list of m_file_m.v change 3, verbatim: SIGP, SSP, RELRO, M_REFUSE (for
   mf_refuse_step0). Closed against G2 FINAL at 6f783602b5e3. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_refuse_c m_file_c m_file_m m_file_k m_file_mdl m_file_rf m_file_s_long_d
  m_file_s_long_l.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac mf_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac mf_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.


(* a register after a run from ss_lkr: the run's register atom k is the start's register k *)
Ltac lkq Q k :=
  unfold A_TEXT in Q; cbn [Nat.leb andb] in Q; rewrite (ew_Ereg_nat _ [] k (Z_to_bv 5 (Z.of_nat k)) eq_refl) in Q.

(* the state of registers only *)
Definition ss_lkr (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition LK_JAL : Z := AF_m_file + 0x330.   (* 0x861ec `jal m_refuse` *)
Definition LK_AFT : Z := AF_m_file + 0x334.   (* 0x861f0, the return point *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma lk_reg_seed : forall (W : world SEGS) regs mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (ss_lkr pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold ss_lkr. apply pa_entry_st_ok_full.
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

(* 0x861f0: TAIL with a7 = s4 *)
Lemma lk_after : forall n, MF_TAIL_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
getr regs1 20 = w64 p -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 line ->
mf_at B v Wc regs1 memc mdc LK_AFT.
Proof.
intros n TAIL v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA R24 Hn LOOP MOD R20 R21 R22.
pose proof CORE as (HJ & _).
pose proof (lk_reg_seed Wc regs1 memc LK_AFT) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
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
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (24%bv : bv 5) Q24. prreg HS (17%bv : bv 5) Q17.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
lkq Q2 2%nat. lkq Q3 3%nat. lkq Q4 4%nat. lkq Q8 8%nat. lkq Q9 9%nat. lkq Q18 18%nat. lkq Q19 19%nat.
lkq Q25 25%nat. lkq Q26 26%nat. lkq Q24 24%nat. lkq Q17 20%nat. lkq Q21 21%nat. lkq Q22 22%nat.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); assumption. }
pmkst HS.
apply (TAIL v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc cur line p rest CX LS FRM CORE' CELLS' RA'
  ltac:(rewrite Q24; exact R24) Hn (LOOPK mcc cur line p rest LOOP) MOD).
- rewrite Q17. exact R20.
- rewrite Q21. exact R21.
- rewrite Q22. exact R22.
Qed.
End e.
End f.
End d.

(* LK_CALLPX from TAIL at every FP state: the cut facts at memc', the moves, m_refuse, lk_after *)
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
(* the shared hypotheses (m_file_m.v change 3, decision (a), amended) this file needs, verbatim *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.

Lemma lk_callp : forall n, (forall fx0 : YK11.FPState, MF_TAIL_stmt (fx := fx0) B n) -> LK_CALLPX_stmt B n.
Proof.
intros n TAIL. unfold LK_CALLPX_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur cur' line p rest memc' mdc' CX LS FRM CORE CELLS RA R24 Hn Hne LOOP
  Hlong Hcur' MOD R20 R22 R21 HJ' KEEP VCUR.
pose proof CORE as (HJ & HPm & VFL & VSH & VSV & V112 & MC & ADDR & TAIL0).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in Sp1.
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof LOOP as (_ & _ & _ & _ & _ & Hcok & Hk0 & Hl0 & Hl1 & _).
set (RW := fun a => mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144).
assert (KEEP' : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc memc' a = rdW Wc memc a) by exact KEEP.
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) memc') (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ intros i Hi. pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
  pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
  apply (mf_val_keep Wc Wc memc memc' RW _ 1 MF_LOW_OFF KEEP'); [unfold SHADOW_OFF; lia | unfold SHADOW_OFF; cbn; lia | | exact (VSH i Hi)].
  intros k Hk. unfold RW. cbn in Hk. unfold SHADOW_OFF. destruct Hs1 as [Hs1|Hs1]; rewrite Hs1; lia. }
assert (MC' : sa_mconf (rdW Wc memc') (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc memc' RW (mv_c v) mcc KEEP'); [lia | lia | | exact MC].
  intros a Ha. unfold RW. destruct Hs1 as [Hs1|Hs1]; rewrite Hs1; lia. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur memc' mdc' RW MF_LOW_OFF cur' mcc CX CORE CELLS
  HJ' KEEP') as (CORE1 & CELLS1 & LOOPK).
{ intros a Ha. unfold mf_rw. unfold RW in Ha. right; right; right; right; right. lia. }
{ intros a Ha _. unfold RW in Ha. right. lia. }
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
(* 0x861e4 .. 0x861e8: a0 = s5, a1 = s6 *)
pose proof (lk_reg_seed Wc regs1 memc' LK_CALLP) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
pose proof CORE1 as (HJ1 & _).
unfold mf_at.
paj_run_to_sh RUNTOP HS HJ1 LK_JAL.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc' a).
{ intros a Ha. refine (kept_of_frame _ _ (w_H Wc) memc' (ms_mem ms) (fun _ => False) HFr _ a Ha (fun x => x)).
  intros bb wlo whi x Hinw Hr. vm_compute in Hinw. destruct Hinw. }
set (mdw := with_vm_backing (m_vm_lazy mdc') mat mdc') in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc' mdc' pos MF_LOW_OFF mcc cur' (ms_mem ms) mdw CX CORE1 CELLS1 HJ1 K0)
  as (CORE2 & CELLS2 & _ & LOOPK2).
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (24%bv : bv 5) Q24. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
lkq Q2 2%nat. lkq Q3 3%nat. lkq Q4 4%nat. lkq Q8 8%nat. lkq Q9 9%nat. lkq Q18 18%nat. lkq Q19 19%nat.
lkq Q25 25%nat. lkq Q26 26%nat. lkq Q24 24%nat. lkq Q20 20%nat. lkq Q21 21%nat. lkq Q22 22%nat.
lkq Q10 21%nat. lkq Q11 22%nat.
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA); assumption. }
pmkst HS.
pose proof (mf_regs_at_call B v lyc pos _ RA2) as (S2r & S3r & S4r & S8r).
change (Z_to_bv 64 (BASE + 5304)) with (Z_to_bv 64 (BASE + LK_JAL)).
apply (mf_refuse_step0 B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos MF_LOW_OFF mcc mcc false
  cur' line p rest LK_JAL CX LS FRM (mf_corek_of_core B v lyc Sc Wc _ _ pos MF_LOW_OFF mcc CORE2) CELLS2
  S2r S3r S4r S8r (LOOPK2 mcc cur' line p rest LOOP1) Hne eq_refl Hk0).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- rewrite Q10. exact R21.
- rewrite Q11. exact R22.
- exact (mf_kept_le_refuse mcc (line + 1) false cur' (line + 1) (lines (mf_rest rest)) (mf_final v) Hcok2 MOD).
- intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfx LS2 CORE3 CELLS3 _ LOOP3 CS.
  assert (Ely2 : ly2 = lyc) by (destruct LS as (E1 & _); destruct LS2 as (E2 & _); congruence).
  subst ly2.
  replace (LK_JAL + 4) with LK_AFT by (unfold LK_JAL, LK_AFT; lia).
  pose proof (mf_regs_at_kept B v lyc pos (ms_regs ms) regs2 RA2 CS) as RA3.
  assert (C20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (CS 20 ltac:(unfold acallee_saved; lia)).
  assert (C21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (CS 21 ltac:(unfold acallee_saved; lia)).
  assert (C22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (CS 22 ltac:(unfold acallee_saved; lia)).
  assert (C24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (CS 24 ltac:(unfold acallee_saved; lia)).
  apply (lk_after (fx := fx1) B n (TAIL fx1) v lyc S2 W2 regs2 mem2 md2 pos (m_refuse mcc (line + 1) false) cur'
    (line + 1) (mf_next p rest) (mf_rest rest) CX LS2 (fxrel_frm0 fx fx1 FRM Hfx) CORE3 CELLS3 RA3).
  + rewrite C24, Q24. exact R24.
  + destruct (mf_break_snd rest) as (_ & Hlt & _). specialize (Hlt Hne). unfold mf_rest. lia.
  + apply (mf_loop_next v W2 mem2 mcc cur' line p rest (m_refuse mcc (line + 1) false) cur' LOOP3 Hne).
    * unfold m_refuse. cbn [mc_refused]. lia.
    * unfold m_refuse. cbn [mc_overflow]. lia.
    * exact (proj1 (proj2 (m_refuse_sizes mcc (line + 1) false))).
    * exact Hcok2.
  + exact MOD.
  + rewrite C20, Q20. exact R20.
  + rewrite C21, Q21. exact R21.
  + rewrite C22, Q22. exact R22.
Qed.
End e2.
End f2.
End d2.

(* S_MF_LONGP at every FP state (m_file_m.v's shape) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.
Lemma s_mf_longp : S_MF_LONGP B.
Proof.
intros n TAIL fx0.
exact (lk_long (fx := fx0) B n (lk_callp (fx := fx0) B SIGP SSP RELRO M_REFUSE n TAIL)).
Qed.
End i.
End h.
End g.
