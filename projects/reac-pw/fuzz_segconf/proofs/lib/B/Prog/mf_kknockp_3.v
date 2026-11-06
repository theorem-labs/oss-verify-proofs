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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 243 of its 287 lines of code are new or changed and 409 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): segment S_MF_KKNOCKP, part 3: the line's
   end after m_refuse (KK_AF_stmt at 0x86c18 and 0x86b00 -> KDONE 0x86c1c) and the path of a key other than "knock"
   (KK_R1 with b = false: 0x86a90 `beqz a0` -> 0x86c0c, m_refuse at 0x86c14, back at 0x86c18). A walk lane of
   the image-B m_file-family owner's G2B. proves no function (kind: segment lemmas of m_file's walk).

   kk_after: 0x86c18 `li s4,511` / 0x86b00 `j 0x86c1c`, a run with no memory access (m_file_sd.v's mf_seed, its
   regions dropped); KDONE's facts: the block holds m_refuse mcc (line + 1) b, the line loop's facts move to the next
   line (m_file_k.v's mf_loop_next: refused + 1, kept not fewer), the text left shrinks (mf_break_snd), 152(s1) keeps
   the next line's address, s11 = line + 1, s4 = 511.
   kk_r1_miss: a0 = 0 pinned (st_ok_pi_pin_reg'), the run 0x86a90 -> 0x86c14 (`beqz` taken; a0 = s9 = c, a1 = s11 =
   line + 1; no memory access), m_file_rf.v's mf_refuse_step (knock = false), then kk_after at the FP state m_refuse
   returns. Section hypotheses: VOBJS (the seed), SIGP, SSP, RELRO, M_REFUSE (mf_refuse_step's). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_refuse_c m_file_m m_file_mdl m_file_sd m_file_k m_file_rf.
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

(* the registers of a list L that a state's symbolic registers keep as the seed's (kk_pres on a list) *)
Lemma kk_pres_l : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word) (L : list Z),
  E = mfE regs1 v lyc pos cur np xs -> mf_regs_base v regs1 ->
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : Z => sv_eqb (sr_get R (Z_to_bv 5 r)) (sr_get sr_mf (Z_to_bv 5 r))) L = true ->
  forall r, In r L -> getr rr (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r).
Proof.
intros E R regs1 v lyc pos cur np xs rr L HE RB HR HC r Hin.
pose proof (mf_regs_ok v regs1 lyc pos cur np xs RB) as HO. rewrite <- HE in HO.
rewrite HR, HO. f_equal. apply sv_eqb_eq. exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Let RUNTO := paj_run_to B LAWS.

(* the end of a refused key line: KDONE from the state m_refuse returned, its registers at the run's end given *)
Lemma kk_kdone_of : forall n v lyc Sc Wc memc mdc pos mcc gi line p rest b (regs2 : bvmap 5 word) mem2 md2,
  MF_KDONE_stmt B n -> mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON (m_refuse mcc (line + 1) b) -> mf_cells v lyc pos memc Wc (Some gi) ->
  (length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
  mf_fin (m_refuse mcc (line + 1) b, Some gi) line rest = mf_final v -> mf_np v memc Wc (mf_next p rest) ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc mem2 a = rdW Wc memc a) ->
  mf_regs_at B v lyc pos regs2 -> getr regs2 27 = w64 (line + 1) -> getr regs2 20 = w64 511 ->
  mf_at B v Wc regs2 mem2 md2 MF_KDONE.
Proof.
intros n v lyc Sc Wc memc mdc pos mcc gi line p rest b regs2 mem2 md2 KD CX LS FRM CORE CELLS Hn Hne LOOP FIN NP
  HJ2 EQV RA2 R27 R20.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON (m_refuse mcc (line + 1) b) (Some gi) mem2 md2 CX CORE
  CELLS HJ2 EQV) as (CORE2 & CELLS2 & NPk & LPk).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _).
destruct (kk_refuse_cnt mcc (line + 1) b) as (Cr & Co & Ck).
pose proof (mf_loop_next v Wc mem2 mcc (Some gi) line p rest (m_refuse mcc (line + 1) b) (Some gi)
  (LPk mcc (Some gi) line p rest LOOP) Hne ltac:(lia) ltac:(lia) Ck (mf_cur_ok_refuse mcc (Some gi) (line + 1) b LCUR))
  as LOOP2.
destruct (mf_break_snd rest) as (_ & Bl & _). specialize (Bl Hne).
apply (KD v lyc Sc Wc regs2 mem2 md2 pos (m_refuse mcc (line + 1) b) (Some gi) (line + 1) (mf_next p rest)
  (mf_rest rest) CX LS FRM CORE2 CELLS2 RA2).
- unfold mf_rest. lia.
- exact LOOP2.
- exact FIN.
- exact (NPk _ NP).
- exact R27.
- exact R20.
Qed.

(* 0x86c18 / 0x86b00 -> KDONE *)
Lemma kk_after : forall n pc, pc = KK_AMISS \/ pc = KK_AHIT -> MF_KDONE_stmt B n -> KK_AF_stmt B pc n.
Proof.
intros n pc Hpc KD. unfold KK_AF_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest b CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP R20.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _).
pose proof (mf_cur_ok_refuse mcc (Some gi) (line + 1) b LCUR) as LCUR'.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON (m_refuse mcc (line + 1) b) (Some gi) CX CORE LCUR')
  as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON (m_refuse mcc (line + 1) b) mcc (Some gi) line p rest
  CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON (m_refuse mcc (line + 1) b) (Some gi) np [] pc
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
assert (LREG : forall (rr : bvmap 5 word) R,
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : Z => sv_eqb (sr_get R (Z_to_bv 5 r)) (sr_get sr_mf (Z_to_bv 5 r)))
    [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 25; 27] = true ->
  mf_regs_at B v lyc pos rr /\ getr rr 27 = w64 (line + 1)).
{ intros rr R HR HC.
  pose proof (kk_pres_l E R regs1 v lyc pos (Some gi) np [] rr _ eq_refl RB HR HC) as P.
  split.
  - apply (mf_regs_at_of B v lyc pos regs1 rr RA);
      [ exact (P 2 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) | exact (P 3 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) | exact (P 4 ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
      | exact (P 8 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) | exact (P 9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) | exact (P 18 ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
      | exact (P 23 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) | exact (P 24 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) | exact (P 19 ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
      | exact (P 22 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) | exact (P 25 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ].
  - rewrite <- R27. exact (P 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
destruct Hpc as [-> | ->].
- (* 0x86c18 `li s4,511`, then KDONE *)
  assert (HS : st_ok_pi SEGS VAL E (mkSS KK_AMISS sr_mf [] None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KK_AMISS)) memc (seg_rom SEGS))))
    by exact (st_ok_pi_submem E (ss_mf KK_AMISS true true [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _)
      eq_refl).
  clear HS0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KDONE.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  destruct (LREG (ms_regs ms) _ (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS) ltac:(vm_compute; reflexivity))
    as (RA2 & R27').
  assert (R20' : getr (ms_regs ms) 20 = w64 511).
  { rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 20%bv HS).
    lazymatch goal with |- sv_denot _ (sr_get ?R ?r) = _ =>
      let e := eval vm_compute in (sr_get R r) in change (sr_get R r) with e end.
    reflexivity. }
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with MF_KDONE by (unfold MF_KDONE, AF_m_file; reflexivity) end.
  exact (kk_kdone_of n v lyc Sc Wc memc mdc pos mcc gi line p rest b (ms_regs ms) (ms_mem ms) mdq KD CX LS FRM CORE
    CELLS Hn Hne LOOP FIN NP HJ EQV RA2 R27' R20').
- (* 0x86b00 `j 0x86c1c`: KDONE, s4 = 511 already *)
  specialize (R20 eq_refl).
  assert (HS : st_ok_pi SEGS VAL E (mkSS KK_AHIT sr_mf [] None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KK_AHIT)) memc (seg_rom SEGS))))
    by exact (st_ok_pi_submem E (ss_mf KK_AHIT true true [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _)
      eq_refl).
  clear HS0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KDONE.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  destruct (LREG (ms_regs ms) _ (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS) ltac:(vm_compute; reflexivity))
    as (RA2 & R27').
  assert (R20' : getr (ms_regs ms) 20 = w64 511).
  { rewrite <- R20.
    exact (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) [20] eq_refl RB
      (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS) ltac:(vm_compute; reflexivity) 20 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with MF_KDONE by (unfold MF_KDONE, AF_m_file; reflexivity) end.
  exact (kk_kdone_of n v lyc Sc Wc memc mdc pos mcc gi line p rest b (ms_regs ms) (ms_mem ms) mdq KD CX LS FRM CORE
    CELLS Hn Hne LOOP FIN NP HJ EQV RA2 R27' R20').
Qed.
End e.
End f.
End d.

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
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
Let RUNTO := paj_run_to B LAWS.

(* KK_R1 with a0 = 0: a key other than "knock", refused at 0x86c14, then KDONE *)
Lemma kk_r1_miss : forall n, (forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n) ->
  forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  mf_regs_at B v lyc pos regs1 ->
  (length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
  mf_fin (m_refuse mcc (line + 1) false, Some gi) line rest = mf_final v ->
  getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
  getr regs1 10 = w64 0 ->
  mf_at B v Wc regs1 memc mdc KK_R1.
Proof.
intros n KD v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_submem E (ss_mf KK_R1 true true [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _)
  eq_refl) as HS1.
clear HS0.
(* a0 = 0 *)
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
clear HS1.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
paj_run_to_tok RUNTO HS HJ SHOK Bspan KK_RMISS.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ eapply (kk_pres E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
  - vm_compute. reflexivity. }
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _ & _ & R25).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
(* a0 = s9 = c, a1 = s11 = line + 1 *)
assert (Q10 : getr (ms_regs ms) 10 = w64 (mv_c v)).
{ rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 10%bv HS).
  lazymatch goal with |- sv_denot _ (sr_get ?R ?r) = _ =>
    let e := eval vm_compute in (sr_get R r) in change (sr_get R r) with e end.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 25 (Z_to_bv 5 25) eq_refl). exact R25. }
assert (Q11 : getr (ms_regs ms) 11 = w64 (line + 1)).
{ rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ ms 11%bv HS).
  lazymatch goal with |- sv_denot _ (sr_get ?R ?r) = _ =>
    let e := eval vm_compute in (sr_get R r) in change (sr_get R r) with e end.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl). exact R27. }
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
pose proof (NPk np NP) as NP'.
assert (HKEPT : (length (mc_kept (m_refuse mcc (line + 1) false)) <= length (mc_kept (mf_final v)))%nat)
  by exact (mf_kept_le_refuse mcc (line + 1) false (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) false LCUR) FIN).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RMISS by (unfold KK_RMISS, AF_m_file; reflexivity) end.
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc mcc false
  (Some gi) line p rest np KK_RMISS CX LS FRM (mf_corek_of_core B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc CORE')
  CELLS' NP' Q2 Q3 Q4 Q8 LOOP' Hne eq_refl Hk0 ltac:(vm_compute; reflexivity) ltac:(unfold KK_RMISS, AF_m_file; lia)
  Q10 Q11 HKEPT).
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfx LS2 CORE2 CELLS2 NP2 LOOP2 HPr.
assert (Ely : ly2 = lyc) by (destruct LS as [E1 _]; destruct LS2 as [E2 _]; congruence). subst ly2.
assert (RA2 : mf_regs_at B v lyc pos regs2)
  by exact (mf_regs_keep B v lyc pos (ms_regs ms) regs2 (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc) HPr).
replace (KK_RMISS + 4) with KK_AMISS by (unfold KK_RMISS, KK_AMISS; lia).
apply (kk_after (fx := fx1) B VOBJS n KK_AMISS (or_introl eq_refl) (KD fx1) v lyc S2 W2 regs2 mem2 md2 pos mcc gi
  line p rest false CX LS2 (fxrel_frm0 fx fx1 FRM Hfx) CORE2 CELLS2 RA2 Hn Hne LOOP2 FIN).
- transitivity (getr (ms_regs ms) 27); [exact (HPr 27 ltac:(unfold acallee_saved; lia))|].
  transitivity (getr regs1 27); [exact (HPc 27 ltac:(unfold acallee_saved; lia)) | exact R27].
- exact NP2.
- intros E'. unfold KK_AMISS, KK_AHIT in E'. lia.
Qed.
End e2.
End f2.
End d2.
