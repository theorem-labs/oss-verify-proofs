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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 90 of its 127 lines of code are new or changed and 416 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the LONG walk of segment A6 of reac_segconf_parse_file's walk,
   `pf_a6_long : forall n, H_REF3 B n -> H_LONG B n` (lib/A/Prog/pf_pieces.v:415-445; S_A6 :736-739).
   Segment A6's proof (its LONG walk), 2026-10-30. pf_a6_r.v proves H_REF3 (the refuse call at 0x87e74) and
   pf_a6.v composes pf_a6_holds : S_A6 B from both.

   The code (dis/reac_segconf_parse_file.fuzz_segconf.asan.s lines 239-257), 22 instructions 0x87e2c .. 0x87e70:
     0x87e2c mv a0, s9 ; 0x87e30 ld a1, 0xa8(s1) ; 0x87e34 jal the strspn trampoline (returns at 0x87e38)
     0x87e38 .. 0x87e70  the span test, check #3 and the '[' mask, the refuse arguments (pf_a6_l_a.v)
   then the cut REF3 at 0x87e74 (F_long, 511, cur' = pfA_facts.r_line_long_rest's choice).
   The walk: pf_a6_l_q.v's a6l_seed0 at LONG (slot 0xa8 = the set " \t\r"); the plain run to the jal (PaCallRun.v
   paj_run_shc), which writes nothing; pf_base at the call state (the run's journal and callee-saved registers);
   the call by pf_a6_l_c.v's a6l_strspn_step (RtString.astrspn_realizes through PaArt.aj_art_at, pf_base again
   by pf_a5_k.v's a5_move0); the line's spine kept across it (its bytes lie below alloc_ceiling); then
   pf_a6_l_a.v's a6l_after from 0x87e38 to H_REF3.

   Section hypotheses (pf_pieces.v's list for A6, the strspn row; no other):
     TL      PALib B, the listing's walk record (aj_art_at's errno cell, pal_env)
     STRSPN  RtString.astrspn_realizes at pa_sigma SS___interceptor_trampoline_strspn, gotwA, guardA, at every FP
             state (the interceptor owner's interface row 2)
   No SSPX, VRO, ROMV, OBJ or SIGP: strspn's guard cells come from pf_obj's sa_ssp, rt_rom_view from a5_rom, pf_base
   after the call from a5_move0, and no step reads a listing object or calls a program function. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_k pf_a6_k pf_a6_l_q pf_a6_l_c pf_a6_l_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the run to the call writes nothing: the seed's one region is read-only *)
Local Ltac a6l_awr0 := lazymatch goal with |- awr_ok ?sg ?b ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg b Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the listing's walk record: the errno cell aj_art_at keeps apart (trim_s.v:124-127) *)
Hypothesis TL : PALib B.
(* the interceptor owner's interface row 2 at the listing's strspn trampoline (pf_pieces.v:669) *)
Hypothesis STRSPN : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strspn) gotwA guardA.

(* the line's spine across the call: the block c and cur_name lie below alloc_ceiling *)
Lemma a6l_keep_st : forall v pos lyc Sc Wc rX memc mdc sc (mem2 : word -> option byte) cf cur nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW Wc mem2 a = rdW Wc memc a) ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_st v pos (rdW Wc mem2) cf cur nm k.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc mem2 cf cur nm k HB HK ((bs & Hbs & Henc) & HC & (f & Hf & Hfe) & HN).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & _ & _ & G & _).
pose proof (a5_text B v pos lyc Sc Wc rX memc mdc sc HB) as (_ & _ & _ & _ & _ & HHC).
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HHC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (bc & mc & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
pose proof asan_consts as (AC1 & _).
split; [|split; [exact HC|split; [|exact HN]]].
- exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
  rewrite HK; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia | left; unfold seg_spec.SEG_C_SIZE in *; lia].
- exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as [Hl _].
  rewrite HK; [exact (Hf i Hi) | unfold PF_O_CN; lia | left; unfold PF_O_CN; lia].
Qed.

Theorem pf_a6_long : forall n, H_REF3 B n -> H_LONG B n.
Proof.
intros n HREF3. unfold H_LONG.
intros v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HINV.
destruct HINV as (HB & HMID & HST & HL & HRG).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
pose proof HB as (HCX & (HJ & _) & _).
pose proof HMID as (Ho & _ & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
assert (R25 : getr rX 25 = w64 (p_t v + Z.of_nat o))
  by exact (a5_rg_get rX _ 25 (p_t v + Z.of_nat o) HRG
    ltac:(unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right]))).
(* the seed at LONG and the plain run to the jal 0x87e34 *)
pose proof (a6l_seed0 B v pos lyc Sc Wc rX memc mdc HB) as HS.
assert (HEI : img_env VAL A_LIM (a6l_E rX [])) by apply a6l_E_img.
change (cfg_at SEGS (BASE + PF_LONG) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_LONG)) memc (seg_rom SEGS)) mdc).
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ a6l_awr0. }
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & Ha). vm_compute in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ |- *. clear HF HFr HG.
(* the callee-saved registers are the cut's *)
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [] HS (a6l_E_agree rX []) ltac:(vm_compute; reflexivity)) as HPR.
assert (HBc : pf_base B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE).
{ apply (a6l_base_at B v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdq PF_SC_LINE HB HJ).
  exact (a5_rg_pres rX (ms_regs ms) (a5_FI B v) HPR (a5_FI_cs B v) HFI). }
(* the call's registers: ra = 0x87e38, a0 = at = t + o, a1 = the set's literal *)
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
assert (C1r : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (PF_LONG + 12))).
{ rewrite Q1. unfold PF_LONG, AF_reac_segconf_parse_file. reflexivity. }
assert (C10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (p_t v + Z.of_nat o)).
{ rewrite Q10, (a6l_ew_reg rX [] 25 (Z_to_bv 5 25) eq_refl). exact R25. }
assert (C11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (seg_litA_rc [SP; TAB; CR])).
{ rewrite Q11, a6l_lit_set. reflexivity. }
assert (HRA : YK0s.ret_ok (Z_to_bv 64 (BASE + (PF_LONG + 12)))).
{ apply ret_ok_codeptr_v; [unfold PF_LONG, AF_reac_segconf_parse_file; lia | reflexivity]. }
(* the strspn call (0x87e34), back at 0x87e38 *)
apply (a6l_strspn_step B TL STRSPN v pos lyc Sc Wc (ms_regs ms) memc mdq (Z_to_bv 64 (BASE + (PF_LONG + 12))) o _
  HBc Ho C1r HRA C10 C11).
intros regs2 mem2 md2 HB2 HP2 R10' HKM.
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (PF_LONG + 12))) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + (PF_LONG + 12)) regs2 mem2 md2).
apply (a6l_after B n HREF3 v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d HB2 HMID).
- exact (a6l_keep_st v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE mem2 cf cur nm _ HBc HKM HST).
- exact HL.
- apply (a5_rg_pres rX regs2 _ HPR2); [|exact HRG].
  apply Forall_app. split; [apply a5_RL_cs|]. apply Forall_app. split; [apply a5_RM_cs|].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
- exact R10'.
Qed.

End e.
End f.
End d.
