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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 494 of its 542 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_kknock.v, with its module paths and module names changed; 30 of its 64 lines of code are new or changed and 508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/mf_krole.v, with its module paths and module names changed; 67 of its 105 lines of code are new or changed and 26 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; entry BASE + AF_m_file = 0x86140,
   3,608 bytes, class-1 side-stack frame): the image-B walk of m_file, assembled from its 13 segment lemmas by
   lib/B/Prog/m_file_m.v's m_file_contract_of_parts (no instruction is executed here). Owner: the image-B m_file-family owner (group G2B).
   proves function m_file (reuse search: rule 24, by name and image-B address over the four shared refs; the result
   is recorded with the commissioning brief): none released; written new, its segments adapted from the image-A m_file-family
   lane's image-A segment walks and the segconf porter's UBSan m_file walk.
   The contract is image B's copy lib/B/Prog/m_file_c.v of the image-A owner's FINAL text (6f783602b5e3; the image-B kit derivation 694f3575dda2),
   accepted for image B by the image-B contract review 2026-10-30T17:19Z, at SegInstB's values (STK_m_file 8,592).
   THE SEGMENTS (cut statements m_file_m.v; the image-B m_file cut map and segment table):
     ENTRY mf_entry.v, FRONT mf_front.v, LONGP mf_longp.v, HDRA mf_hdra.v, HDRB mf_hdrb.v, KEYA mf_keya.v,
     KROLE mf_krole.v, KMOD mf_kmod.v, KIGNP mf_kignp.v, KKNOCKP mf_kknockp.v, KDONE mf_kdone.v, TAIL mf_tail.v,
     EXIT mf_exit.v; shared steps m_file_k / _iq / _sn / _rf / _fold / _memchr / _strip.v.
   Section hypotheses: the callee contracts and runtime entries of m_file's calls (each at every FP state where the
   callee's text has one) and the image / record facts the segments take (seg_val_objs, seg_sig_prog, PALib, PALibF,
   the model laws, seg_img_facts, the stack-protector cell, the side-stack frame laws); the close discharges them.
   RELRO is derived here from seg_img_facts' cif_relro_img. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG05 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString RtSeg RtPFSeg RtPFCmd RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegGlob SegPa SegPaLib PaLibF SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
  ieq_c fold_c strip_c m_find_c m_refuse_c fuzz_catalogue_row_c m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require
  mf_entry mf_front mf_longp mf_hdra mf_hdrb mf_keya mf_krole mf_kmod mf_kignp mf_kknockp mf_kdone mf_tail mf_exit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
(* image, listing and record facts *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis IMG : SegRecBase.seg_img_facts SEGS B.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
(* the side-stack frame (class 1) *)
Hypothesis SM1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* runtime entries and wrappers, at the listing's call targets *)
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis STRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strchr).
Hypothesis STRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstB.memchr_loA SegInstB.memchr_hiA
    (SIGMA SS___interceptor_trampoline_memchr).
Hypothesis MCROM : memchr_rom_fact SEGS B.
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
(* the program callees, at BASE + AF_<F> and SegInstB's values *)
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis M_FIND : forall fx0 : YK11.FPState,
  m_find_contract (fx := fx0) SEGS B (BASE + AF_m_find) SegInstB.STK_m_find SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
Hypothesis ROW : forall fx0 : YK11.FPState, fuzz_catalogue_row_contract (fx := fx0) SEGS B
  (BASE + AF_fuzz_catalogue_row) SegInstB.STK_fuzz_catalogue_row SegInstB.RLO_A SegInstB.RHI_A SegInstB.catA.
Hypothesis STRIP : forall fx0 : YK11.FPState,
  strip_contract (fx := fx0) SEGS B (BASE + AF_strip) SegInstB.STK_strip.
Hypothesis FOLD : forall fx0 : YK11.FPState, fold_contract (fx := fx0) SEGS B (BASE + AF_fold) SegInstB.STK_fold.

(* RELRO, as the segments state it, from the record's cif_relro_img (SegInstB.RLO_A / RHI_A are SegGlob's bounds) *)
Lemma mf_relro : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Proof.
intros a Ha. apply (SegRecBase.cif_relro_img _ _ IMG a).
assert (E1 : SegInstB.RLO_A = SEG_RLO) by (vm_compute; reflexivity).
assert (E2 : SegInstB.RHI_A = SEG_RHI) by (vm_compute; reflexivity).
rewrite <- E1, <- E2. exact Ha.
Qed.

Theorem m_file_walkB : forall fx0 : YK11.FPState,
  m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) SegInstB.STK_m_file SegInstB.RLO_A SegInstB.RHI_A
    SegInstB.seg_litA_fz SegInstB.wordsA SegInstB.rolesA SegInstB.catA SegInstB.gotwA SegInstB.guardA.
Proof.
pose proof mf_relro as RELRO.
apply (m_file_contract_of_parts B).
- eapply mf_entry.S_MF_ENTRY_ok; eassumption.
- eapply mf_exit.S_MF_EXIT_ok; eassumption.
- eapply mf_tail.S_MF_TAIL_ok; eassumption.
- eapply mf_front.S_MF_FRONT_ok; eassumption.
- eapply mf_longp.S_MF_LONGP_ok; eassumption.
- eapply mf_hdra.S_MF_HDRA_ok; eassumption.
- eapply mf_hdrb.S_MF_HDRB_ok; eassumption.
- eapply mf_keya.S_MF_KEYA_ok; eassumption.
- eapply mf_krole.S_MF_KROLE_ok; eassumption.
- eapply mf_kmod.S_MF_KMOD_ok; eassumption.
- eapply mf_kignp.S_MF_KIGNP_ok; eassumption.
- eapply mf_kknockp.S_MF_KKNOCKP_ok; eassumption.
- eapply mf_kdone.S_MF_KDONE_ok; eassumption.
Qed.
End i.
End h.
End g.

About m_file_walkB.
Print Assumptions m_file_walkB.
