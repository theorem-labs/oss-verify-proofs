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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 914 of its 958 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_hdrb.v, with its module paths and module names changed; 29 of its 62 lines of code are new or changed and 925 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3): the segment S_MF_KEYA of its walk
   (m_file_m.v: `forall n, MF_TAIL_F B n -> MF_KDISP_F B n -> MF_KEY_F B n`), chained from the seven pieces of this
   lane. No instruction is executed here. KEY 0x8661c -> KDISP 0x86714, or -> TAIL through the refusal 0x867dc.
     mf_keya_k.v   kb_key   : KB_RMC_stmt n -> MF_KEY_stmt n        the memchr call 0x86624
     mf_keya_rmc.v kb_rmc   : KB_REF_stmt n -> KB_S1_stmt n -> KB_RMC_stmt n   0x86628-0x86654, the two refusal
                                                                              tests, the four scratch stores
     mf_keya_r.v   kb_ref   : MF_TAIL_F n -> KB_REF_stmt n          m_refuse 0x867dc, then 0x867e0-0x867e8 to TAIL
     mf_keya_s.v   kb_s1    : KB_S2_stmt n -> KB_S1_stmt n          strip(&k, &ke) 0x86658
                   kb_s2    : KB_Q_stmt n -> KB_S2_stmt n           strip(&v, &ve) 0x86664
     mf_keya_q.v   kb_quote : KB_U_stmt n -> KB_Q_stmt n            the quotes 0x86668-0x866e8
     mf_keya_u.v   kb_u     : MF_KDISP_stmt n -> KB_U_stmt n        low.i marked usable 0x866ec-0x86710
   The segment's callee hypotheses (the image-B m_file segment table section 6): MemchrDef.amemchr_realizesM (0x86624), strip_contract
   (0x86658, 0x86664), m_refuse_contract (0x867dc); with them the shared step files' own hypotheses: VOBJS (the
   listing's object values, m_file_sd.v), MCROM (musl memchr's constant window is read-only image bytes,
   m_file_memchr.v), and SIGP / SSP / RELRO, which m_file_rf.v's mf_refuse_step asks of every m_refuse site.
   A walk lane of the image-B m_file-family owner's G2B. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_refuse_c strip_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_keya_d mf_keya_u mf_keya_r mf_keya_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_keya_q mf_keya_s mf_keya_rmc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
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
(* the listing's object values (m_file_sd.v's literal bridge) *)
Hypothesis VOBJS : seg_val_objs.
(* the three callee contracts the segment's calls need, at every FP state (the image-B m_file segment table section 6) *)
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstB.memchr_loA SegInstB.memchr_hiA
    (SIGMA SS___interceptor_trampoline_memchr).
Hypothesis STRIP : forall fx0 : YK11.FPState,
  strip_contract (fx := fx0) SEGS B (BASE + AF_strip) SegInstB.STK_strip.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
(* the image facts the shared step files ask of every site *)
Hypothesis MCROM : memchr_rom_fact SEGS B.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.

Theorem S_MF_KEYA_ok : S_MF_KEYA (rc := rc) (SK := SK) (PI := PI) B.
Proof.
intros n TL KD fx0.
pose proof (kb_ref (fx := fx0) B SIGP SSP RELRO M_REFUSE n TL) as REF.
pose proof (kb_u (fx := fx0) B VOBJS n (KD fx0)) as U.
pose proof (kb_quote (fx := fx0) B VOBJS n U) as Q.
pose proof (kb_s2 (fx := fx0) B SIGP STRIP n Q) as S2.
pose proof (kb_s1 (fx := fx0) B SIGP STRIP n S2) as S1.
pose proof (kb_rmc (fx := fx0) B VOBJS n REF S1) as RMC.
exact (kb_key (fx := fx0) B AMEMCHR MCROM RELRO n RMC).
Qed.
About S_MF_KEYA_ok. Print Assumptions S_MF_KEYA_ok.
End i.
End h.
End g.
About S_MF_KEYA_ok. Print Assumptions S_MF_KEYA_ok.
