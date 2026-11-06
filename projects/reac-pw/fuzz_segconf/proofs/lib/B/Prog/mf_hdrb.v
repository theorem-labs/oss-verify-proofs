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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_hdrb.v, with its module paths and module names changed; 24 of its 72 lines of code are new or changed and 910 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), the segment S_MF_HDRB
   of its walk (HFIND 0x865c0 -> TAIL 0x86820; the image-B m_file segment table section 5, the image-B m_file cut map
   section 4): `S_MF_HDRB_ok : S_MF_HDRB B` of lib/B/Prog/m_file_m.v, chained from the pieces of mf_hdrb_5.v ..
   mf_hdrb_10.v over the inner cut statements of mf_hdrb_2.v. A walk lane of the image-B m_file-family owner's G2B. proves function
   m_file (one segment of its image-B walk; the assembly lane proves m_file_contract by m_file_contract_of_parts).
   ADAPTED from image A's lane of the same segment (the image-A m_file-family lane, commit d8beabc2758c,
   and its piece commits: lib/A/Prog/m_file_s_hdrb_1..7.v and m_file_s_hdrb.v) at image B's numbers, plus the four UBSan
   trap branches.
   THE CHAIN (each arrow one lemma; mf_hdrb_2.v's header describes the code of each path):
     TAIL n  -> JOIN    hb5_join   (0x86ba0: the trap 0x86ba4, cur = g, g->gen = c->gen, s10 = 152(s1))
     JOIN    -> RREF1   hb5_rref1  (0x86618 `j 0x86ba0`)
     JOIN    -> RMCPY   hb5_rmcpy  (0x86b9c `li s4,511`)
     RMCPY   -> RMSET   hb6_rmset  (0x86b8c: the checked memcpy of the name)
     RMSET   -> NEWE    hb7_newe   (0x86b54: c->n = n + 1, the traps 0x86b68 / 0x86b74, the checked memset)
     TAIL n  -> RREF2   hb5_rref2  (0x86b4c: cur = NULL, s10 = 152(s1))
     NEWE, RREF2 -> NFIND   hb8_nfind  (0x86b04: c->n, the test against 32, overflow + 1 and m_refuse)
     JOIN, RREF1, NFIND -> RFIND   hb9_rfind  (0x865cc: m_find's result, the trap 0x865d4, the gen test, m_refuse)
     RFIND   -> HFIND   hb10_hfind (0x865c0: m_find(c, name, |name|))
   UBSAN TRAPS of the segment (all to the `unimp` 0x86e84), each refuted at its branch: 0x865d4 g & 3 (hb9_rfind:
   g = c + 256 i, c mod 16 = 0, m_find's post), 0x86b68 n >= 33 (hb7_newe: 0 <= n < 32), 0x86b74 ~c < 256 n (hb7_newe:
   c + 9236 <= 2^64, mf_core's sa_addr), 0x86ba4 g & 3 (hb5_join: g = c + 256 i). The seven instrumented checks
   (0x865e8, 0x865f4, 0x86b0c, 0x86b2c, 0x86b54, 0x86bac, 0x86bc4) are decided by the token executor from the
   block's shadow entry (m_file_sd.v's mf_she_blk) and the entry's (mf_she_at); no error path is reached.
   Section hypotheses: VOBJS (the seed's literal bridge), SIGP / SSP / RELRO (the image facts m_file_k.v and
   m_file_rf.v take), the callees m_find_contract, m_refuse_contract, and the runtime's checked memset / memcpy
   (aintrin_realizes OSet / OCpy), each at every FP state at its listing term. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YL08 YN1f YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegObj SegGlob SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m
  mf_hdrb_2 mf_hdrb_5 mf_hdrb_6 mf_hdrb_7 mf_hdrb_8 mf_hdrb_9 mf_hdrb_10.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

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
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_FIND : forall fx0 : YK11.FPState, m_find_contract (fx := fx0) SEGS B (BASE + AF_m_find)
  SegInstB.STK_m_find SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).

Lemma S_MF_HDRB_ok : S_MF_HDRB (rc := rc) (SK := SK) (PI := PI) B.
Proof.
unfold S_MF_HDRB. intros n HT.
assert (JN : MFB_JOIN_F B n) by (eapply hb5_join; eauto).
assert (R1 : MFB_RREF1_F B n) by (eapply hb5_rref1; eauto).
assert (RM : MFB_RMCPY_F B n) by (eapply hb5_rmcpy; eauto).
assert (RS : MFB_RMSET_F B n) by (eapply hb6_rmset; eauto).
assert (NE : MFB_NEWE_F B n) by (eapply hb7_newe; eauto).
assert (R2 : MFB_RREF2_F B n) by (eapply hb5_rref2; eauto).
assert (NF : MFB_NFIND_F B n) by (eapply hb8_nfind; eauto).
assert (RF : MFB_RFIND_F B n) by (eapply hb9_rfind; eauto).
eapply hb10_hfind; eauto.
Qed.
End i.
End h.
End g.

About S_MF_HDRB_ok.
Print Assumptions S_MF_HDRB_ok.
