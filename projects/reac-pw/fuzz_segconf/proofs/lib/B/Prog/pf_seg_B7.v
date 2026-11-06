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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 327 of its 371 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a7_w3_c.v, with its module paths and module names changed; 922 of its 1017 lines of code are new or changed and 276 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B7_cl.v, with its module paths and module names changed; 36 of its 68 lines of code are new or changed and 985 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B7 of
   reac_segconf_parse_file's walk, the header branch -- HDR 0x883b4 -> TAIL 0x88600 (through CLR 0x885fc) or
   SEG 0x88ca0, HREF 0x885ec -> TAIL, REFTL 0x887cc -> TAIL, CLR 0x885fc -> TAIL. 101 instructions, the inline
  checks B#8 (load of close[1]), B#12 (store of the NUL at close), B#20 (load of body[7]), B#21 (load of the
  name's first byte), the UBSan trap branches T10 0x883cc,
   T13 0x884e0, T19 0x88768 (none taken), and eight calls (strchr 0x883bc; trim 0x884e8, 0x8878c;
   strncasecmp 0x88500; strlen 0x887b4; refuse 0x885f8, 0x887d8, 0x88c98).
   The B7 segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B7; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; reuse verdict:
   none released, ADAPTED from the image-A G3 walk owner's image-A segment A7 and the unit owner's UBSan piece walks).

   This file ASSEMBLES the segment. The statement S_B7 is lib/B/Prog/pf_pieces.v's; the five internal cuts
   (CLOSE 0x884cc, UNK 0x88508, CALL 0x885f8, KWOK 0x88764, NONAME 0x88c88) and the four piece statements are
   lib/B/Prog/pf_seg_B7_m.v's; the pieces themselves are proved in pf_seg_B7_ref.v (CLR, CALL, HREF, UNK),
   pf_seg_B7_rt.v (REFTL, NONAME), pf_seg_B7_hdr.v (HDR), pf_seg_B7_cl.v (CLOSE) and pf_seg_B7_kw.v (KWOK),
   over the vocabulary pf_seg_B7_d.v, the pure spine pf_seg_B7_f.v, the interceptor premises pf_seg_B7_r.v,
   the program call sites pf_seg_B7_s.v (VERIFY rule 1j-bis) and the transport kit pf_seg_B7_k.v.

   `S_B7_holds` is the chaining, and it is where the order of the pieces is fixed:
     H_CLR comes straight from HA_TAIL;
     H_CALL from H_CLR at every FP state (refuse returns at another one);
     H_HREF and H_UNK from H_CALL; H_REFTL and H_NONAME from H_CLR;
     H_KWOK from H_UNK, H_NONAME, H_REFTL and HA_SEG; H_CLOSE from H_KWOK and H_UNK;
     H_HDR from H_HREF and H_CLOSE.
   Every cut a call can land on is taken at EVERY FP state, which is why the HA_ forms and not the bare H_
   forms are chained. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegObj SegGlob SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B7_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B7_ref pf_seg_B7_rt
  pf_seg_B7_hdr pf_seg_B7_cl pf_seg_B7_kw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the listing's facts over the walk's abstract instance (lib/B/Prog/SegObj.v) *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* the image-A owner's route A: the stack-protector cells at every AR state, which image B's stage-2 SegRecCells
   discharges (as lib/B/Prog/reac_segconf_parse.v takes it) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
(* the runtime library's record facts at image B (lib/B/Prog/SegPaLib.v) *)
Hypothesis TL : PALib B.
(* the two program callees of B7, at image B's entries and windows, at every FP state *)
Hypothesis REFUSE : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse
  RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
(* the image-A wrapper-layer owner's interface rows, at the listing's trampolines (lib/B/Rt/RtSeg.v rows 6 and 7,
   lib/B/Rt/RtString.v astrlen_realizes) *)
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis ANCASE : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncasecmp).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).

(* the nine pieces give S_B7 *)
Theorem S_B7_holds : S_B7 B.
Proof.
intros f0 n.
assert (ACLR : HA_TAIL B n -> HA_CLR B n)
  by (intros HT f1; apply b7ref_clr_ok; assumption).
assert (ACALL : HA_TAIL B n -> HA_CALL B n)
  by (intros HT f1; apply b7ref_call_ok; first [assumption | exact (ACLR HT)]).
split; [|split; [|split]].
- intros HT HS.
  assert (AHREF : HA_HREF B n) by (intros f1; apply b7ref_href_ok; first [assumption | exact (ACALL HT)]).
  assert (AUNK : HA_UNK B n) by (intros f1; apply b7ref_unk_ok; first [assumption | exact (ACALL HT)]).
  assert (AREFTL : HA_REFTL B n) by (intros f1; apply b7rt_reftl_ok; first [assumption | exact (ACLR HT)]).
  assert (ANON : HA_NONAME B n) by (intros f1; apply b7rt_noname_ok; first [assumption | exact (ACLR HT)]).
  assert (AKWOK : HA_KWOK B n) by (intros f1; apply b7kw_ok; assumption).
  assert (ACLOSE : HA_CLOSE B n) by (intros f1; apply b7cl_ok; assumption).
  apply b7hdr_ok; assumption.
- intros HT. apply b7ref_href_ok; first [assumption | exact (ACALL HT)].
- intros HT. apply b7rt_reftl_ok; first [assumption | exact (ACLR HT)].
- intros HT. apply b7ref_clr_ok; assumption.
Qed.

End a.
