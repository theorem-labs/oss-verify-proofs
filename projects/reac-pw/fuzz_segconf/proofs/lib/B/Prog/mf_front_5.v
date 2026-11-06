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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 718 of its 785 lines of code are new or changed and 386 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_FRONT, piece 5 (cl): one pass
   of the comment loop 0x86430-0x864b0 (the image-B m_file segment table section 2; B.s lines 190-222, the trap 0x86e84 at line 851,
   the error-path calls 0x86ed0 / 0x86ed8 at lines 870-873), and by induction every index of it: `fr_cl`, the
   statement `FR_ST_stmt B n -> forall i, FR_CL_stmt B n i` of lib/B/Prog/mf_front_m.v. A walk lane of
   the image-B m_file-family owner's G2B (a piece worker, on a working branch).
   ADAPTED from image A's lib/A/Prog/m_file_s_front_cl.v (the image-A m_file-family lane, commit
   ae5120b8b0ec): the same one-pass state of the registers and the one or two text bytes, at image B's registers, plus
   the frame cell 168(s1) the cut exit stores (image A keeps the cut in a register).

   What the code does at index i < L (FR_CL: s10 = a1 = p + i, a3 = -i, a0 = p + L, a6 = 0x20; L = |mf_line rest|):
     0x86430-0x8643c  the instrumented check of the byte at p + i (a load of the shadow byte at ((p + i) >> 3) + the
                      shadow base s2 and a compare; its slow path 0x86498-0x864a0 and the error path 0x86ed0, a call of
                      errpath_load1, are not reached: the token run turns the check into the obligation `p + i is
                      addressable', which mf_loop's sa_addr p (|rest| + 1) gives, f5_rad)
     0x86440          `lbu a2,0(s10)`: the byte b_i = nth i (mf_line rest) 0 (mf_loop's sa_str, f5_text_facts)
     0x86444-0x86450  b_i = ';' (59) or '#' (35)?  no: 0x86484 (no cut at i: fr_cut_at_nomark)
     0x86454          a mark: `beqz a3` -> 0x864b0 when i = 0 (a cut at 0: fr_cut_at0)
     0x8645c          i > 0: `beq s10,a2` (a2 = 1) -> unimp 0x86e84 (UBSan: the pointer s10 - 1 is null): not taken,
                      decided by the token run from the fact s10 = p + i >= 4096 (atom 26, PTR 0; p is in a heap block,
                      f5_text_facts)
     0x86460-0x86470  the instrumented check of the byte at p + i - 1 (slow path 0x864a4-0x864ac, error path 0x86ed8,
                      not reached: the obligation `p + i - 1 is addressable', from the same sa_addr)
     0x86474-0x86480  `lbu a2,-1(s10)`: b_{i-1} = ' ' (a6 = 32) or '\t' (9)? yes: 0x864b0 (fr_cut_atS); no: 0x86484
                      (fr_cut_at_nosp)
     0x86484-0x86490  s10, a1 += 1, a3 -= 1; s10 <> a0: FR_CL (S i)
     0x86494          else `j` FR_ST 0x864b4 (no cut in the line: C = L, fr_cut_all; 168(s1) already holds p + L)
     0x864b0          `sd s10,168(s1)`: 168(s1) = p + i = p + C (fr_cut_at_first), then FR_ST 0x864b4
   The pass's state (f5_text1 / f5_text0, f5_slot): the one or two text bytes at s10 (atom 26) as atoms 32 / 33, and the
   writable frame cell [s1 + 168, s1 + 176) at s1 (atom 9) holding a0 (atom 10) = p + L. The head's facts are carried
   by m_file_k.v's mf_keep_run_s over the written set [s1 + 168, s1 + 176) (f5_ctx_run), 168(s1) is read off the
   final state's cell region. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_k mf_front_mdl mf_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the pass's state: s10 (x26) is the cursor q = p + i, the bytes q[0] (atom 32) and, for i > 0, q[-1] (atom 33);
   the frame cell 168(s1) (s1 = x9) holds a0 (x10) = p + L until the cut exit stores s10 there *)
Definition f5_text1 : YP09.region := YP09.mkRegion (Some 26%nat) (-1) 1 0 0
  [YP09.mkChunk (-1) (CVal 1 (SOff 33 0)); YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition f5_text0 : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition f5_slot : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 168 176 [YP09.mkChunk 168 (CVal 8 (SOff 10 0))].
Definition f5_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (11%nat, PTR 0); (26%nat, PTR 0); (18%nat, mkAF SB SB 0);
           (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] [].
(* the registers a pass leaves as they were and the head's facts (mf_regs_at, fr_short) name *)
Definition F5_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 27]%bv.

(* an atom of the environment, offset by k (image A's m_file_s_front_g.v fr_U_atom_off) *)
Lemma f5_U_atom_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 ->
U E (SOff n k) = v + k.
Proof.
intros E n v k Hn Hv Hvk. rewrite U_SOff, Hn, unsigned_lit_small by exact Hv. apply zcanon_id. unfold M64. lia.
Qed.
(* range_addressable reads only the shadow bytes of its range *)
Lemma f5_ra_eq : forall (rd rd' : Z -> option Z) Bx a n,
(forall x, a <= x < a + n -> rd' (shadow_of_addr Bx x) = rd (shadow_of_addr Bx x)) ->
range_addressable rd Bx a n -> range_addressable rd' Bx a n.
Proof. intros rd rd' Bx a n Hk H x Hx. rewrite (Hk x Hx). exact (H x Hx). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the written set of a pass: the frame cell 168(s1) *)
Definition f5_rw (v : mfv) (a : Z) : Prop := mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 176.

(* the cell 168(s1) as the final state's cell region shows it *)
Lemma f5_slot_of_region : forall E (m : word -> option byte) s1 cs e x,
region_ok SEGS E m (YP09.mkRegion (Some 9%nat) 168 176 168 176 cs) -> bv_unsigned (ew E 9) = s1 ->
In (YP09.mkChunk 168 (CVal 8 e)) cs -> U E e = x -> val_mem SEGS m (s1 + 168) 8 x.
Proof.
intros E m s1 cs e x HR Hb Hin Hx.
pose proof (@field_of_region_any SEGS E m 9 s1 cs 168 176 168 176 168 8%N e HR Hb Hin ltac:(cbn; lia)) as V.
change (N.to_nat 8) with 8%nat in V. change (8 * Z.of_N 8) with 64 in V.
rewrite <- Hx. unfold U. rewrite Z.mod_small in V; [exact V|].
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as HR'. change (bv_modulus 64) with (2 ^ 64) in HR'. exact HR'.
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation JE v pos ly S W mem md :=
  (ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] ly S W mem md 0).

(* the text left at the head: inside a live heap block, the line's bytes as the reader sees them, and the text with
   its NUL addressable (image A's fr_text_facts, from m_file_k.v's mf_loop_blk) *)
Lemma f5_text_facts : forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n,
fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
4096 <= p /\ p + Z.of_nat (length rest) + 1 <= alloc_ceiling /\
(forall k, (k < length (mf_line rest))%nat -> rdW Wc memc (p + Z.of_nat k) = Some (nth k (mf_line rest) 0)) /\
(forall k, (k < length (mf_line rest))%nat -> 0 <= nth k (mf_line rest) 0 < 256) /\
range_addressable (rdW Wc memc) SHADOW_OFF p (Z.of_nat (length rest) + 1).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX.
destruct CTX as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & EQ).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP)
  as (b & m & Hb & Hb1 & Hb2 & _).
pose proof CORE as (HJ & _). pose proof (proj1 HJ) as HAR.
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hb) as (_ & B4096 & Bceil & _).
destruct LOOP as (Hlr & Hrest & Hp & STR & ADDR & _).
destruct STR as ((ZS & NZ) & TAIL).
destruct ADDR as (_ & _ & _ & RA0 & _).
pose proof (fr_line_len rest) as HLL.
assert (BY : forall k, (k < length (mf_line rest))%nat -> rdW Wc memc (p + Z.of_nat k) = Some (nth k (mf_line rest) 0)).
{ intros k Hk. rewrite <- (fr_line_nth rest k Hk). rewrite (ZS k) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by lia. reflexivity. }
split; [lia|]. split; [lia|]. split; [exact BY|]. split; [|exact RA0].
intros k Hk. destruct (aview_byte SEGS (w_H Wc) memc _ _ (BY k Hk)) as (bb & _ & _ & Hr). exact Hr.
Qed.

(* the frame cells' base s1 at the head: its bounds, the cells writable, s1 and the shadow base in their registers *)
Lemma f5_s1 : forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n,
fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
2 ^ 46 <= mf_s1 (mv_sp v) /\ mf_s1 (mv_sp v) + 216 <= 2 ^ 47 /\ mf_s1 (mv_sp v) mod 32 = 0 /\
alloc_ceiling + 8000 <= mf_s1 (mv_sp v) /\
(mf_s1 (mv_sp v) = mv_sp v - 320 \/ mf_s1 (mv_sp v) = mv_sp v - 336) /\
(forall a, mf_s1 (mv_sp v) + 16 <= a < mf_s1 (mv_sp v) + 216 -> writable_at SEGS (mrestrict (w_H Wc) memc) a) /\
getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 18 = w64 SHADOW_OFF.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX.
destruct CTX as (CX & LS & FRM & CORE & CELLS & RA & _).
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & Hsp).
destruct (mf_sp0 B v CX) as (_ & Hsp47 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof CORE as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
split; [lia|]. split; [lia|]. split; [exact Hs32|]. split; [lia|]. split; [exact Hs1|].
split; [|split; [exact R9 | exact R18]].
intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
Qed.

(* the shadow byte of a text byte is a 64-bit address outside the written set *)
Lemma f5_sh_apart : forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n y,
fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
p <= y < p + Z.of_nat (length rest) + 1 ->
0 <= shadow_of_addr SHADOW_OFF y < 2 ^ 64 /\ ~ f5_rw v (shadow_of_addr SHADOW_OFF y).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n y CTX Hy.
destruct (f5_text_facts v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & _).
destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & Q4 & _).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.div_mod y 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as M.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
unfold shadow_of_addr, f5_rw. rewrite HSB. lia.
Qed.

(* the head's facts across a pass: the reader unchanged outside 168(s1), the registers the facts name kept
   (m_file_k.v's mf_keep_run_s with the written set [s1 + 168, s1 + 176)) *)
Lemma f5_ctx_run : forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n regs2 mem2 md2,
fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short v regs1 memc Wc line p rest ->
mf_slot v memc Wc 176 p ->
JE v pos lyc Sc Wc mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> rdW Wc mem2 a = rdW Wc memc a) ->
(forall r, In r F5_KEPT -> getr regs2 r = getr regs1 r) ->
fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n /\ fr_short v regs2 mem2 Wc line p rest /\
mf_slot v mem2 Wc 176 p.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n regs2 mem2 md2 CTX SH S176 HJ2 K KR.
pose proof CTX as CTX0.
destruct CTX as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & EQ).
destruct SH as (R27 & R20 & NP & HL).
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & _).
destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX0) as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & _).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
assert (RWok : forall a, f5_rw v a -> mf_rw v lyc pos a).
{ intros a Ha. unfold f5_rw in Ha. unfold mf_rw. right; right; right; right; right. lia. }
assert (RWS : mf_rws v (f5_rw v)) by (intros a Ha _; unfold f5_rw in Ha; right; lia).
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ intros i Hi. apply (mf_val_keep Wc Wc memc mem2 (f5_rw v) _ 1 _ K); [rewrite HSB; lia | change (Z.of_nat 1) with 1; rewrite HSB; lia | | exact (VSH i Hi)].
  intros k Hk. change (Z.of_nat 1) with 1 in Hk. unfold f5_rw. rewrite HSB. lia. }
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) mem2) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur)).
{ apply (mf_val_keep Wc Wc memc mem2 (f5_rw v) _ 8 _ K); [lia | change (Z.of_nat 8) with 8; lia | | exact V136].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. unfold f5_rw. lia. }
assert (MC' : sa_mconf (rdW Wc mem2) (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc mem2 (f5_rw v) _ _ K); [lia | unfold seg_spec.SEG_M_SIZE in *; lia | | exact Hmc].
  intros a Ha. unfold f5_rw. unfold seg_spec.SEG_M_SIZE in *. lia. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur mem2 md2 (f5_rw v) MF_LOW_OFF cur mcc
  CX CORE CELLS HJ2 K RWok RWS VSH' V136' MC') as (C1 & C2 & C3).
assert (RA' : mf_regs_at B v lyc pos regs2).
{ apply (mf_regs_at_of B v lyc pos regs1 regs2 RA); apply KR; cbv; tauto. }
assert (NP' : mf_np v mem2 Wc (mf_next p rest)).
{ unfold mf_np, mf_slot in NP |- *.
  apply (mf_val_keep Wc Wc memc mem2 (f5_rw v) _ 8 _ K); [lia | change (Z.of_nat 8) with 8; lia | | exact NP].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. unfold f5_rw. lia. }
assert (S176' : mf_slot v mem2 Wc 176 p).
{ unfold mf_slot in S176 |- *.
  apply (mf_val_keep Wc Wc memc mem2 (f5_rw v) _ 8 _ K); [lia | change (Z.of_nat 8) with 8; lia | | exact S176].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. unfold f5_rw. lia. }
split; [|split; [|exact S176']].
- refine (conj CX (conj LS (conj FRM (conj C1 (conj C2 (conj RA' (conj Hn (conj Hne (conj (C3 _ _ _ _ _ LOOP) EQ))))))))).
- refine (conj _ (conj _ (conj NP' HL))).
  + rewrite (KR 27%bv ltac:(cbv; tauto)). exact R27.
  + rewrite (KR 20%bv ltac:(cbv; tauto)). exact R20.
Qed.

(* a stop at FR_ST: the head's facts carried, 168(s1) = p + C *)
Lemma f5_leaf_st : forall n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest regs2 mem2 md2 x,
FR_ST_stmt B n ->
fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short v regs1 memc Wc line p rest ->
mf_slot v memc Wc 176 p -> JE v pos lyc Sc Wc mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> rdW Wc mem2 a = rdW Wc memc a) ->
(forall r, In r F5_KEPT -> getr regs2 r = getr regs1 r) ->
mf_slot v mem2 Wc 168 x -> x = p + Z.of_nat (fr_C rest) ->
mf_at B v Wc regs2 mem2 md2 FR_ST.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest regs2 mem2 md2 x HST CTX SH S176 HJ2 K KR S168 Hx.
subst x.
destruct (f5_ctx_run v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n regs2 mem2 md2 CTX SH S176 HJ2 K KR)
  as (C1 & C2 & C3).
exact (HST v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest C1 C2 C3 S168).
Qed.
(* a stop at FR_CL j: the head's facts carried, 168(s1) = p + L, the loop's registers *)
Lemma f5_leaf_cl : forall n j v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest regs2 mem2 md2 x,
FR_CL_stmt B n j ->
fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n -> fr_short v regs1 memc Wc line p rest ->
mf_slot v memc Wc 176 p -> JE v pos lyc Sc Wc mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> rdW Wc mem2 a = rdW Wc memc a) ->
(forall r, In r F5_KEPT -> getr regs2 r = getr regs1 r) ->
mf_slot v mem2 Wc 168 x -> x = p + Z.of_nat (length (mf_line rest)) ->
getr regs2 10 = w64 (p + Z.of_nat (length (mf_line rest))) -> getr regs2 16 = w64 0x20 ->
getr regs2 26 = w64 (p + Z.of_nat j) -> getr regs2 11 = w64 (p + Z.of_nat j) -> getr regs2 13 = w64 (- Z.of_nat j) ->
(j < length (mf_line rest))%nat -> (forall k, (k < j)%nat -> cut_at (mf_line rest) k = false) ->
mf_at B v Wc regs2 mem2 md2 FR_CL.
Proof.
intros n j v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest regs2 mem2 md2 x HNX CTX SH S176 HJ2 K KR S168 Hx
  R10 R16 R26 R11 R13 Hj Hcut.
subst x.
destruct (f5_ctx_run v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n regs2 mem2 md2 CTX SH S176 HJ2 K KR)
  as (C1 & C2 & C3).
exact (HNX v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest C1 C2 C3 S168 R10 R16 R26 R11 R13 Hj Hcut).
Qed.

(* ===================== the tactics every pass uses ===================== *)
Ltac f5_agree := let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; repeat rewrite ew_ewset_other by lia; reflexivity.
(* the write goal of a run: the text region is read-only, the cell 168(s1) lies in m_file's stack window *)
Ltac f5_awr v U9 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat first
    [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (YCbq.awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (mf_s1 (mv_sp v) - mv_sp v));
      [ reflexivity
      | lazymatch goal with |- bv_unsigned (ew ?Ex 9%nat) = _ => rewrite (U9 Ex ltac:(f5_agree)); lia end
      | cbn [YP09.r_wlo YP09.r_whi]; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia
      | ] ];
  apply awr_ok_nil.
(* after a run: the reader is the pass's start reader outside 168(s1) (MEQ) *)
Ltac f5_meq U9 :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw ?vv a -> aview _ _ ?m0 a = aview _ _ ?mc a |- _ =>
    let MEQ' := fresh "MEQ" in
    assert (MEQ' : forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw vv a -> aview SEGS H m1 a = aview SEGS H mc a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
      intros a Ha Hn;
      refine (eq_trans (kept_of_frame Ex rs H m0 m1 (f5_rw vv) HFr _ a Ha Hn) (MEQ a Ha Hn));
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hinw := fresh "Hinw" in let Hr := fresh "Hr" in
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (let Hq := fresh "Hq" in destruct Hinw as [Hq | Hinw];
        [ injection Hq as <- <- <-; cbn [base_val] in Hr;
          first [ lia | rewrite (U9 Ex ltac:(f5_agree)) in Hr; unfold f5_rw; lia ] | ]);
      destruct Hinw
    | clear MEQ HFr; rename MEQ' into MEQ ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* 168(s1) at a stop, read off the final state's cell region (index 1) *)
Ltac f5_slotv v HR V U9 :=
  lazymatch type of HR with region_ok _ ?Ex ?m (YP09.mkRegion (Some 9%nat) _ _ _ _ ?cs) =>
  lazymatch cs with context [YP09.mkChunk 168 (CVal 8 ?e)] =>
    pose proof (f5_slot_of_region Ex m (mf_s1 (mv_sp v)) cs e (U Ex e) HR (U9 Ex ltac:(f5_agree))
      ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl) as V
  end end.
(* a goal U Ex e = x from the pass's atom table UXL *)
Ltac f5_uxa UXL :=
  lazymatch goal with |- U ?Ex _ = _ =>
    let UXq := fresh "UXq" in pose proof (UXL Ex ltac:(f5_agree)) as UXq;
    repeat match type of UXq with _ /\ _ => let Ua := fresh "Ua" in destruct UXq as [Ua UXq] end;
    first [assumption | exact UXq] end.

Section iter.
(* one pass at index i = S i' > 0 *)
Variables (n i' : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HST : FR_ST_stmt B n.
Hypothesis HNX : FR_CL_stmt B n (S (S i')).
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short v regs1 memc Wc line p rest.
Hypothesis S176 : mf_slot v memc Wc 176 p.
Hypothesis S168 : mf_slot v memc Wc 168 (p + Z.of_nat (length (mf_line rest))).
Hypothesis R10 : getr regs1 10 = w64 (p + Z.of_nat (length (mf_line rest))).
Hypothesis R16 : getr regs1 16 = w64 0x20.
Hypothesis R26 : getr regs1 26 = w64 (p + Z.of_nat (S i')).
Hypothesis R11 : getr regs1 11 = w64 (p + Z.of_nat (S i')).
Hypothesis R13 : getr regs1 13 = w64 (- Z.of_nat (S i')).
Hypothesis Hi : (S i' < length (mf_line rest))%nat.
Hypothesis Hcut : forall k, (k < S i')%nat -> cut_at (mf_line rest) k = false.

Definition f5_bi : Z := nth (S i') (mf_line rest) 0.
Definition f5_bj : Z := nth (S i' - 1) (mf_line rest) 0.
Definition f5_E : env := Eimg (Ereg regs1 [Z_to_bv 64 f5_bi; Z_to_bv 64 f5_bj]).

Lemma f5_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\
  0 <= f5_bi < 256 /\ 0 <= f5_bj < 256 /\ (length (mf_line rest) < 512)%nat.
Proof.
destruct (f5_text_facts v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & BY & BR8 & RAD).
pose proof (fr_line_len rest) as HLL. pose proof SH as (_ & _ & _ & HL512).
split; [exact H1|]. split; [lia|]. split; [apply BR8; exact Hi|]. split; [apply BR8; lia | exact HL512].
Qed.
Lemma f5_bytes : rdW Wc memc (p + Z.of_nat (S i')) = Some f5_bi /\ rdW Wc memc (p + Z.of_nat i') = Some f5_bj.
Proof.
destruct (f5_text_facts v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & BY & _ & _).
split; [exact (BY _ Hi)|]. unfold f5_bj. replace (S i' - 1)%nat with i' by lia. apply BY. lia.
Qed.
Lemma f5_rad : forall x, p <= x < p + Z.of_nat (length (mf_line rest)) ->
  range_addressable (rdW Wc memc) SHADOW_OFF x 1.
Proof.
destruct (f5_text_facts v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & RAD).
pose proof (fr_line_len rest) as HLL. intros x Hx y Hy. apply RAD. lia.
Qed.
Lemma f5_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew f5_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold f5_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma f5_HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 f5_bi; Z_to_bv 64 f5_bj]) f5_E.
Proof. unfold f5_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* s1 at any later environment of the pass (its fresh atoms are 1024 and up) *)
Lemma f5_U9 : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew f5_E k) -> bv_unsigned (ew Ex 9) = mf_s1 (mv_sp v).
Proof.
intros Ex HEx. destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (Q1 & Q2 & _ & _ & _ & _ & R9 & _).
rewrite HEx by lia. rewrite (f5_EN 9%nat 9%bv eq_refl) by lia. rewrite R9. unfold w64. apply unsigned_lit_small. lia.
Qed.
(* the atoms' values at any later environment of the pass *)
Lemma f5_UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew f5_E k) ->
  U Ex (SOff 32 0) = f5_bi /\ U Ex (SOff 33 0) = f5_bj /\ U Ex (SOff 13 0) = 2 ^ 64 - Z.of_nat (S i') /\
  U Ex (SOff 26 1) = p + Z.of_nat (S i') + 1 /\ U Ex (SOff 10 0) = p + Z.of_nat (length (mf_line rest)) /\
  U Ex (SOff 26 0) = p + Z.of_nat (S i') /\ U Ex (SOff 11 0) = p + Z.of_nat (S i') /\
  U Ex (SOff 11 (-1)) = p + Z.of_nat (S i') - 1 /\ U Ex (SOff 18 0) = SHADOW_OFF.
Proof.
intros Ex HEx. pose proof f5_tf as (T1 & T2 & T5 & T6 & T7).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (fr_line_len rest) as HLL.
destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & _ & _ & _ & R18).
assert (E13 : ew f5_E 13 = Z_to_bv 64 (2 ^ 64 - Z.of_nat (S i'))).
{ rewrite (f5_EN 13%nat 13%bv eq_refl) by lia. rewrite R13. unfold w64. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- (Z_mod_plus_full (- Z.of_nat (S i')) 1). f_equal; lia. }
assert (E32 : ew f5_E 32 = Z_to_bv 64 f5_bi)
  by (unfold f5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew f5_E 33 = Z_to_bv 64 f5_bj)
  by (unfold f5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
split; [apply U_atom; [rewrite HEx by lia; exact E32 | lia]|].
split; [apply U_atom; [rewrite HEx by lia; exact E33 | lia]|].
split; [apply U_atom; [rewrite HEx by lia; exact E13 | lia]|].
split; [apply f5_U_atom_off; [rewrite HEx, (f5_EN 26%nat 26%bv eq_refl) by lia; exact R26 | lia | lia]|].
split; [apply U_atom; [rewrite HEx, (f5_EN 10%nat 10%bv eq_refl) by lia; exact R10 | lia]|].
split; [apply U_atom; [rewrite HEx, (f5_EN 26%nat 26%bv eq_refl) by lia; exact R26 | lia]|].
split; [apply U_atom; [rewrite HEx, (f5_EN 11%nat 11%bv eq_refl) by lia; exact R11 | lia]|].
split; [apply f5_U_atom_off; [rewrite HEx, (f5_EN 11%nat 11%bv eq_refl) by lia; exact R11 | lia | lia]|].
apply U_atom; [rewrite HEx, (f5_EN 18%nat 18%bv eq_refl) by lia; exact R18 | unfold SHADOW_OFF; lia].
Qed.
(* the cut at i = S i' as the bytes decide it *)
Lemma f5_CUTP : (f5_bi = 59 \/ f5_bi = 35) -> (f5_bj = 9 \/ f5_bj = 32) -> cut_at (mf_line rest) (S i') = true.
Proof.
intros Hm Hs. unfold cut_at. fold f5_bi. fold f5_bj.
unfold is_mark, sp_tab. destruct Hm as [-> | ->]; destruct Hs as [-> | ->]; reflexivity.
Qed.
Lemma f5_CUTN1 : f5_bi <> 59 -> f5_bi <> 35 -> cut_at (mf_line rest) (S i') = false.
Proof.
intros H1 H2. unfold cut_at. fold f5_bi. unfold is_mark.
rewrite (proj2 (Z.eqb_neq f5_bi 35) H2), (proj2 (Z.eqb_neq f5_bi 59) H1). reflexivity.
Qed.
Lemma f5_CUTN2 : f5_bj <> 9 -> f5_bj <> 32 -> cut_at (mf_line rest) (S i') = false.
Proof.
intros H1 H2. unfold cut_at. fold f5_bj. unfold sp_tab.
rewrite (proj2 (Z.eqb_neq f5_bj 32) H2), (proj2 (Z.eqb_neq f5_bj 9) H1). apply andb_false_r.
Qed.
(* the pass's start state *)
Lemma f5_seed : st_ok_pi SEGS VAL f5_E
  (mkSS FR_CL (sr_set sr_atoms (16%bv : bv 5) (SLit 32)) [f5_text1; f5_slot] None f5_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_CL)) memc (seg_rom SEGS))).
Proof.
pose proof f5_tf as (T1 & T2 & T5 & T6 & T7). pose proof f5_bytes as (BY1 & BY0).
destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (Q1 & Q2 & Q3 & Q4 & Q5 & QW & R9 & R18).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (fr_line_len rest) as HLL.
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL f5_E (mkSS FR_CL sr_atoms [f5_text1; f5_slot] None f5_facts)
  (mkst regs1 (Z_to_bv 64 (BASE + FR_CL)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  + unfold f5_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * unfold region_ok, f5_text1.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (f5_EN 26%nat 26%bv eq_refl), R26 by lia. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS f5_E _ (p + Z.of_nat (S i')) (-1) 1 (SOff 33 0) f5_bj);
           [cbn [sv_denot]; unfold f5_E; rewrite Eimg_low by (unfold A_TEXT; lia);
            rewrite (ew_Ereg_extra regs1 _ 1); cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | cbn; lia | cbn; lia |].
         replace (p + Z.of_nat (S i') + -1) with (p + Z.of_nat i') by lia. exact (mf_val1_of_aview _ _ _ _ BY0).
      -- apply (chunk_ok_val SEGS f5_E _ (p + Z.of_nat (S i')) 0 1 (SOff 32 0) f5_bi);
           [cbn [sv_denot]; unfold f5_E; rewrite Eimg_low by (unfold A_TEXT; lia);
            rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | cbn; lia | cbn; lia |].
         rewrite Z.add_0_r. exact (mf_val1_of_aview _ _ _ _ BY1).
    * unfold region_ok, f5_slot.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (f5_EN 9%nat 9%bv eq_refl), R9 by lia. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply QW; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS f5_E _ (mf_s1 (mv_sp v)) 168 8 (SOff 10 0) (p + Z.of_nat (length (mf_line rest))));
        [cbn [sv_denot]; rewrite (f5_EN 10%nat 10%bv eq_refl), R10 by lia; unfold w64;
         rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | cbn; lia | cbn; lia | exact S168].
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, f5_text1, f5_slot.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (f5_EN 26%nat 26%bv eq_refl), (f5_EN 9%nat 9%bv eq_refl), R26, R9 by lia. unfold w64.
    rewrite !unsigned_lit_small by lia. repeat split; first [exact I | lia].
  + split; [|split; [exact I | exact I]].
    cbn [f5_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite (f5_EN 9%nat 9%bv eq_refl), (f5_EN 11%nat 11%bv eq_refl), (f5_EN 26%nat 26%bv eq_refl),
      (f5_EN 18%nat 18%bv eq_refl) by lia.
    rewrite R9, R11, R26, R18. unfold f5_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_extra regs1 _ 0), (ew_Ereg_extra regs1 _ 1). cbn [nth].
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB, SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; try exact Q3; lia. }
exact (st_ok_pi_pin_reg' f5_E _ _ (16%bv : bv 5) 32 HS0 R16 eq_refl).
Qed.

(* the pass's tactics over this Section's facts *)
Ltac f5_obl :=
  lazymatch goal with
  | MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> aview _ _ _ a = aview _ _ memc a
    |- range_addressable _ (U ?Ex (SOff 18 0)) (U ?Ex ?x) _ =>
    let UXO := fresh "UXO" in pose proof (f5_UX Ex ltac:(f5_agree)) as UXO;
    let U11 := fresh "U11" in let U11m := fresh "U11m" in let U18 := fresh "U18" in
    destruct UXO as (_ & _ & _ & _ & _ & _ & U11 & U11m & U18);
    rewrite <- (aview_rd_of SEGS); rewrite U18; rewrite ?U11, ?U11m;
    pose proof (fr_line_len rest); pose proof Hi;
    apply (f5_ra_eq (aview SEGS (w_H Wc) memc));
    [ let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy;
      let Hs1 := fresh "Hs1" in let Hs2 := fresh "Hs2" in
      destruct (f5_sh_apart v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n y CTX ltac:(lia)) as [Hs1 Hs2];
      exact (MEQ _ Hs1 Hs2)
    | apply f5_rad; lia ]
  end.
Ltac f5_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (f5_awr v f5_U9; fail); try (f5_obl; fail); f5_meq f5_U9 end.
Ltac f5_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (f5_awr v f5_U9; fail); try (f5_obl; fail); f5_meq f5_U9 end.
Ltac f5_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
(* the branch condition Hc as a fact of the atoms' values *)
Ltac f5_cond :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = _ |- _ =>
    let UXc := fresh "UXc" in pose proof (f5_UX Ex ltac:(f5_agree)) as UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in let a3 := fresh "a" in let a4 := fresh "a" in
    let a5 := fresh "a" in let a6 := fresh "a" in let a7 := fresh "a" in let a8 := fresh "a" in
    let a9 := fresh "a" in
    destruct UXc as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9);
    rewrite ?branch_eq_U, ?branch_ne_U in Hc;
    rewrite ?a1, ?a2, ?a3, ?a4, ?a5, ?a6, ?a7, ?a8, ?a9 in Hc;
    repeat match type of Hc with context [U Ex (SLit ?z)] => rewrite (U_lit Ex z) in Hc by lia end;
    clear a1 a2 a3 a4 a5 a6 a7 a8 a9
  end.
(* a stop: the kept registers HK and 168(s1) (V) at the final state; K proves the stop's statement *)
Ltac f5_leaf K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 f5_bi; Z_to_bv 64 f5_bj]) Ecur) by (env_agree_chain f5_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (F5_KEPT ++ [10]%bv) HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let HR := fresh "HR" in pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR; cbn [restrict ms_mem] in HR;
    let V := fresh "V" in f5_slotv v HR V f5_U9;
    pmkst HS;
    K HS HK V HJ MEQ
  end.
(* the two exits of a pass that found no cut at its index (HNC): the next index, or the line's end *)
Ltac f5_nomark HNC :=
  f5_run; f5_branch;
  [ f5_cond; lazymatch goal with Hc : negb _ = true |- _ => apply Bool.negb_true_iff, Z.eqb_neq in Hc end;
    f5_runto FR_CL;
    f5_leaf ltac:(fun HS HK V HJ MEQ =>
      pose proof f5_tf as (T1 & T2 & T5 & T6 & T7);
      pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _); unfold YG0f.ASAN_CEIL in CR1, CR2;
      pose proof (fr_line_len rest);
      eapply (f5_leaf_cl n (S (S i')) v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest _ _ _ _ HNX CTX SH S176 HJ MEQ
        (fun r Hr => HK r (in_or_app _ _ _ (or_introl Hr))) V);
      first
      [ f5_uxa f5_UX
      | rewrite (HK 10%bv ltac:(cbv; tauto)); exact R10
      | let R := fresh in prreg HS (16%bv : bv 5) R; rewrite R; reflexivity
      | let R := fresh in prreg HS (26%bv : bv 5) R; rewrite R, (f5_EN 26%nat 26%bv eq_refl), R26 by lia; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia
      | let R := fresh in prreg HS (11%bv : bv 5) R; rewrite R, (f5_EN 11%nat 11%bv eq_refl), R11 by lia; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia
      | let R := fresh in prreg HS (13%bv : bv 5) R; rewrite R, (f5_EN 13%nat 13%bv eq_refl), R13 by lia; unfold w64;
        apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
        rewrite Zplus_mod_idemp_l; f_equal; lia
      | lia
      | intros ?k ?Hk; destruct (Nat.eq_dec k (S i')) as [->|?]; [exact HNC | apply Hcut; lia] ])
  | f5_cond; lazymatch goal with Hc : negb _ = false |- _ => apply Bool.negb_false_iff, Z.eqb_eq in Hc end;
    let HALL := fresh "HALL" in
    assert (HALL : forall k, (k < length (mf_line rest))%nat -> cut_at (mf_line rest) k = false)
      by (intros ?k ?Hk; destruct (Nat.eq_dec k (S i')) as [->|?]; [exact HNC | apply Hcut; lia]);
    let HEQC := fresh "HEQC" in
    assert (HEQC : fr_C rest = length (mf_line rest)) by (unfold fr_C, fr_cut; exact (proj2 (fr_cut_all _ HALL)));
    f5_runto FR_ST;
    f5_leaf ltac:(fun HS HK V HJ MEQ =>
      eapply (f5_leaf_st n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest _ _ _ _ HST CTX SH S176 HJ MEQ
        (fun r Hr => HK r (in_or_app _ _ _ (or_introl Hr))) V);
      rewrite HEQC; f5_uxa f5_UX) ].
(* a cut at i: the store 168(s1) = s10 = p + i, the stop at FR_ST with C = S i' *)
Ltac f5_cut HCT :=
  let HCL := fresh "HCL" in pose proof (fr_cut_at_first _ _ Hi Hcut HCT) as [_ HCL];
  let HEQC := fresh "HEQC" in assert (HEQC : fr_C rest = S i') by (unfold fr_C, fr_cut; exact HCL);
  f5_runto FR_ST;
  f5_leaf ltac:(fun HS HK V HJ MEQ =>
    eapply (f5_leaf_st n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest _ _ _ _ HST CTX SH S176 HJ MEQ
      (fun r Hr => HK r (in_or_app _ _ _ (or_introl Hr))) V);
    rewrite HEQC; f5_uxa f5_UX).
(* a pass whose byte is ';' or '#' (HM): a3 = -i is not 0 (the `beqz a3` 0x86454 refuted), the trap 0x8645c is
   decided not taken by the run, the byte before is checked and loaded and tested for ' ' then '\t' *)
Ltac f5_mark HM :=
  f5_run; f5_branch;
  [ f5_cond; lazymatch goal with Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc end;
    exfalso; pose proof Hi; pose proof f5_tf as (_ & _ & _ & _ & ?T7); lia
  | f5_run; f5_branch;
    [ f5_cond; lazymatch goal with Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc;
        f5_cut (f5_CUTP HM (or_intror Hc)) end
    | f5_cond; lazymatch goal with Hc : (_ =? _) = false |- _ => apply Z.eqb_neq in Hc;
        let H32 := fresh "H32" in rename Hc into H32;
        f5_run; f5_branch;
        [ f5_cond; lazymatch goal with Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc;
            f5_cut (f5_CUTP HM (or_introl Hc)) end
        | f5_cond; lazymatch goal with Hc : (_ =? _) = false |- _ => apply Z.eqb_neq in Hc;
            f5_nomark (f5_CUTN2 Hc H32) end ] end ] ].

Lemma f5_step_S : mf_at B v Wc regs1 memc mdc FR_CL.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof f5_seed as HS.
assert (HEI : img_env VAL A_LIM f5_E) by (unfold f5_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] f5_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a)
  by (intros; reflexivity).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
unfold mf_at.
f5_run; f5_branch.
- f5_cond. apply Z.eqb_eq in Hc. f5_mark (or_introl (B := f5_bi = 35) Hc).
- f5_cond. apply Z.eqb_neq in Hc. rename Hc into H59.
  f5_run; f5_branch.
  + f5_cond. apply Bool.negb_true_iff, Z.eqb_neq in Hc. f5_nomark (f5_CUTN1 H59 Hc).
  + f5_cond. apply Bool.negb_false_iff, Z.eqb_eq in Hc. f5_mark (or_intror (A := f5_bi = 59) Hc).
Qed.
End iter.

Section iter0.
(* the pass at index 0: no byte before it; a3 = 0, so a mark is a cut at 0 (the `beqz a3` 0x86454 decided taken) *)
Variables (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HST : FR_ST_stmt B n.
Hypothesis HNX : FR_CL_stmt B n 1.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis SH : fr_short v regs1 memc Wc line p rest.
Hypothesis S176 : mf_slot v memc Wc 176 p.
Hypothesis S168 : mf_slot v memc Wc 168 (p + Z.of_nat (length (mf_line rest))).
Hypothesis R10 : getr regs1 10 = w64 (p + Z.of_nat (length (mf_line rest))).
Hypothesis R16 : getr regs1 16 = w64 0x20.
Hypothesis R26 : getr regs1 26 = w64 (p + Z.of_nat 0).
Hypothesis R11 : getr regs1 11 = w64 (p + Z.of_nat 0).
Hypothesis R13 : getr regs1 13 = w64 (- Z.of_nat 0).
Hypothesis Hi : (0 < length (mf_line rest))%nat.

Definition f5z_b : Z := nth 0 (mf_line rest) 0.
Definition f5z_E : env := Eimg (Ereg regs1 [Z_to_bv 64 f5z_b; Z_to_bv 64 0]).

Lemma f5z_tf : 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) + 1 <= alloc_ceiling /\ 0 <= f5z_b < 256 /\
  (length (mf_line rest) < 512)%nat /\ rdW Wc memc p = Some f5z_b.
Proof.
destruct (f5_text_facts v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & BY & BR8 & RAD).
pose proof (fr_line_len rest) as HLL. pose proof SH as (_ & _ & _ & HL512).
split; [exact H1|]. split; [lia|]. split; [apply BR8; exact Hi|]. split; [exact HL512|].
pose proof (BY 0%nat Hi) as B0. rewrite Z.add_0_r in B0. exact B0.
Qed.
Lemma f5z_rad : forall x, p <= x < p + Z.of_nat (length (mf_line rest)) ->
  range_addressable (rdW Wc memc) SHADOW_OFF x 1.
Proof.
destruct (f5_text_facts v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & RAD).
pose proof (fr_line_len rest) as HLL. intros x Hx y Hy. apply RAD. lia.
Qed.
Lemma f5z_EN : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew f5z_E k = getr regs1 r.
Proof. intros k r Hk Hk32. unfold f5z_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. Qed.
Lemma f5z_HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 f5z_b; Z_to_bv 64 0]) f5z_E.
Proof. unfold f5z_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma f5z_U9 : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew f5z_E k) -> bv_unsigned (ew Ex 9) = mf_s1 (mv_sp v).
Proof.
intros Ex HEx. destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (Q1 & Q2 & _ & _ & _ & _ & R9 & _).
rewrite HEx by lia. rewrite (f5z_EN 9%nat 9%bv eq_refl) by lia. rewrite R9. unfold w64. apply unsigned_lit_small. lia.
Qed.
Lemma f5z_UX : forall Ex, (forall k, (k < 1024)%nat -> ew Ex k = ew f5z_E k) ->
  U Ex (SOff 32 0) = f5z_b /\ U Ex (SOff 26 1) = p + Z.of_nat 0 + 1 /\
  U Ex (SOff 10 0) = p + Z.of_nat (length (mf_line rest)) /\ U Ex (SOff 26 0) = p + Z.of_nat 0 /\
  U Ex (SOff 11 0) = p + Z.of_nat 0 /\ U Ex (SOff 18 0) = SHADOW_OFF.
Proof.
intros Ex HEx. pose proof f5z_tf as (T1 & T2 & T4 & T5 & _).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (fr_line_len rest) as HLL.
destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (_ & _ & _ & _ & _ & _ & _ & R18).
split; [apply U_atom; [rewrite HEx by lia; unfold f5z_E; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs1 _ 0) | lia]|].
split; [apply f5_U_atom_off; [rewrite HEx, (f5z_EN 26%nat 26%bv eq_refl) by lia; exact R26 | lia | lia]|].
split; [apply U_atom; [rewrite HEx, (f5z_EN 10%nat 10%bv eq_refl) by lia; exact R10 | lia]|].
split; [apply U_atom; [rewrite HEx, (f5z_EN 26%nat 26%bv eq_refl) by lia; exact R26 | lia]|].
split; [apply U_atom; [rewrite HEx, (f5z_EN 11%nat 11%bv eq_refl) by lia; exact R11 | lia]|].
apply U_atom; [rewrite HEx, (f5z_EN 18%nat 18%bv eq_refl) by lia; exact R18 | unfold SHADOW_OFF; lia].
Qed.
Lemma f5z_CUTP : (f5z_b = 59 \/ f5z_b = 35) -> cut_at (mf_line rest) 0 = true.
Proof. intros Hm. unfold cut_at. fold f5z_b. unfold is_mark. destruct Hm as [-> | ->]; reflexivity. Qed.
Lemma f5z_CUTN : f5z_b <> 59 -> f5z_b <> 35 -> cut_at (mf_line rest) 0 = false.
Proof.
intros H1 H2. unfold cut_at. fold f5z_b. unfold is_mark.
rewrite (proj2 (Z.eqb_neq f5z_b 35) H2), (proj2 (Z.eqb_neq f5z_b 59) H1). reflexivity.
Qed.
Lemma f5z_seed : st_ok_pi SEGS VAL f5z_E
  (mkSS FR_CL (sr_set (sr_set sr_atoms (16%bv : bv 5) (SLit 32)) (13%bv : bv 5) (SLit 0)) [f5_text0; f5_slot] None
    f5_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + FR_CL)) memc (seg_rom SEGS))).
Proof.
pose proof f5z_tf as (T1 & T2 & T4 & T5 & BY0).
destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (Q1 & Q2 & Q3 & Q4 & Q5 & QW & R9 & R18).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (fr_line_len rest) as HLL.
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL f5z_E (mkSS FR_CL sr_atoms [f5_text0; f5_slot] None f5_facts)
  (mkst regs1 (Z_to_bv 64 (BASE + FR_CL)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ apply pa_entry_st_ok_full.
  + unfold f5z_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * unfold region_ok, f5_text0.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (f5z_EN 26%nat 26%bv eq_refl), R26 by lia. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS f5z_E _ (p + Z.of_nat 0) 0 1 (SOff 32 0) f5z_b);
        [cbn [sv_denot]; unfold f5z_E; rewrite Eimg_low by (unfold A_TEXT; lia);
         rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; lia | cbn; lia |].
      replace (p + Z.of_nat 0 + 0) with p by lia. exact (mf_val1_of_aview _ _ _ _ BY0).
    * unfold region_ok, f5_slot.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (f5z_EN 9%nat 9%bv eq_refl), R9 by lia. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply QW; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS f5z_E _ (mf_s1 (mv_sp v)) 168 8 (SOff 10 0) (p + Z.of_nat (length (mf_line rest))));
        [cbn [sv_denot]; rewrite (f5z_EN 10%nat 10%bv eq_refl), R10 by lia; unfold w64;
         rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | cbn; lia | cbn; lia | exact S168].
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, f5_text0, f5_slot.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (f5z_EN 26%nat 26%bv eq_refl), (f5z_EN 9%nat 9%bv eq_refl), R26, R9 by lia. unfold w64.
    rewrite !unsigned_lit_small by lia. repeat split; first [exact I | lia].
  + split; [|split; [exact I | exact I]].
    cbn [f5_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite (f5z_EN 9%nat 9%bv eq_refl), (f5z_EN 11%nat 11%bv eq_refl), (f5z_EN 26%nat 26%bv eq_refl),
      (f5z_EN 18%nat 18%bv eq_refl) by lia.
    rewrite R9, R11, R26, R18. unfold f5z_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_extra regs1 _ 0), (ew_Ereg_extra regs1 _ 1). cbn [nth].
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB, SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; try exact Q3; lia. }
pose proof (st_ok_pi_pin_reg' f5z_E _ _ (16%bv : bv 5) 32 HS0 R16 eq_refl) as HS1.
exact (st_ok_pi_pin_reg' f5z_E _ _ (13%bv : bv 5) 0 HS1 R13 eq_refl).
Qed.

Ltac f5z_obl :=
  lazymatch goal with
  | MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> aview _ _ _ a = aview _ _ memc a
    |- range_addressable _ (U ?Ex (SOff 18 0)) (U ?Ex ?x) _ =>
    let UXO := fresh "UXO" in pose proof (f5z_UX Ex ltac:(f5_agree)) as UXO;
    let U11 := fresh "U11" in let U18 := fresh "U18" in
    destruct UXO as (_ & _ & _ & _ & U11 & U18);
    rewrite <- (aview_rd_of SEGS); rewrite U18; rewrite ?U11;
    pose proof (fr_line_len rest); pose proof Hi;
    apply (f5_ra_eq (aview SEGS (w_H Wc) memc));
    [ let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy;
      let Hs1 := fresh "Hs1" in let Hs2 := fresh "Hs2" in
      destruct (f5_sh_apart v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n y CTX ltac:(lia)) as [Hs1 Hs2];
      exact (MEQ _ Hs1 Hs2)
    | apply f5z_rad; lia ]
  end.
Ltac f5z_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (f5_awr v f5z_U9; fail); try (f5z_obl; fail); f5_meq f5z_U9 end.
Ltac f5z_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (f5_awr v f5z_U9; fail); try (f5z_obl; fail); f5_meq f5z_U9 end.
Ltac f5z_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
Ltac f5z_cond :=
  lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = _ |- _ =>
    let UXc := fresh "UXc" in pose proof (f5z_UX Ex ltac:(f5_agree)) as UXc;
    let a1 := fresh "a" in let a2 := fresh "a" in let a3 := fresh "a" in let a4 := fresh "a" in
    let a5 := fresh "a" in let a6 := fresh "a" in
    destruct UXc as (a1 & a2 & a3 & a4 & a5 & a6);
    rewrite ?branch_eq_U, ?branch_ne_U in Hc;
    rewrite ?a1, ?a2, ?a3, ?a4, ?a5, ?a6 in Hc;
    repeat match type of Hc with context [U Ex (SLit ?z)] => rewrite (U_lit Ex z) in Hc by lia end;
    clear a1 a2 a3 a4 a5 a6
  end.
Ltac f5z_leaf K :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> aview _ _ _ a = aview _ _ memc a |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 f5z_b; Z_to_bv 64 0]) Ecur) by (env_agree_chain f5z_HAE);
    let HK := fresh "HK" in
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ (F5_KEPT ++ [10]%bv) HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2;
    let HR := fresh "HR" in pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR; cbn [restrict ms_mem] in HR;
    let V := fresh "V" in f5_slotv v HR V f5z_U9;
    pmkst HS;
    K HS HK V HJ MEQ
  end.
Ltac f5z_cut HCT :=
  let HCL := fresh "HCL" in
  pose proof (fr_cut_at_first _ _ Hi ltac:(intros ?k ?Hk; lia) HCT) as [_ HCL];
  let HEQC := fresh "HEQC" in assert (HEQC : fr_C rest = 0%nat) by (unfold fr_C, fr_cut; exact HCL);
  f5z_runto FR_ST;
  f5z_leaf ltac:(fun HS HK V HJ MEQ =>
    eapply (f5_leaf_st n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest _ _ _ _ HST CTX SH S176 HJ MEQ
      (fun r Hr => HK r (in_or_app _ _ _ (or_introl Hr))) V);
    rewrite HEQC; f5_uxa f5z_UX).
Ltac f5z_nomark HNC :=
  f5z_run; f5z_branch;
  [ f5z_cond; lazymatch goal with Hc : negb _ = true |- _ => apply Bool.negb_true_iff, Z.eqb_neq in Hc end;
    f5z_runto FR_CL;
    f5z_leaf ltac:(fun HS HK V HJ MEQ =>
      pose proof f5z_tf as (T1 & T2 & T4 & T5 & _);
      pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _); unfold YG0f.ASAN_CEIL in CR1, CR2;
      pose proof (fr_line_len rest);
      eapply (f5_leaf_cl n 1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest _ _ _ _ HNX CTX SH S176 HJ MEQ
        (fun r Hr => HK r (in_or_app _ _ _ (or_introl Hr))) V);
      first
      [ f5_uxa f5z_UX
      | rewrite (HK 10%bv ltac:(cbv; tauto)); exact R10
      | let R := fresh in prreg HS (16%bv : bv 5) R; rewrite R; reflexivity
      | let R := fresh in prreg HS (26%bv : bv 5) R; rewrite R, (f5z_EN 26%nat 26%bv eq_refl), R26 by lia; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia
      | let R := fresh in prreg HS (11%bv : bv 5) R; rewrite R, (f5z_EN 11%nat 11%bv eq_refl), R11 by lia; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia
      | let R := fresh in prreg HS (13%bv : bv 5) R; rewrite R; unfold w64; apply bv_eq; vm_compute; reflexivity
      | lia
      | intros ?k ?Hk; replace k with 0%nat by lia; exact HNC ])
  | f5z_cond; lazymatch goal with Hc : negb _ = false |- _ => apply Bool.negb_false_iff, Z.eqb_eq in Hc end;
    let HALL := fresh "HALL" in
    assert (HALL : forall k, (k < length (mf_line rest))%nat -> cut_at (mf_line rest) k = false)
      by (intros ?k ?Hk; replace k with 0%nat by lia; exact HNC);
    let HEQC := fresh "HEQC" in
    assert (HEQC : fr_C rest = length (mf_line rest)) by (unfold fr_C, fr_cut; exact (proj2 (fr_cut_all _ HALL)));
    f5z_runto FR_ST;
    f5z_leaf ltac:(fun HS HK V HJ MEQ =>
      eapply (f5_leaf_st n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest _ _ _ _ HST CTX SH S176 HJ MEQ
        (fun r Hr => HK r (in_or_app _ _ _ (or_introl Hr))) V);
      rewrite HEQC; f5_uxa f5z_UX) ].

Lemma f5z_step : mf_at B v Wc regs1 memc mdc FR_CL.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _).
pose proof f5z_seed as HS.
assert (HEI : img_env VAL A_LIM f5z_E) by (unfold f5z_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 18 0) [] f5z_E (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ f5_rw v a -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a)
  by (intros; reflexivity).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
destruct (f5_s1 v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
unfold mf_at.
f5z_run; f5z_branch.
- f5z_cond. apply Z.eqb_eq in Hc. f5z_cut (f5z_CUTP (or_introl Hc)).
- f5z_cond. apply Z.eqb_neq in Hc. rename Hc into H59.
  f5z_run; f5z_branch.
  + f5z_cond. apply Bool.negb_true_iff, Z.eqb_neq in Hc. f5z_nomark (f5z_CUTN H59 Hc).
  + f5z_cond. apply Bool.negb_false_iff, Z.eqb_eq in Hc. f5z_cut (f5z_CUTP (or_intror Hc)).
Qed.
End iter0.

Lemma f5_cl_step : forall n i, FR_ST_stmt B n -> FR_CL_stmt B n (S i) -> FR_CL_stmt B n i.
Proof.
intros n i HST HNX v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX SH S176 S168 R10 R16 R26 R11 R13 Hi Hcut.
destruct i as [|i'].
- exact (f5z_step n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest HST HNX CTX SH S176 S168 R10 R16 R26 R11 R13 Hi).
- exact (f5_step_S n i' v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest HST HNX CTX SH S176 S168 R10 R16 R26 R11 R13
    Hi Hcut).
Qed.
(* every index of the comment loop, from FR_ST (by induction on 512 - i: a line here is shorter than 512) *)
Lemma fr_cl : forall n, FR_ST_stmt B n -> forall i, FR_CL_stmt B n i.
Proof.
intros n HST.
assert (HD : forall d i, (512 - d <= i)%nat -> FR_CL_stmt B n i).
{ induction d as [|d IH]; intros i Hd.
  - intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX SH. destruct SH as (_ & _ & _ & HL). intros. lia.
  - destruct (Nat.le_gt_cases (512 - d) i) as [Hle | Hlt]; [exact (IH i Hle)|].
    apply f5_cl_step; [exact HST | apply IH; lia]. }
intros i. apply (HD 512%nat i). lia.
Qed.
End e.
End f.
End d.

About fr_cl. Print Assumptions fr_cl.
